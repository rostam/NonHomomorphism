//! Agent Q: alpha-profiles of large targets against a small test basis.
//! alpha(T, H) = min #edges of T broken by a map V(T) -> V(H).
//! Branch and bound: T small (<= 16 v), H up to 128 v (u128 rows).
use nonhom_param as np;
use rayon::prelude::*;
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, Ordering};
use std::time::{Duration, Instant};

#[derive(Clone)]
struct G {
    n: usize,
    adj: Vec<u128>,
}
impl G {
    fn new(n: usize) -> G {
        assert!(n <= 128);
        G { n, adj: vec![0; n] }
    }
    fn add(&mut self, u: usize, v: usize) {
        assert!(u != v);
        self.adj[u] |= 1u128 << v;
        self.adj[v] |= 1u128 << u;
    }
    fn has(&self, u: usize, v: usize) -> bool {
        (self.adj[u] >> v) & 1 == 1
    }
    fn m(&self) -> usize {
        self.adj.iter().map(|x| x.count_ones() as usize).sum::<usize>() / 2
    }
    fn deg(&self, u: usize) -> u32 {
        self.adj[u].count_ones()
    }
    fn from(g: &np::Graph) -> G {
        let mut h = G::new(g.n);
        for (u, v) in g.edges() {
            h.add(u, v);
        }
        h
    }
}

fn kneser(n: usize, k: usize) -> G {
    let s = np::k_subsets(n, k);
    let mut g = G::new(s.len());
    for i in 0..s.len() {
        for j in i + 1..s.len() {
            if s[i] & s[j] == 0 {
                g.add(i, j);
            }
        }
    }
    g
}
fn chvatal() -> G {
    let l: [&[usize]; 10] = [&[1, 4, 6, 9], &[2, 5, 7], &[3, 6, 8], &[4, 7, 9], &[5, 8], &[10, 11], &[10, 11], &[8, 11], &[10], &[10, 11]];
    let mut g = G::new(12);
    for (u, ns) in l.iter().enumerate() {
        for &v in *ns {
            g.add(u, v);
        }
    }
    g
}
fn clebsch() -> G {
    let mut g = G::new(16);
    for u in 0..16usize {
        for v in u + 1..16 {
            let d = (u ^ v).count_ones();
            if d == 1 || d == 4 {
                g.add(u, v);
            }
        }
    }
    g
}
fn circ(n: usize, j: &[usize]) -> G {
    let mut g = G::new(n);
    for i in 0..n {
        for &s in j {
            let k = (i + s) % n;
            if !g.has(i, k) && i != k {
                g.add(i, k);
            }
        }
    }
    g
}
fn wheel(k: usize) -> G {
    let mut g = circ(k, &[1]);
    let mut h = G::new(k + 1);
    for u in 0..k {
        for v in u + 1..k {
            if g.has(u, v) {
                h.add(u, v);
            }
        }
        h.add(u, k);
    }
    g = h;
    g
}
fn gnp(n: usize, p: f64, seed: u64) -> G {
    let mut r = Rng(seed.wrapping_mul(0x9E3779B97F4A7C15) | 1);
    let mut g = G::new(n);
    for u in 0..n {
        for v in u + 1..n {
            if r.f() < p {
                g.add(u, v);
            }
        }
    }
    g
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn f(&mut self) -> f64 {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// Iterated min-conflicts local search: an upper bound on alpha(T,H).
fn local_search(t: &G, h: &G, iters: usize, seed: u64) -> u32 {
    let mut r = Rng(seed | 1);
    let mut best = t.m() as u32;
    let mut map: Vec<usize> = (0..t.n).map(|_| r.below(h.n)).collect();
    let cost = |map: &Vec<usize>| -> u32 {
        let mut c = 0;
        for u in 0..t.n {
            for v in u + 1..t.n {
                if t.has(u, v) && !h.has(map[u], map[v]) {
                    c += 1;
                }
            }
        }
        c
    };
    for it in 0..iters {
        // descend
        loop {
            let mut improved = false;
            for u in 0..t.n {
                let cur = (0..t.n).filter(|&v| t.has(u, v) && !h.has(map[u], map[v])).count();
                let mut bestv = map[u];
                let mut bc = cur;
                let off = r.below(h.n);
                for k in 0..h.n {
                    let x = (k + off) % h.n;
                    let c = (0..t.n).filter(|&v| t.has(u, v) && !h.has(x, map[v])).count();
                    if c < bc {
                        bc = c;
                        bestv = x;
                    }
                }
                if bestv != map[u] {
                    map[u] = bestv;
                    improved = true;
                }
            }
            if !improved {
                break;
            }
        }
        let c = cost(&map);
        if c < best {
            best = c;
        }
        if best == 0 {
            break;
        }
        // perturb
        let k = 1 + (it % 3);
        for _ in 0..k {
            let u = r.below(t.n);
            map[u] = r.below(h.n);
        }
        if it % 50 == 49 {
            map = (0..t.n).map(|_| r.below(h.n)).collect();
        }
    }
    best
}

struct Ctx<'a> {
    h: &'a G,
    nt: usize,
    order: Vec<usize>,
    later: Vec<Vec<usize>>, // later[d] = positions i>d adjacent (in T) to position d
    best: AtomicU32,
    stop: AtomicBool,
    nodes: AtomicU64,
    deadline: Instant,
}

fn dfs(c: &Ctx, d: usize, cost: u32, cnt: &mut Vec<u8>, map: &mut Vec<usize>, local: &mut u64) {
    if c.stop.load(Ordering::Relaxed) {
        return;
    }
    *local += 1;
    if *local & 0xFFF == 0 {
        c.nodes.fetch_add(0x1000, Ordering::Relaxed);
        if Instant::now() > c.deadline {
            c.stop.store(true, Ordering::Relaxed);
            return;
        }
    }
    let nh = c.h.n;
    if d == c.nt {
        c.best.fetch_min(cost, Ordering::Relaxed);
        return;
    }
    // lookahead: sum of per-vertex minima for positions > d
    let mut rest = 0u32;
    for i in d + 1..c.nt {
        let row = &cnt[i * nh..(i + 1) * nh];
        rest += *row.iter().min().unwrap() as u32;
    }
    let best = c.best.load(Ordering::Relaxed);
    if cost + rest + *cnt[d * nh..(d + 1) * nh].iter().min().unwrap() as u32 >= best {
        return;
    }
    // candidates sorted by delta
    let mut cand: Vec<(u8, usize)> = (0..nh).map(|x| (cnt[d * nh + x], x)).collect();
    cand.sort_unstable();
    for (delta, x) in cand {
        let nc = cost + delta as u32;
        if nc + rest >= c.best.load(Ordering::Relaxed) {
            break;
        }
        map[d] = x;
        let nonadj = !c.h.adj[x];
        for &i in &c.later[d] {
            for y in 0..nh {
                cnt[i * nh + y] += ((nonadj >> y) & 1) as u8;
            }
        }
        dfs(c, d + 1, nc, cnt, map, local);
        for &i in &c.later[d] {
            for y in 0..nh {
                cnt[i * nh + y] -= ((nonadj >> y) & 1) as u8;
            }
        }
        if c.stop.load(Ordering::Relaxed) {
            return;
        }
    }
}

/// sym: 0 none, 1 vertex-transitive, 2 arc-transitive.
fn alpha(t: &G, h: &G, sym: u8, limit: Duration) -> (u32, bool, u64) {
    if t.m() == 0 {
        return (0, true, 0);
    }
    if h.m() == 0 {
        return (t.m() as u32, true, 0);
    }
    let nt = t.n;
    // order: max assigned-neighbour count, ties by degree
    let mut order = Vec::new();
    let mut used = vec![false; nt];
    for _ in 0..nt {
        let v = (0..nt)
            .filter(|&v| !used[v])
            .max_by_key(|&v| (order.iter().filter(|&&w| t.has(v, w)).count(), t.deg(v)))
            .unwrap();
        used[v] = true;
        order.push(v);
    }
    let ord2 = order.clone();
    let pos_adj = |a: usize, b: usize| t.has(ord2[a], ord2[b]);
    let later: Vec<Vec<usize>> = (0..nt).map(|d| (d + 1..nt).filter(|&i| pos_adj(d, i)).collect()).collect();
    let ub = local_search(t, h, 300, 12345);
    let c = Ctx {
        h,
        nt,
        order,
        later,
        best: AtomicU32::new(ub + 1),
        stop: AtomicBool::new(false),
        nodes: AtomicU64::new(0),
        deadline: Instant::now() + limit,
    };
    // we look for value < ub+1, i.e. <= ub; result equals true optimum
    let nh = h.n;
    let firsts: Vec<usize> = if sym >= 1 { vec![0] } else { (0..nh).collect() };
    let mut prefixes = Vec::new();
    for &a in &firsts {
        let seconds: Vec<usize> = if sym == 2 && pos_adj(0, 1) {
            let nb = h.adj[a].trailing_zeros() as usize;
            (0..nh).filter(|&y| y == nb || !h.has(a, y)).collect()
        } else {
            (0..nh).collect()
        };
        for b in seconds {
            prefixes.push((a, b));
        }
    }
    let _ = &c.order;
    prefixes.par_iter().for_each(|&(a, b)| {
        let mut cnt = vec![0u8; nt * nh];
        let mut map = vec![usize::MAX; nt];
        let mut local = 0u64;
        // assign position 0 -> a, 1 -> b
        map[0] = a;
        let na = !h.adj[a];
        for &i in &c.later[0] {
            for y in 0..nh {
                cnt[i * nh + y] += ((na >> y) & 1) as u8;
            }
        }
        let cost1 = cnt[nh + b] as u32;
        map[1] = b;
        let nb = !h.adj[b];
        for &i in &c.later[1] {
            for y in 0..nh {
                cnt[i * nh + y] += ((nb >> y) & 1) as u8;
            }
        }
        if nt == 2 {
            c.best.fetch_min(cost1, Ordering::Relaxed);
        } else {
            dfs(&c, 2, cost1, &mut cnt, &mut map, &mut local);
        }
        c.nodes.fetch_add(local & 0xFFF, Ordering::Relaxed);
    });
    let v = c.best.load(Ordering::Relaxed).min(ub);
    (v, !c.stop.load(Ordering::Relaxed), c.nodes.load(Ordering::Relaxed))
}


// ── Generalized Petersen profiles against the 85-core test family ──────────
fn read_tests(meta: &str) -> Vec<(String, G)> {
    let mut out = Vec::new();
    for line in std::fs::read_to_string(meta).unwrap().lines().skip(1) {
        let f: Vec<&str> = line.split(',').collect();
        let g = np::from_graph6(f[2]).unwrap();
        out.push((f[1].to_string(), G::from(&g)));
    }
    out
}

fn bipartite(g: &G) -> bool {
    let mut col = vec![-1i32; g.n];
    for s in 0..g.n {
        if col[s] >= 0 { continue; }
        col[s] = 0;
        let mut st = vec![s];
        while let Some(u) = st.pop() {
            for v in 0..g.n {
                if g.has(u, v) {
                    if col[v] < 0 { col[v] = 1 - col[u]; st.push(v); } else if col[v] == col[u] { return false; }
                }
            }
        }
    }
    true
}

fn odd_girth(g: &G) -> usize {
    // shortest odd closed walk = shortest odd cycle; BFS on bipartite double cover
    let n = g.n;
    let mut best = usize::MAX;
    for s in 0..n {
        let mut dist = vec![usize::MAX; 2 * n];
        dist[2 * s] = 0;
        let mut q = std::collections::VecDeque::from([2 * s]);
        while let Some(x) = q.pop_front() {
            let (u, p) = (x / 2, x % 2);
            for v in 0..n {
                if g.has(u, v) {
                    let y = 2 * v + (1 - p);
                    if dist[y] == usize::MAX { dist[y] = dist[x] + 1; q.push_back(y); }
                }
            }
        }
        best = best.min(dist[2 * s + 1]);
    }
    best
}

fn circular_clique(p: usize, q: usize) -> G {
    // K_{p/q}: vertices 0..p, i ~ j iff q <= |i - j| <= p - q
    let mut g = G::new(p);
    for i in 0..p {
        for j in i + 1..p {
            let d = j - i;
            if d >= q && d <= p - q {
                g.add(i, j);
            }
        }
    }
    g
}

fn gcd(a: usize, b: usize) -> usize { if b == 0 { a } else { gcd(b, a % b) } }

/// Profiles of the circular cliques K_{p/q} (gcd(p,q) = 1, 2 <= p/q <= qmax_ratio, p <= pmax).
fn circular_main(tests: &[(String, G)], limit: Duration, pmax: usize, rmax: f64) {
    println!("target,p,q,n,m,{},exact_all", tests.iter().map(|t| t.0.clone()).collect::<Vec<_>>().join(","));
    for p in 2..=pmax {
        for q in 1..=p / 2 {
            if gcd(p, q) != 1 || (p as f64) / (q as f64) > rmax { continue; }
            let h = circular_clique(p, q);
            let mut vals = Vec::new();
            let mut all = true;
            for (tn, t) in tests {
                let (v, ex, _) = alpha(t, &h, 1, limit); // circular cliques are vertex-transitive
                if !ex { eprintln!("K{p}/{q} <- {tn}: timeout, UB {v}"); }
                all &= ex;
                vals.push(if ex { format!("{v}") } else { format!("<={v}") });
            }
            eprintln!("K{p}/{q} done");
            println!("K{p}/{q},{p},{q},{},{},{},{}", h.n, h.m(), vals.join(","), all);
        }
    }
}

/// Profiles of graphs given as lines `name|family|n|u-v,u-v,...`.
fn list_main(tests: &[(String, G)], limit: Duration, file: &str) {
    println!("target,n,m,{},exact_all", tests.iter().map(|t| t.0.clone()).collect::<Vec<_>>().join(","));
    for line in std::fs::read_to_string(file).unwrap().lines().filter(|l| !l.trim().is_empty()) {
        let f: Vec<&str> = line.split('|').collect();
        let n: usize = f[2].parse().unwrap();
        let mut h = G::new(n);
        for e in f[3].split(',') {
            let (u, v) = e.split_once('-').unwrap();
            h.add(u.parse().unwrap(), v.parse().unwrap());
        }
        let mut vals = Vec::new();
        let mut all = true;
        for (tn, t) in tests {
            let (v, ex, _) = alpha(t, &h, 0, limit);
            if !ex { eprintln!("{} <- {tn}: timeout, UB {v}", f[0]); }
            all &= ex;
            vals.push(if ex { format!("{v}") } else { format!("<={v}") });
        }
        eprintln!("{} done (exact: {all})", f[0]);
        println!("\"{}\",{n},{},{},{}", f[0], h.m(), vals.join(","), all);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(|s| s.as_str()) == Some("list") {
        let tests = read_tests(&args[2]);
        let limit = Duration::from_secs(args.get(4).map(|s| s.parse().unwrap()).unwrap_or(10));
        list_main(&tests, limit, &args[3]);
        return;
    }
    if args.get(1).map(|s| s.as_str()) == Some("circular") {
        let tests = read_tests(&args[2]);
        let limit = Duration::from_secs(args.get(3).map(|s| s.parse().unwrap()).unwrap_or(30));
        let pmax: usize = args.get(4).map(|s| s.parse().unwrap()).unwrap_or(13);
        let rmax: f64 = args.get(5).map(|s| s.parse().unwrap()).unwrap_or(8.0);
        circular_main(&tests, limit, pmax, rmax);
        return;
    }
    let meta = &args[1];
    let limit = Duration::from_secs(args.get(2).map(|s| s.parse().unwrap()).unwrap_or(30));
    let nmax: usize = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(12);
    let tests = read_tests(meta);
    let cyc = |k: usize| G::from(&np::cycle(k));
    println!("target,n,m,equiv,{},exact_all", tests.iter().map(|t| t.0.clone()).collect::<Vec<_>>().join(","));
    for n in 3..=nmax {
        for k in 1..=((n - 1) / 2) {
            let name = format!("GP({n};{k})");
            let h = G::from(&np::gen_petersen(n, k));
            // shortcut: hom-equivalent to K2 or to an odd cycle C_g
            let equiv = if bipartite(&h) {
                "K2".to_string()
            } else {
                let g = odd_girth(&h);
                if g == 3 { String::new() } else {
                    let (a, ex, _) = alpha(&h, &cyc(g), 0, limit);
                    if a == 0 && ex { format!("C{g}") } else { String::new() }
                }
            };
            let target = if equiv == "K2" { G::from(&np::complete(2)) }
                         else if let Some(g) = equiv.strip_prefix('C') { cyc(g.parse().unwrap()) }
                         else { h.clone() };
            let mut vals = Vec::new();
            let mut all = true;
            for (tn, t) in &tests {
                let st = Instant::now();
                let (v, ex, _) = alpha(t, &target, 0, limit);
                if !ex { eprintln!("{name} <- {tn}: timeout, UB {v} ({:.1}s)", st.elapsed().as_secs_f64()); }
                all &= ex;
                vals.push(if ex { format!("{v}") } else { format!("<={v}") });
            }
            eprintln!("{name}: equiv={} done", if equiv.is_empty() { "-" } else { &equiv });
            println!("{name},{},{},{},{},{}", h.n, h.m(), if equiv.is_empty() { "-" } else { &equiv }, vals.join(","), all);
        }
    }
}
