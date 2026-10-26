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

fn tests() -> Vec<(String, G)> {
    let mut v: Vec<(String, G)> = Vec::new();
    for k in 2..=6 {
        v.push((format!("K{k}"), G::from(&np::complete(k))));
    }
    for k in [5, 7, 9] {
        v.push((format!("C{k}"), G::from(&np::cycle(k))));
    }
    v.push(("Petersen".into(), G::from(&np::petersen())));
    v.push(("Grotzsch".into(), G::from(&np::mycielski(4))));
    v.push(("W5".into(), wheel(5)));
    v.push(("Icosahedron".into(), G::from(&np::icosahedron())));
    v
}

fn targets() -> Vec<(String, G, u8)> {
    let mut v: Vec<(String, G, u8)> = Vec::new();
    // sanity targets (also in alpha.csv)
    v.push(("K2".into(), G::from(&np::complete(2)), 2));
    v.push(("K3".into(), G::from(&np::complete(3)), 2));
    v.push(("K4".into(), G::from(&np::complete(4)), 2));
    v.push(("C5".into(), G::from(&np::cycle(5)), 2));
    v.push(("Petersen".into(), G::from(&np::petersen()), 2));
    v.push(("Grotzsch".into(), G::from(&np::mycielski(4)), 0));
    v.push(("Icosahedron".into(), G::from(&np::icosahedron()), 2));
    // new
    v.push(("M5_Mycielski".into(), G::from(&np::mycielski(5)), 0));
    v.push(("Chvatal".into(), chvatal(), 0));
    v.push(("Clebsch".into(), clebsch(), 2));
    v.push(("Dodecahedron".into(), G::from(&np::dodecahedron()), 2));
    v.push(("Heawood".into(), G::from(&np::heawood()), 2));
    v.push(("Paley13".into(), G::from(&np::paley_13()), 2));
    v.push(("Kneser(6,2)".into(), kneser(6, 2), 2));
    v.push(("Kneser(7,2)".into(), kneser(7, 2), 2));
    v.push(("Kneser(7,3)".into(), kneser(7, 3), 2));
    v.push(("Kneser(8,3)".into(), kneser(8, 3), 2));
    v.push(("Kneser(9,4)".into(), kneser(9, 4), 2));
    v.push(("GP(7,2)".into(), G::from(&np::gen_petersen(7, 2)), 1));
    v.push(("GP(9,2)".into(), G::from(&np::gen_petersen(9, 2)), 1));
    v.push(("GP(11,2)".into(), G::from(&np::gen_petersen(11, 2)), 1));
    v.push(("Circ(13;1,5)".into(), circ(13, &[1, 5]), 1));
    v.push(("Circ(11;1,2)=C11^2".into(), circ(11, &[1, 2]), 1));
    v.push(("Circ(17;1,2,4,8)=Paley17".into(), circ(17, &[1, 2, 4, 8]), 2));
    v.push(("Circ(14;1,4)".into(), circ(14, &[1, 4]), 1));
    v.push(("Circ(16;1,3,8)".into(), circ(16, &[1, 3, 8]), 1));
    v.push(("C13".into(), circ(13, &[1]), 2));
    v.push(("C15".into(), circ(15, &[1]), 2));
    for (n, p, s) in [(20, 0.2, 1), (20, 0.2, 2), (20, 0.3, 1), (20, 0.3, 2), (20, 0.5, 1), (20, 0.5, 2), (30, 0.1, 1), (30, 0.2, 1), (40, 0.1, 1)] {
        v.push((format!("G({n},{p})#{s}"), gnp(n, p, s), 0));
    }
    v
}

/// generalized Mycielskian mu_r(G): layers V_0..V_r, apex adjacent to V_r.
fn genmyc(g: &G, r: usize) -> G {
    let n = g.n;
    let mut h = G::new(n * (r + 1) + 1);
    for u in 0..n {
        for v in 0..n {
            if g.has(u, v) {
                if u < v { h.add(u, v); }
                for i in 0..r {
                    let a = i * n + u; let b = (i + 1) * n + v;
                    if !h.has(a, b) { h.add(a, b); }
                }
            }
        }
    }
    for v in 0..n { h.add(r * n + v, n * (r + 1)); }
    h
}
fn disjoint(a: &G, b: &G, bridge: bool) -> G {
    let mut h = G::new(a.n + b.n);
    for u in 0..a.n { for v in u+1..a.n { if a.has(u,v) { h.add(u,v); } } }
    for u in 0..b.n { for v in u+1..b.n { if b.has(u,v) { h.add(a.n+u,a.n+v); } } }
    if bridge { h.add(0, a.n); }
    h
}
fn odd_girth(g: &G) -> usize {
    // shortest odd closed walk = shortest odd cycle; BFS on bipartite double cover
    let mut best = usize::MAX;
    for s in 0..g.n {
        let mut dist = vec![usize::MAX; 2 * g.n];
        dist[2 * s] = 0;
        let mut q = std::collections::VecDeque::from([2 * s]);
        while let Some(x) = q.pop_front() {
            let (u, p) = (x / 2, x % 2);
            for v in 0..g.n { if g.has(u, v) { let y = 2 * v + (1 - p); if dist[y] == usize::MAX { dist[y] = dist[x] + 1; q.push_back(y); } } }
        }
        if dist[2 * s + 1] < best { best = dist[2 * s + 1]; }
    }
    best
}
fn gm_mode(limit: Duration) {
    let ts = tests();
    let c5 = G::from(&np::cycle(5));
    let mut list: Vec<(String, G)> = Vec::new();
    for (k, r) in [(2usize, 2usize), (3, 3), (4, 4), (5, 5), (6, 6)] {
        let base = G::from(&np::cycle(2 * k + 1));
        list.push((format!("mu_{r}(C{})", 2 * k + 1), genmyc(&base, r)));
    }
    let big = genmyc(&G::from(&np::cycle(13)), 6);
    list.push(("mu_6(C13)+C5 (disjoint)".into(), disjoint(&big, &c5, false)));
    list.push(("mu_6(C13)+C5 (bridged)".into(), disjoint(&big, &c5, true)));
    println!("target,n,m,odd_girth,{},exact_all", ts.iter().map(|x| x.0.clone()).collect::<Vec<_>>().join(","));
    for (hn, h) in list {
        let mut vals = Vec::new(); let mut all = true;
        for (tn, t) in &ts {
            let st = Instant::now();
            let (v, ex, _) = alpha(t, &h, 0, limit);
            eprintln!("{hn} <- {tn} = {v} {ex} {:.1}s", st.elapsed().as_secs_f64());
            all &= ex; vals.push(if ex { format!("{v}") } else { format!("<={v}") });
        }
        println!("{hn},{},{},{},{},{}", h.n, h.m(), odd_girth(&h), vals.join(","), all);
    }
    // dump mu_6(C13) edges for external chi check
    let mut s = String::new();
    for u in 0..big.n { for v in u+1..big.n { if big.has(u,v) { s += &format!("{u} {v}\n"); } } }
    std::fs::write("../Q_mu6C13.edges", s).unwrap();
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let limit = Duration::from_secs(args.get(1).map(|s| s.parse().unwrap()).unwrap_or(20));
    let only: Option<String> = args.get(2).cloned();
    if only.as_deref() == Some("gm") { gm_mode(limit); return; }
    let ts = tests();
    // self-check against repo solver on small pairs
    if only.as_deref() == Some("check") {
        let small = ["K2", "K3", "K4", "C5", "Petersen", "Grotzsch", "Icosahedron"];
        for (tn, t) in &ts {
            for (hn, h, sym) in targets().into_iter().filter(|x| small.contains(&x.0.as_str())) {
                let to = |g: &G| {
                    let mut x = np::Graph::new(g.n);
                    for u in 0..g.n {
                        for v in u + 1..g.n {
                            if g.has(u, v) {
                                x.add_edge(u, v);
                            }
                        }
                    }
                    x
                };
                let a = np::nonhom_param(&to(t), &to(&h));
                let (b, ex, _) = alpha(t, &h, sym, limit);
                if a != b || !ex {
                    println!("MISMATCH {tn}->{hn}: repo {a} mine {b} exact {ex}");
                }
            }
        }
        println!("check done");
        return;
    }
    println!("target,n,m,{},exact_all", ts.iter().map(|x| x.0.clone()).collect::<Vec<_>>().join(","));
    for (hn, h, sym) in targets() {
        if let Some(o) = &only {
            if !hn.contains(o.as_str()) {
                continue;
            }
        }
        let mut vals = Vec::new();
        let mut all = true;
        for (tn, t) in &ts {
            let st = Instant::now();
            let (v, ex, nodes) = alpha(t, &h, sym, limit);
            eprintln!("{hn:>24} <- {tn:<12} alpha={v}{} nodes={nodes} {:.2}s", if ex { "" } else { " (UB, timeout)" }, st.elapsed().as_secs_f64());
            all &= ex;
            vals.push(if ex { format!("{v}") } else { format!("<={v}") });
        }
        println!("{hn},{},{},{},{}", h.n, h.m(), vals.join(","), all);
    }
}
