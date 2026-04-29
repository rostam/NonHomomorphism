/// Prints the diverse |G,H|_0 table for the README.
/// Run with: cargo run --release --bin table

use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;
use std::time::Instant;
use rayon::prelude::*;

#[derive(Clone, Debug)]
struct Graph {
    n: usize,
    adj: Vec<u64>,
}

impl Graph {
    fn new(n: usize) -> Self {
        assert!(n <= 64);
        Graph { n, adj: vec![0u64; n] }
    }
    fn add_edge(&mut self, u: usize, v: usize) {
        self.adj[u] |= 1u64 << v;
        self.adj[v] |= 1u64 << u;
    }
    fn has_edge(&self, u: usize, v: usize) -> bool { self.adj[u] & (1u64 << v) != 0 }
    fn degree(&self, u: usize) -> u32 { self.adj[u].count_ones() }
    fn edge_count(&self) -> usize { self.adj.iter().map(|&m| m.count_ones() as usize).sum::<usize>() / 2 }
}

fn complete(n: usize) -> Graph {
    let mut g = Graph::new(n);
    for u in 0..n { for v in (u+1)..n { g.add_edge(u, v); } }
    g
}
fn cycle(n: usize) -> Graph {
    let mut g = Graph::new(n);
    for i in 0..n { g.add_edge(i, (i+1)%n); }
    g
}
fn petersen() -> Graph {
    let mut g = Graph::new(10);
    for i in 0..5 { g.add_edge(i, (i+1)%5); g.add_edge(i, i+5); g.add_edge(i+5, ((i+2)%5)+5); }
    g
}
fn octahedron() -> Graph {
    let mut g = Graph::new(6);
    for u in 0..6usize { for v in (u+1)..6 { if u/2 != v/2 { g.add_edge(u, v); } } }
    g
}
fn mycielski_step(g: &Graph) -> Graph {
    let n = g.n;
    assert!(2*n+1 <= 64);
    let mut h = Graph::new(2*n+1);
    for u in 0..n {
        let mut mask = g.adj[u];
        while mask != 0 {
            let v = mask.trailing_zeros() as usize; mask &= mask - 1;
            if v > u { h.add_edge(u, v); }
            h.add_edge(n+u, v);
        }
    }
    for i in 0..n { h.add_edge(2*n, n+i); }
    h
}
fn mycielski(k: usize) -> Graph {
    assert!(k >= 2);
    let mut g = complete(2);
    for _ in 2..k { g = mycielski_step(&g); }
    g
}
fn k_subsets(n: usize, k: usize) -> Vec<u64> {
    let mut out = Vec::new();
    fn pick(pos: usize, n: usize, rem: usize, cur: u64, out: &mut Vec<u64>) {
        if rem == 0 { out.push(cur); return; }
        if pos + rem > n { return; }
        pick(pos+1, n, rem-1, cur|(1u64<<pos), out);
        pick(pos+1, n, rem, cur, out);
    }
    pick(0, n, k, 0, &mut out);
    out
}
fn kneser(n: usize, k: usize) -> Graph {
    let subs = k_subsets(n, k);
    let m = subs.len();
    assert!(m <= 64);
    let mut g = Graph::new(m);
    for i in 0..m { for j in (i+1)..m { if subs[i] & subs[j] == 0 { g.add_edge(i, j); } } }
    g
}
fn icosahedron() -> Graph {
    let mut g = Graph::new(12);
    for &(u,v) in &[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,3),(3,4),(4,5),(5,1),
                    (1,6),(2,6),(2,7),(3,7),(3,8),(4,8),(4,9),(5,9),(5,10),(1,10),
                    (6,7),(7,8),(8,9),(9,10),(10,6),(6,11),(7,11),(8,11),(9,11),(10,11)] {
        g.add_edge(u, v);
    }
    g
}
fn dodecahedron() -> Graph {
    let mut g = Graph::new(20);
    for &(u,v) in &[(0,1),(0,4),(0,5),(1,2),(1,6),(2,3),(2,7),(3,4),(3,8),(4,9),
                    (5,10),(5,14),(6,10),(6,11),(7,11),(7,12),(8,12),(8,13),(9,13),(9,14),
                    (10,15),(11,16),(12,17),(13,18),(14,19),
                    (15,16),(15,19),(16,17),(17,18),(18,19)] {
        g.add_edge(u, v);
    }
    g
}
fn heawood() -> Graph {
    let mut g = Graph::new(14);
    for i in 0..14 { g.add_edge(i, (i+1)%14); }
    for &(u,v) in &[(0,5),(1,10),(2,7),(3,12),(4,9),(6,11),(8,13)] { g.add_edge(u, v); }
    g
}
fn paley_13() -> Graph {
    let qr: [bool; 13] = { let mut a = [false; 13]; for x in 1usize..13 { a[(x*x)%13] = true; } a };
    let mut g = Graph::new(13);
    for i in 0..13usize { for j in (i+1)..13 { if qr[(j+13-i)%13] { g.add_edge(i, j); } } }
    g
}

struct Problem<'a> {
    g: &'a Graph,
    h: &'a Graph,
    g_order: Vec<usize>,
    best: Arc<AtomicU32>,
}
impl<'a> Problem<'a> {
    fn new(g: &'a Graph, h: &'a Graph, best: Arc<AtomicU32>) -> Self {
        let mut order: Vec<usize> = (0..g.n).collect();
        order.sort_by_key(|&v| std::cmp::Reverse(g.degree(v)));
        Problem { g, h, g_order: order, best }
    }
    fn search(&self, mapping: &mut Vec<usize>, cost: u32, depth: usize) {
        if depth == self.g.n { self.best.fetch_min(cost, Ordering::Relaxed); return; }
        let u = self.g_order[depth];
        for hv in 0..self.h.n {
            let mut delta = 0u32;
            let mut nb_mask = self.g.adj[u];
            while nb_mask != 0 {
                let nb = nb_mask.trailing_zeros() as usize; nb_mask &= nb_mask - 1;
                let nb_img = mapping[nb];
                if nb_img != usize::MAX && !self.h.has_edge(hv, nb_img) { delta += 1; }
            }
            let new_cost = cost + delta;
            if new_cost >= self.best.load(Ordering::Relaxed) { continue; }
            mapping[u] = hv;
            self.search(mapping, new_cost, depth + 1);
            mapping[u] = usize::MAX;
        }
    }
}
fn nonhom_param(g: &Graph, h: &Graph) -> u32 {
    if g.n == 0 || h.n == 0 { return 0; }
    let upper = g.edge_count() as u32 + 1;
    let best = Arc::new(AtomicU32::new(upper));
    let prob = Arc::new(Problem::new(g, h, Arc::clone(&best)));
    let u0 = prob.g_order[0];
    (0..h.n).into_par_iter().for_each(|hv| {
        let prob = Arc::clone(&prob);
        let mut mapping = vec![usize::MAX; prob.g.n];
        mapping[u0] = hv;
        prob.search(&mut mapping, 0, 1);
    });
    best.load(Ordering::Relaxed)
}

fn main() {
    let rows: &[(&str, &str, Graph, usize)] = &[
        // (display name, properties note, graph, vertex count)
        ("$C_5$",         "5v, 5e, χ=3",  cycle(5),       5),
        ("$C_7$",         "7v, 7e, χ=3",  cycle(7),       7),
        ("Petersen",      "10v, 15e, χ=3",petersen(),     10),
        ("Octahedron",    "6v, 12e, χ=3", octahedron(),    6),
        ("Grötzsch",      "11v, 20e, χ=4",mycielski(4),   11),
        ("Kneser K(6,2)", "15v, 45e, χ=4",kneser(6,2),   15),
        ("Icosahedron",   "12v, 30e, χ=4",icosahedron(),  12),
        ("Dodecahedron",  "20v, 30e, χ=3",dodecahedron(), 20),
        ("Paley(13)",     "13v, 39e, χ=5",paley_13(),     13),
        ("Heawood",       "14v, 21e, χ=2",heawood(),      14),
    ];

    let k2  = complete(2);
    let k3  = complete(3);
    let k4  = complete(4);
    let k5  = complete(5);
    let c5  = cycle(5);
    let pet = petersen();

    // Compute all values; use Option::None if we decide to skip large+slow entries.
    // Heuristic: skip source_n > 15 with non-complete targets that could be slow.
    // (name, target, max_source_n_allowed)  — None = always compute
    let col_targets: &[(&str, &Graph, Option<usize>)] = &[
        ("$K_2$",    &k2,  None),
        ("$K_3$",    &k3,  None),
        ("$K_4$",    &k4,  None),
        ("$K_5$",    &k5,  None),
        ("$C_5$",    &c5,  Some(20)),  // Dodecahedron (20v) included; anything larger skipped
        ("Petersen", &pet, Some(12)),  // skip if source_n > 12 (15v+ → 10v is too slow)
    ];

    println!("Computing table… (this may take a few minutes)");
    println!();

    // header
    print!("| G \\ H |");
    for (cname, _, _) in col_targets { print!(" {cname} |"); }
    println!();
    print!("|:---|");
    for _ in col_targets { print!(":---:|"); }
    println!();

    for (rname, _note, rg, rn) in rows {
        print!("| {rname} |");
        for (_, cg, max_n) in col_targets {
            let skip = max_n.map_or(false, |lim| *rn > lim);
            if skip {
                print!(" — |");
            } else {
                let t0 = Instant::now();
                let v = nonhom_param(rg, cg);
                let elapsed = t0.elapsed();
                eprint!("  {rname} → target({})v  = {v}  [{:.2?}]\n", cg.n, elapsed);
                print!(" {v} |");
            }
        }
        println!();
    }

    println!();
    println!("Done.");
}
