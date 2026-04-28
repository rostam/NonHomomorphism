/// Fast computation of |G,H|_0 = minimum edges to remove from G so G→H homomorphism exists.
///
/// Strategy: for every mapping f: V(G)→V(H), count edges {u,v}∈E(G) where {f(u),f(v)}∉E(H).
/// The minimum over all f is |G,H|_0.
///
/// Optimisations:
///   • Bitmask adjacency (u64) – edge-lookup is a single bit-test.
///   • Branch-and-bound: maintain a global best; prune when partial cost ≥ best.
///   • Vertex ordering: process high-degree G-vertices first so conflicts appear early.
///   • Rayon parallel search over first-level branches.

use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;
use std::time::Instant;

use rayon::prelude::*;

// ── Graph representation ────────────────────────────────────────────────────

#[derive(Clone, Debug)]
struct Graph {
    n: usize,
    /// adj[u] is a bitmask of neighbours of u
    adj: Vec<u64>,
}

impl Graph {
    fn new(n: usize) -> Self {
        assert!(n <= 64, "bitmask graph supports at most 64 vertices");
        Graph { n, adj: vec![0u64; n] }
    }

    fn add_edge(&mut self, u: usize, v: usize) {
        self.adj[u] |= 1u64 << v;
        self.adj[v] |= 1u64 << u;
    }

    fn has_edge(&self, u: usize, v: usize) -> bool {
        self.adj[u] & (1u64 << v) != 0
    }

    fn degree(&self, u: usize) -> u32 {
        self.adj[u].count_ones()
    }

    fn edge_count(&self) -> usize {
        self.adj.iter().map(|&m| m.count_ones() as usize).sum::<usize>() / 2
    }
}

// ── Builder helpers ─────────────────────────────────────────────────────────

fn complete(n: usize) -> Graph {
    let mut g = Graph::new(n);
    for u in 0..n {
        for v in (u + 1)..n {
            g.add_edge(u, v);
        }
    }
    g
}

fn cycle(n: usize) -> Graph {
    let mut g = Graph::new(n);
    for i in 0..n {
        g.add_edge(i, (i + 1) % n);
    }
    g
}

fn petersen() -> Graph {
    let mut g = Graph::new(10);
    for i in 0..5 {
        g.add_edge(i, (i + 1) % 5);
        g.add_edge(i, i + 5);
        g.add_edge(i + 5, ((i + 2) % 5) + 5);
    }
    g
}

fn grid(rows: usize, cols: usize) -> Graph {
    let n = rows * cols;
    let mut g = Graph::new(n);
    for r in 0..rows {
        for c in 0..cols {
            let u = r * cols + c;
            if c + 1 < cols {
                g.add_edge(u, u + 1);
            }
            if r + 1 < rows {
                g.add_edge(u, u + cols);
            }
        }
    }
    g
}

fn circulant(n: usize, jumps: &[usize]) -> Graph {
    let mut g = Graph::new(n);
    for u in 0..n {
        for &j in jumps {
            let v = (u + j) % n;
            if v != u {
                g.add_edge(u, v);
            }
        }
    }
    g
}

fn bipartite_complete(a: usize, b: usize) -> Graph {
    let n = a + b;
    let mut g = Graph::new(n);
    for u in 0..a {
        for v in a..n {
            g.add_edge(u, v);
        }
    }
    g
}

/// Mycielski lifting: given G on n vertices produces a new graph on 2n+1 vertices.
/// Shadows u' of each u get the same neighbourhood as u in G; a new root connects
/// to every shadow. One application raises the chromatic number by 1 without
/// introducing new triangles.
fn mycielski_step(g: &Graph) -> Graph {
    let n = g.n;
    assert!(2 * n + 1 <= 64, "Mycielski graph would exceed 64 vertices");
    let mut h = Graph::new(2 * n + 1);
    for u in 0..n {
        let mut mask = g.adj[u];
        while mask != 0 {
            let v = mask.trailing_zeros() as usize;
            mask &= mask - 1;
            if v > u {
                h.add_edge(u, v);       // copy original edge
            }
            h.add_edge(n + u, v);       // shadow u' → neighbour v
        }
    }
    for i in 0..n {
        h.add_edge(2 * n, n + i);       // root → every shadow
    }
    h
}

/// Mycielski graph M(k): χ = k, triangle-free for k ≥ 2.
/// M(2)=K2, M(3)=C5, M(4)=Grötzsch (11 v), M(5)=23 v.
fn mycielski(k: usize) -> Graph {
    assert!(k >= 2);
    let mut g = complete(2);
    for _ in 2..k {
        g = mycielski_step(&g);
    }
    g
}

/// All k-subsets of {0..n-1} encoded as bitmasks.
fn k_subsets(n: usize, k: usize) -> Vec<u64> {
    let mut out = Vec::new();
    fn pick(pos: usize, n: usize, rem: usize, cur: u64, out: &mut Vec<u64>) {
        if rem == 0 { out.push(cur); return; }
        if pos + rem > n { return; }
        pick(pos + 1, n, rem - 1, cur | (1u64 << pos), out);
        pick(pos + 1, n, rem, cur, out);
    }
    pick(0, n, k, 0, &mut out);
    out
}

/// Kneser graph K(n,k): vertices = k-subsets of {0..n-1}, edges between disjoint pairs.
/// χ(K(n,k)) = n−2k+2  (Lovász).  K(5,2) = Petersen.
fn kneser(n: usize, k: usize) -> Graph {
    let subs = k_subsets(n, k);
    let m = subs.len();
    assert!(m <= 64, "Kneser graph has too many vertices");
    let mut g = Graph::new(m);
    for i in 0..m {
        for j in (i + 1)..m {
            if subs[i] & subs[j] == 0 {
                g.add_edge(i, j);
            }
        }
    }
    g
}

/// Generalized Petersen graph GP(n, k):
/// outer n-cycle, inner n-star with step k, spokes connecting them.
fn gen_petersen(n: usize, k: usize) -> Graph {
    assert!(2 * n <= 64);
    let mut g = Graph::new(2 * n);
    for i in 0..n {
        g.add_edge(i, (i + 1) % n);            // outer cycle
        g.add_edge(i, n + i);                  // spoke
        g.add_edge(n + i, n + (i + k) % n);   // inner star
    }
    g
}

/// Icosahedron: 12 vertices, 5-regular, 30 edges.
fn icosahedron() -> Graph {
    let mut g = Graph::new(12);
    let edges: &[(usize, usize)] = &[
        (0,1),(0,2),(0,3),(0,4),(0,5),
        (1,2),(2,3),(3,4),(4,5),(5,1),
        (1,6),(2,6),(2,7),(3,7),(3,8),(4,8),(4,9),(5,9),(5,10),(1,10),
        (6,7),(7,8),(8,9),(9,10),(10,6),
        (6,11),(7,11),(8,11),(9,11),(10,11),
    ];
    for &(u, v) in edges { g.add_edge(u, v); }
    g
}

/// Dodecahedron: 20 vertices, 3-regular, 30 edges.
fn dodecahedron() -> Graph {
    let mut g = Graph::new(20);
    let edges: &[(usize, usize)] = &[
        (0,1),(0,4),(0,5),
        (1,2),(1,6),
        (2,3),(2,7),
        (3,4),(3,8),
        (4,9),
        (5,10),(5,14),
        (6,10),(6,11),
        (7,11),(7,12),
        (8,12),(8,13),
        (9,13),(9,14),
        (10,15),(11,16),(12,17),(13,18),(14,19),
        (15,16),(15,19),
        (16,17),(17,18),(18,19),
    ];
    for &(u, v) in edges { g.add_edge(u, v); }
    g
}

/// Heawood graph: 14 vertices, 3-regular, bipartite, girth 6 — the (3,6)-cage.
/// Built from a 14-cycle plus 7 chords given by LCF [5,−5]^7.
fn heawood() -> Graph {
    let mut g = Graph::new(14);
    for i in 0..14 { g.add_edge(i, (i + 1) % 14); }
    for &(u, v) in &[(0,5),(1,10),(2,7),(3,12),(4,9),(6,11),(8,13)] {
        g.add_edge(u, v);
    }
    g
}

/// Paley graph P(13): 13 vertices, 6-regular, self-complementary, strongly regular (13,6,2,3).
/// {i,j} is an edge iff j−i is a quadratic residue mod 13.
fn paley_13() -> Graph {
    let qr: [bool; 13] = {
        let mut a = [false; 13];
        for x in 1usize..13 { a[(x * x) % 13] = true; }
        a
    };
    let mut g = Graph::new(13);
    for i in 0..13usize {
        for j in (i + 1)..13 {
            if qr[(j + 13 - i) % 13] { g.add_edge(i, j); }
        }
    }
    g
}

/// Petersen graph + one extra edge between two non-adjacent vertices.
/// All non-edges are automorphically equivalent (S5 acts transitively on them),
/// so any choice gives an isomorphic graph. Here we add edge 0–2 (vertices 0
/// and 2 are both on the outer pentagon but not adjacent; each has exactly one
/// common neighbour with the other, confirming they are genuinely non-adjacent).
fn petersen_plus_one_edge() -> Graph {
    let mut g = petersen();
    // Verify 0 and 2 are not adjacent before adding the edge
    assert!(!g.has_edge(0, 2), "0-2 is already an edge");
    g.add_edge(0, 2);
    g
}

/// Octahedron = K_{2,2,2}: 6 vertices, 4-regular, 12 edges, χ = 3.
fn octahedron() -> Graph {
    let mut g = Graph::new(6);
    for u in 0..6usize {
        for v in (u + 1)..6 {
            if u / 2 != v / 2 { g.add_edge(u, v); }
        }
    }
    g
}

/// Möbius–Kantor graph GP(8,3): 16 vertices, 3-regular, bipartite, girth 6.
fn mobius_kantor() -> Graph { gen_petersen(8, 3) }

/// Pappus graph: 18 vertices, 3-regular, bipartite, girth 6.
/// LCF notation [5,7,−7,7,−7,−5]^3.
fn pappus() -> Graph {
    let n = 18usize;
    let lcf = [5i64, 7, -7, 7, -7, -5];
    let mut g = Graph::new(n);
    for i in 0..n { g.add_edge(i, (i + 1) % n); }
    for i in 0..n {
        let offset = lcf[i % lcf.len()];
        let j = ((i as i64 + offset).rem_euclid(n as i64)) as usize;
        if j > i { g.add_edge(i, j); }
    }
    g
}

// ── Core branch-and-bound ────────────────────────────────────────────────────

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
        if depth == self.g.n {
            self.best.fetch_min(cost, Ordering::Relaxed);
            return;
        }

        let u = self.g_order[depth];

        for hv in 0..self.h.n {
            // Count conflicts introduced by assigning u → hv
            let mut delta = 0u32;
            let mut nb_mask = self.g.adj[u];
            while nb_mask != 0 {
                let nb = nb_mask.trailing_zeros() as usize;
                nb_mask &= nb_mask - 1;
                let nb_img = mapping[nb];
                if nb_img != usize::MAX && !self.h.has_edge(hv, nb_img) {
                    delta += 1;
                }
            }

            let new_cost = cost + delta;
            if new_cost >= self.best.load(Ordering::Relaxed) {
                continue;
            }

            mapping[u] = hv;
            self.search(mapping, new_cost, depth + 1);
            mapping[u] = usize::MAX;
        }
    }
}

fn nonhom_param(g: &Graph, h: &Graph) -> u32 {
    if g.n == 0 || h.n == 0 {
        return 0;
    }

    let upper = g.edge_count() as u32 + 1;
    let best = Arc::new(AtomicU32::new(upper));

    let prob = Arc::new(Problem::new(g, h, Arc::clone(&best)));

    // Parallelise over H-images of the first G-vertex
    let u0 = prob.g_order[0];
    (0..h.n).into_par_iter().for_each(|hv| {
        let prob = Arc::clone(&prob);
        let mut mapping = vec![usize::MAX; prob.g.n];
        mapping[u0] = hv;
        prob.search(&mut mapping, 0, 1);
    });

    best.load(Ordering::Relaxed)
}

// ── Experiment runner ────────────────────────────────────────────────────────

fn run(label: &str, g: &Graph, h: &Graph) -> std::time::Duration {
    let t = Instant::now();
    let val = nonhom_param(g, h);
    let elapsed = t.elapsed();
    println!(
        "{:<52} |G,H|_0 = {:<4}  (|V(G)|={}, |E(G)|={}, |V(H)|={}, |E(H)|={})  [{:.3?}]",
        label,
        val,
        g.n,
        g.edge_count(),
        h.n,
        h.edge_count(),
        elapsed
    );
    elapsed
}

fn main() {
    println!("=== Non-homomorphism parameter |G,H|_0 ===\n");
    println!("Using {} threads\n", std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1));

    let timeout = std::time::Duration::from_secs(300);

    let k2 = complete(2);
    let k3 = complete(3);
    let k4 = complete(4);
    let k5 = complete(5);
    let c5 = cycle(5);
    let c7 = cycle(7);
    let pet = petersen();

    println!("── Classic cases ──────────────────────────────────────────");
    run("C5 → K2", &c5, &k2);
    run("C7 → K2", &c7, &k2);
    run("Petersen → K3", &pet, &k3);
    run("Petersen → K4", &pet, &k4);
    run("Petersen → C5", &pet, &c5);
    run("K4 → K3", &k4, &k3);
    run("K5 → K3", &k5, &k3);
    run("K5 → K4", &k5, &k4);

    println!("\n── Series 1: C_n → K3 ─────────────────────────────────────");
    for n in [5, 7, 9, 11, 13, 15, 17, 19, 21, 25, 30, 35, 40] {
        let g = cycle(n);
        let label = format!("C{n} → K3");
        let elapsed = run(&label, &g, &k3);
        if elapsed > timeout {
            println!("  >> 5-min limit hit, stopping series.");
            break;
        }
    }

    println!("\n── Series 2: K_n → K3 ─────────────────────────────────────");
    for n in [4, 5, 6, 7, 8, 9, 10, 11] {
        let g = complete(n);
        let label = format!("K{n} → K3");
        let elapsed = run(&label, &g, &k3);
        if elapsed > timeout {
            println!("  >> 5-min limit hit, stopping series.");
            break;
        }
    }

    println!("\n── Series 3: Grid(r×r) → K3 ───────────────────────────────");
    for r in [2, 3, 4, 5, 6, 7] {
        let g = grid(r, r);
        if g.n > 64 {
            break;
        }
        let label = format!("Grid({r}×{r}) → K3");
        let elapsed = run(&label, &g, &k3);
        if elapsed > timeout {
            println!("  >> 5-min limit hit, stopping series.");
            break;
        }
    }

    println!("\n── Series 4: Circulant(n,{{1,floor(n/2)-1}}) → K3 ─────────");
    for n in [10, 12, 14, 16, 18, 20, 24, 28, 32] {
        if n > 64 {
            break;
        }
        let j = n / 2 - 1;
        let g = circulant(n, &[1, j]);
        let label = format!("Circ({n},{{1,{j}}}) → K3");
        let elapsed = run(&label, &g, &k3);
        if elapsed > timeout {
            println!("  >> 5-min limit hit, stopping series.");
            break;
        }
    }

    println!("\n── Series 5: Dense circulants → K3 ────────────────────────");
    for (n, jumps) in [
        (10usize, vec![1usize, 2, 3, 4]),
        (12, vec![1, 2, 3, 4, 5]),
        (15, vec![1, 2, 3, 4, 5, 6, 7]),
        (18, vec![1, 2, 3, 4, 5, 6, 7, 8]),
        (20, vec![1, 2, 3, 4, 5, 6, 7, 8, 9]),
        (24, vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]),
    ] {
        if n > 64 {
            break;
        }
        let g = circulant(n, &jumps);
        let label = format!("DenseCirc({n}) → K3");
        let elapsed = run(&label, &g, &k3);
        if elapsed > timeout {
            println!("  >> 5-min limit hit, stopping series.");
            break;
        }
    }

    println!("\n── Series 6: K_{{a,b}} → K2 (bipartite, expect 0) ─────────");
    for (a, b) in [(2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 8)] {
        let g = bipartite_complete(a, b);
        if g.n > 64 {
            break;
        }
        let label = format!("K_{{{a},{b}}} → K2");
        let elapsed = run(&label, &g, &k2);
        if elapsed > timeout {
            println!("  >> 5-min limit hit, stopping series.");
            break;
        }
    }

    println!("\n── Series 7: Petersen → K_n ───────────────────────────────");
    for n in [2, 3, 4, 5] {
        let h = complete(n);
        let label = format!("Petersen → K{n}");
        run(&label, &pet, &h);
    }

    // ── Petersen + one edge ─────────────────────────────────────────────────
    {
        println!("\n── Petersen + one edge ─────────────────────────────────────");
        let pet_plus = petersen_plus_one_edge();
        println!(
            "  PetGraphPlusOneEdge: {} vertices, {} edges (Petersen had {})",
            pet_plus.n, pet_plus.edge_count(), petersen().edge_count()
        );
        // Show adjacency of the added vertices for clarity
        print!("  Neighbours of 0 after adding edge 0-2: {{");
        let mut mask = pet_plus.adj[0];
        let mut first = true;
        while mask != 0 {
            let v = mask.trailing_zeros() as usize;
            mask &= mask - 1;
            if !first { print!(", "); }
            print!("{v}");
            first = false;
        }
        println!("}}");
        run("PetGraphPlusOneEdge → K3", &pet_plus, &k3);
        run("PetGraphPlusOneEdge → K2", &pet_plus, &k2);
        run("PetGraphPlusOneEdge → K4", &pet_plus, &k4);
        run("PetGraphPlusOneEdge → C5", &pet_plus, &c5);
    }

    // ── New uncommon / interesting graphs ───────────────────────────────────

    println!("\n── Series 8: Mycielski M(k) — χ=k, triangle-free ──────────");
    // M(k) → K_{k-1}: requires removing edges (χ too high for K_{k-1})
    // M(k) → K_k:     = 0 (k-colourable)
    {
        let m3 = mycielski(3); // C5
        let m4 = mycielski(4); // Grötzsch, 11 verts
        let m5 = mycielski(5); // 23 verts
        run("M(3)=C5  → K2  (odd, expect 1)",   &m3, &k2);
        run("M(3)=C5  → K3  (3-chrom, expect 0)",&m3, &k3);
        run("M(4)=Grötzsch → K3 (4-chrom→K3?)", &m4, &k3);
        run("M(4)=Grötzsch → K4 (expect 0)",     &m4, &k4);
        run("M(5) → K4 (5-chrom, expect >0)",    &m5, &k4);
        run("M(5) → K5 (expect 0)",              &m5, &k5);
    }

    println!("\n── Series 9: Kneser K(n,2) — χ = n−2 ─────────────────────");
    {
        // K(5,2) = Petersen, χ=3
        // K(6,2): 15 verts, χ=4
        // K(7,2): 21 verts, χ=5
        let kn52 = kneser(5, 2);
        let kn62 = kneser(6, 2);
        let kn72 = kneser(7, 2);
        run("K(5,2)=Petersen → K3 (χ=3, exp 0)", &kn52, &k3);
        run("K(6,2) → K3  (χ=4, exp >0)",        &kn62, &k3);
        run("K(6,2) → K4  (χ=4, exp 0)",         &kn62, &k4);
        run("K(7,2) → K4  (χ=5, exp >0)",        &kn72, &k4);
        run("K(7,2) → K5  (χ=5, exp 0)",         &kn72, &k5);
    }

    println!("\n── Series 10: Generalized Petersen GP(n,k) → K3 ───────────");
    for (n, k) in [(5,2),(6,2),(7,2),(8,3),(10,2),(10,3),(12,4),(15,4),(20,4)] {
        if 2 * n > 64 { break; }
        let g = gen_petersen(n, k);
        let label = format!("GP({n},{k}) → K3");
        let elapsed = run(&label, &g, &k3);
        if elapsed > timeout { println!("  >> 5-min limit hit."); break; }
    }

    println!("\n── Series 11: Platonic solids ──────────────────────────────");
    {
        let tet  = complete(4);          // tetrahedron = K4
        let oct  = octahedron();         // K_{2,2,2}
        let ico  = icosahedron();
        let dod  = dodecahedron();
        run("Tetrahedron (K4) → K3",    &tet, &k3);
        run("Octahedron → K3",          &oct, &k3);
        run("Octahedron → K4",          &oct, &k4);
        run("Icosahedron → K2",         &ico, &k2);
        run("Icosahedron → K3",         &ico, &k3);
        run("Icosahedron → K4",         &ico, &k4);
        run("Dodecahedron → K2",        &dod, &k2);
        run("Dodecahedron → K3",        &dod, &k3);
        run("Dodecahedron → K4",        &dod, &k4);
    }

    println!("\n── Series 12: Cage / symmetric graphs ──────────────────────");
    {
        let hea = heawood();       // (3,6)-cage, bipartite
        let mob = mobius_kantor(); // GP(8,3), bipartite
        let pap = pappus();        // 18 v, bipartite
        run("Heawood (14v,bip) → K2",      &hea, &k2);
        run("Heawood → K3",                &hea, &k3);
        run("Möbius–Kantor (16v,bip) → K2",&mob, &k2);
        run("Möbius–Kantor → K3",          &mob, &k3);
        run("Pappus (18v,bip) → K2",       &pap, &k2);
        run("Pappus → K3",                 &pap, &k3);
    }

    println!("\n── Series 13: Paley P(13) — self-complementary, s.r.(13,6,2,3)");
    {
        let p13 = paley_13();
        run("Paley(13) → K2", &p13, &k2);
        run("Paley(13) → K3", &p13, &k3);
        run("Paley(13) → K4", &p13, &k4);
        run("Paley(13) → K5", &p13, &k5);
    }

    println!("\n── Series 14: χ reduction — how many edges break the colour bound?");
    {
        // For each (G, target chromatic number t), compute |G, K_t|_0
        let cases: &[(&str, Graph, usize)] = &[
            ("Petersen",             petersen(),    2),
            ("Petersen",             petersen(),    3),
            ("Grötzsch (M4)",        mycielski(4),  3),
            ("Grötzsch (M4)",        mycielski(4),  4),
            ("Kneser K(6,2)",        kneser(6, 2),  3),
            ("Kneser K(6,2)",        kneser(6, 2),  4),
            ("Icosahedron",          icosahedron(), 3),
            ("Icosahedron",          icosahedron(), 4),
            ("Paley(13)",            paley_13(),    3),
            ("Paley(13)",            paley_13(),    4),
        ];
        for (name, g, t) in cases {
            let h = complete(*t);
            let label = format!("{name} → K{t}");
            run(&label, g, &h);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── Graph primitive tests ────────────────────────────────────────────────

    #[test]
    fn graph_empty_has_no_edges() {
        let g = Graph::new(5);
        assert_eq!(g.edge_count(), 0);
        for u in 0..5 {
            assert_eq!(g.degree(u), 0);
            for v in 0..5 {
                assert!(!g.has_edge(u, v));
            }
        }
    }

    #[test]
    fn graph_add_edge_is_symmetric() {
        let mut g = Graph::new(4);
        g.add_edge(0, 3);
        assert!(g.has_edge(0, 3));
        assert!(g.has_edge(3, 0));
        assert!(!g.has_edge(0, 1));
    }

    #[test]
    fn graph_edge_count_and_degree() {
        let g = complete(4);
        assert_eq!(g.edge_count(), 6);
        for u in 0..4 {
            assert_eq!(g.degree(u), 3);
        }
    }

    #[test]
    fn graph_add_edge_idempotent() {
        let mut g = Graph::new(3);
        g.add_edge(0, 1);
        g.add_edge(0, 1);
        assert_eq!(g.edge_count(), 1);
    }

    // ── Builder tests ────────────────────────────────────────────────────────

    #[test]
    fn complete_graph_structure() {
        for n in 1..=6 {
            let g = complete(n);
            assert_eq!(g.n, n);
            assert_eq!(g.edge_count(), n * (n - 1) / 2);
            for u in 0..n {
                assert_eq!(g.degree(u) as usize, n - 1);
                for v in 0..n {
                    if u != v {
                        assert!(g.has_edge(u, v));
                    } else {
                        assert!(!g.has_edge(u, v));
                    }
                }
            }
        }
    }

    #[test]
    fn cycle_graph_structure() {
        for n in 3..=8 {
            let g = cycle(n);
            assert_eq!(g.n, n);
            assert_eq!(g.edge_count(), n);
            for u in 0..n {
                assert_eq!(g.degree(u), 2);
                assert!(g.has_edge(u, (u + 1) % n));
            }
        }
    }

    #[test]
    fn petersen_graph_structure() {
        let g = petersen();
        assert_eq!(g.n, 10);
        assert_eq!(g.edge_count(), 15);
        for u in 0..10 {
            assert_eq!(g.degree(u), 3);
        }
    }

    #[test]
    fn grid_structure() {
        let g = grid(3, 4);
        assert_eq!(g.n, 12);
        // 3 rows × 3 horizontal + 2 col-gaps × 4 vertical = 9 + 8
        assert_eq!(g.edge_count(), 17);
    }

    #[test]
    fn bipartite_complete_structure() {
        let g = bipartite_complete(3, 4);
        assert_eq!(g.n, 7);
        assert_eq!(g.edge_count(), 12);
        for u in 0..3 {
            for v in 0..3 {
                if u != v { assert!(!g.has_edge(u, v)); }
            }
        }
        for u in 3..7 {
            for v in 3..7 {
                if u != v { assert!(!g.has_edge(u, v)); }
            }
        }
        for u in 0..3 {
            for v in 3..7 {
                assert!(g.has_edge(u, v));
            }
        }
    }

    #[test]
    fn circulant_structure() {
        let g = circulant(6, &[1, 2]);
        assert_eq!(g.n, 6);
        for u in 0..6 {
            assert_eq!(g.degree(u), 4);
        }
    }

    // ── nonhom_param: known values ───────────────────────────────────────────

    #[test]
    fn same_graph_target_is_zero() {
        let k4 = complete(4);
        assert_eq!(nonhom_param(&k4, &k4), 0);
    }

    #[test]
    fn k1_target_removes_all_edges() {
        let k3 = complete(3);
        let k1 = complete(1);
        assert_eq!(nonhom_param(&k3, &k1), 3);
    }

    #[test]
    fn edgeless_source_is_zero() {
        let empty = Graph::new(4);
        assert_eq!(nonhom_param(&empty, &complete(3)), 0);
    }

    #[test]
    fn single_edge_to_k1_is_one() {
        assert_eq!(nonhom_param(&complete(2), &complete(1)), 1);
    }

    #[test]
    fn single_edge_to_k2_is_zero() {
        assert_eq!(nonhom_param(&complete(2), &complete(2)), 0);
    }

    #[test]
    fn c5_to_k2_is_one() {
        assert_eq!(nonhom_param(&cycle(5), &complete(2)), 1);
    }

    #[test]
    fn c7_to_k2_is_one() {
        assert_eq!(nonhom_param(&cycle(7), &complete(2)), 1);
    }

    #[test]
    fn even_cycles_to_k2_are_zero() {
        for n in [4, 6, 8, 10] {
            assert_eq!(nonhom_param(&cycle(n), &complete(2)), 0,
                "C{n} → K2 should be 0");
        }
    }

    #[test]
    fn petersen_to_k3_is_zero() {
        assert_eq!(nonhom_param(&petersen(), &complete(3)), 0);
    }

    #[test]
    fn petersen_to_k4_is_zero() {
        assert_eq!(nonhom_param(&petersen(), &complete(4)), 0);
    }

    #[test]
    fn petersen_to_k2_is_three() {
        assert_eq!(nonhom_param(&petersen(), &complete(2)), 3);
    }

    #[test]
    fn petersen_to_c5_is_two() {
        assert_eq!(nonhom_param(&petersen(), &cycle(5)), 2);
    }

    #[test]
    fn k4_to_k3_is_one() {
        assert_eq!(nonhom_param(&complete(4), &complete(3)), 1);
    }

    #[test]
    fn k5_to_k3_is_two() {
        assert_eq!(nonhom_param(&complete(5), &complete(3)), 2);
    }

    #[test]
    fn k5_to_k4_is_one() {
        assert_eq!(nonhom_param(&complete(5), &complete(4)), 1);
    }

    #[test]
    fn kn_to_k3_sequence() {
        let expected = [(4, 1u32), (5, 2), (6, 3), (7, 5), (8, 7), (9, 9), (10, 12)];
        for (n, exp) in expected {
            assert_eq!(nonhom_param(&complete(n), &complete(3)), exp,
                "|K{n},K3|_0 should be {exp}");
        }
    }

    #[test]
    fn cycles_to_k3_are_zero() {
        for n in [3, 5, 7, 9, 12, 15, 20] {
            assert_eq!(nonhom_param(&cycle(n), &complete(3)), 0,
                "C{n} → K3 should be 0");
        }
    }

    #[test]
    fn bipartite_complete_to_k2_is_zero() {
        for (a, b) in [(2, 3), (3, 4), (4, 5), (5, 6)] {
            assert_eq!(nonhom_param(&bipartite_complete(a, b), &complete(2)), 0,
                "K_{{{a},{b}}} → K2 should be 0");
        }
    }

    #[test]
    fn grids_to_k3_are_zero() {
        for r in [2, 3, 4, 5] {
            assert_eq!(nonhom_param(&grid(r, r), &complete(3)), 0,
                "Grid({r}×{r}) → K3 should be 0");
        }
    }

    #[test]
    fn petersen_to_kn_sequence() {
        assert_eq!(nonhom_param(&petersen(), &complete(2)), 3);
        assert_eq!(nonhom_param(&petersen(), &complete(3)), 0);
        assert_eq!(nonhom_param(&petersen(), &complete(4)), 0);
        assert_eq!(nonhom_param(&petersen(), &complete(5)), 0);
    }

    // ── Uncommon graph builder tests ─────────────────────────────────────────

    #[test]
    fn mycielski_m3_is_c5() {
        let m3 = mycielski(3);
        assert_eq!(m3.n, 5);
        assert_eq!(m3.edge_count(), 5);
        for u in 0..5 { assert_eq!(m3.degree(u), 2); }
    }

    #[test]
    fn mycielski_m4_grotzsch() {
        let m4 = mycielski(4);
        assert_eq!(m4.n, 11);
        assert_eq!(m4.edge_count(), 20);
    }

    #[test]
    fn mycielski_m5_structure() {
        let m5 = mycielski(5);
        assert_eq!(m5.n, 23);
        assert_eq!(m5.edge_count(), 71);
    }

    #[test]
    fn kneser_52_is_petersen() {
        let kn = kneser(5, 2);
        assert_eq!(kn.n, 10);
        assert_eq!(kn.edge_count(), 15);
        for u in 0..10 { assert_eq!(kn.degree(u), 3); }
    }

    #[test]
    fn kneser_62_structure() {
        let kn = kneser(6, 2);
        assert_eq!(kn.n, 15);
        assert_eq!(kn.edge_count(), 45); // each of 15 verts has degree 6 → 15*6/2
        for u in 0..15 { assert_eq!(kn.degree(u), 6); }
    }

    #[test]
    fn kneser_72_structure() {
        let kn = kneser(7, 2);
        assert_eq!(kn.n, 21);
        assert_eq!(kn.edge_count(), 105); // degree 10 each
        for u in 0..21 { assert_eq!(kn.degree(u), 10); }
    }

    #[test]
    fn gen_petersen_52_is_petersen() {
        let gp = gen_petersen(5, 2);
        assert_eq!(gp.n, 10);
        assert_eq!(gp.edge_count(), 15);
        for u in 0..10 { assert_eq!(gp.degree(u), 3); }
    }

    #[test]
    fn gen_petersen_structure() {
        // GP(n,k) always has 2n vertices, 3n edges, is 3-regular
        for (n, k) in [(6, 2), (8, 3), (10, 3), (12, 4)] {
            let g = gen_petersen(n, k);
            assert_eq!(g.n, 2 * n, "GP({n},{k}) vertex count");
            assert_eq!(g.edge_count(), 3 * n, "GP({n},{k}) edge count");
            for u in 0..2 * n { assert_eq!(g.degree(u), 3); }
        }
    }

    #[test]
    fn icosahedron_structure() {
        let g = icosahedron();
        assert_eq!(g.n, 12);
        assert_eq!(g.edge_count(), 30);
        for u in 0..12 { assert_eq!(g.degree(u), 5); }
    }

    #[test]
    fn dodecahedron_structure() {
        let g = dodecahedron();
        assert_eq!(g.n, 20);
        assert_eq!(g.edge_count(), 30);
        for u in 0..20 { assert_eq!(g.degree(u), 3); }
    }

    #[test]
    fn heawood_structure() {
        let g = heawood();
        assert_eq!(g.n, 14);
        assert_eq!(g.edge_count(), 21);
        for u in 0..14 { assert_eq!(g.degree(u), 3); }
    }

    #[test]
    fn paley_13_structure() {
        let g = paley_13();
        assert_eq!(g.n, 13);
        assert_eq!(g.edge_count(), 39); // 13 verts × 6-regular / 2
        for u in 0..13 { assert_eq!(g.degree(u), 6); }
    }

    #[test]
    fn octahedron_structure() {
        let g = octahedron();
        assert_eq!(g.n, 6);
        assert_eq!(g.edge_count(), 12);
        for u in 0..6 { assert_eq!(g.degree(u), 4); }
    }

    // ── nonhom_param for uncommon graphs — known / derivable values ──────────

    #[test]
    fn mycielski_chromatic_homomorphism() {
        // M(k) is k-chromatic, so M(k)→K_k has a homomorphism (= 0)
        // and M(k)→K_{k-1} does not (> 0)
        let m3 = mycielski(3); // χ=3
        assert_eq!(nonhom_param(&m3, &complete(3)), 0);
        assert_eq!(nonhom_param(&m3, &complete(2)), 1); // C5→K2 = 1
        let m4 = mycielski(4); // χ=4
        assert_eq!(nonhom_param(&m4, &complete(4)), 0);
        assert!(nonhom_param(&m4, &complete(3)) > 0); // 4-chromatic → not 3-colourable
    }

    #[test]
    fn kneser_chromatic_homomorphism() {
        // χ(K(n,2)) = n-2, so K(n,2)→K_{n-2} exists, K(n,2)→K_{n-3} does not
        let kn52 = kneser(5, 2); // χ=3
        assert_eq!(nonhom_param(&kn52, &complete(3)), 0);
        assert!(nonhom_param(&kn52, &complete(2)) > 0);

        let kn62 = kneser(6, 2); // χ=4
        assert_eq!(nonhom_param(&kn62, &complete(4)), 0);
        assert!(nonhom_param(&kn62, &complete(3)) > 0);
    }

    #[test]
    fn heawood_is_bipartite() {
        // Heawood is bipartite ⇒ |Heawood, K2|_0 = 0
        assert_eq!(nonhom_param(&heawood(), &complete(2)), 0);
        assert_eq!(nonhom_param(&heawood(), &complete(3)), 0);
    }

    #[test]
    fn mobius_kantor_is_bipartite() {
        assert_eq!(nonhom_param(&mobius_kantor(), &complete(2)), 0);
    }

    #[test]
    fn pappus_is_bipartite() {
        assert_eq!(nonhom_param(&pappus(), &complete(2)), 0);
    }

    #[test]
    fn octahedron_is_3_colourable() {
        // K_{2,2,2}: parts give a proper 3-colouring
        assert_eq!(nonhom_param(&octahedron(), &complete(3)), 0);
        // But it is not bipartite (contains odd cycles C3)
        assert!(nonhom_param(&octahedron(), &complete(2)) > 0);
    }

    #[test]
    fn gen_petersen_gp62_to_k3() {
        // GP(6,2) is 3-colourable
        assert_eq!(nonhom_param(&gen_petersen(6, 2), &complete(3)), 0);
    }

    #[test]
    fn petersen_plus_one_edge_structure() {
        let g = petersen_plus_one_edge();
        assert_eq!(g.n, 10);
        assert_eq!(g.edge_count(), 16); // Petersen's 15 + 1
        assert!(g.has_edge(0, 2));
        assert!(g.has_edge(2, 0));
        // Original Petersen edges still present
        assert!(g.has_edge(0, 1));
        assert!(g.has_edge(0, 4));
        assert!(g.has_edge(0, 5));
    }

    #[test]
    fn petersen_plus_one_edge_to_k3() {
        let g = petersen_plus_one_edge();
        let k3 = complete(3);
        let result = nonhom_param(&g, &k3);
        println!("|PetGraphPlusOneEdge, K3|_0 = {result}");
        // The Petersen graph has a 3-colouring where 0 and 2 get different
        // colours, so adding edge 0-2 leaves the graph 3-colourable.
        assert_eq!(result, 0);
    }

    #[test]
    fn kneser_21_equals_complete() {
        // K(n,1) = K_n (only 1-subsets, all disjoint → fully connected)
        for n in [3, 4, 5] {
            let kn1 = kneser(n, 1);
            let kn  = complete(n);
            assert_eq!(kn1.edge_count(), kn.edge_count());
        }
    }
}
