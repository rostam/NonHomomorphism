use petgraph::graph::{NodeIndex, UnGraph};

/// Returns a homomorphism mapping from G to H (as a Vec indexed by G node index),
/// or None if no homomorphism exists.
fn find_homomorphism(g: &UnGraph<(), ()>, h: &UnGraph<(), ()>) -> Option<Vec<NodeIndex>> {
    let g_nodes: Vec<NodeIndex> = g.node_indices().collect();
    let h_nodes: Vec<NodeIndex> = h.node_indices().collect();
    let mut mapping: Vec<Option<NodeIndex>> = vec![None; g_nodes.len()];

    fn backtrack(
        g: &UnGraph<(), ()>,
        h: &UnGraph<(), ()>,
        g_nodes: &[NodeIndex],
        h_nodes: &[NodeIndex],
        mapping: &mut Vec<Option<NodeIndex>>,
        index: usize,
    ) -> bool {
        if index == g_nodes.len() {
            return true;
        }

        let u = g_nodes[index];
        for &v in h_nodes {
            // Early constraint check: every already-mapped neighbor of u
            // must be adjacent to v in H.
            let valid = g.neighbors(u).all(|nb| {
                let nb_idx = nb.index();
                match mapping[nb_idx] {
                    Some(mapped_nb) => h.contains_edge(v, mapped_nb),
                    None => true,
                }
            });

            if valid {
                mapping[u.index()] = Some(v);
                if backtrack(g, h, g_nodes, h_nodes, mapping, index + 1) {
                    return true;
                }
                mapping[u.index()] = None;
            }
        }
        false
    }

    if backtrack(g, h, &g_nodes, &h_nodes, &mut mapping, 0) {
        Some(mapping.into_iter().map(|m| m.unwrap()).collect())
    } else {
        None
    }
}

fn build_petersen() -> UnGraph<(), ()> {
    let mut g = UnGraph::new_undirected();
    let nodes: Vec<NodeIndex> = (0..10).map(|_| g.add_node(())).collect();
    for i in 0..5 {
        g.add_edge(nodes[i], nodes[(i + 1) % 5], ());       // outer pentagon
        g.add_edge(nodes[i], nodes[i + 5], ());              // spokes
        g.add_edge(nodes[i + 5], nodes[((i + 2) % 5) + 5], ()); // inner pentagram
    }
    g
}

fn build_complete(n: usize) -> UnGraph<(), ()> {
    let mut g = UnGraph::new_undirected();
    let nodes: Vec<NodeIndex> = (0..n).map(|_| g.add_node(())).collect();
    for i in 0..n {
        for j in (i + 1)..n {
            g.add_edge(nodes[i], nodes[j], ());
        }
    }
    g
}

fn build_cycle(n: usize) -> UnGraph<(), ()> {
    let mut g = UnGraph::new_undirected();
    let nodes: Vec<NodeIndex> = (0..n).map(|_| g.add_node(())).collect();
    for i in 0..n {
        g.add_edge(nodes[i], nodes[(i + 1) % n], ());
    }
    g
}

fn main() {
    let petersen = build_petersen();
    let k3 = build_complete(3);
    let k4 = build_complete(4);
    let c4 = build_cycle(4);

    // Petersen is 3-chromatic, so it maps to K3.
    match find_homomorphism(&petersen, &k3) {
        Some(m) => {
            println!("Petersen -> K3: homomorphism found");
            for (i, t) in m.iter().enumerate() {
                println!("  G[{}] -> H[{}]", i, t.index());
            }
        }
        None => println!("Petersen -> K3: no homomorphism (unexpected)"),
    }

    // Petersen also maps to K4.
    match find_homomorphism(&petersen, &k4) {
        Some(_) => println!("\nPetersen -> K4: homomorphism found"),
        None => println!("\nPetersen -> K4: no homomorphism (unexpected)"),
    }

    // C4 is bipartite (2-chromatic); Petersen is 3-chromatic — no homomorphism.
    match find_homomorphism(&petersen, &c4) {
        Some(_) => println!("\nPetersen -> C4: homomorphism found (unexpected)"),
        None => println!("\nPetersen -> C4: no homomorphism (correct)"),
    }

    // Triangle -> K4: should exist.
    let triangle = build_complete(3);
    match find_homomorphism(&triangle, &k4) {
        Some(_) => println!("\nK3 -> K4: homomorphism found"),
        None => println!("\nK3 -> K4: no homomorphism (unexpected)"),
    }
}
