use petgraph::graph::{Graph, NodeIndex};
use petgraph::visit::EdgeRef;
use std::collections::HashMap;

// Check if there is a homomorphism from G to H
fn has_homomorphism(g: &Graph<(), ()>, h: &Graph<(), ()>) -> bool {
    let g_nodes: Vec<NodeIndex> = g.node_indices().collect();
    let h_nodes: Vec<NodeIndex> = h.node_indices().collect();

    fn is_homomorphism(
        g: &Graph<(), ()>,
        h: &Graph<(), ()>,
        g_nodes: &[NodeIndex],
        h_nodes: &[NodeIndex],
        mapping: &mut HashMap<NodeIndex, NodeIndex>,
        index: usize,
    ) -> bool {
        if index == g_nodes.len() {
            return true;
        }

        let u = g_nodes[index];
        for &v in h_nodes {
            mapping.insert(u, v);

            let mut valid = true;
            for edge in g.edges(u) {
                let neighbor = edge.target();
                if let Some(&mapped_neighbor) = mapping.get(&neighbor) {
                    if !h.contains_edge(v, mapped_neighbor) {
                        valid = false;
                        break;
                    }
                }
            }

            if valid && is_homomorphism(g, h, g_nodes, h_nodes, mapping, index + 1) {
                return true;
            }

            mapping.remove(&u);
        }

        false
    }

    is_homomorphism(
        g,
        h,
        &g_nodes,
        &h_nodes,
        &mut HashMap::new(),
        0,
    )
}

fn main() {
    // Create graph G
    let mut g = Graph::new();
    let g_a = g.add_node(());
    let g_b = g.add_node(());
    let g_c = g.add_node(());
    g.add_edge(g_a, g_b, ());
    g.add_edge(g_b, g_c, ());
    g.add_edge(g_c, g_a, ());

    // Create graph H
    let mut h = Graph::new();
    let h_a = h.add_node(());
    let h_b = h.add_node(());
    let h_c = h.add_node(());
    let h_d = h.add_node(());
    h.add_edge(h_a, h_b, ());
    h.add_edge(h_b, h_c, ());
    h.add_edge(h_c, h_d, ());
    h.add_edge(h_d, h_a, ());
    h.add_edge(h_a, h_c, ());
    h.add_edge(h_b, h_d, ());

    // Check for homomorphism from G to H
    if has_homomorphism(&g, &h) {
        println!("There is a homomorphism from G to H");
    } else {
        println!("There is no homomorphism from G to H");
    }
}
