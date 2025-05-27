#include <iostream>
#include <vector>
#include <set>
#include <algorithm>
#include <functional>
#include <numeric>
#include <optional>
#include <random>

using namespace std;

struct Graph {
    int n;
    vector<pair<int, int>> edges;
    vector<vector<int>> adj;

    explicit Graph(const int nodes) : n(nodes), adj(nodes) {}

    void add_edge(int u, int v) {
        edges.emplace_back(u, v);
        adj[u].push_back(v);
        adj[v].push_back(u);
    }

    void remove_edges(const set<int>& to_remove) {
        adj.assign(n, {});
        for (int i = 0; i < edges.size(); ++i) {
            if (to_remove.contains(i)) continue;
            int u = edges[i].first, v = edges[i].second;
            adj[u].push_back(v);
            adj[v].push_back(u);
        }
    }
};

optional<vector<int>> find_homomorphism(const Graph& G, const Graph& H) {
    const int nG = G.n;
    const int nH = H.n;
    vector<int> mapping(nG);
    function<bool(int)> dfs = [&](const int i) {
        if (i == nG) {
            for (int u = 0; u < nG; ++u) {
                for (const int v : G.adj[u]) {
                    bool found = false;
                    for (const int w : H.adj[mapping[u]]) {
                        if (w == mapping[v]) {
                            found = true;
                            break;
                        }
                    }
                    if (!found) return false;
                }
            }
            return true;
        }
        for (int j = 0; j < nH; ++j) {
            mapping[i] = j;
            if (dfs(i + 1)) return true;
        }
        return false;
    };
    if (dfs(0)) return mapping;
    return nullopt;
}

// Try removing up to k edges and check homomorphism
pair<int, optional<vector<int>>> estimate_non_homomorphism_factor(Graph& G, const Graph& H, const int max_k = 5) {
    const auto m = G.edges.size();
    for (int k = 0; k <= max_k; ++k) {
        vector<int> idx(m);
        iota(idx.begin(), idx.end(), 0);
        vector<bool> select(m, false);
        fill(select.end() - k, select.end(), true);
        do {
            set<int> remove_idx;
            for (int i = 0; i < m; ++i) {
                if (select[i]) remove_idx.insert(i);
            }
            G.remove_edges(remove_idx);
            if (auto mapping = find_homomorphism(G, H); mapping.has_value()) {
                return {k, mapping};
            }
        } while (ranges::next_permutation(select).found);
    }
    return {-1, nullopt};  // Homomorphism isn't found within k deletions
}

Graph build_petersen() {
    Graph G(10);
    for (int i = 0; i < 5; ++i) {
        G.add_edge(i, (i + 1) % 5);             // Outer pentagon
        G.add_edge(i, i + 5);                   // Spokes
        G.add_edge(i + 5, ((i + 2) % 5) + 5);   // Inner star
    }
    return G;
}

Graph build_triangle() {
    Graph H(3);
    H.add_edge(0, 1);
    H.add_edge(1, 2);
    H.add_edge(2, 0);
    return H;
}

Graph build_random_graph(int n, double edge_prob = 0.3) {
    Graph G(n);
    random_device rd;
    mt19937 gen(rd());
    uniform_real_distribution<> dis(0.0, 1.0);

    for (int u = 0; u < n; ++u) {
        for (int v = u + 1; v < n; ++v) {
            if (dis(gen) < edge_prob) {
                G.add_edge(u, v);
            }
        }
    }
    return G;
}

Graph build_complete_graph(int n) {
    Graph G(n);
    for (int u = 0; u < n; ++u) {
        for (int v = u + 1; v < n; ++v) {
            G.add_edge(u, v);
        }
    }
    return G;
}

Graph build_cycle_graph(int n) {
    Graph G(n);
    for (int i = 0; i < n; ++i) {
        G.add_edge(i, (i + 1) % n);
    }
    return G;
}

Graph build_bipartite_graph(int n1, int n2) {
    Graph G(n1 + n2);
    for (int u = 0; u < n1; ++u) {
        for (int v = 0; v < n2; ++v) {
            G.add_edge(u, n1 + v);
        }
    }
    return G;
}


bool is_valid_homomorphism(const Graph& G, const Graph& H, const vector<int>& mapping) {
    for (int u = 0; u < G.n; ++u) {
        for (const int v : G.adj[u]) {
            const int hu = mapping[u];
            const int hv = mapping[v];
            bool edge_exists = false;
            for (int w : H.adj[hu]) {
                if (w == hv) {
                    edge_exists = true;
                    break;
                }
            }
            if (!edge_exists) {
                return false;
            }
        }
    }
    return true;
}


int main() {
    Graph G = build_petersen();
    const Graph H = build_triangle();

    vector<pair<string, Graph>> test_graphs = {
        {"Petersen", build_petersen()},
        {"Random10", build_random_graph(10, 0.3)},
        {"Complete5", build_complete_graph(5)},
        {"Cycle10", build_cycle_graph(10)},
        {"Bipartite_5_5", build_bipartite_graph(5, 5)}
    };

    for (auto& [name, G] : test_graphs) {
        cout << "=== Testing Graph: " << name << " ===" << endl;
        if (auto [k, mapping] = estimate_non_homomorphism_factor(G, H, 5); k >= 0 && mapping.has_value()) {
            cout << "|" << name << ", K3| = " << k << endl;
            cout << "Homomorphism mapping (vertex in " << name << " → vertex in K3):" << endl;
            cout << "Homomorphism validity: " << is_valid_homomorphism(G, H, *mapping) << endl;
            for (int i = 0; i < mapping->size(); ++i) {
                cout << "G[" << i << "] → H[" << (*mapping)[i] << "]" << endl;
            }
        } else {
            cout << "No homomorphism found with ≤ 5 deletions for " << name << ".\n";
        }
        cout << endl;
    }
    return 0;
}
