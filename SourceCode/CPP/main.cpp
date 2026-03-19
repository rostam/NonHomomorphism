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
    vector<vector<bool>> adj_matrix;

    explicit Graph(const int nodes)
        : n(nodes), adj(nodes), adj_matrix(nodes, vector<bool>(nodes, false)) {}

    void add_edge(int u, int v) {
        edges.emplace_back(u, v);
        adj[u].push_back(v);
        adj[v].push_back(u);
        adj_matrix[u][v] = true;
        adj_matrix[v][u] = true;
    }

    void remove_edges(const set<int>& to_remove) {
        adj.assign(n, {});
        adj_matrix.assign(n, vector<bool>(n, false));
        for (int i = 0; i < (int)edges.size(); ++i) {
            if (to_remove.contains(i)) continue;
            int u = edges[i].first, v = edges[i].second;
            adj[u].push_back(v);
            adj[v].push_back(u);
            adj_matrix[u][v] = true;
            adj_matrix[v][u] = true;
        }
    }
};

// DFS with early pruning: as soon as vertex i is assigned to j,
// check all already-assigned neighbors of i for adjacency in H.
optional<vector<int>> find_homomorphism(const Graph& G, const Graph& H) {
    const int nG = G.n;
    const int nH = H.n;
    vector<int> mapping(nG, -1);

    function<bool(int)> dfs = [&](int i) -> bool {
        if (i == nG) return true;
        for (int j = 0; j < nH; ++j) {
            // Early constraint check: every already-assigned neighbor of i
            // must be connected to j in H.
            bool valid = true;
            for (int nb : G.adj[i]) {
                if (mapping[nb] != -1 && !H.adj_matrix[j][mapping[nb]]) {
                    valid = false;
                    break;
                }
            }
            if (!valid) continue;

            mapping[i] = j;
            if (dfs(i + 1)) return true;
            mapping[i] = -1;
        }
        return false;
    };

    if (dfs(0)) return mapping;
    return nullopt;
}

// Try removing up to max_k edges from G and check for a homomorphism to H.
// Returns {k, mapping} where k is the non-homomorphism factor |G,H|.
pair<int, optional<vector<int>>> estimate_non_homomorphism_factor(
        Graph& G, const Graph& H, const int max_k = 5) {
    const int m = (int)G.edges.size();
    for (int k = 0; k <= max_k; ++k) {
        vector<bool> select(m, false);
        fill(select.end() - k, select.end(), true);
        do {
            set<int> remove_idx;
            for (int i = 0; i < m; ++i) {
                if (select[i]) remove_idx.insert(i);
            }
            G.remove_edges(remove_idx);
            if (auto mapping = find_homomorphism(G, H)) {
                return {k, mapping};
            }
        } while (ranges::next_permutation(select).found);
    }
    return {-1, nullopt};
}

bool is_valid_homomorphism(const Graph& G, const Graph& H, const vector<int>& mapping) {
    for (int u = 0; u < G.n; ++u) {
        for (const int v : G.adj[u]) {
            if (!H.adj_matrix[mapping[u]][mapping[v]]) return false;
        }
    }
    return true;
}

Graph build_petersen() {
    Graph G(10);
    for (int i = 0; i < 5; ++i) {
        G.add_edge(i, (i + 1) % 5);              // outer pentagon
        G.add_edge(i, i + 5);                    // spokes
        G.add_edge(i + 5, ((i + 2) % 5) + 5);    // inner pentagram
    }
    return G;
}

Graph build_complete_graph(int n) {
    Graph G(n);
    for (int u = 0; u < n; ++u)
        for (int v = u + 1; v < n; ++v)
            G.add_edge(u, v);
    return G;
}

Graph build_cycle_graph(int n) {
    Graph G(n);
    for (int i = 0; i < n; ++i)
        G.add_edge(i, (i + 1) % n);
    return G;
}

Graph build_bipartite_graph(int n1, int n2) {
    Graph G(n1 + n2);
    for (int u = 0; u < n1; ++u)
        for (int v = 0; v < n2; ++v)
            G.add_edge(u, n1 + v);
    return G;
}

Graph build_random_graph(int n, double edge_prob = 0.3) {
    Graph G(n);
    mt19937 gen(random_device{}());
    uniform_real_distribution<> dis(0.0, 1.0);
    for (int u = 0; u < n; ++u)
        for (int v = u + 1; v < n; ++v)
            if (dis(gen) < edge_prob)
                G.add_edge(u, v);
    return G;
}

int main() {
    const Graph K3 = build_complete_graph(3);

    vector<pair<string, Graph>> test_graphs = {
        {"Petersen",     build_petersen()},
        {"Random10",     build_random_graph(10, 0.3)},
        {"Complete5",    build_complete_graph(5)},
        {"Cycle10",      build_cycle_graph(10)},
        {"Bipartite_5_5",build_bipartite_graph(5, 5)},
    };

    for (auto& [name, G] : test_graphs) {
        cout << "=== " << name << " ===" << endl;
        auto [k, mapping] = estimate_non_homomorphism_factor(G, K3, 5);
        if (k >= 0 && mapping) {
            cout << "|" << name << ", K3| = " << k << endl;
            cout << "Homomorphism valid: "
                 << boolalpha << is_valid_homomorphism(G, K3, *mapping) << endl;
            for (int i = 0; i < (int)mapping->size(); ++i)
                cout << "  G[" << i << "] -> K3[" << (*mapping)[i] << "]\n";
        } else {
            cout << "No homomorphism found within " << 5 << " deletions.\n";
        }
        cout << endl;
    }
    return 0;
}
