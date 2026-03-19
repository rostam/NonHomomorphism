#include <iostream>
#include <vector>
#include <set>
#include <algorithm>
#include <functional>
#include <numeric>
#include <optional>
#include <limits>
#include <iomanip>

using namespace std;

struct Graph {
    int n;
    string name;
    vector<pair<int, int>> edges;
    vector<vector<int>> adj;
    vector<vector<bool>> adj_matrix;

    explicit Graph(int nodes, string nm = "")
        : n(nodes), name(std::move(nm)), adj(nodes),
          adj_matrix(nodes, vector<bool>(nodes, false)) {}

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
            auto [u, v] = edges[i];
            adj[u].push_back(v);
            adj[v].push_back(u);
            adj_matrix[u][v] = true;
            adj_matrix[v][u] = true;
        }
    }
};

// ── Graph builders ───────────────────────────────────────────────────────────

Graph complete(int n) {
    Graph G(n, "K" + to_string(n));
    for (int u = 0; u < n; ++u)
        for (int v = u + 1; v < n; ++v)
            G.add_edge(u, v);
    return G;
}

Graph cycle(int n) {
    Graph G(n, "C" + to_string(n));
    for (int i = 0; i < n; ++i)
        G.add_edge(i, (i + 1) % n);
    return G;
}

Graph petersen() {
    Graph G(10, "Petersen");
    for (int i = 0; i < 5; ++i) {
        G.add_edge(i, (i + 1) % 5);
        G.add_edge(i, i + 5);
        G.add_edge(i + 5, ((i + 2) % 5) + 5);
    }
    return G;
}

Graph bipartite(int n1, int n2) {
    Graph G(n1 + n2, "K_{" + to_string(n1) + "," + to_string(n2) + "}");
    for (int u = 0; u < n1; ++u)
        for (int v = 0; v < n2; ++v)
            G.add_edge(u, n1 + v);
    return G;
}

// ── Core search routines ─────────────────────────────────────────────────────

// Find ONE homomorphism (backtracking with early pruning).
optional<vector<int>> find_homomorphism(const Graph& G, const Graph& H) {
    vector<int> mapping(G.n, -1);
    function<bool(int)> dfs = [&](int i) -> bool {
        if (i == G.n) return true;
        for (int j = 0; j < H.n; ++j) {
            bool ok = true;
            for (int nb : G.adj[i])
                if (mapping[nb] != -1 && !H.adj_matrix[j][mapping[nb]])
                    { ok = false; break; }
            if (!ok) continue;
            mapping[i] = j;
            if (dfs(i + 1)) return true;
            mapping[i] = -1;
        }
        return false;
    };
    if (dfs(0)) return mapping;
    return nullopt;
}

// Enumerate ALL homomorphisms from G to H.
vector<vector<int>> all_homomorphisms(const Graph& G, const Graph& H) {
    vector<vector<int>> results;
    vector<int> mapping(G.n, -1);
    function<void(int)> dfs = [&](int i) {
        if (i == G.n) { results.push_back(mapping); return; }
        for (int j = 0; j < H.n; ++j) {
            bool ok = true;
            for (int nb : G.adj[i])
                if (mapping[nb] != -1 && !H.adj_matrix[j][mapping[nb]])
                    { ok = false; break; }
            if (!ok) continue;
            mapping[i] = j;
            dfs(i + 1);
            mapping[i] = -1;
        }
    };
    dfs(0);
    return results;
}

// Non-homomorphism factor |G, H| (exact, tries k = 0, 1, 2, ..., max_k).
int non_homo_factor(Graph G, const Graph& H, int max_k = 6) {
    int m = (int)G.edges.size();
    for (int k = 0; k <= max_k; ++k) {
        vector<bool> sel(m, false);
        fill(sel.end() - k, sel.end(), true);
        do {
            set<int> rm;
            for (int i = 0; i < m; ++i) if (sel[i]) rm.insert(i);
            G.remove_edges(rm);
            if (find_homomorphism(G, H)) return k;
        } while (ranges::next_permutation(sel).found);
    }
    return -1;  // not found within max_k
}

// Concentration parameter γ(G, H): min over all homs of max edge multiplicity.
// Returns -1 if G does not map to H.
int gamma(const Graph& G, const Graph& H) {
    auto homs = all_homomorphisms(G, H);
    if (homs.empty()) return -1;

    int best = numeric_limits<int>::max();
    int m_H = (int)H.edges.size();

    for (const auto& f : homs) {
        // For each H-edge, count how many G-edges map to it.
        vector<int> count(m_H, 0);
        for (auto [u, v] : G.edges) {
            int fu = f[u], fv = f[v];
            // find which H-edge index {fu,fv} corresponds to
            for (int ei = 0; ei < m_H; ++ei) {
                auto [a, b] = H.edges[ei];
                if ((a == fu && b == fv) || (a == fv && b == fu)) {
                    ++count[ei];
                    break;
                }
            }
        }
        int alpha = *max_element(count.begin(), count.end());
        best = min(best, alpha);
    }
    return best;
}

// ── Result tables ────────────────────────────────────────────────────────────

void table_Kn_Km() {
    cout << "\n=== Table 1: |K_n, K_m| ===\n";
    cout << "     ";
    for (int m = 2; m <= 6; ++m) cout << setw(5) << ("K"+to_string(m));
    cout << "\n";
    for (int n = 2; n <= 7; ++n) {
        cout << setw(4) << ("K"+to_string(n)) << " ";
        for (int m = 2; m <= 6; ++m) {
            Graph G = complete(n);
            Graph H = complete(m);
            int f = non_homo_factor(G, H, 8);
            if (f < 0) cout << setw(5) << ">8";
            else       cout << setw(5) << f;
        }
        cout << "\n";
    }
}

void table_Cn_K3() {
    cout << "\n=== Table 2: |C_n, K_3| and γ(C_n, K_3) ===\n";
    cout << setw(6) << "C_n"
         << setw(8) << "|E(C_n)|"
         << setw(12) << "|C_n, K3|"
         << setw(14) << "γ(C_n, K3)"
         << "\n";
    Graph K3 = complete(3);
    for (int n = 3; n <= 11; ++n) {
        Graph G = cycle(n);
        int nhf = non_homo_factor(G, K3, 4);
        int gam = gamma(G, K3);
        string gam_str = (gam < 0) ? "∞" : to_string(gam);
        cout << setw(6) << ("C"+to_string(n))
             << setw(8) << n
             << setw(12) << (nhf < 0 ? ">4" : to_string(nhf))
             << setw(14) << gam_str
             << "\n";
    }
}

void table_petersen_Km() {
    cout << "\n=== Table 3: |Petersen, K_m| and γ(Petersen, K_m) ===\n";
    cout << setw(6) << "K_m"
         << setw(14) << "|Petersen,Km|"
         << setw(16) << "γ(Petersen,Km)"
         << "\n";
    Graph P = petersen();
    for (int m = 2; m <= 5; ++m) {
        Graph H = complete(m);
        int nhf = non_homo_factor(P, H, 6);
        int gam = gamma(P, H);
        string gam_str = (gam < 0) ? "∞" : to_string(gam);
        cout << setw(6) << ("K"+to_string(m))
             << setw(14) << (nhf < 0 ? ">6" : to_string(nhf))
             << setw(16) << gam_str
             << "\n";
    }
}

void table_bipartite_K3() {
    cout << "\n=== Table 4: |K_{n,n}, K_3| ===\n";
    Graph K3 = complete(3);
    for (int n = 1; n <= 4; ++n) {
        Graph G = bipartite(n, n);
        int nhf = non_homo_factor(G, K3, 4);
        int gam = gamma(G, K3);
        string gam_str = (gam < 0) ? "∞" : to_string(gam);
        cout << "  |K_{" << n << "," << n << "}, K3| = " << nhf
             << "   γ = " << gam_str << "\n";
    }
}

void verify_propositions() {
    cout << "\n=== Proposition verification ===\n";

    // Prop: if H1 -> H2 then |G,H1| >= |G,H2| for all G
    // K3 -> K4, so |G,K3| >= |G,K4| for any G.
    {
        Graph G = petersen();
        Graph K3 = complete(3), K4 = complete(4);
        int a = non_homo_factor(G, K3, 5);
        int b = non_homo_factor(G, K4, 5);
        cout << "  |Petersen,K3|=" << a << " >= |Petersen,K4|=" << b
             << " : " << (a >= b ? "OK" : "FAIL") << "\n";
    }

    // Prop: |K_{n+1}, K_n| = 1 for n = 2,3,4
    for (int n = 2; n <= 4; ++n) {
        Graph G = complete(n + 1);
        Graph H = complete(n);
        int f = non_homo_factor(G, H, 3);
        cout << "  |K" << (n+1) << ",K" << n << "| = " << f
             << " (expected 1): " << (f == 1 ? "OK" : "FAIL") << "\n";
    }

    // Gamma triangle inequality: γ(G,K) <= γ(G,H) * γ(H,K)
    // Use G=Petersen, H=K3, K=K4 (K3->K4).
    {
        Graph P = petersen(), K3 = complete(3), K4 = complete(4);
        int gPK3 = gamma(P, K3);
        int gK3K4 = gamma(K3, K4);
        int gPK4 = gamma(P, K4);
        cout << "  γ(Petersen,K4)=" << gPK4
             << " <= γ(Petersen,K3)*γ(K3,K4)=" << gPK3 << "*" << gK3K4
             << "=" << gPK3*gK3K4
             << " : " << (gPK4 <= gPK3*gK3K4 ? "OK" : "FAIL") << "\n";
    }

    // Lemma: |G,K| <= γ(G,H) * |H,K|
    // G=Petersen, H=K3, K=K4 (|K3,K4|=0 since K3->K4, so trivial).
    // Use K=K2 instead: |K3,K2|=1.
    {
        Graph P = petersen(), K3 = complete(3), K2 = complete(2);
        int gPK3 = gamma(P, K3);
        int nhfK3K2 = non_homo_factor(K3, K2, 3);
        int nhfPK2 = non_homo_factor(P, K2, 10);
        cout << "  |Petersen,K2|=" << nhfPK2
             << " <= γ(Petersen,K3)*|K3,K2|=" << gPK3 << "*" << nhfK3K2
             << "=" << gPK3*nhfK3K2
             << " : " << (nhfPK2 <= gPK3*nhfK3K2 ? "OK" : "FAIL") << "\n";
    }
}

int main() {
    table_Kn_Km();
    table_Cn_K3();
    table_petersen_Km();
    table_bipartite_K3();
    verify_propositions();
    return 0;
}
