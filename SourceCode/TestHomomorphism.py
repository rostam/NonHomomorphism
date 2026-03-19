import unittest
import networkx as nx
import FindHomomorphisms as fh


class TestHomomorphisms(unittest.TestCase):
    def test_petersen_to_k3(self):
        # Petersen graph is 3-chromatic, so it maps to K3.
        peterson = nx.petersen_graph()
        k3 = nx.complete_graph(3)
        part = fh.find_a_homomorphism(peterson, k3)
        self.assertTrue(len(part) >= 1, "Expected homomorphism from Petersen to K3")

    def test_petersen_to_k4(self):
        peterson = nx.petersen_graph()
        k4 = nx.complete_graph(4)
        part = fh.find_a_homomorphism(peterson, k4)
        self.assertTrue(len(part) >= 1, "Expected homomorphism from Petersen to K4")

    def test_petersen_not_to_c4(self):
        # C4 is bipartite (2-colourable), Petersen is 3-chromatic — no homomorphism.
        peterson = nx.petersen_graph()
        c4 = nx.cycle_graph(4)
        part = fh.find_a_homomorphism(peterson, c4)
        self.assertEqual(len(part), 0, "Expected no homomorphism from Petersen to C4")

    def test_petersen_to_graphs_up_to_6_vertices(self):
        peterson = nx.petersen_graph()
        for n in range(2, 7):
            filename = f"n{n}.g6"
            with open(filename, "r") as f:
                for line in f:
                    line = line.strip()
                    if line:
                        fh.handle_one_g6_string(peterson, line)


if __name__ == '__main__':
    unittest.main()
