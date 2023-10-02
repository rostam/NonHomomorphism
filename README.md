# Introduction
In this section, I aim to present a series of results that build upon the definitions outlined in [[1]](#1), specifically those pertaining to Homomorphisms and Nonhomomorphisms. Before delving into the main topics, let's first familiarize ourselves with some essential definitions and established theorems.

Let $G=(V(G),E(G))$ and $H=(V(H),E(H))$ be two graphs. A homomorphism from $G$ to $H$ is a function $f:V(G)→V(H)$ such that for every edge $(u,v)$ in $E(G)$, the pair $(f(u),f(v))$ is an edge in $E(H)$. A homomorphism between two graphs doesn't always exist. When a function provides a homomorphism from graph $G$ to $H$, it is denoted as $G\rightarrow H$. It's important to highlight that the function $f$ is not necessarily injective or surjective. However, such specific types of homomorphisms are also worthy of study. If the function $f$ is both injective and surjective, the graphs are isomorphic. An isomorphism of a graph to itself is called automorphism. 

A vertex coloring of a graph is to color vertices with some colors such that no two connected vertices have same colors. The smallest number of colors needed to color the vertices of a graph $G$ is called its chromatic number, and is often denoted by $\chi (G)$. A known [[3]](#3) connection of graph coloring and homomorphism is as follows,
$$G\rightarrow H \Rightarrow \chi (G)\leq\chi (H)$$

A graph $H$ is called vertex transitive if for any two vertex $u$ and $v$, an isomorphism exists that maps $u$ to $v$. Let $n(G,H)$ denote the number of vertices in the largest induced subgraph of $G$ that is homomorphic to $H$. The following theorem is presented in [[3]](#3):
$$\frac{n(H,K)}{|V(H)|}\leq \frac{n(G,K)}{|V(G)|}$$
Also, if the independence number $\alpha(G)$ represents the maximum number of vertices you can select from the graph $G$ such that no two of them are connected by an edge. Then, if there is a homomorphism from $G$ to a vertex-transitive graph $H$,  [[3]](#3) shows the followings,
$$\frac{\alpha (G)}{|V(G)|}\geq \frac{\alpha (H)}{|V(H)|}$$

Let the distance between two vertices $u$ and $v$ in graph $G$, denoted by $d(u,v)$, be the minimum path between them in graph $G$. Assume the function $f$ is the homomorphism from $G$ to $H$, the following result is shown in  [[3]](#3),
$$d_H(f(u), f(v)) \leq d_G(u,v)$$.

If $H$ is a subgraph of $G$, then a retraction of $G$ to $H$ is a homomorphism $r : G \rightarrow H$ such that $r(x) = x$ for all $x \in V (H)$. A graph is a core if it does not admit a homomorphism to a proper subgraph of itself. Every graph $G$ contains a unique (up to isomorphism) subgraph $H$ which is a core and admits a retraction $r : G \rightarrow H$. Then usually this subgraph $H$ is called the core of $G$, and is denoted by $core(G)$. Also note that in this situation for each graph $K$, there exists a homomorphism $f : K \rightarrow G$ if and only if there exists a homomorphism $f : K \rightarrow core(G)$.
Another interesting fact mentioned in [[4]](#4) is as follows. Let G be a vertex–transitive graph. Then, $core(G)$ is a vertex–transitive graph. If $f$ is a homomorphism from G to core(G), then for all vertex $x$, the inverse images $f^{−1}(x)$ have the same cardinality of $\frac{|V(G)|}{|V(core(G))|}$.

# NonHomomorphism Factors
The concept of NonHomomorphism Factors was first introduced in [[1]](#1). While the thesis explores various definitions, here we will focus on a particular version to extend upon. Let's define the Non-Homomorphism Factor between two graphs $G$ and $H$,  denoted as $|G,H|$. as the fewest number of edges one must remove from $G$ to establish at lease one homomorphism from $G$ to $H$. So, if there is already a homomorphism from $G$ to $H$, the nonhomomorphism factor is $0$. Here are some more examples:
- $|K_n,K_{n+1}|=0$
- $|K_{n+1},K_n|=1$

Clearly, this factor shows us how far two graphs are from being homomorphic. 

The followings are some initial propositions, as outlined according to [[1]](#1), 
- $H_1 \rightarrow H_2, \forall G: |G,H_1| \geq |G,H_2|$
- $H_1 \leftrightarrow H_2, \forall G: |G,H_1| = |G,H_2|$
- $G_1 \rightarrow G_2$ is edge injective, $\forall H: |G_1,H| \leq |G_2,H|$



# Concentration Parameter
Suppose $G$ is homomorphic to $H$. I introduce a new parameter, $\gamma$, defined as follows. Consider a specific map mm from $G$ to $H$. Let $\alpha$ represent the maximum number of edges in $G$ that are mapped to a single edge in $H$ under this map. There is a similar parameter $M^{\sigma}$ defined in [[2]](#2).for each homomorphism $\sigma$. Now, we define $\gamma(G,H)$ to be the smallest value of $\alpha$ taken over all possible maps from $G$ to $H$.

Once I have defined $\gamma$, we can build upon it to establish various lemmas. Let's propose a few hypothetical lemmas based on the given definition of $\gamma(G, H)$:
- $\gamma(G,G)=0$
- If $G\rightarrow H$, then $\gamma(G,H) > 0$.
- $\gamma(G, H) + \gamma(H,K) \geq \gamma(G,K)$
- If $G\rightarrow H$, then $|G,K| \leq \gamma (G,H)\times|H,K|$.
- If $G\rightarrow H$ and $K\rightarrow H$, then $|G,K| \leq min(\gamma (G,H)\times|H,K|, \gamma (K,H)\times|G,K|)$
- If $G\rightarrow H$ and $H$ is both vertex- and edge-transitive, then $\gamma(G,H) \leq \frac{|E(G)|}{|E(H)|}$
 
If there is no homomorphism from $G$ to $H$ then we need to define $\gamma$. Maybe, a logical way is to define it as inifinite??

Assume the funciton $f$ is the homomorphism from $G$ to $H$, then we have the following results,
$$d_G(u,v)  \geq d_H(f(u), f(v)) + \gamma (G,H)$$
This results in,
$$0 \leq d_G(u,v)  - d_H(f(u), f(v)) \leq \gamma (G,H)$$


# Extras
In the thesis, a function $d$ is also defined which is improved to be a metric measure as follows:
- $m(G,H) = max(|G,H|,|H,G|)$

So, this metric $m$ possesses the following properties for any two graphs $G$ and $H$:
- $m(G,H) \geq 0$ (Non-negativity)
- $m(G,G) = 0$  (Identity of indiscernibles, partially)
- $m(G,H) = m(H,G)$  (Symmetry)
- $m(G,H) + m(H,K) > m(G,K)$  (Triangle inequality)

For the property of Identity of indiscernibles, we need to consider classes of graph in which they are homomorphic to each other. 


## References
<a id="1">[1]</a> 
Kaveh Khoshkha (2005)
Nonhomomorphism Factors
[Thesis at Sharif University](http://library.sharif.ir/parvan/resource/286721/%D9%85%D8%B9%DB%8C%D8%A7%D8%B1%D9%87%D8%A7%DB%8C%DB%8C-%D8%A7%D8%B2-%D8%B9%D8%AF%D9%85-%D9%88%D8%AC%D9%88%D8%AF-%D9%87%D9%85-%D8%B1%DB%8C%D8%AE%D8%AA%DB%8C-%D8%AF%D8%B1-%DA%AF%D8%B1%D8%A7%D9%81-%D9%87%D8%A7/&from=search&&query=%D9%87%D9%85%20%D8%B1%DB%8C%D8%AE%D8%AA%DB%8C%20homomorphism&field=subjectkeyword&count=20&execute=true#!resource)

<a id="2">[2]</a> 
Amir Daneshgar, Hossein Hajiabolhassan (2007)
Circular colouring and algebraic no-homomorphism theorems
European Journal of Combinatorics
Volume 28, Issue 6
Pages 1843-1853,
ISSN 0195-6698,
[Link1](https://doi.org/10.1016/j.ejc.2006.04.010)
[Link2](https://www.sciencedirect.com/science/article/pii/S0195669806000898)

<a id="3">[3]</a> 
Pavol Hell and Jaroslav Nesetril (2004)
Graphs and homomorphisms
Oxford lecture series in mathematics and its applications
Oxford University Press

<a id="4">[4]</a> 
Graph Homomorphisms Through Random Walks
Amir Daneshgar, Hossein Hajiabolhassan (2003)
JGT 44 (2003) 15–38
[Link][(https://doi.org/10.1016/j.ejc.2006.04.010](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=39f742b250b21aa83fae0e861c25d446829a77ed)https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=39f742b250b21aa83fae0e861c25d446829a77ed)
