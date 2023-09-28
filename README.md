# NonHomomorphism Factors
The concept of NonHomomorphism Factors was first introduced in [the thesis of Kaveh Khoshkhah](http://library.sharif.ir/parvan/resource/286721/%D9%85%D8%B9%DB%8C%D8%A7%D8%B1%D9%87%D8%A7%DB%8C%DB%8C-%D8%A7%D8%B2-%D8%B9%D8%AF%D9%85-%D9%88%D8%AC%D9%88%D8%AF-%D9%87%D9%85-%D8%B1%DB%8C%D8%AE%D8%AA%DB%8C-%D8%AF%D8%B1-%DA%AF%D8%B1%D8%A7%D9%81-%D9%87%D8%A7/&from=search&&query=%D9%87%D9%85%20%D8%B1%DB%8C%D8%AE%D8%AA%DB%8C%20homomorphism&field=subjectkeyword&count=20&execute=true#!resource). While the thesis explores various definitions, here we will focus on a particular version to extend upon. Let's define the Non-Homomorphism Factor between two graphs $G$ and $H$,  denoted as $|G,H|$. as the fewest number of edges one must remove from $G$ to establish at lease one homomorphism from $G$ to $H$. So, if there is already a homomorphism from $G$ to $H$, the nonhomomorphism factor is $0$. Here are some more examples:
- $|K_n,K_{n+1}|=0$
- $|K_{n+1},K_n|=1$

Clearly, this factor shows us how far two graphs are from being homomorphic.

# Shrinkage Factor
Suppose $G$ is homomorphic to $H$. I introduce a new parameter, $\gamma$, defined as follows. Consider a specific map mm from $G$ to $H$. Let $\alpha$ represent the maximum number of edges in $G$ that are mapped to a single edge in $H$ under this map. Now, we define $\gamma$ to be the smallest value of $\alpha$ taken over all possible maps from $G$ to $H$.

Once I have defined $\gamma$, we can build upon it to establish various lemmas. Let's propose a few hypothetical lemmas based on the given definition of $\gamma(G, H)$:
- $\gamma(G, H) + \gamma(H,K) > \gamma(G,K)$


# Extras
In the thesis, a function $d$ is also defined which is improved to be a metric measure as follows:
- $d(G,H) = max(|G,H|,|H,G|)$

So, this metric $d$ possesses the following properties for any two graphs $G$ and $H$:
- $d(G,H) \geq 0$ (Non-negativity)
- $d(G,G) = 0$  (Identity of indiscernibles, partially)
- $d(G,H) = d(H,G)$  (Symmetry)
- $d(G,H) + d(H,K) > d(G,K)$  (Triangle inequality)

For the property of Identity of indiscernibles, we need to consider classes of graph in which they are homomorphic to each other. 


