# NonHomomorphism Factors
NonHomomorphism Factors are defined first in [the thesis of Kaveh Khoshkhah](http://library.sharif.ir/parvan/resource/286721/%D9%85%D8%B9%DB%8C%D8%A7%D8%B1%D9%87%D8%A7%DB%8C%DB%8C-%D8%A7%D8%B2-%D8%B9%D8%AF%D9%85-%D9%88%D8%AC%D9%88%D8%AF-%D9%87%D9%85-%D8%B1%DB%8C%D8%AE%D8%AA%DB%8C-%D8%AF%D8%B1-%DA%AF%D8%B1%D8%A7%D9%81-%D9%87%D8%A7/&from=search&&query=%D9%87%D9%85%20%D8%B1%DB%8C%D8%AE%D8%AA%DB%8C%20homomorphism&field=subjectkeyword&count=20&execute=true#!resource). There are different definitions in the thesis, but I just introduce one version based on which I want to extend the topic. So, let us define a Nonhomomorphism factor between two graphs $G$ and $H$ (shown with $|G,H|$) as the minimum number of edges that we should remove from $G$ such that we have at lease one homomorphism from $G$ to $H$. So, if there is already a homomorphism from $G$ to $H$, the nonhomomorphism factor is $0$. Here are some more examples:
- $|K_n,K_{n+1}|=0$
- $|K_{n+1},K_n|=1$

In the thesis, a function $d$ is also defined which is improved to be a metric measure as follows:
- $d(G,H) = max(|G,H|,|H,G|)$
