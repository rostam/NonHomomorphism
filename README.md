# NonHomomorphism Factors
The concept of NonHomomorphism Factors was first introduced in [the thesis of Kaveh Khoshkhah](http://library.sharif.ir/parvan/resource/286721/%D9%85%D8%B9%DB%8C%D8%A7%D8%B1%D9%87%D8%A7%DB%8C%DB%8C-%D8%A7%D8%B2-%D8%B9%D8%AF%D9%85-%D9%88%D8%AC%D9%88%D8%AF-%D9%87%D9%85-%D8%B1%DB%8C%D8%AE%D8%AA%DB%8C-%D8%AF%D8%B1-%DA%AF%D8%B1%D8%A7%D9%81-%D9%87%D8%A7/&from=search&&query=%D9%87%D9%85%20%D8%B1%DB%8C%D8%AE%D8%AA%DB%8C%20homomorphism&field=subjectkeyword&count=20&execute=true#!resource). While the thesis explores various definitions, here we will focus on a particular version to extend upon. Let's define the Non-Homomorphism Factor between two graphs $G$ and $H$,  denoted as $|G,H|$. as the fewest number of edges one must remove from $G$ to establish at lease one homomorphism from $G$ to $H$. So, if there is already a homomorphism from $G$ to $H$, the nonhomomorphism factor is $0$. Here are some more examples:
- $|K_n,K_{n+1}|=0$
- $|K_{n+1},K_n|=1$

Clearly, this factor shows us how far two graphs are from being homomorphic. Here, the notation $G\rightarrow H$ specifies that there is a homomorphism from $G$ to $H$.

# Concentration Parameter
Suppose $G$ is homomorphic to $H$. I introduce a new parameter, $\gamma$, defined as follows. Consider a specific map mm from $G$ to $H$. Let $\alpha$ represent the maximum number of edges in $G$ that are mapped to a single edge in $H$ under this map. There is a similar parameter $M_{\sigma}$ defined in [Daneshgar, Hajiabolhassan 2007](https://pdf.sciencedirectassets.com/272420/1-s2.0-S0195669807X01173/1-s2.0-S0195669806000898/main.pdf?X-Amz-Security-Token=IQoJb3JpZ2luX2VjEK7%2F%2F%2F%2F%2F%2F%2F%2F%2F%2FwEaCXVzLWVhc3QtMSJGMEQCIDCTwnMol4WQJJDyHq60mZQ%2BLJ%2F8FR65pB0u5yUR9FIPAiBqwdm2ISMy%2FtAfkU4kv0JCHcOXBKVNCGLyqvwU3qOjACq8BQim%2F%2F%2F%2F%2F%2F%2F%2F%2F%2F8BEAUaDDA1OTAwMzU0Njg2NSIMQomeF4Qu4Ksq34IZKpAFUjcsRLWKuLpbrgbB5OZMPAdIf%2BIdLDnz9Tth%2FIcBnKTdrHuNJ0bPySPTAynslt1HXUFbwmLJIv%2F5lqPbNhJ0dZxExQjDNlD1NOBzTDvBA3X67RxiQOIf08GMO3RL0sSMOwnGJZtwQEGSR0Xx85D5xQqqkJG13b3jjJF8MZvbtP5dwMI%2BVBY2ixDGb6Ql4gPAXoViMYCvp2sUgG8trojSBj1wg82Y%2BikcNinf9k4nzZ6SnYGpsjFd5xKx4aJIiTkkjjTyBrq3cO0xsci3cJwBVLvORSNYI0wKV3GsjUsEp3Ad6aAUm5xcncd6wlt8%2FSL8v3l4wrJiJ3QcEllkBEBua6zHtUGMFn84V8nYiSOV2M4A1z8hruX%2F1nWmRdW81MTIVza4yfIaW8%2B8wyRvEQPqj2vDcZcjgbLpHjvP98r9fPpA4vsQfGHssthv%2BsC6jkRcSvohSKbPPcx7BHBi9oIARWYa0UgbZCjxDPssPGJelHaAQs06cKzPAbZhtwq1qab0Uz96%2FSsAvaQ3LpmXzzkPLXqcOkzAkbvhgiPTZdt8WYzw2FqOyVJK4ZAF2lRRdFbf4PMRvEasCsOTX8eceXDdTdjz6X5PoSbht5plcQETipqbk1jJPW2IeJQNFRGRSj243MGljE4wtflXWMJ9KDdsBGrdTxqqRgMxYmZt9YE%2FZ3PY4WdG8JU59bjGoceNv1lMDYyv2qn%2F%2BxGxMEJ%2BhFSZOQXL%2F6tMk0g6bZft5mOdXqmktByE4AmFrsHyQFnYQxTAiKIr25GIH9Bj%2BJv5j6CXzvooivZ5Uel74yIzvQcgor55e3uxH8aIzfruAEuYq%2FBG%2BO0CJ34rdUSlzg7pNhotJjBgg9kCDrYsAd%2FuG%2BO2bb4w5fnVqAY6sgHizfzntgmDsNGx3lcV1l2zXw36osl8dyFisLb2jSZXhbw%2BQ8wCnW9szzGPtsI4bqUmgO4TG8uZSYnccs5Bko2nhO%2B1s8ISOpqN7EUpM4lmFvIn1lkelufFDYkENR%2FVETrgXQjQB6WGEh2WFBmmHUp3%2BNcsnngzZBQ3%2FUlY224afulpEr252d%2FWlIuITgrmeTjPCtYUM2upcBk1mmx0BC00JUQZgs78vIQXaUsSl0Fm9tWR&X-Amz-Algorithm=AWS4-HMAC-SHA256&X-Amz-Date=20230928T142925Z&X-Amz-SignedHeaders=host&X-Amz-Expires=300&X-Amz-Credential=ASIAQ3PHCVTYRDPY5LUF%2F20230928%2Fus-east-1%2Fs3%2Faws4_request&X-Amz-Signature=85d74f591610a0f5aadae6171e5232d04a785ef88463971c214380d3ccda5cd6&hash=fb843b0cfa3656a430ccf6adb2f121e8a154ea5050c50939e34db7dd9252d3bc&host=68042c943591013ac2b2430a89b270f6af2c76d8dfd086a07176afe7c76c2c61&pii=S0195669806000898&tid=spdf-cb20bac7-a61f-4f47-8d63-61ba08cae907&sid=ef63c48533e65641e539c6781c0081460b01gxrqb&type=client&tsoh=d3d3LnNjaWVuY2VkaXJlY3QuY29t&ua=02065750070404070652&rr=80dcadb3faf70c3b&cc=de) for each homomorphism $\sigma$. Now, we define $\gamma$ to be the smallest value of $\alpha$ taken over all possible maps from $G$ to $H$.

Once I have defined $\gamma$, we can build upon it to establish various lemmas. Let's propose a few hypothetical lemmas based on the given definition of $\gamma(G, H)$:
- $\gamma(G,G)=0$
- If $G\rightarrow H$, then $\gamma(G,H) > 0$.
- $\gamma(G, H) + \gamma(H,K) \geq \gamma(G,K)$
- If $G\rightarrow H$, then $|G,K| \leq \gamma (G,H)\times|H,K|$.
- If $G\rightarrow H$ and $K\rightarrow H$, then $|G,K| \leq min(\gamma (G,H)\times|H,K|, \gamma (K,H)\times|G,K|)$

If there is no homomorphism from $G$ to $H$ then we need to define $\gamma$. Maybe, a logical way is to define it as inifinite??

# Extras
In the thesis, a function $d$ is also defined which is improved to be a metric measure as follows:
- $d(G,H) = max(|G,H|,|H,G|)$

So, this metric $d$ possesses the following properties for any two graphs $G$ and $H$:
- $d(G,H) \geq 0$ (Non-negativity)
- $d(G,G) = 0$  (Identity of indiscernibles, partially)
- $d(G,H) = d(H,G)$  (Symmetry)
- $d(G,H) + d(H,K) > d(G,K)$  (Triangle inequality)

For the property of Identity of indiscernibles, we need to consider classes of graph in which they are homomorphic to each other. 


