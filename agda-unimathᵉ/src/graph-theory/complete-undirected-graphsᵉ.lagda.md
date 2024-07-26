# Complete undirected graphs

```agda
module graph-theory.complete-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import graph-theory.complete-multipartite-graphsᵉ
open import graph-theory.finite-graphsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "completeᵉ undirectedᵉ graph"ᵉ Agda=complete-Undirected-Graph-𝔽ᵉ WD="completeᵉ graph"ᵉ WDID=Q45715ᵉ}}
isᵉ aᵉ [completeᵉ multipartiteᵉ graph](graph-theory.complete-multipartite-graphs.mdᵉ)
in whichᵉ everyᵉ blockᵉ hasᵉ exactlyᵉ oneᵉ vertex.ᵉ Inᵉ otherᵉ words,ᵉ itᵉ isᵉ anᵉ
[undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) in whichᵉ everyᵉ vertexᵉ isᵉ
connectedᵉ to everyᵉ otherᵉ vertex.ᵉ

Thereᵉ areᵉ manyᵉ waysᵉ ofᵉ presentingᵉ completeᵉ undirectedᵉ graphs.ᵉ Forᵉ example,ᵉ theᵉ
typeᵉ ofᵉ edgesᵉ in aᵉ completeᵉ undirectedᵉ graphᵉ isᵉ aᵉ
[2-elementᵉ subtype](univalent-combinatorics.2-element-subtypes.mdᵉ) ofᵉ theᵉ typeᵉ
ofᵉ itsᵉ vertices.ᵉ

## Definition

```agda
complete-Undirected-Graph-𝔽ᵉ : {lᵉ : Level} → 𝔽ᵉ lᵉ → Undirected-Graph-𝔽ᵉ lᵉ lᵉ
complete-Undirected-Graph-𝔽ᵉ Xᵉ =
  complete-multipartite-Undirected-Graph-𝔽ᵉ Xᵉ (λ xᵉ → unit-𝔽ᵉ)
```

## External links

-ᵉ [Completeᵉ graph](https://d3gt.com/unit.html?complete-graphᵉ) atᵉ D3ᵉ Graphᵉ theoryᵉ
-ᵉ [Completeᵉ graph](https://www.wikidata.org/entity/Q45715ᵉ) onᵉ Wikidataᵉ
-ᵉ [Completeᵉ graph](https://en.wikipedia.org/wiki/Complete_graphᵉ) onᵉ Wikipediaᵉ
-ᵉ [Completeᵉ graph](https://mathworld.wolfram.com/CompleteGraph.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ