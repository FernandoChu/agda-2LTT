# Complete bipartite graphs

```agda
module graph-theory.complete-bipartite-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.finite-graphsᵉ

open import univalent-combinatorics.2-element-typesᵉ
open import univalent-combinatorics.cartesian-product-typesᵉ
open import univalent-combinatorics.coproduct-typesᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.fibers-of-mapsᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Considerᵉ twoᵉ [finiteᵉ sets](univalent-combinatorics.finite-types.mdᵉ) `X`ᵉ andᵉ `Y`.ᵉ
Theᵉ
{{#conceptᵉ "completeᵉ bipartiteᵉ graph"ᵉ Agda=complete-bipartite-Undirected-Graph-𝔽ᵉ WDID=Q913598ᵉ WD="completeᵉ bipartiteᵉ graph"ᵉ}}
onᵉ `X`ᵉ andᵉ `Y`ᵉ isᵉ theᵉ [undirectedᵉ finiteᵉ graph](graph-theory.finite-graphs.mdᵉ)
consistingᵉ ofᵉ:

-ᵉ Theᵉ finiteᵉ setᵉ ofᵉ verticesᵉ isᵉ theᵉ
  [coproductᵉ type](univalent-combinatorics.coproduct-types.mdᵉ) `Xᵉ +ᵉ Y`.ᵉ
-ᵉ Givenᵉ anᵉ [unorderedᵉ pair](foundation.unordered-pairs.mdᵉ) `fᵉ : Iᵉ → Xᵉ +ᵉ Y`ᵉ ofᵉ
  vertices,ᵉ theᵉ finiteᵉ typeᵉ ofᵉ edgesᵉ onᵉ theᵉ unorderedᵉ pairᵉ `(Iᵉ ,ᵉ f)`ᵉ isᵉ givenᵉ byᵉ

  ```text
    (Σᵉ (xᵉ : X),ᵉ fiberᵉ fᵉ (inlᵉ xᵉ))  ×ᵉ (Σᵉ (yᵉ : Y),ᵉ fiberᵉ fᵉ (inrᵉ y)).ᵉ
  ```

  Inᵉ otherᵉ words,ᵉ anᵉ unorderedᵉ pairᵉ ofᵉ elementsᵉ ofᵉ theᵉ coproductᵉ typeᵉ `Xᵉ +ᵉ Y`ᵉ isᵉ
  anᵉ edgeᵉ in theᵉ completeᵉ bipartiteᵉ graphᵉ onᵉ `X`ᵉ andᵉ `Y`ᵉ preciselyᵉ whenᵉ oneᵉ ofᵉ
  theᵉ elementsᵉ ofᵉ theᵉ unorderedᵉ pairᵉ comesᵉ fromᵉ `X`ᵉ andᵉ theᵉ otherᵉ comesᵉ fromᵉ
  `Y`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Yᵉ : 𝔽ᵉ l2ᵉ)
  where

  vertex-finite-type-complete-bipartite-Undirected-Graph-𝔽ᵉ : 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  vertex-finite-type-complete-bipartite-Undirected-Graph-𝔽ᵉ = coproduct-𝔽ᵉ Xᵉ Yᵉ

  vertex-complete-bipartite-Undirected-Graph-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  vertex-complete-bipartite-Undirected-Graph-𝔽ᵉ =
    type-𝔽ᵉ vertex-finite-type-complete-bipartite-Undirected-Graph-𝔽ᵉ

  unordered-pair-vertices-complete-bipartite-Undirected-Graph-𝔽ᵉ :
    UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  unordered-pair-vertices-complete-bipartite-Undirected-Graph-𝔽ᵉ =
    unordered-pairᵉ vertex-complete-bipartite-Undirected-Graph-𝔽ᵉ

  edge-finite-type-complete-bipartite-Undirected-Graph-𝔽ᵉ :
    unordered-pair-vertices-complete-bipartite-Undirected-Graph-𝔽ᵉ → 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  edge-finite-type-complete-bipartite-Undirected-Graph-𝔽ᵉ pᵉ =
    product-𝔽ᵉ
      ( Σ-𝔽ᵉ Xᵉ
        ( λ xᵉ →
          fiber-𝔽ᵉ
            ( finite-type-2-Element-Typeᵉ (pr1ᵉ pᵉ))
            ( coproduct-𝔽ᵉ Xᵉ Yᵉ)
            ( element-unordered-pairᵉ pᵉ)
            ( inlᵉ xᵉ)))
      ( Σ-𝔽ᵉ Yᵉ
        ( λ yᵉ →
          fiber-𝔽ᵉ
            ( finite-type-2-Element-Typeᵉ (pr1ᵉ pᵉ))
            ( coproduct-𝔽ᵉ Xᵉ Yᵉ)
            ( element-unordered-pairᵉ pᵉ)
            ( inrᵉ yᵉ)))

  edge-complete-bipartite-Undirected-Graphᵉ :
    unordered-pair-vertices-complete-bipartite-Undirected-Graph-𝔽ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  edge-complete-bipartite-Undirected-Graphᵉ pᵉ =
    type-𝔽ᵉ (edge-finite-type-complete-bipartite-Undirected-Graph-𝔽ᵉ pᵉ)

  complete-bipartite-Undirected-Graph-𝔽ᵉ :
    Undirected-Graph-𝔽ᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ complete-bipartite-Undirected-Graph-𝔽ᵉ =
    vertex-finite-type-complete-bipartite-Undirected-Graph-𝔽ᵉ
  pr2ᵉ complete-bipartite-Undirected-Graph-𝔽ᵉ =
    edge-finite-type-complete-bipartite-Undirected-Graph-𝔽ᵉ
```

## External links

-ᵉ [Completeᵉ bipartiteᵉ graph](https://d3gt.com/unit.html?complete-bipartiteᵉ) atᵉ
  D3ᵉ Graphᵉ Theoryᵉ
-ᵉ [Bipartiteᵉ graphs](https://ncatlab.org/nlab/show/bipartite+graphᵉ) atᵉ $n$Labᵉ
-ᵉ [Completeᵉ bipartiteᵉ graph](https://www.wikidata.org/entity/Q913598ᵉ) atᵉ
  Wikidataᵉ
-ᵉ [Completeᵉ bipartiteᵉ graph](https://en.wikipedia.org/wiki/Complete_bipartite_graphᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Completeᵉ bipartiteᵉ graphs](https://mathworld.wolfram.com/CompleteBipartiteGraph.htmlᵉ)
  atᵉ Wolframᵉ Mathworldᵉ