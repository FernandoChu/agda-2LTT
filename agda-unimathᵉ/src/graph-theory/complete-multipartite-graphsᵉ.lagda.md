# Complete multipartite graphs

```agda
module graph-theory.complete-multipartite-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.finite-graphsᵉ

open import univalent-combinatorics.2-element-typesᵉ
open import univalent-combinatorics.dependent-function-typesᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.function-typesᵉ
```

</details>

## Idea

Considerᵉ aᵉ familyᵉ ofᵉ [finiteᵉ types](univalent-combinatorics.finite-types.mdᵉ) `Y`ᵉ
indexedᵉ byᵉ aᵉ finiteᵉ typeᵉ `X`.ᵉ Theᵉ
{{#conceptᵉ "completeᵉ multipartiteᵉ graph"ᵉ Agda=complete-multipartite-Undirected-Graph-𝔽ᵉ WD="multipartiteᵉ graph"ᵉ WDID=Q1718082ᵉ}}
atᵉ `Y`ᵉ isᵉ theᵉ [finiteᵉ undirectedᵉ graph](graph-theory.finite-graphs.mdᵉ)
consistingᵉ ofᵉ:

-ᵉ Theᵉ finiteᵉ typeᵉ ofᵉ verticesᵉ isᵉ theᵉ
  [dependentᵉ pairᵉ type](univalent-combinatorics.dependent-pair-types.mdᵉ)
  `Σᵉ (xᵉ : X),ᵉ Yᵉ x`.ᵉ
-ᵉ Anᵉ [unorderedᵉ pair](foundation.unordered-pairs.mdᵉ) `fᵉ : Iᵉ → Σᵉ (xᵉ : X),ᵉ Yᵉ x`ᵉ isᵉ
  anᵉ edgeᵉ ifᵉ theᵉ inducedᵉ unorderedᵉ pairᵉ `pr1ᵉ ∘ᵉ fᵉ : Iᵉ → X`ᵉ isᵉ anᵉ
  [embedding](foundation-core.embeddings.md).ᵉ

**Note:**ᵉ Theᵉ formalizationᵉ ofᵉ theᵉ finiteᵉ typeᵉ ofᵉ edgesᵉ belowᵉ isᵉ differentᵉ fromᵉ
theᵉ aboveᵉ description,ᵉ andᵉ needsᵉ to beᵉ changed.ᵉ

## Definitions

### Complete multipartite graphs

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Yᵉ : type-𝔽ᵉ Xᵉ → 𝔽ᵉ l2ᵉ)
  where

  vertex-finite-type-complete-multipartite-Undirected-Graph-𝔽ᵉ : 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  vertex-finite-type-complete-multipartite-Undirected-Graph-𝔽ᵉ =
    Σ-𝔽ᵉ Xᵉ Yᵉ

  vertex-complete-multipartite-Undirected-Graph-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  vertex-complete-multipartite-Undirected-Graph-𝔽ᵉ =
    type-𝔽ᵉ vertex-finite-type-complete-multipartite-Undirected-Graph-𝔽ᵉ

  unordered-pair-vertices-complete-multipartite-Undirected-Graph-𝔽ᵉ :
    UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  unordered-pair-vertices-complete-multipartite-Undirected-Graph-𝔽ᵉ =
    unordered-pairᵉ vertex-complete-multipartite-Undirected-Graph-𝔽ᵉ

  edge-finite-type-complete-multipartite-Undirected-Graph-𝔽ᵉ :
    unordered-pair-vertices-complete-multipartite-Undirected-Graph-𝔽ᵉ → 𝔽ᵉ l1ᵉ
  edge-finite-type-complete-multipartite-Undirected-Graph-𝔽ᵉ pᵉ =
    ( Π-𝔽ᵉ
      ( finite-type-2-Element-Typeᵉ (pr1ᵉ pᵉ))
      ( λ xᵉ →
        Π-𝔽ᵉ
          ( finite-type-2-Element-Typeᵉ (pr1ᵉ pᵉ))
          ( λ yᵉ →
            Id-𝔽ᵉ Xᵉ
              ( pr1ᵉ (element-unordered-pairᵉ pᵉ xᵉ))
              ( pr1ᵉ (element-unordered-pairᵉ pᵉ yᵉ))))) →-𝔽ᵉ
    ( empty-𝔽ᵉ)

  edge-complete-multipartite-Undirected-Graph-𝔽ᵉ :
    unordered-pair-vertices-complete-multipartite-Undirected-Graph-𝔽ᵉ → UUᵉ l1ᵉ
  edge-complete-multipartite-Undirected-Graph-𝔽ᵉ pᵉ =
    type-𝔽ᵉ (edge-finite-type-complete-multipartite-Undirected-Graph-𝔽ᵉ pᵉ)

  complete-multipartite-Undirected-Graph-𝔽ᵉ : Undirected-Graph-𝔽ᵉ (l1ᵉ ⊔ l2ᵉ) l1ᵉ
  pr1ᵉ complete-multipartite-Undirected-Graph-𝔽ᵉ =
    vertex-finite-type-complete-multipartite-Undirected-Graph-𝔽ᵉ
  pr2ᵉ complete-multipartite-Undirected-Graph-𝔽ᵉ =
    edge-finite-type-complete-multipartite-Undirected-Graph-𝔽ᵉ
```

## External links

-ᵉ [Multipartiteᵉ graph](https://www.wikidata.org/entity/Q1718082ᵉ) onᵉ Wikidataᵉ
-ᵉ [Multipartiteᵉ graph](https://en.wikipedia.org/wiki/Multipartite_graphᵉ) onᵉ
  Wikipediaᵉ
-ᵉ [Completeᵉ multipartiteᵉ graph](https://mathworld.wolfram.com/CompleteMultipartiteGraph.htmlᵉ)
  onᵉ Wolframᵉ Mathworldᵉ