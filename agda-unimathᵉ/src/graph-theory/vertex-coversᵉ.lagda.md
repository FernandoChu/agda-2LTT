# Vertex covers

```agda
module graph-theory.vertex-coversᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.undirected-graphsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ **vertexᵉ cover**ᵉ onᵉ aᵉ [undirectᵉ graph](graph-theory.undirected-graphs.mdᵉ) isᵉ aᵉ
setᵉ ofᵉ verticesᵉ thatᵉ includesᵉ atᵉ leastᵉ oneᵉ extremityᵉ ofᵉ eachᵉ edgeᵉ ofᵉ theᵉ graph.ᵉ

## Definitions

```agda
vertex-coverᵉ :
  {l1ᵉ l2ᵉ : Level} → Undirected-Graphᵉ l1ᵉ l2ᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
vertex-coverᵉ Gᵉ =
  Σᵉ ( vertex-Undirected-Graphᵉ Gᵉ → Finᵉ 2ᵉ)
    ( λ cᵉ →
      (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
      edge-Undirected-Graphᵉ Gᵉ pᵉ →
        type-trunc-Propᵉ
          ( Σᵉ (vertex-Undirected-Graphᵉ Gᵉ)
            ( λ xᵉ → is-in-unordered-pairᵉ pᵉ xᵉ ×ᵉ Idᵉ (cᵉ xᵉ) (inrᵉ starᵉ))))
```

## External links

-ᵉ [Vertexᵉ cover](https://en.wikipedia.org/wiki/Vertex_coverᵉ) atᵉ Wikipediaᵉ
-ᵉ [Vertexᵉ cover](https://mathworld.wolfram.com/VertexCover.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ
-ᵉ [Vertexᵉ coverᵉ problem](https://www.wikidata.org/entity/Q924362ᵉ) onᵉ Wikidataᵉ