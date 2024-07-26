# Undirected graphs

```agda
module graph-theory.undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.directed-graphsᵉ
```

</details>

## Idea

Anᵉ **undirectedᵉ graph**ᵉ consistsᵉ ofᵉ aᵉ typeᵉ `V`ᵉ ofᵉ verticesᵉ andᵉ aᵉ familyᵉ `E`ᵉ ofᵉ
typesᵉ overᵉ theᵉ [unorderedᵉ pairs](foundation.unordered-pairs.mdᵉ) ofᵉ `V`.ᵉ

## Definition

```agda
Undirected-Graphᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Undirected-Graphᵉ l1ᵉ l2ᵉ = Σᵉ (UUᵉ l1ᵉ) (λ Vᵉ → unordered-pairᵉ Vᵉ → UUᵉ l2ᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  vertex-Undirected-Graphᵉ : UUᵉ l1ᵉ
  vertex-Undirected-Graphᵉ = pr1ᵉ Gᵉ

  unordered-pair-vertices-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ)
  unordered-pair-vertices-Undirected-Graphᵉ =
    unordered-pairᵉ vertex-Undirected-Graphᵉ

  type-unordered-pair-vertices-Undirected-Graphᵉ :
    unordered-pair-vertices-Undirected-Graphᵉ → UUᵉ lzero
  type-unordered-pair-vertices-Undirected-Graphᵉ pᵉ = type-unordered-pairᵉ pᵉ

  element-unordered-pair-vertices-Undirected-Graphᵉ :
    (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ) →
    type-unordered-pair-vertices-Undirected-Graphᵉ pᵉ → vertex-Undirected-Graphᵉ
  element-unordered-pair-vertices-Undirected-Graphᵉ pᵉ = element-unordered-pairᵉ pᵉ

  edge-Undirected-Graphᵉ : unordered-pair-vertices-Undirected-Graphᵉ → UUᵉ l2ᵉ
  edge-Undirected-Graphᵉ = pr2ᵉ Gᵉ

  total-edge-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  total-edge-Undirected-Graphᵉ =
    Σᵉ unordered-pair-vertices-Undirected-Graphᵉ edge-Undirected-Graphᵉ
```

### The forgetful functor from directed graphs to undirected graphs

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  undirected-graph-Graphᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ
  pr1ᵉ undirected-graph-Graphᵉ = vertex-Directed-Graphᵉ Gᵉ
  pr2ᵉ undirected-graph-Graphᵉ pᵉ =
    Σᵉ ( type-unordered-pairᵉ pᵉ)
      ( λ xᵉ →
        Σᵉ ( type-unordered-pairᵉ pᵉ)
          ( λ yᵉ →
            edge-Directed-Graphᵉ Gᵉ
              ( element-unordered-pairᵉ pᵉ xᵉ)
              ( element-unordered-pairᵉ pᵉ yᵉ)))

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  graph-Undirected-Graphᵉ : Directed-Graphᵉ l1ᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ graph-Undirected-Graphᵉ = vertex-Undirected-Graphᵉ Gᵉ
  pr2ᵉ graph-Undirected-Graphᵉ xᵉ yᵉ =
    Σᵉ ( unordered-pair-vertices-Undirected-Graphᵉ Gᵉ)
      ( λ pᵉ →
        ( mere-Eq-unordered-pairᵉ (standard-unordered-pairᵉ xᵉ yᵉ) pᵉ) ×ᵉ
        ( edge-Undirected-Graphᵉ Gᵉ pᵉ))

  graph-Undirected-Graph'ᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ
  pr1ᵉ graph-Undirected-Graph'ᵉ = vertex-Undirected-Graphᵉ Gᵉ
  pr2ᵉ graph-Undirected-Graph'ᵉ xᵉ yᵉ =
    edge-Undirected-Graphᵉ Gᵉ (standard-unordered-pairᵉ xᵉ yᵉ)
```

### Transporting edges along equalities of unordered pairs of vertices

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  equiv-tr-edge-Undirected-Graphᵉ :
    (pᵉ qᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ)
    (αᵉ : Eq-unordered-pairᵉ pᵉ qᵉ) →
    edge-Undirected-Graphᵉ Gᵉ pᵉ ≃ᵉ edge-Undirected-Graphᵉ Gᵉ qᵉ
  equiv-tr-edge-Undirected-Graphᵉ pᵉ qᵉ αᵉ =
    equiv-trᵉ (edge-Undirected-Graphᵉ Gᵉ) (eq-Eq-unordered-pair'ᵉ pᵉ qᵉ αᵉ)

  tr-edge-Undirected-Graphᵉ :
    (pᵉ qᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ)
    (αᵉ : Eq-unordered-pairᵉ pᵉ qᵉ) →
    edge-Undirected-Graphᵉ Gᵉ pᵉ → edge-Undirected-Graphᵉ Gᵉ qᵉ
  tr-edge-Undirected-Graphᵉ pᵉ qᵉ αᵉ =
    trᵉ (edge-Undirected-Graphᵉ Gᵉ) (eq-Eq-unordered-pair'ᵉ pᵉ qᵉ αᵉ)
```

## External links

-ᵉ [Graph](https://ncatlab.org/nlab/show/graphᵉ) atᵉ $n$Labᵉ
-ᵉ [Graph](https://www.wikidata.org/entity/Q141488ᵉ) onᵉ Wikidataᵉ
-ᵉ [Graphᵉ (discreteᵉ mathematics)](<https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)>ᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Graph](https://mathworld.wolfram.com/Graph.htmlᵉ) atᵉ Wolframᵉ Mathworldᵉ