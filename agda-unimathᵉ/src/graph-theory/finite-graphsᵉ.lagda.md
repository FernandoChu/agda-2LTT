# Finite graphs

```agda
module graph-theory.finite-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.undirected-graphsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ **finiteᵉ undirectedᵉ graph**ᵉ consistsᵉ ofᵉ aᵉ
[finiteᵉ set](univalent-combinatorics.finite-types.mdᵉ) ofᵉ verticesᵉ andᵉ aᵉ familyᵉ
ofᵉ finiteᵉ typesᵉ ofᵉ edgesᵉ indexedᵉ byᵉ
[unorderedᵉ pairs](foundation.unordered-pairs.mdᵉ) ofᵉ vertices.ᵉ

**Note:**ᵉ Inᵉ ourᵉ definitionᵉ ofᵉ finiteᵉ graph,ᵉ weᵉ allowᵉ forᵉ theᵉ possibilityᵉ thatᵉ
thereᵉ areᵉ multipleᵉ edgesᵉ betweenᵉ theᵉ sameᵉ twoᵉ nodes.ᵉ Inᵉ discreteᵉ mathematicsᵉ itᵉ
isᵉ alsoᵉ commonᵉ to callᵉ suchᵉ graphsᵉ _multigraphs_.ᵉ

## Definitions

### Finite undirected graphs

```agda
Undirected-Graph-𝔽ᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Undirected-Graph-𝔽ᵉ l1ᵉ l2ᵉ = Σᵉ (𝔽ᵉ l1ᵉ) (λ Xᵉ → unordered-pairᵉ (type-𝔽ᵉ Xᵉ) → 𝔽ᵉ l2ᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graph-𝔽ᵉ l1ᵉ l2ᵉ)
  where

  vertex-Undirected-Graph-𝔽ᵉ : UUᵉ l1ᵉ
  vertex-Undirected-Graph-𝔽ᵉ = type-𝔽ᵉ (pr1ᵉ Gᵉ)

  unordered-pair-vertices-Undirected-Graph-𝔽ᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ)
  unordered-pair-vertices-Undirected-Graph-𝔽ᵉ =
    unordered-pairᵉ vertex-Undirected-Graph-𝔽ᵉ

  is-finite-vertex-Undirected-Graph-𝔽ᵉ : is-finiteᵉ vertex-Undirected-Graph-𝔽ᵉ
  is-finite-vertex-Undirected-Graph-𝔽ᵉ = is-finite-type-𝔽ᵉ (pr1ᵉ Gᵉ)

  edge-Undirected-Graph-𝔽ᵉ :
    (pᵉ : unordered-pair-vertices-Undirected-Graph-𝔽ᵉ) → UUᵉ l2ᵉ
  edge-Undirected-Graph-𝔽ᵉ pᵉ = type-𝔽ᵉ (pr2ᵉ Gᵉ pᵉ)

  is-finite-edge-Undirected-Graph-𝔽ᵉ :
    (pᵉ : unordered-pair-vertices-Undirected-Graph-𝔽ᵉ) →
    is-finiteᵉ (edge-Undirected-Graph-𝔽ᵉ pᵉ)
  is-finite-edge-Undirected-Graph-𝔽ᵉ pᵉ = is-finite-type-𝔽ᵉ (pr2ᵉ Gᵉ pᵉ)

  total-edge-Undirected-Graph-𝔽ᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  total-edge-Undirected-Graph-𝔽ᵉ =
    Σᵉ unordered-pair-vertices-Undirected-Graph-𝔽ᵉ edge-Undirected-Graph-𝔽ᵉ

  undirected-graph-Undirected-Graph-𝔽ᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ
  pr1ᵉ undirected-graph-Undirected-Graph-𝔽ᵉ = vertex-Undirected-Graph-𝔽ᵉ
  pr2ᵉ undirected-graph-Undirected-Graph-𝔽ᵉ = edge-Undirected-Graph-𝔽ᵉ
```

### The following type is expected to be equivalent to Undirected-Graph-𝔽

```agda
Undirected-Graph-𝔽'ᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Undirected-Graph-𝔽'ᵉ l1ᵉ l2ᵉ =
  Σᵉ ( 𝔽ᵉ l1ᵉ)
    ( λ Vᵉ →
      Σᵉ ( type-𝔽ᵉ Vᵉ → type-𝔽ᵉ Vᵉ → 𝔽ᵉ l2ᵉ)
        ( λ Eᵉ →
          Σᵉ ( (xᵉ yᵉ : type-𝔽ᵉ Vᵉ) → type-𝔽ᵉ (Eᵉ xᵉ yᵉ) ≃ᵉ type-𝔽ᵉ (Eᵉ yᵉ xᵉ))
            ( λ σᵉ →
              (xᵉ yᵉ : type-𝔽ᵉ Vᵉ) → map-equivᵉ ((σᵉ yᵉ xᵉ) ∘eᵉ (σᵉ xᵉ yᵉ)) ~ᵉ idᵉ)))
```

Theᵉ degreeᵉ ofᵉ aᵉ vertexᵉ xᵉ ofᵉ aᵉ graphᵉ Gᵉ isᵉ theᵉ setᵉ ofᵉ occurencesᵉ ofᵉ xᵉ asᵉ anᵉ
endpointᵉ ofᵉ x.ᵉ Noteᵉ thatᵉ theᵉ unorderedᵉ pairᵉ {x,xᵉ} addsᵉ twoᵉ elementsᵉ to theᵉ
degreeᵉ ofᵉ x.ᵉ

```agda
incident-edges-vertex-Undirected-Graph-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graph-𝔽ᵉ l1ᵉ l2ᵉ)
  (xᵉ : vertex-Undirected-Graph-𝔽ᵉ Gᵉ) → UUᵉ (lsuc lzero ⊔ l1ᵉ)
incident-edges-vertex-Undirected-Graph-𝔽ᵉ Gᵉ xᵉ =
  Σᵉ ( unordered-pairᵉ (vertex-Undirected-Graph-𝔽ᵉ Gᵉ))
    ( λ pᵉ → fiberᵉ (element-unordered-pairᵉ pᵉ) xᵉ)
```

## External links

-ᵉ [Multigraph](https://ncatlab.org/nlab/show/multigraphᵉ) atᵉ $n$Labᵉ
-ᵉ [Multigraph](https://www.wikidata.org/entity/Q2642629ᵉ) onᵉ Wikidataᵉ
-ᵉ [Multigraph](https://en.wikipedia.org/wiki/Multigraphᵉ) atᵉ Wikipediaᵉ
-ᵉ [Multigraph](https://mathworld.wolfram.com/Multigraph.htmlᵉ) atᵉ Wolframᵉ
  mathworldᵉ