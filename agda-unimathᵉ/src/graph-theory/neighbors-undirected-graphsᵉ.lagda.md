# Incidence in undirected graphs

```agda
module graph-theory.neighbors-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.equivalences-undirected-graphsᵉ
open import graph-theory.undirected-graphsᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ neighborsᵉ aᵉ vertexᵉ `x`ᵉ ofᵉ anᵉ undirectedᵉ graphᵉ `G`ᵉ isᵉ theᵉ typeᵉ ofᵉ allᵉ
verticesᵉ `y`ᵉ in `G`ᵉ equippedᵉ with anᵉ edgeᵉ fromᵉ `x`ᵉ to `y`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  neighbor-Undirected-Graphᵉ : vertex-Undirected-Graphᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  neighbor-Undirected-Graphᵉ xᵉ =
    Σᵉ ( vertex-Undirected-Graphᵉ Gᵉ)
      ( λ yᵉ → edge-Undirected-Graphᵉ Gᵉ (standard-unordered-pairᵉ xᵉ yᵉ))
```

## Properties

### Equivalences of undirected graphs induce equivalences on types of neighbors

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Undirected-Graphᵉ l3ᵉ l4ᵉ)
  where

  equiv-neighbor-equiv-Undirected-Graphᵉ :
    (eᵉ : equiv-Undirected-Graphᵉ Gᵉ Hᵉ) (xᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
    neighbor-Undirected-Graphᵉ Gᵉ xᵉ ≃ᵉ
    neighbor-Undirected-Graphᵉ Hᵉ (vertex-equiv-Undirected-Graphᵉ Gᵉ Hᵉ eᵉ xᵉ)
  equiv-neighbor-equiv-Undirected-Graphᵉ eᵉ xᵉ =
    equiv-Σᵉ
      ( λ yᵉ →
        edge-Undirected-Graphᵉ Hᵉ
          ( standard-unordered-pairᵉ (vertex-equiv-Undirected-Graphᵉ Gᵉ Hᵉ eᵉ xᵉ) yᵉ))
      ( equiv-vertex-equiv-Undirected-Graphᵉ Gᵉ Hᵉ eᵉ)
      ( equiv-edge-standard-unordered-pair-vertices-equiv-Undirected-Graphᵉ
          Gᵉ Hᵉ eᵉ xᵉ)

  neighbor-equiv-Undirected-Graphᵉ :
    (eᵉ : equiv-Undirected-Graphᵉ Gᵉ Hᵉ) (xᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
    neighbor-Undirected-Graphᵉ Gᵉ xᵉ →
    neighbor-Undirected-Graphᵉ Hᵉ (vertex-equiv-Undirected-Graphᵉ Gᵉ Hᵉ eᵉ xᵉ)
  neighbor-equiv-Undirected-Graphᵉ eᵉ xᵉ =
    map-equivᵉ (equiv-neighbor-equiv-Undirected-Graphᵉ eᵉ xᵉ)

neighbor-id-equiv-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ : Level}
  (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (xᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
  neighbor-equiv-Undirected-Graphᵉ Gᵉ Gᵉ (id-equiv-Undirected-Graphᵉ Gᵉ) xᵉ ~ᵉ idᵉ
neighbor-id-equiv-Undirected-Graphᵉ Gᵉ xᵉ (pairᵉ yᵉ eᵉ) =
  eq-pair-eq-fiberᵉ
    ( edge-standard-unordered-pair-vertices-id-equiv-Undirected-Graphᵉ Gᵉ xᵉ yᵉ eᵉ)
```

## External links

-ᵉ [Neighborhood](https://www.wikidata.org/entity/Q1354987ᵉ) onᵉ Wikidataᵉ
-ᵉ [Neighborhoodᵉ (graphᵉ theory)](<https://en.wikipedia.org/wiki/Neighbourhood_(graph_theory)>ᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Graphᵉ neighborhood](https://mathworld.wolfram.com/GraphNeighborhood.htmlᵉ) atᵉ
  Wolframᵉ Mathworldᵉ