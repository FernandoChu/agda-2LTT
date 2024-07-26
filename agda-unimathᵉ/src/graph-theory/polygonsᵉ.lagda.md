# Polygons

```agda
module graph-theory.polygonsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmeticᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.decidable-equalityᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.equivalences-undirected-graphsᵉ
open import graph-theory.mere-equivalences-undirected-graphsᵉ
open import graph-theory.undirected-graphsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ **polygon**ᵉ isᵉ anᵉ [undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) thatᵉ
isᵉ [merelyᵉ equivalent](graph-theory.mere-equivalences-undirected-graphs.mdᵉ) to aᵉ
graphᵉ with verticesᵉ theᵉ underlyingᵉ typeᵉ ofᵉ theᵉ
[standardᵉ cyclicᵉ group](elementary-number-theory.standard-cyclic-groups.mdᵉ)
`ℤ-Modᵉ k`ᵉ andᵉ anᵉ edgeᵉ fromᵉ eachᵉ `xᵉ ∈ᵉ ℤ-Modᵉ k`ᵉ to `x+1`.ᵉ Thisᵉ definesᵉ forᵉ eachᵉ
`kᵉ ∈ᵉ ℕ`ᵉ theᵉ typeᵉ ofᵉ allᵉ `k`-gons.ᵉ Theᵉ typeᵉ ofᵉ allᵉ `k`-gonsᵉ isᵉ aᵉ concreteᵉ
presentationᵉ ofᵉ theᵉ [dihedralᵉ group](group-theory.dihedral-groups.mdᵉ) `D_k`.ᵉ

## Definition

### Standard polygons

```agda
vertex-standard-polygon-Undirected-Graphᵉ : ℕᵉ → UUᵉ lzero
vertex-standard-polygon-Undirected-Graphᵉ kᵉ = ℤ-Modᵉ kᵉ

unordered-pair-vertices-standard-polygon-Undirected-Graphᵉ : ℕᵉ → UUᵉ (lsuc lzero)
unordered-pair-vertices-standard-polygon-Undirected-Graphᵉ kᵉ =
  unordered-pairᵉ (vertex-standard-polygon-Undirected-Graphᵉ kᵉ)

edge-standard-polygon-Undirected-Graphᵉ :
  (kᵉ : ℕᵉ) →
  unordered-pair-vertices-standard-polygon-Undirected-Graphᵉ kᵉ → UUᵉ lzero
edge-standard-polygon-Undirected-Graphᵉ kᵉ pᵉ =
  Σᵉ ( type-unordered-pairᵉ pᵉ)
    ( λ xᵉ →
      fiberᵉ
        ( element-unordered-pairᵉ pᵉ)
        ( succ-ℤ-Modᵉ kᵉ (element-unordered-pairᵉ pᵉ xᵉ)))

standard-polygon-Undirected-Graphᵉ : ℕᵉ → Undirected-Graphᵉ lzero lzero
pr1ᵉ (standard-polygon-Undirected-Graphᵉ kᵉ) =
  vertex-standard-polygon-Undirected-Graphᵉ kᵉ
pr2ᵉ (standard-polygon-Undirected-Graphᵉ kᵉ) =
  edge-standard-polygon-Undirected-Graphᵉ kᵉ
```

### The type of all polygons with `k` vertices

```agda
Polygonᵉ : ℕᵉ → UUᵉ (lsuc lzero)
Polygonᵉ kᵉ =
  Σᵉ ( Undirected-Graphᵉ lzero lzero)
    ( mere-equiv-Undirected-Graphᵉ (standard-polygon-Undirected-Graphᵉ kᵉ))

module _
  (kᵉ : ℕᵉ) (Xᵉ : Polygonᵉ kᵉ)
  where

  undirected-graph-Polygonᵉ : Undirected-Graphᵉ lzero lzero
  undirected-graph-Polygonᵉ = pr1ᵉ Xᵉ

  mere-equiv-Polygonᵉ :
    mere-equiv-Undirected-Graphᵉ
      ( standard-polygon-Undirected-Graphᵉ kᵉ)
      ( undirected-graph-Polygonᵉ)
  mere-equiv-Polygonᵉ = pr2ᵉ Xᵉ

  vertex-Polygonᵉ : UUᵉ lzero
  vertex-Polygonᵉ = vertex-Undirected-Graphᵉ undirected-graph-Polygonᵉ

  unordered-pair-vertices-Polygonᵉ : UUᵉ (lsuc lzero)
  unordered-pair-vertices-Polygonᵉ = unordered-pairᵉ vertex-Polygonᵉ

  edge-Polygonᵉ : unordered-pair-vertices-Polygonᵉ → UUᵉ lzero
  edge-Polygonᵉ = edge-Undirected-Graphᵉ undirected-graph-Polygonᵉ

  mere-equiv-vertex-Polygonᵉ : mere-equivᵉ (ℤ-Modᵉ kᵉ) vertex-Polygonᵉ
  mere-equiv-vertex-Polygonᵉ =
    map-trunc-Propᵉ
      ( equiv-vertex-equiv-Undirected-Graphᵉ
        ( standard-polygon-Undirected-Graphᵉ kᵉ)
        ( undirected-graph-Polygonᵉ))
      ( mere-equiv-Polygonᵉ)

  is-finite-vertex-Polygonᵉ : is-nonzero-ℕᵉ kᵉ → is-finiteᵉ vertex-Polygonᵉ
  is-finite-vertex-Polygonᵉ Hᵉ =
    is-finite-mere-equivᵉ mere-equiv-vertex-Polygonᵉ (is-finite-ℤ-Modᵉ Hᵉ)

  is-set-vertex-Polygonᵉ : is-setᵉ vertex-Polygonᵉ
  is-set-vertex-Polygonᵉ =
    is-set-mere-equiv'ᵉ mere-equiv-vertex-Polygonᵉ (is-set-ℤ-Modᵉ kᵉ)

  has-decidable-equality-vertex-Polygonᵉ : has-decidable-equalityᵉ vertex-Polygonᵉ
  has-decidable-equality-vertex-Polygonᵉ =
    has-decidable-equality-mere-equiv'ᵉ
      ( mere-equiv-vertex-Polygonᵉ)
      ( has-decidable-equality-ℤ-Modᵉ kᵉ)
```

## Properties

### The type of vertices of a polygon is a set

```agda
is-set-vertex-standard-polygon-Undirected-Graphᵉ :
  (kᵉ : ℕᵉ) → is-setᵉ (vertex-standard-polygon-Undirected-Graphᵉ kᵉ)
is-set-vertex-standard-polygon-Undirected-Graphᵉ kᵉ = is-set-ℤ-Modᵉ kᵉ
```

### Every edge is between distinct points

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

### Every polygon is a simple graph

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}

## External links

-ᵉ [Cycleᵉ graph](https://www.wikidata.org/entity/Q622506ᵉ) onᵉ Wikidataᵉ
-ᵉ [Cycleᵉ graph](https://en.wikipedia.org/wiki/Cycle_graphᵉ) atᵉ Wikipediaᵉ
-ᵉ [Cycleᵉ graph](https://mathworld.wolfram.com/CycleGraph.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ