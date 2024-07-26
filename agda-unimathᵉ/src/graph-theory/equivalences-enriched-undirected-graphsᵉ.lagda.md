# Equivalences of enriched undirected graphs

```agda
module graph-theory.equivalences-enriched-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.enriched-undirected-graphsᵉ
open import graph-theory.equivalences-undirected-graphsᵉ
open import graph-theory.neighbors-undirected-graphsᵉ
```

</details>

## Idea

Anᵉ **equivalenceᵉ ofᵉ `(A,B)`-enrichedᵉ undirectedᵉ graphs**ᵉ fromᵉ anᵉ
[`(A,B)`-enrichedᵉ undirectedᵉ graph](graph-theory.enriched-undirected-graphs.mdᵉ)
`G`ᵉ to anᵉ `(A,B)`-enrichedᵉ undirectedᵉ graphᵉ `H`ᵉ consistsᵉ ofᵉ anᵉ
[equivalence](graph-theory.equivalences-undirected-graphs.mdᵉ) `e`ᵉ ofᵉ theᵉ
underlyingᵉ graphsᵉ ofᵉ `G`ᵉ andᵉ `H`ᵉ suchᵉ thatᵉ preservingᵉ theᵉ labelingᵉ andᵉ theᵉ
[equivalences](foundation-core.equivalences.mdᵉ) onᵉ theᵉ
[neighbors](graph-theory.neighbors-undirected-graphs.md).ᵉ

## Definition

### Equivalences between enriched undirected graphs

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Gᵉ : Enriched-Undirected-Graphᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  (Hᵉ : Enriched-Undirected-Graphᵉ l5ᵉ l6ᵉ Aᵉ Bᵉ)
  where

  equiv-Enriched-Undirected-Graphᵉ :
    UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  equiv-Enriched-Undirected-Graphᵉ =
    Σᵉ ( equiv-Undirected-Graphᵉ
        ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
        ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ))
      ( λ eᵉ →
        Σᵉ ( ( shape-vertex-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ) ~ᵉ
            ( ( shape-vertex-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ) ∘ᵉ
              ( vertex-equiv-Undirected-Graphᵉ
                ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
                ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ)
                ( eᵉ))))
          ( λ αᵉ →
            ( xᵉ : vertex-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ) →
            htpy-equivᵉ
              ( ( equiv-neighbor-equiv-Undirected-Graphᵉ
                  ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
                  ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ)
                  ( eᵉ)
                  ( xᵉ)) ∘eᵉ
                ( equiv-neighbor-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ xᵉ))
              ( ( equiv-neighbor-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ
                  ( vertex-equiv-Undirected-Graphᵉ
                    ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
                    ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ)
                    ( eᵉ)
                    ( xᵉ))) ∘eᵉ
                ( equiv-trᵉ Bᵉ (αᵉ xᵉ)))))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Gᵉ : Enriched-Undirected-Graphᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  (Hᵉ : Enriched-Undirected-Graphᵉ l5ᵉ l6ᵉ Aᵉ Bᵉ)
  (eᵉ : equiv-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ Hᵉ)
  where

  equiv-undirected-graph-equiv-Enriched-Undirected-Graphᵉ :
    equiv-Undirected-Graphᵉ
      ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
      ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ)
  equiv-undirected-graph-equiv-Enriched-Undirected-Graphᵉ = pr1ᵉ eᵉ

  equiv-vertex-equiv-Enriched-Undirected-Graphᵉ :
    vertex-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ ≃ᵉ
    vertex-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ
  equiv-vertex-equiv-Enriched-Undirected-Graphᵉ =
    equiv-vertex-equiv-Undirected-Graphᵉ
      ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
      ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ)
      ( equiv-undirected-graph-equiv-Enriched-Undirected-Graphᵉ)

  vertex-equiv-Enriched-Undirected-Graphᵉ :
    vertex-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ →
    vertex-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ
  vertex-equiv-Enriched-Undirected-Graphᵉ =
    vertex-equiv-Undirected-Graphᵉ
      ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
      ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ)
      ( equiv-undirected-graph-equiv-Enriched-Undirected-Graphᵉ)

  equiv-unordered-pair-vertices-equiv-Enriched-Undirected-Graphᵉ :
    unordered-pair-vertices-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ ≃ᵉ
    unordered-pair-vertices-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ
  equiv-unordered-pair-vertices-equiv-Enriched-Undirected-Graphᵉ =
    equiv-unordered-pair-vertices-equiv-Undirected-Graphᵉ
      ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
      ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ)
      ( equiv-undirected-graph-equiv-Enriched-Undirected-Graphᵉ)

  unordered-pair-vertices-equiv-Enriched-Undirected-Graphᵉ :
    unordered-pair-vertices-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ →
    unordered-pair-vertices-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ
  unordered-pair-vertices-equiv-Enriched-Undirected-Graphᵉ =
    unordered-pair-vertices-equiv-Undirected-Graphᵉ
      ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
      ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ)
      ( equiv-undirected-graph-equiv-Enriched-Undirected-Graphᵉ)

  equiv-edge-equiv-Enriched-Undirected-Graphᵉ :
    ( pᵉ : unordered-pair-vertices-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ) →
    edge-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ pᵉ ≃ᵉ
    edge-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ
      ( unordered-pair-vertices-equiv-Enriched-Undirected-Graphᵉ pᵉ)
  equiv-edge-equiv-Enriched-Undirected-Graphᵉ =
    equiv-edge-equiv-Undirected-Graphᵉ
      ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
      ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ)
      ( equiv-undirected-graph-equiv-Enriched-Undirected-Graphᵉ)

  edge-equiv-Enriched-Undirected-Graphᵉ :
    ( pᵉ : unordered-pair-vertices-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ) →
    edge-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ pᵉ →
    edge-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ
      ( unordered-pair-vertices-equiv-Enriched-Undirected-Graphᵉ pᵉ)
  edge-equiv-Enriched-Undirected-Graphᵉ =
    edge-equiv-Undirected-Graphᵉ
      ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
      ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ)
      ( equiv-undirected-graph-equiv-Enriched-Undirected-Graphᵉ)

  shape-equiv-Enriched-Undirected-Graphᵉ :
    (vᵉ : vertex-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ) →
    ( shape-vertex-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ vᵉ) ＝ᵉ
    ( shape-vertex-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ
      ( vertex-equiv-Enriched-Undirected-Graphᵉ vᵉ))
  shape-equiv-Enriched-Undirected-Graphᵉ = pr1ᵉ (pr2ᵉ eᵉ)
```

### The identity equivalence of an enriched undirected graph

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Gᵉ : Enriched-Undirected-Graphᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  where

  id-equiv-Enriched-Undirected-Graphᵉ :
    equiv-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ Gᵉ
  pr1ᵉ id-equiv-Enriched-Undirected-Graphᵉ =
    id-equiv-Undirected-Graphᵉ (undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
  pr1ᵉ (pr2ᵉ id-equiv-Enriched-Undirected-Graphᵉ) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ id-equiv-Enriched-Undirected-Graphᵉ) xᵉ bᵉ =
    neighbor-id-equiv-Undirected-Graphᵉ
      ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
      ( xᵉ)
      ( map-equiv-neighbor-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ xᵉ bᵉ)
```

## Properties

### Univalence for enriched undirected graphs

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Gᵉ : Enriched-Undirected-Graphᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  where

  is-torsorial-equiv-Enriched-Undirected-Graphᵉ :
    is-torsorialᵉ (equiv-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
  is-torsorial-equiv-Enriched-Undirected-Graphᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equiv-Undirected-Graphᵉ
        ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ))
      ( pairᵉ
        ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
        ( id-equiv-Undirected-Graphᵉ
          ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)))
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ
          ( shape-vertex-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ))
        ( pairᵉ
          ( shape-vertex-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
          ( refl-htpyᵉ))
        ( is-torsorial-Eq-Πᵉ
          ( λ xᵉ →
            is-torsorial-htpy-equivᵉ
              ( equiv-neighbor-equiv-Undirected-Graphᵉ
                  ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
                  ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
                  ( id-equiv-Undirected-Graphᵉ
                    ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ))
                  ( xᵉ) ∘eᵉ
                ( equiv-neighbor-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ xᵉ)))))

  equiv-eq-Enriched-Undirected-Graphᵉ :
    (Hᵉ : Enriched-Undirected-Graphᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ) →
    (Gᵉ ＝ᵉ Hᵉ) → equiv-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ Hᵉ
  equiv-eq-Enriched-Undirected-Graphᵉ Hᵉ reflᵉ =
    id-equiv-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ

  is-equiv-equiv-eq-Enriched-Undirected-Graphᵉ :
    (Hᵉ : Enriched-Undirected-Graphᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ) →
    is-equivᵉ (equiv-eq-Enriched-Undirected-Graphᵉ Hᵉ)
  is-equiv-equiv-eq-Enriched-Undirected-Graphᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-equiv-Enriched-Undirected-Graphᵉ)
      ( equiv-eq-Enriched-Undirected-Graphᵉ)

  extensionality-Enriched-Undirected-Graphᵉ :
    (Hᵉ : Enriched-Undirected-Graphᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ) →
    (Gᵉ ＝ᵉ Hᵉ) ≃ᵉ equiv-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ Hᵉ
  pr1ᵉ (extensionality-Enriched-Undirected-Graphᵉ Hᵉ) =
    equiv-eq-Enriched-Undirected-Graphᵉ Hᵉ
  pr2ᵉ (extensionality-Enriched-Undirected-Graphᵉ Hᵉ) =
    is-equiv-equiv-eq-Enriched-Undirected-Graphᵉ Hᵉ

  eq-equiv-Enriched-Undirected-Graphᵉ :
    (Hᵉ : Enriched-Undirected-Graphᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ) →
    equiv-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ Hᵉ → (Gᵉ ＝ᵉ Hᵉ)
  eq-equiv-Enriched-Undirected-Graphᵉ Hᵉ =
    map-inv-equivᵉ (extensionality-Enriched-Undirected-Graphᵉ Hᵉ)
```

## External links

-ᵉ [Graphᵉ isomoprhism](https://www.wikidata.org/entity/Q303100ᵉ) atᵉ Wikidataᵉ
-ᵉ [Graphᵉ isomorphism](https://en.wikipedia.org/wiki/Graph_isomorphismᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [Graphᵉ isomorphism](https://mathworld.wolfram.com/GraphIsomorphism.htmlᵉ) atᵉ
  Wolframᵉ Mathworldᵉ
-ᵉ [Isomorphism](https://ncatlab.org/nlab/show/isomorphismᵉ) atᵉ $n$Labᵉ