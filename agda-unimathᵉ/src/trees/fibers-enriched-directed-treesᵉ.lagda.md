# Fibers of enriched directed trees

```agda
module trees.fibers-enriched-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.walks-directed-graphsᵉ

open import trees.bases-enriched-directed-treesᵉ
open import trees.directed-treesᵉ
open import trees.enriched-directed-treesᵉ
open import trees.fibers-directed-treesᵉ
```

</details>

## Idea

Theᵉ **fiber**ᵉ ofᵉ anᵉ enrichedᵉ directedᵉ treeᵉ atᵉ aᵉ nodeᵉ `x`ᵉ isᵉ theᵉ fiberᵉ ofᵉ theᵉ
underlyingᵉ directedᵉ treeᵉ atᵉ `x`ᵉ equippedᵉ with theᵉ inheritedᵉ enrichedᵉ structure.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ) (xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
  where

  directed-tree-fiber-Enriched-Directed-Treeᵉ : Directed-Treeᵉ (l3ᵉ ⊔ l4ᵉ) (l3ᵉ ⊔ l4ᵉ)
  directed-tree-fiber-Enriched-Directed-Treeᵉ =
    fiber-Directed-Treeᵉ (directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) xᵉ

  node-fiber-Enriched-Directed-Treeᵉ : UUᵉ (l3ᵉ ⊔ l4ᵉ)
  node-fiber-Enriched-Directed-Treeᵉ =
    node-fiber-Directed-Treeᵉ (directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) xᵉ

  node-inclusion-fiber-Enriched-Directed-Treeᵉ :
    node-fiber-Enriched-Directed-Treeᵉ → node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
  node-inclusion-fiber-Enriched-Directed-Treeᵉ =
    node-inclusion-fiber-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( xᵉ)

  walk-node-inclusion-fiber-Enriched-Directed-Treeᵉ :
    ( yᵉ : node-fiber-Enriched-Directed-Treeᵉ) →
    walk-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-inclusion-fiber-Enriched-Directed-Treeᵉ yᵉ)
      ( xᵉ)
  walk-node-inclusion-fiber-Enriched-Directed-Treeᵉ =
    walk-node-inclusion-fiber-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( xᵉ)

  edge-fiber-Enriched-Directed-Treeᵉ :
    (yᵉ zᵉ : node-fiber-Enriched-Directed-Treeᵉ) → UUᵉ (l3ᵉ ⊔ l4ᵉ)
  edge-fiber-Enriched-Directed-Treeᵉ =
    edge-fiber-Directed-Treeᵉ (directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) xᵉ

  edge-inclusion-fiber-Enriched-Directed-Treeᵉ :
    (yᵉ zᵉ : node-fiber-Enriched-Directed-Treeᵉ) →
    edge-fiber-Enriched-Directed-Treeᵉ yᵉ zᵉ →
    edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-inclusion-fiber-Enriched-Directed-Treeᵉ yᵉ)
      ( node-inclusion-fiber-Enriched-Directed-Treeᵉ zᵉ)
  edge-inclusion-fiber-Enriched-Directed-Treeᵉ =
    edge-inclusion-fiber-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( xᵉ)

  direct-predecessor-fiber-Enriched-Directed-Treeᵉ :
    (xᵉ : node-fiber-Enriched-Directed-Treeᵉ) → UUᵉ (l3ᵉ ⊔ l4ᵉ)
  direct-predecessor-fiber-Enriched-Directed-Treeᵉ =
    direct-predecessor-fiber-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( xᵉ)

  shape-fiber-Enriched-Directed-Treeᵉ :
    node-fiber-Enriched-Directed-Treeᵉ → Aᵉ
  shape-fiber-Enriched-Directed-Treeᵉ yᵉ =
    shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-inclusion-fiber-Enriched-Directed-Treeᵉ yᵉ)

  enrichment-fiber-Enriched-Directed-Treeᵉ :
    (yᵉ : node-fiber-Enriched-Directed-Treeᵉ) →
    Bᵉ (shape-fiber-Enriched-Directed-Treeᵉ yᵉ) ≃ᵉ
    direct-predecessor-fiber-Enriched-Directed-Treeᵉ yᵉ
  enrichment-fiber-Enriched-Directed-Treeᵉ (yᵉ ,ᵉ wᵉ) =
    ( interchange-Σ-Σᵉ (λ uᵉ eᵉ vᵉ → vᵉ ＝ᵉ cons-walk-Directed-Graphᵉ eᵉ wᵉ)) ∘eᵉ
    ( ( inv-right-unit-law-Σ-is-contrᵉ
        ( λ iᵉ →
          is-torsorial-Id'ᵉ (cons-walk-Directed-Graphᵉ (pr2ᵉ iᵉ) wᵉ))) ∘eᵉ
      ( enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ yᵉ))

  fiber-Enriched-Directed-Treeᵉ : Enriched-Directed-Treeᵉ (l3ᵉ ⊔ l4ᵉ) (l3ᵉ ⊔ l4ᵉ) Aᵉ Bᵉ
  pr1ᵉ fiber-Enriched-Directed-Treeᵉ = directed-tree-fiber-Enriched-Directed-Treeᵉ
  pr1ᵉ (pr2ᵉ fiber-Enriched-Directed-Treeᵉ) = shape-fiber-Enriched-Directed-Treeᵉ
  pr2ᵉ (pr2ᵉ fiber-Enriched-Directed-Treeᵉ) =
    enrichment-fiber-Enriched-Directed-Treeᵉ

  map-enrichment-fiber-Enriched-Directed-Treeᵉ :
    (yᵉ : node-fiber-Enriched-Directed-Treeᵉ) →
    Bᵉ ( shape-fiber-Enriched-Directed-Treeᵉ yᵉ) →
    direct-predecessor-fiber-Enriched-Directed-Treeᵉ yᵉ
  map-enrichment-fiber-Enriched-Directed-Treeᵉ =
    map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ fiber-Enriched-Directed-Treeᵉ

  node-enrichment-fiber-Enriched-Directed-Treeᵉ :
    (yᵉ : node-fiber-Enriched-Directed-Treeᵉ)
    (bᵉ : Bᵉ (shape-fiber-Enriched-Directed-Treeᵉ yᵉ)) →
    node-fiber-Enriched-Directed-Treeᵉ
  node-enrichment-fiber-Enriched-Directed-Treeᵉ =
    node-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ fiber-Enriched-Directed-Treeᵉ

  edge-enrichment-fiber-Enriched-Directed-Treeᵉ :
    (yᵉ : node-fiber-Enriched-Directed-Treeᵉ)
    (bᵉ : Bᵉ (shape-fiber-Enriched-Directed-Treeᵉ yᵉ)) →
    edge-fiber-Enriched-Directed-Treeᵉ
      ( node-enrichment-fiber-Enriched-Directed-Treeᵉ yᵉ bᵉ)
      ( yᵉ)
  edge-enrichment-fiber-Enriched-Directed-Treeᵉ =
    edge-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ fiber-Enriched-Directed-Treeᵉ

  eq-map-enrichment-fiber-Enriched-Directed-Treeᵉ :
    (yᵉ : node-fiber-Enriched-Directed-Treeᵉ)
    (bᵉ : Bᵉ (shape-fiber-Enriched-Directed-Treeᵉ yᵉ)) →
    (wᵉ :
      walk-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
        ( node-inclusion-fiber-Enriched-Directed-Treeᵉ
          ( node-enrichment-fiber-Enriched-Directed-Treeᵉ yᵉ bᵉ))
        ( xᵉ)) →
    (pᵉ :
      ( wᵉ) ＝ᵉ
      ( cons-walk-Directed-Graphᵉ
        ( edge-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
          ( node-inclusion-fiber-Enriched-Directed-Treeᵉ yᵉ)
          ( bᵉ))
        ( walk-node-inclusion-fiber-Enriched-Directed-Treeᵉ yᵉ))) →
    ( ( ( node-inclusion-fiber-Enriched-Directed-Treeᵉ
          ( node-enrichment-fiber-Enriched-Directed-Treeᵉ yᵉ bᵉ)) ,ᵉ
        ( wᵉ)) ,ᵉ
      ( edge-inclusion-fiber-Enriched-Directed-Treeᵉ
        ( node-enrichment-fiber-Enriched-Directed-Treeᵉ yᵉ bᵉ)
        ( yᵉ)
        ( edge-enrichment-fiber-Enriched-Directed-Treeᵉ yᵉ bᵉ)) ,ᵉ
      ( pᵉ)) ＝ᵉ
    map-enrichment-fiber-Enriched-Directed-Treeᵉ yᵉ bᵉ
  eq-map-enrichment-fiber-Enriched-Directed-Treeᵉ yᵉ bᵉ wᵉ pᵉ =
    eq-interchange-Σ-Σ-is-contrᵉ _
      ( is-torsorial-Id'ᵉ
        ( cons-walk-Directed-Graphᵉ
          ( edge-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
            ( node-inclusion-fiber-Enriched-Directed-Treeᵉ yᵉ)
            ( bᵉ))
          ( walk-node-inclusion-fiber-Enriched-Directed-Treeᵉ yᵉ)))
```

### Computing the direct predecessors of a node in a fiber

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  (xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
  where

  compute-direct-predecessor-fiber-Enriched-Directed-Treeᵉ :
    (yᵉ : node-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ) →
    direct-predecessor-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ yᵉ ≃ᵉ
    direct-predecessor-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-inclusion-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ yᵉ)
  compute-direct-predecessor-fiber-Enriched-Directed-Treeᵉ =
    compute-direct-predecessor-fiber-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( xᵉ)

  map-compute-direct-predecessor-fiber-Enriched-Directed-Treeᵉ :
    (yᵉ : node-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ) →
    direct-predecessor-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ yᵉ →
    direct-predecessor-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-inclusion-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ yᵉ)
  map-compute-direct-predecessor-fiber-Enriched-Directed-Treeᵉ =
    map-compute-direct-predecessor-fiber-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( xᵉ)

  inv-compute-direct-predecessor-fiber-Enriched-Directed-Treeᵉ :
    (yᵉ : node-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ) →
    direct-predecessor-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-inclusion-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ yᵉ) ≃ᵉ
    direct-predecessor-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ yᵉ
  inv-compute-direct-predecessor-fiber-Enriched-Directed-Treeᵉ =
    inv-compute-direct-predecessor-fiber-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( xᵉ)

  Eq-direct-predecessor-fiber-Enriched-Directed-Treeᵉ :
    (yᵉ : node-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ) →
    (uᵉ vᵉ : direct-predecessor-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ yᵉ) →
    UUᵉ (l3ᵉ ⊔ l4ᵉ)
  Eq-direct-predecessor-fiber-Enriched-Directed-Treeᵉ =
    Eq-direct-predecessor-fiber-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( xᵉ)

  eq-Eq-direct-predecessor-fiber-Enriched-Directed-Treeᵉ :
    (yᵉ : node-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ) →
    ( uᵉ vᵉ : direct-predecessor-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ yᵉ) →
    Eq-direct-predecessor-fiber-Enriched-Directed-Treeᵉ yᵉ uᵉ vᵉ → uᵉ ＝ᵉ vᵉ
  eq-Eq-direct-predecessor-fiber-Enriched-Directed-Treeᵉ =
    eq-Eq-direct-predecessor-fiber-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( xᵉ)
```

### The fiber of a tree at a base node

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  (bᵉ : Bᵉ (shape-root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ))
  where

  fiber-base-Enriched-Directed-Treeᵉ :
    Enriched-Directed-Treeᵉ (l3ᵉ ⊔ l4ᵉ) (l3ᵉ ⊔ l4ᵉ) Aᵉ Bᵉ
  fiber-base-Enriched-Directed-Treeᵉ =
    fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ)

  node-fiber-base-Enriched-Directed-Treeᵉ : UUᵉ (l3ᵉ ⊔ l4ᵉ)
  node-fiber-base-Enriched-Directed-Treeᵉ =
    node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ fiber-base-Enriched-Directed-Treeᵉ

  edge-fiber-base-Enriched-Directed-Treeᵉ :
    (xᵉ yᵉ : node-fiber-base-Enriched-Directed-Treeᵉ) → UUᵉ (l3ᵉ ⊔ l4ᵉ)
  edge-fiber-base-Enriched-Directed-Treeᵉ =
    edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ fiber-base-Enriched-Directed-Treeᵉ

  root-fiber-base-Enriched-Directed-Treeᵉ :
    node-fiber-base-Enriched-Directed-Treeᵉ
  root-fiber-base-Enriched-Directed-Treeᵉ =
    root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ fiber-base-Enriched-Directed-Treeᵉ

  walk-fiber-base-Enriched-Directed-Treeᵉ :
    (xᵉ yᵉ : node-fiber-base-Enriched-Directed-Treeᵉ) → UUᵉ (l3ᵉ ⊔ l4ᵉ)
  walk-fiber-base-Enriched-Directed-Treeᵉ =
    walk-Enriched-Directed-Treeᵉ Aᵉ Bᵉ fiber-base-Enriched-Directed-Treeᵉ

  shape-fiber-base-Enriched-Directed-Treeᵉ :
    node-fiber-base-Enriched-Directed-Treeᵉ → Aᵉ
  shape-fiber-base-Enriched-Directed-Treeᵉ =
    shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ fiber-base-Enriched-Directed-Treeᵉ

  enrichment-fiber-base-Enriched-Directed-Treeᵉ :
    (yᵉ : node-fiber-base-Enriched-Directed-Treeᵉ) →
    Bᵉ (shape-fiber-base-Enriched-Directed-Treeᵉ yᵉ) ≃ᵉ
    Σᵉ ( node-fiber-base-Enriched-Directed-Treeᵉ)
      ( λ zᵉ → edge-fiber-base-Enriched-Directed-Treeᵉ zᵉ yᵉ)
  enrichment-fiber-base-Enriched-Directed-Treeᵉ =
    enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ fiber-base-Enriched-Directed-Treeᵉ

  map-enrichment-fiber-base-Enriched-Directed-Treeᵉ :
    (yᵉ : node-fiber-base-Enriched-Directed-Treeᵉ) →
    Bᵉ (shape-fiber-base-Enriched-Directed-Treeᵉ yᵉ) →
    Σᵉ ( node-fiber-base-Enriched-Directed-Treeᵉ)
      ( λ zᵉ → edge-fiber-base-Enriched-Directed-Treeᵉ zᵉ yᵉ)
  map-enrichment-fiber-base-Enriched-Directed-Treeᵉ =
    map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ fiber-base-Enriched-Directed-Treeᵉ

  directed-tree-fiber-base-Enriched-Directed-Treeᵉ :
    Directed-Treeᵉ (l3ᵉ ⊔ l4ᵉ) (l3ᵉ ⊔ l4ᵉ)
  directed-tree-fiber-base-Enriched-Directed-Treeᵉ =
    directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ fiber-base-Enriched-Directed-Treeᵉ
```