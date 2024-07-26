# Fibers of directed trees

```agda
module trees.fibers-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
open import graph-theory.fibers-directed-graphsᵉ

open import trees.bases-directed-treesᵉ
open import trees.directed-treesᵉ
open import trees.morphisms-directed-treesᵉ
```

</details>

## Idea

Theᵉ **fiber**ᵉ ofᵉ aᵉ directedᵉ treeᵉ `T`ᵉ atᵉ aᵉ nodeᵉ `x`ᵉ consistsᵉ ofᵉ allᵉ nodesᵉ `y`ᵉ
equippedᵉ with aᵉ walkᵉ `wᵉ : walkᵉ Tᵉ yᵉ x`.ᵉ Anᵉ edgeᵉ fromᵉ `(y,ᵉ w)`ᵉ to `(zᵉ ,ᵉ v)`ᵉ
consistsᵉ ofᵉ anᵉ edgeᵉ `eᵉ : edgeᵉ Tᵉ xᵉ y`ᵉ suchᵉ thatᵉ `wᵉ ＝ᵉ cons-walkᵉ eᵉ v`.ᵉ

## Definitions

### The underlying graph of the fiber of `T` at `x`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (xᵉ : node-Directed-Treeᵉ Tᵉ)
  where

  node-fiber-Directed-Treeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  node-fiber-Directed-Treeᵉ =
    node-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  node-inclusion-fiber-Directed-Treeᵉ :
    node-fiber-Directed-Treeᵉ → node-Directed-Treeᵉ Tᵉ
  node-inclusion-fiber-Directed-Treeᵉ =
    node-inclusion-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  walk-node-inclusion-fiber-Directed-Treeᵉ :
    (yᵉ : node-fiber-Directed-Treeᵉ) →
    walk-Directed-Treeᵉ Tᵉ (node-inclusion-fiber-Directed-Treeᵉ yᵉ) xᵉ
  walk-node-inclusion-fiber-Directed-Treeᵉ =
    walk-node-inclusion-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  root-fiber-Directed-Treeᵉ : node-fiber-Directed-Treeᵉ
  root-fiber-Directed-Treeᵉ =
    root-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  is-root-fiber-Directed-Treeᵉ : node-fiber-Directed-Treeᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-root-fiber-Directed-Treeᵉ =
    is-root-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  edge-fiber-Directed-Treeᵉ : (yᵉ zᵉ : node-fiber-Directed-Treeᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  edge-fiber-Directed-Treeᵉ =
    edge-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  edge-inclusion-fiber-Directed-Treeᵉ :
    (yᵉ zᵉ : node-fiber-Directed-Treeᵉ) (eᵉ : edge-fiber-Directed-Treeᵉ yᵉ zᵉ) →
    edge-Directed-Treeᵉ Tᵉ
      ( node-inclusion-fiber-Directed-Treeᵉ yᵉ)
      ( node-inclusion-fiber-Directed-Treeᵉ zᵉ)
  edge-inclusion-fiber-Directed-Treeᵉ =
    edge-inclusion-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  walk-edge-fiber-Directed-Treeᵉ :
    (yᵉ zᵉ : node-fiber-Directed-Treeᵉ) (eᵉ : edge-fiber-Directed-Treeᵉ yᵉ zᵉ) →
    walk-node-inclusion-fiber-Directed-Treeᵉ yᵉ ＝ᵉ
    cons-walk-Directed-Treeᵉ Tᵉ
      ( edge-inclusion-fiber-Directed-Treeᵉ yᵉ zᵉ eᵉ)
      ( walk-node-inclusion-fiber-Directed-Treeᵉ zᵉ)
  walk-edge-fiber-Directed-Treeᵉ =
    walk-edge-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  graph-fiber-Directed-Treeᵉ : Directed-Graphᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  graph-fiber-Directed-Treeᵉ =
    graph-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  walk-fiber-Directed-Treeᵉ : (yᵉ zᵉ : node-fiber-Directed-Treeᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  walk-fiber-Directed-Treeᵉ =
    walk-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  walk-to-root-fiber-walk-Directed-Treeᵉ :
    (yᵉ : node-Directed-Treeᵉ Tᵉ) (wᵉ : walk-Directed-Treeᵉ Tᵉ yᵉ xᵉ) →
    walk-fiber-Directed-Treeᵉ (yᵉ ,ᵉ wᵉ) root-fiber-Directed-Treeᵉ
  walk-to-root-fiber-walk-Directed-Treeᵉ =
    walk-to-root-fiber-walk-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  walk-to-root-fiber-Directed-Treeᵉ :
    (yᵉ : node-fiber-Directed-Treeᵉ) →
    walk-fiber-Directed-Treeᵉ yᵉ root-fiber-Directed-Treeᵉ
  walk-to-root-fiber-Directed-Treeᵉ =
    walk-to-root-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ
```

### The fiber of `T` at `x`

```agda
  center-unique-direct-successor-fiber-Directed-Treeᵉ :
    (yᵉ : node-fiber-Directed-Treeᵉ) →
    ( is-root-fiber-Directed-Treeᵉ yᵉ) +ᵉ
    ( Σᵉ ( node-fiber-Directed-Treeᵉ) ( edge-fiber-Directed-Treeᵉ yᵉ))
  center-unique-direct-successor-fiber-Directed-Treeᵉ =
    center-unique-direct-successor-fiber-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Tᵉ) xᵉ

  contraction-unique-direct-successor-fiber-Directed-Treeᵉ :
    (yᵉ : node-fiber-Directed-Treeᵉ) →
    ( pᵉ :
      ( is-root-fiber-Directed-Treeᵉ yᵉ) +ᵉ
      ( Σᵉ ( node-fiber-Directed-Treeᵉ) (edge-fiber-Directed-Treeᵉ yᵉ))) →
    center-unique-direct-successor-fiber-Directed-Treeᵉ yᵉ ＝ᵉ pᵉ
  contraction-unique-direct-successor-fiber-Directed-Treeᵉ =
    contraction-unique-direct-successor-fiber-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Tᵉ) xᵉ

  unique-direct-successor-fiber-Directed-Treeᵉ :
    unique-direct-successor-Directed-Graphᵉ
      ( graph-fiber-Directed-Treeᵉ)
      ( root-fiber-Directed-Treeᵉ)
  unique-direct-successor-fiber-Directed-Treeᵉ =
    unique-direct-successor-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  is-tree-fiber-Directed-Treeᵉ :
    is-tree-Directed-Graphᵉ graph-fiber-Directed-Treeᵉ
  is-tree-fiber-Directed-Treeᵉ =
    is-tree-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  fiber-Directed-Treeᵉ : Directed-Treeᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  fiber-Directed-Treeᵉ = fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  inclusion-fiber-Directed-Treeᵉ : hom-Directed-Treeᵉ fiber-Directed-Treeᵉ Tᵉ
  inclusion-fiber-Directed-Treeᵉ =
    inclusion-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ
```

### Computing the children of a node in a fiber

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (xᵉ : node-Directed-Treeᵉ Tᵉ)
  where

  direct-predecessor-fiber-Directed-Treeᵉ :
    (yᵉ : node-fiber-Directed-Treeᵉ Tᵉ xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  direct-predecessor-fiber-Directed-Treeᵉ =
    direct-predecessor-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  direct-predecessor-inclusion-fiber-Directed-Treeᵉ :
    (yᵉ : node-fiber-Directed-Treeᵉ Tᵉ xᵉ) →
    direct-predecessor-fiber-Directed-Treeᵉ yᵉ →
    direct-predecessor-Directed-Treeᵉ Tᵉ
      ( node-inclusion-fiber-Directed-Treeᵉ Tᵉ xᵉ yᵉ)
  direct-predecessor-inclusion-fiber-Directed-Treeᵉ =
    direct-predecessor-inclusion-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  compute-direct-predecessor-fiber-Directed-Treeᵉ :
    (yᵉ : node-fiber-Directed-Treeᵉ Tᵉ xᵉ) →
    direct-predecessor-fiber-Directed-Treeᵉ yᵉ ≃ᵉ
    direct-predecessor-Directed-Treeᵉ Tᵉ
      ( node-inclusion-fiber-Directed-Treeᵉ Tᵉ xᵉ yᵉ)
  compute-direct-predecessor-fiber-Directed-Treeᵉ =
    compute-direct-predecessor-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  map-compute-direct-predecessor-fiber-Directed-Treeᵉ :
    (yᵉ : node-fiber-Directed-Treeᵉ Tᵉ xᵉ) →
    direct-predecessor-fiber-Directed-Treeᵉ yᵉ →
    direct-predecessor-Directed-Treeᵉ Tᵉ
      ( node-inclusion-fiber-Directed-Treeᵉ Tᵉ xᵉ yᵉ)
  map-compute-direct-predecessor-fiber-Directed-Treeᵉ =
    map-compute-direct-predecessor-fiber-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Tᵉ)
      ( xᵉ)

  htpy-compute-direct-predecessor-fiber-Directed-Treeᵉ :
    (yᵉ : node-fiber-Directed-Treeᵉ Tᵉ xᵉ) →
    direct-predecessor-inclusion-fiber-Directed-Treeᵉ yᵉ ~ᵉ
    map-compute-direct-predecessor-fiber-Directed-Treeᵉ yᵉ
  htpy-compute-direct-predecessor-fiber-Directed-Treeᵉ =
    htpy-compute-direct-predecessor-fiber-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Tᵉ)
      ( xᵉ)

  inv-compute-direct-predecessor-fiber-Directed-Treeᵉ :
    (yᵉ : node-fiber-Directed-Treeᵉ Tᵉ xᵉ) →
    direct-predecessor-Directed-Treeᵉ Tᵉ
      ( node-inclusion-fiber-Directed-Treeᵉ Tᵉ xᵉ yᵉ) ≃ᵉ
    direct-predecessor-fiber-Directed-Treeᵉ yᵉ
  inv-compute-direct-predecessor-fiber-Directed-Treeᵉ =
    inv-compute-direct-predecessor-fiber-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Tᵉ)
      ( xᵉ)

  Eq-direct-predecessor-fiber-Directed-Treeᵉ :
    (yᵉ : node-fiber-Directed-Treeᵉ Tᵉ xᵉ) →
    (uᵉ vᵉ : direct-predecessor-fiber-Directed-Treeᵉ yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  Eq-direct-predecessor-fiber-Directed-Treeᵉ =
    Eq-direct-predecessor-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ

  eq-Eq-direct-predecessor-fiber-Directed-Treeᵉ :
    (yᵉ : node-fiber-Directed-Treeᵉ Tᵉ xᵉ) →
    ( uᵉ vᵉ : direct-predecessor-fiber-Directed-Treeᵉ yᵉ) →
    Eq-direct-predecessor-fiber-Directed-Treeᵉ yᵉ uᵉ vᵉ → uᵉ ＝ᵉ vᵉ
  eq-Eq-direct-predecessor-fiber-Directed-Treeᵉ =
    eq-Eq-direct-predecessor-fiber-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ) xᵉ
```

### The fiber of a tree at a base node

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (bᵉ : base-Directed-Treeᵉ Tᵉ)
  where

  fiber-base-Directed-Treeᵉ : Directed-Treeᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  fiber-base-Directed-Treeᵉ = fiber-Directed-Treeᵉ Tᵉ (node-base-Directed-Treeᵉ Tᵉ bᵉ)

  node-fiber-base-Directed-Treeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  node-fiber-base-Directed-Treeᵉ = node-Directed-Treeᵉ fiber-base-Directed-Treeᵉ

  edge-fiber-base-Directed-Treeᵉ :
    (xᵉ yᵉ : node-fiber-base-Directed-Treeᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  edge-fiber-base-Directed-Treeᵉ = edge-Directed-Treeᵉ fiber-base-Directed-Treeᵉ

  root-fiber-base-Directed-Treeᵉ : node-fiber-base-Directed-Treeᵉ
  root-fiber-base-Directed-Treeᵉ = root-Directed-Treeᵉ fiber-base-Directed-Treeᵉ

  walk-fiber-base-Directed-Treeᵉ :
    (xᵉ yᵉ : node-fiber-base-Directed-Treeᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  walk-fiber-base-Directed-Treeᵉ = walk-Directed-Treeᵉ fiber-base-Directed-Treeᵉ
```