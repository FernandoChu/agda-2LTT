# Fibers of directed graphs

```agda
module graph-theory.fibers-directed-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
open import graph-theory.morphisms-directed-graphsᵉ
open import graph-theory.walks-directed-graphsᵉ

open import trees.directed-treesᵉ
```

</details>

## Idea

Considerᵉ aᵉ vertexᵉ `x`ᵉ in aᵉ [directedᵉ graph](graph-theory.directed-graphs.mdᵉ)
`G`.ᵉ Theᵉ **fiber**ᵉ ofᵉ `G`ᵉ atᵉ `x`ᵉ isᵉ aᵉ [directedᵉ tree](trees.directed-trees.mdᵉ)
ofᵉ whichᵉ theᵉ typeᵉ ofᵉ nodesᵉ consistsᵉ ofᵉ verticesᵉ `y`ᵉ equippedᵉ with aᵉ
[walk](graph-theory.walks-directed-graphs.mdᵉ) `w`ᵉ fromᵉ `y`ᵉ to `x`,ᵉ andᵉ theᵉ typeᵉ
ofᵉ edgesᵉ fromᵉ `(yᵉ ,ᵉ w)`ᵉ to `(zᵉ ,ᵉ v)`ᵉ consistᵉ ofᵉ anᵉ edgeᵉ `eᵉ : yᵉ → z`ᵉ suchᵉ thatᵉ
`wᵉ ＝ᵉ consᵉ eᵉ v`.ᵉ

## Definitions

### The underlying graph of the fiber of `G` at `x`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (xᵉ : vertex-Directed-Graphᵉ Gᵉ)
  where

  node-fiber-Directed-Graphᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  node-fiber-Directed-Graphᵉ =
    Σᵉ (vertex-Directed-Graphᵉ Gᵉ) (λ yᵉ → walk-Directed-Graphᵉ Gᵉ yᵉ xᵉ)

  module _
    (uᵉ : node-fiber-Directed-Graphᵉ)
    where

    node-inclusion-fiber-Directed-Graphᵉ : vertex-Directed-Graphᵉ Gᵉ
    node-inclusion-fiber-Directed-Graphᵉ = pr1ᵉ uᵉ

    walk-node-inclusion-fiber-Directed-Graphᵉ :
      walk-Directed-Graphᵉ Gᵉ node-inclusion-fiber-Directed-Graphᵉ xᵉ
    walk-node-inclusion-fiber-Directed-Graphᵉ = pr2ᵉ uᵉ

  root-fiber-Directed-Graphᵉ : node-fiber-Directed-Graphᵉ
  pr1ᵉ root-fiber-Directed-Graphᵉ = xᵉ
  pr2ᵉ root-fiber-Directed-Graphᵉ = refl-walk-Directed-Graphᵉ

  is-root-fiber-Directed-Graphᵉ : node-fiber-Directed-Graphᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-root-fiber-Directed-Graphᵉ yᵉ = root-fiber-Directed-Graphᵉ ＝ᵉ yᵉ

  edge-fiber-Directed-Graphᵉ : (yᵉ zᵉ : node-fiber-Directed-Graphᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  edge-fiber-Directed-Graphᵉ yᵉ zᵉ =
    Σᵉ ( edge-Directed-Graphᵉ Gᵉ
        ( node-inclusion-fiber-Directed-Graphᵉ yᵉ)
        ( node-inclusion-fiber-Directed-Graphᵉ zᵉ))
      ( λ eᵉ →
        ( walk-node-inclusion-fiber-Directed-Graphᵉ yᵉ) ＝ᵉ
        ( cons-walk-Directed-Graphᵉ eᵉ
          ( walk-node-inclusion-fiber-Directed-Graphᵉ zᵉ)))

  module _
    (yᵉ zᵉ : node-fiber-Directed-Graphᵉ) (eᵉ : edge-fiber-Directed-Graphᵉ yᵉ zᵉ)
    where

    edge-inclusion-fiber-Directed-Graphᵉ :
      edge-Directed-Graphᵉ Gᵉ
        ( node-inclusion-fiber-Directed-Graphᵉ yᵉ)
        ( node-inclusion-fiber-Directed-Graphᵉ zᵉ)
    edge-inclusion-fiber-Directed-Graphᵉ = pr1ᵉ eᵉ

    walk-edge-fiber-Directed-Graphᵉ :
      walk-node-inclusion-fiber-Directed-Graphᵉ yᵉ ＝ᵉ
      cons-walk-Directed-Graphᵉ
        ( edge-inclusion-fiber-Directed-Graphᵉ)
        ( walk-node-inclusion-fiber-Directed-Graphᵉ zᵉ)
    walk-edge-fiber-Directed-Graphᵉ = pr2ᵉ eᵉ

  graph-fiber-Directed-Graphᵉ : Directed-Graphᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ graph-fiber-Directed-Graphᵉ = node-fiber-Directed-Graphᵉ
  pr2ᵉ graph-fiber-Directed-Graphᵉ = edge-fiber-Directed-Graphᵉ

  walk-fiber-Directed-Graphᵉ : (yᵉ zᵉ : node-fiber-Directed-Graphᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  walk-fiber-Directed-Graphᵉ = walk-Directed-Graphᵉ graph-fiber-Directed-Graphᵉ

  walk-to-root-fiber-walk-Directed-Graphᵉ :
    (yᵉ : vertex-Directed-Graphᵉ Gᵉ) (wᵉ : walk-Directed-Graphᵉ Gᵉ yᵉ xᵉ) →
    walk-fiber-Directed-Graphᵉ (yᵉ ,ᵉ wᵉ) root-fiber-Directed-Graphᵉ
  walk-to-root-fiber-walk-Directed-Graphᵉ yᵉ refl-walk-Directed-Graphᵉ =
    refl-walk-Directed-Graphᵉ
  walk-to-root-fiber-walk-Directed-Graphᵉ .yᵉ
    ( cons-walk-Directed-Graphᵉ {yᵉ} {zᵉ} eᵉ wᵉ) =
    cons-walk-Directed-Graphᵉ
      ( eᵉ ,ᵉ reflᵉ)
      ( walk-to-root-fiber-walk-Directed-Graphᵉ zᵉ wᵉ)

  walk-to-root-fiber-Directed-Graphᵉ :
    (yᵉ : node-fiber-Directed-Graphᵉ) →
    walk-fiber-Directed-Graphᵉ yᵉ root-fiber-Directed-Graphᵉ
  walk-to-root-fiber-Directed-Graphᵉ (yᵉ ,ᵉ wᵉ) =
    walk-to-root-fiber-walk-Directed-Graphᵉ yᵉ wᵉ

  inclusion-fiber-Directed-Graphᵉ :
    hom-Directed-Graphᵉ graph-fiber-Directed-Graphᵉ Gᵉ
  pr1ᵉ inclusion-fiber-Directed-Graphᵉ = node-inclusion-fiber-Directed-Graphᵉ
  pr2ᵉ inclusion-fiber-Directed-Graphᵉ = edge-inclusion-fiber-Directed-Graphᵉ
```

### The fiber of `G` at `x` as a directed tree

```agda
  center-unique-direct-successor-fiber-Directed-Graphᵉ :
    (yᵉ : node-fiber-Directed-Graphᵉ) →
    ( is-root-fiber-Directed-Graphᵉ yᵉ) +ᵉ
    ( Σᵉ ( node-fiber-Directed-Graphᵉ) ( edge-fiber-Directed-Graphᵉ yᵉ))
  center-unique-direct-successor-fiber-Directed-Graphᵉ
    ( yᵉ ,ᵉ refl-walk-Directed-Graphᵉ) =
    inlᵉ reflᵉ
  center-unique-direct-successor-fiber-Directed-Graphᵉ
    ( yᵉ ,ᵉ cons-walk-Directed-Graphᵉ {yᵉ} {zᵉ} eᵉ wᵉ) = inrᵉ ((zᵉ ,ᵉ wᵉ) ,ᵉ (eᵉ ,ᵉ reflᵉ))

  contraction-unique-direct-successor-fiber-Directed-Graphᵉ :
    (yᵉ : node-fiber-Directed-Graphᵉ) →
    ( pᵉ :
      ( is-root-fiber-Directed-Graphᵉ yᵉ) +ᵉ
      ( Σᵉ ( node-fiber-Directed-Graphᵉ) (edge-fiber-Directed-Graphᵉ yᵉ))) →
    center-unique-direct-successor-fiber-Directed-Graphᵉ yᵉ ＝ᵉ pᵉ
  contraction-unique-direct-successor-fiber-Directed-Graphᵉ ._ (inlᵉ reflᵉ) = reflᵉ
  contraction-unique-direct-successor-fiber-Directed-Graphᵉ
    ( yᵉ ,ᵉ .(cons-walk-Directed-Graphᵉ eᵉ vᵉ)) (inrᵉ ((zᵉ ,ᵉ vᵉ) ,ᵉ eᵉ ,ᵉ reflᵉ)) =
    reflᵉ

  unique-direct-successor-fiber-Directed-Graphᵉ :
    unique-direct-successor-Directed-Graphᵉ
      ( graph-fiber-Directed-Graphᵉ)
      ( root-fiber-Directed-Graphᵉ)
  pr1ᵉ (unique-direct-successor-fiber-Directed-Graphᵉ yᵉ) =
    center-unique-direct-successor-fiber-Directed-Graphᵉ yᵉ
  pr2ᵉ (unique-direct-successor-fiber-Directed-Graphᵉ yᵉ) =
    contraction-unique-direct-successor-fiber-Directed-Graphᵉ yᵉ

  is-tree-fiber-Directed-Graphᵉ :
    is-tree-Directed-Graphᵉ graph-fiber-Directed-Graphᵉ
  is-tree-fiber-Directed-Graphᵉ =
    is-tree-unique-direct-successor-Directed-Graphᵉ
      graph-fiber-Directed-Graphᵉ
      root-fiber-Directed-Graphᵉ
      unique-direct-successor-fiber-Directed-Graphᵉ
      walk-to-root-fiber-Directed-Graphᵉ

  fiber-Directed-Graphᵉ : Directed-Treeᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ fiber-Directed-Graphᵉ = graph-fiber-Directed-Graphᵉ
  pr2ᵉ fiber-Directed-Graphᵉ = is-tree-fiber-Directed-Graphᵉ
```

### Computing the direct predecessors of a node in a fiber

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (xᵉ : vertex-Directed-Graphᵉ Gᵉ)
  where

  direct-predecessor-fiber-Directed-Graphᵉ :
    (yᵉ : node-fiber-Directed-Graphᵉ Gᵉ xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  direct-predecessor-fiber-Directed-Graphᵉ =
    direct-predecessor-Directed-Graphᵉ (graph-fiber-Directed-Graphᵉ Gᵉ xᵉ)

  direct-predecessor-inclusion-fiber-Directed-Graphᵉ :
    (yᵉ : node-fiber-Directed-Graphᵉ Gᵉ xᵉ) →
    direct-predecessor-fiber-Directed-Graphᵉ yᵉ →
    direct-predecessor-Directed-Graphᵉ Gᵉ
      ( node-inclusion-fiber-Directed-Graphᵉ Gᵉ xᵉ yᵉ)
  direct-predecessor-inclusion-fiber-Directed-Graphᵉ =
    direct-predecessor-hom-Directed-Graphᵉ
      ( graph-fiber-Directed-Graphᵉ Gᵉ xᵉ)
      ( Gᵉ)
      ( inclusion-fiber-Directed-Graphᵉ Gᵉ xᵉ)

  compute-direct-predecessor-fiber-Directed-Graphᵉ :
    (yᵉ : node-fiber-Directed-Graphᵉ Gᵉ xᵉ) →
    direct-predecessor-fiber-Directed-Graphᵉ yᵉ ≃ᵉ
    direct-predecessor-Directed-Graphᵉ Gᵉ
      ( node-inclusion-fiber-Directed-Graphᵉ Gᵉ xᵉ yᵉ)
  compute-direct-predecessor-fiber-Directed-Graphᵉ yᵉ =
    ( right-unit-law-Σ-is-contrᵉ (λ (uᵉ ,ᵉ eᵉ) → is-torsorial-Id'ᵉ _)) ∘eᵉ
    ( interchange-Σ-Σᵉ _)

  map-compute-direct-predecessor-fiber-Directed-Graphᵉ :
    (yᵉ : node-fiber-Directed-Graphᵉ Gᵉ xᵉ) →
    direct-predecessor-fiber-Directed-Graphᵉ yᵉ →
    direct-predecessor-Directed-Graphᵉ Gᵉ
      ( node-inclusion-fiber-Directed-Graphᵉ Gᵉ xᵉ yᵉ)
  map-compute-direct-predecessor-fiber-Directed-Graphᵉ yᵉ =
    map-equivᵉ (compute-direct-predecessor-fiber-Directed-Graphᵉ yᵉ)

  htpy-compute-direct-predecessor-fiber-Directed-Graphᵉ :
    (yᵉ : node-fiber-Directed-Graphᵉ Gᵉ xᵉ) →
    direct-predecessor-inclusion-fiber-Directed-Graphᵉ yᵉ ~ᵉ
    map-compute-direct-predecessor-fiber-Directed-Graphᵉ yᵉ
  htpy-compute-direct-predecessor-fiber-Directed-Graphᵉ yᵉ tᵉ = reflᵉ

  inv-compute-direct-predecessor-fiber-Directed-Graphᵉ :
    (yᵉ : node-fiber-Directed-Graphᵉ Gᵉ xᵉ) →
    direct-predecessor-Directed-Graphᵉ Gᵉ
      ( node-inclusion-fiber-Directed-Graphᵉ Gᵉ xᵉ yᵉ) ≃ᵉ
    direct-predecessor-fiber-Directed-Graphᵉ yᵉ
  inv-compute-direct-predecessor-fiber-Directed-Graphᵉ yᵉ =
    inv-equivᵉ (compute-direct-predecessor-fiber-Directed-Graphᵉ yᵉ)

  Eq-direct-predecessor-fiber-Directed-Graphᵉ :
    (yᵉ : node-fiber-Directed-Graphᵉ Gᵉ xᵉ) →
    (uᵉ vᵉ : direct-predecessor-fiber-Directed-Graphᵉ yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  Eq-direct-predecessor-fiber-Directed-Graphᵉ yᵉ uᵉ vᵉ =
    Σᵉ ( pr1ᵉ (direct-predecessor-inclusion-fiber-Directed-Graphᵉ yᵉ uᵉ) ＝ᵉ
        pr1ᵉ (direct-predecessor-inclusion-fiber-Directed-Graphᵉ yᵉ vᵉ))
      ( λ pᵉ →
        trᵉ
          ( λ tᵉ →
            edge-Directed-Graphᵉ Gᵉ tᵉ (node-inclusion-fiber-Directed-Graphᵉ Gᵉ xᵉ yᵉ))
          ( pᵉ)
          ( pr2ᵉ (direct-predecessor-inclusion-fiber-Directed-Graphᵉ yᵉ uᵉ)) ＝ᵉ
            pr2ᵉ (direct-predecessor-inclusion-fiber-Directed-Graphᵉ yᵉ vᵉ))

  eq-Eq-direct-predecessor-fiber-Directed-Graphᵉ :
    (yᵉ : node-fiber-Directed-Graphᵉ Gᵉ xᵉ) →
    ( uᵉ vᵉ : direct-predecessor-fiber-Directed-Graphᵉ yᵉ) →
    Eq-direct-predecessor-fiber-Directed-Graphᵉ yᵉ uᵉ vᵉ → uᵉ ＝ᵉ vᵉ
  eq-Eq-direct-predecessor-fiber-Directed-Graphᵉ yᵉ uᵉ vᵉ pᵉ =
    map-inv-equivᵉ
      ( equiv-apᵉ (compute-direct-predecessor-fiber-Directed-Graphᵉ yᵉ) uᵉ vᵉ)
      ( eq-pair-Σ'ᵉ pᵉ)
```