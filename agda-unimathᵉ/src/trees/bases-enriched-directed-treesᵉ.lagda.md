# Bases of enriched directed trees

```agda
module trees.bases-enriched-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.universe-levelsᵉ

open import trees.bases-directed-treesᵉ
open import trees.enriched-directed-treesᵉ
```

</details>

## Idea

Theᵉ **base**ᵉ ofᵉ anᵉ enrichedᵉ directedᵉ treeᵉ consistsᵉ ofᵉ itsᵉ nodesᵉ equippedᵉ with anᵉ
edgeᵉ to theᵉ root.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  where

  base-Enriched-Directed-Treeᵉ : UUᵉ l2ᵉ
  base-Enriched-Directed-Treeᵉ = Bᵉ (shape-root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)

  compute-base-Enriched-Directed-Treeᵉ :
    base-Enriched-Directed-Treeᵉ ≃ᵉ
    direct-predecessor-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
  compute-base-Enriched-Directed-Treeᵉ =
    enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ (root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)

  map-compute-base-Enriched-Directed-Treeᵉ :
    base-Enriched-Directed-Treeᵉ →
    direct-predecessor-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
  map-compute-base-Enriched-Directed-Treeᵉ =
    map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)

  module _
    (bᵉ : base-Enriched-Directed-Treeᵉ)
    where

    node-base-Enriched-Directed-Treeᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
    node-base-Enriched-Directed-Treeᵉ =
      node-base-Directed-Treeᵉ
        ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
        ( map-compute-base-Enriched-Directed-Treeᵉ bᵉ)

    edge-base-Enriched-Directed-Treeᵉ :
      edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
        ( node-base-Enriched-Directed-Treeᵉ)
        ( root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
    edge-base-Enriched-Directed-Treeᵉ =
      edge-base-Directed-Treeᵉ
        ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
        ( map-compute-base-Enriched-Directed-Treeᵉ bᵉ)
```

## Properties

### The root is not a base element

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  where

  is-proper-node-base-Enriched-Directed-Treeᵉ :
    (bᵉ : base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) →
    is-proper-node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ)
  is-proper-node-base-Enriched-Directed-Treeᵉ bᵉ =
    is-proper-node-base-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( map-compute-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ)

  no-walk-to-base-root-Enriched-Directed-Treeᵉ :
    (bᵉ : base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) →
    ¬ᵉ ( walk-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
        ( root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
        ( node-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ))
  no-walk-to-base-root-Enriched-Directed-Treeᵉ bᵉ =
    no-walk-to-base-root-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( map-compute-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ)
```

### There are no edges between base elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  where

  no-edge-base-Enriched-Directed-Treeᵉ :
    (aᵉ bᵉ : base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) →
    ¬ᵉ ( edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
        ( node-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ aᵉ)
        ( node-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ))
  no-edge-base-Enriched-Directed-Treeᵉ aᵉ bᵉ =
    no-edge-base-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( map-compute-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ aᵉ)
      ( map-compute-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ)
```

### For any node `x`, the coproduct of `is-root x` and the type of base elements `b` equipped with a walk from `x` to `b` is contractible

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  where

  unique-walk-to-base-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) →
    is-contrᵉ
      ( is-root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ +ᵉ
        Σᵉ ( base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
          ( walk-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ ∘ᵉ
            node-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ))
  unique-walk-to-base-Enriched-Directed-Treeᵉ xᵉ =
    is-contr-equivᵉ
      ( is-root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ +ᵉ
        Σᵉ ( direct-predecessor-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
            ( root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ))
          ( walk-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ ∘ᵉ pr1ᵉ))
      ( equiv-coproductᵉ
        ( id-equivᵉ)
        ( equiv-Σᵉ
          ( walk-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ ∘ᵉ pr1ᵉ)
          ( compute-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
          ( λ bᵉ → id-equivᵉ)))
      ( unique-walk-to-base-Directed-Treeᵉ
        ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
        ( xᵉ))

  is-root-or-walk-to-base-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) →
    is-root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ +ᵉ
    Σᵉ ( base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( walk-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ ∘ᵉ
        node-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
  is-root-or-walk-to-base-Enriched-Directed-Treeᵉ xᵉ =
    centerᵉ (unique-walk-to-base-Enriched-Directed-Treeᵉ xᵉ)

  is-root-is-root-or-walk-to-base-root-Enriched-Directed-Treeᵉ :
    is-root-or-walk-to-base-Enriched-Directed-Treeᵉ
      ( root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) ＝ᵉ
    inlᵉ reflᵉ
  is-root-is-root-or-walk-to-base-root-Enriched-Directed-Treeᵉ =
    eq-is-contrᵉ
      ( unique-walk-to-base-Enriched-Directed-Treeᵉ
        ( root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ))

  unique-walk-to-base-is-not-root-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) →
    ¬ᵉ (is-root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ) →
    is-contrᵉ
      ( Σᵉ ( base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
          ( walk-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ ∘ᵉ
            node-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ))
  unique-walk-to-base-is-not-root-Enriched-Directed-Treeᵉ xᵉ fᵉ =
    is-contr-equiv'ᵉ
      ( is-root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ +ᵉ
        Σᵉ ( base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
          ( walk-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ ∘ᵉ
            node-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ))
      ( left-unit-law-coproduct-is-emptyᵉ
        ( is-root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ)
        ( Σᵉ ( base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
            ( walk-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ ∘ᵉ
              node-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ))
        ( fᵉ))
      ( unique-walk-to-base-Enriched-Directed-Treeᵉ xᵉ)

  unique-walk-to-base-direct-successor-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
    (uᵉ :
      Σᵉ ( node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
        ( edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ)) →
    is-contrᵉ
      ( Σᵉ ( base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
          ( walk-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ ∘ᵉ
            node-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ))
  unique-walk-to-base-direct-successor-Enriched-Directed-Treeᵉ xᵉ (yᵉ ,ᵉ eᵉ) =
    unique-walk-to-base-is-not-root-Enriched-Directed-Treeᵉ xᵉ
      ( is-proper-node-direct-successor-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ eᵉ)
```