# Rooted morphisms of directed trees

```agda
module trees.rooted-morphisms-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-transportᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import trees.bases-directed-treesᵉ
open import trees.directed-treesᵉ
open import trees.morphisms-directed-treesᵉ
```

</details>

## Idea

Aᵉ **rootedᵉ morphism**ᵉ ofᵉ directedᵉ treesᵉ fromᵉ `S`ᵉ to `T`ᵉ isᵉ aᵉ morphismᵉ ofᵉ
directedᵉ treesᵉ thatᵉ mapsᵉ theᵉ rootᵉ ofᵉ `S`ᵉ to theᵉ rootᵉ ofᵉ `T`ᵉ

## Definition

### Rooted morphisms of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  where

  preserves-root-hom-directed-tree-Propᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ → Propᵉ l3ᵉ
  preserves-root-hom-directed-tree-Propᵉ fᵉ =
    is-root-directed-tree-Propᵉ Tᵉ
      ( node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ (root-Directed-Treeᵉ Sᵉ))

  preserves-root-hom-Directed-Treeᵉ :
    hom-Directed-Treeᵉ Sᵉ Tᵉ → UUᵉ l3ᵉ
  preserves-root-hom-Directed-Treeᵉ fᵉ =
    type-Propᵉ (preserves-root-hom-directed-tree-Propᵉ fᵉ)

  is-prop-preserves-root-hom-Directed-Treeᵉ :
    (fᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ) → is-propᵉ (preserves-root-hom-Directed-Treeᵉ fᵉ)
  is-prop-preserves-root-hom-Directed-Treeᵉ fᵉ =
    is-prop-type-Propᵉ (preserves-root-hom-directed-tree-Propᵉ fᵉ)

  rooted-hom-Directed-Treeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  rooted-hom-Directed-Treeᵉ =
    Σᵉ (hom-Directed-Treeᵉ Sᵉ Tᵉ) preserves-root-hom-Directed-Treeᵉ

  module _
    (fᵉ : rooted-hom-Directed-Treeᵉ)
    where

    hom-rooted-hom-Directed-Treeᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ
    hom-rooted-hom-Directed-Treeᵉ = pr1ᵉ fᵉ

    node-rooted-hom-Directed-Treeᵉ :
      node-Directed-Treeᵉ Sᵉ → node-Directed-Treeᵉ Tᵉ
    node-rooted-hom-Directed-Treeᵉ =
      node-hom-Directed-Treeᵉ Sᵉ Tᵉ hom-rooted-hom-Directed-Treeᵉ

    edge-rooted-hom-Directed-Treeᵉ :
      {xᵉ yᵉ : node-Directed-Treeᵉ Sᵉ} →
      edge-Directed-Treeᵉ Sᵉ xᵉ yᵉ →
      edge-Directed-Treeᵉ Tᵉ
        ( node-rooted-hom-Directed-Treeᵉ xᵉ)
        ( node-rooted-hom-Directed-Treeᵉ yᵉ)
    edge-rooted-hom-Directed-Treeᵉ =
      edge-hom-Directed-Treeᵉ Sᵉ Tᵉ hom-rooted-hom-Directed-Treeᵉ

    walk-rooted-hom-Directed-Treeᵉ :
      {xᵉ yᵉ : node-Directed-Treeᵉ Sᵉ} →
      walk-Directed-Treeᵉ Sᵉ xᵉ yᵉ →
      walk-Directed-Treeᵉ Tᵉ
        ( node-rooted-hom-Directed-Treeᵉ xᵉ)
        ( node-rooted-hom-Directed-Treeᵉ yᵉ)
    walk-rooted-hom-Directed-Treeᵉ =
      walk-hom-Directed-Treeᵉ Sᵉ Tᵉ hom-rooted-hom-Directed-Treeᵉ

    direct-predecessor-rooted-hom-Directed-Treeᵉ :
      (xᵉ : node-Directed-Treeᵉ Sᵉ) →
      direct-predecessor-Directed-Treeᵉ Sᵉ xᵉ →
      direct-predecessor-Directed-Treeᵉ Tᵉ (node-rooted-hom-Directed-Treeᵉ xᵉ)
    direct-predecessor-rooted-hom-Directed-Treeᵉ =
      direct-predecessor-hom-Directed-Treeᵉ Sᵉ Tᵉ hom-rooted-hom-Directed-Treeᵉ

    preserves-root-rooted-hom-Directed-Treeᵉ :
      preserves-root-hom-Directed-Treeᵉ hom-rooted-hom-Directed-Treeᵉ
    preserves-root-rooted-hom-Directed-Treeᵉ = pr2ᵉ fᵉ

    base-rooted-hom-Directed-Treeᵉ :
      base-Directed-Treeᵉ Sᵉ → base-Directed-Treeᵉ Tᵉ
    base-rooted-hom-Directed-Treeᵉ (xᵉ ,ᵉ eᵉ) =
      node-rooted-hom-Directed-Treeᵉ xᵉ ,ᵉ
      trᵉ
        ( edge-Directed-Treeᵉ Tᵉ (node-rooted-hom-Directed-Treeᵉ xᵉ))
        ( invᵉ preserves-root-rooted-hom-Directed-Treeᵉ)
        ( edge-rooted-hom-Directed-Treeᵉ eᵉ)
```

### The identity rooted morphism of directed trees

```agda
id-rooted-hom-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) → rooted-hom-Directed-Treeᵉ Tᵉ Tᵉ
pr1ᵉ (id-rooted-hom-Directed-Treeᵉ Tᵉ) = id-hom-Directed-Treeᵉ Tᵉ
pr2ᵉ (id-rooted-hom-Directed-Treeᵉ Tᵉ) = reflᵉ
```

### Composition of rooted morphisms of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Rᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Sᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ) (Tᵉ : Directed-Treeᵉ l5ᵉ l6ᵉ)
  (gᵉ : rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ)
  (fᵉ : rooted-hom-Directed-Treeᵉ Rᵉ Sᵉ)
  where

  hom-comp-rooted-hom-Directed-Treeᵉ :
    hom-Directed-Treeᵉ Rᵉ Tᵉ
  hom-comp-rooted-hom-Directed-Treeᵉ =
    comp-hom-Directed-Treeᵉ Rᵉ Sᵉ Tᵉ
      ( hom-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ gᵉ)
      ( hom-rooted-hom-Directed-Treeᵉ Rᵉ Sᵉ fᵉ)

  preserves-root-comp-rooted-hom-Directed-Treeᵉ :
    preserves-root-hom-Directed-Treeᵉ Rᵉ Tᵉ hom-comp-rooted-hom-Directed-Treeᵉ
  preserves-root-comp-rooted-hom-Directed-Treeᵉ =
    ( preserves-root-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ gᵉ) ∙ᵉ
    ( apᵉ
      ( node-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ gᵉ)
      ( preserves-root-rooted-hom-Directed-Treeᵉ Rᵉ Sᵉ fᵉ))

  comp-rooted-hom-Directed-Treeᵉ :
    rooted-hom-Directed-Treeᵉ Rᵉ Tᵉ
  pr1ᵉ comp-rooted-hom-Directed-Treeᵉ = hom-comp-rooted-hom-Directed-Treeᵉ
  pr2ᵉ comp-rooted-hom-Directed-Treeᵉ =
    preserves-root-comp-rooted-hom-Directed-Treeᵉ
```

### Homotopies of rooted morphisms of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  where

  htpy-rooted-hom-Directed-Treeᵉ :
    (fᵉ gᵉ : rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-rooted-hom-Directed-Treeᵉ fᵉ gᵉ =
    htpy-hom-Directed-Treeᵉ Sᵉ Tᵉ
      ( hom-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
      ( hom-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ gᵉ)

  refl-htpy-rooted-hom-Directed-Treeᵉ :
    (fᵉ : rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ) →
    htpy-rooted-hom-Directed-Treeᵉ fᵉ fᵉ
  refl-htpy-rooted-hom-Directed-Treeᵉ fᵉ =
    refl-htpy-hom-Directed-Treeᵉ Sᵉ Tᵉ (hom-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)

  module _
    (fᵉ gᵉ : rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ)
    (Hᵉ : htpy-rooted-hom-Directed-Treeᵉ fᵉ gᵉ)
    where

    node-htpy-rooted-hom-Directed-Treeᵉ :
      node-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ ~ᵉ node-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ gᵉ
    node-htpy-rooted-hom-Directed-Treeᵉ =
      node-htpy-hom-Directed-Treeᵉ Sᵉ Tᵉ
        ( hom-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
        ( hom-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ gᵉ)
        ( Hᵉ)

    edge-htpy-rooted-hom-Directed-Treeᵉ :
      ( xᵉ yᵉ : node-Directed-Treeᵉ Sᵉ) (eᵉ : edge-Directed-Treeᵉ Sᵉ xᵉ yᵉ) →
      binary-trᵉ
        ( edge-Directed-Treeᵉ Tᵉ)
        ( node-htpy-rooted-hom-Directed-Treeᵉ xᵉ)
        ( node-htpy-rooted-hom-Directed-Treeᵉ yᵉ)
        ( edge-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ eᵉ) ＝ᵉ
      edge-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ gᵉ eᵉ
    edge-htpy-rooted-hom-Directed-Treeᵉ =
      edge-htpy-hom-Directed-Treeᵉ Sᵉ Tᵉ
        ( hom-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
        ( hom-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ gᵉ)
        ( Hᵉ)

    direct-predecessor-htpy-rooted-hom-Directed-Treeᵉ :
      ( xᵉ : node-Directed-Treeᵉ Sᵉ) →
      ( ( totᵉ
          ( λ yᵉ →
            trᵉ
              ( edge-Directed-Treeᵉ Tᵉ yᵉ)
              ( node-htpy-rooted-hom-Directed-Treeᵉ xᵉ))) ∘ᵉ
        ( direct-predecessor-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ)) ~ᵉ
      ( direct-predecessor-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ gᵉ xᵉ)
    direct-predecessor-htpy-rooted-hom-Directed-Treeᵉ =
      direct-predecessor-htpy-hom-Directed-Treeᵉ Sᵉ Tᵉ
        ( hom-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
        ( hom-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ gᵉ)
        ( Hᵉ)
```

## Properties

### Homotopies of rooted morphisms characterize identifications of rooted morphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  (fᵉ : rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ)
  where

  extensionality-rooted-hom-Directed-Treeᵉ :
    (gᵉ : rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ gᵉ
  extensionality-rooted-hom-Directed-Treeᵉ =
    extensionality-type-subtypeᵉ
      ( preserves-root-hom-directed-tree-Propᵉ Sᵉ Tᵉ)
      ( preserves-root-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
      ( refl-htpy-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
      ( extensionality-hom-Directed-Treeᵉ Sᵉ Tᵉ
        ( hom-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ))

  htpy-eq-rooted-hom-Directed-Treeᵉ :
    (gᵉ : rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ) →
    (fᵉ ＝ᵉ gᵉ) → htpy-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ gᵉ
  htpy-eq-rooted-hom-Directed-Treeᵉ gᵉ =
    map-equivᵉ (extensionality-rooted-hom-Directed-Treeᵉ gᵉ)

  eq-htpy-rooted-hom-Directed-Treeᵉ :
    (gᵉ : rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ) →
    htpy-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-rooted-hom-Directed-Treeᵉ gᵉ =
    map-inv-equivᵉ (extensionality-rooted-hom-Directed-Treeᵉ gᵉ)

  is-torsorial-htpy-rooted-hom-Directed-Treeᵉ :
    is-torsorialᵉ (htpy-rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
  is-torsorial-htpy-rooted-hom-Directed-Treeᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ) (λ gᵉ → fᵉ ＝ᵉ gᵉ))
      ( equiv-totᵉ extensionality-rooted-hom-Directed-Treeᵉ)
      ( is-torsorial-Idᵉ fᵉ)
```