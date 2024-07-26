# Dependent descent for the circle

```agda
module synthetic-homotopy-theory.dependent-descent-circleᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import structured-types.dependent-types-equipped-with-automorphismsᵉ

open import synthetic-homotopy-theory.descent-circleᵉ
open import synthetic-homotopy-theory.free-loopsᵉ
```

</details>

## Idea

Theᵉ **dependentᵉ descentᵉ propertyᵉ ofᵉ theᵉ circle**ᵉ assertsᵉ thatᵉ aᵉ familyᵉ overᵉ aᵉ
familyᵉ `P`ᵉ overᵉ theᵉ [circle](synthetic-homotopy-theory.circle.mdᵉ) isᵉ
[equivalently](foundation-core.equivalences.mdᵉ) describedᵉ byᵉ **dependentᵉ descentᵉ
data**ᵉ overᵉ theᵉ [descentᵉ data](synthetic-homotopy-theory.descent-circle.mdᵉ) ofᵉ
`P`,ᵉ whichᵉ isᵉ definedᵉ asᵉ aᵉ
[dependentᵉ typeᵉ with anᵉ automorphism](structured-types.dependent-types-equipped-with-automorphisms.md).ᵉ
Moreᵉ precisely,ᵉ dependentᵉ descentᵉ data overᵉ descentᵉ data `(X,e)`ᵉ forᵉ theᵉ circleᵉ
consistsᵉ ofᵉ aᵉ typeᵉ familyᵉ `Rᵉ : Xᵉ → U`ᵉ equippedᵉ with aᵉ familyᵉ ofᵉ equivalencesᵉ
`kᵉ : (xᵉ : Xᵉ) → R(xᵉ) ≃ᵉ R(e(x))`ᵉ _overᵉ_ `e`.ᵉ

## Definitions

### Dependent descent data for the circle

```agda
dependent-descent-data-circleᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) →
  descent-data-circleᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
dependent-descent-data-circleᵉ l2ᵉ Pᵉ =
  Dependent-Type-With-Automorphismᵉ l2ᵉ Pᵉ

module _
  { l1ᵉ l2ᵉ : Level} (Pᵉ : descent-data-circleᵉ l1ᵉ)
  ( Qᵉ : dependent-descent-data-circleᵉ l2ᵉ Pᵉ)
  where

  type-dependent-descent-data-circleᵉ : type-descent-data-circleᵉ Pᵉ → UUᵉ l2ᵉ
  type-dependent-descent-data-circleᵉ =
    family-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ

  dependent-automorphism-dependent-descent-data-circleᵉ :
    equiv-famᵉ
      ( type-dependent-descent-data-circleᵉ)
      ( type-dependent-descent-data-circleᵉ ∘ᵉ (map-descent-data-circleᵉ Pᵉ))
  dependent-automorphism-dependent-descent-data-circleᵉ =
    dependent-automorphism-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ

  map-dependent-descent-data-circleᵉ :
    { xᵉ : type-descent-data-circleᵉ Pᵉ} →
    ( type-dependent-descent-data-circleᵉ xᵉ) →
    ( type-dependent-descent-data-circleᵉ (map-descent-data-circleᵉ Pᵉ xᵉ))
  map-dependent-descent-data-circleᵉ =
    map-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ
```

### Canonical dependent descent data for a family over a family over the circle

```agda
dependent-descent-data-double-family-circleᵉ :
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ) →
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ) →
  ( (xᵉ : Sᵉ) → (family-family-with-descent-data-circleᵉ Aᵉ xᵉ) → UUᵉ l3ᵉ) →
  dependent-descent-data-circleᵉ l3ᵉ
    ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
pr1ᵉ (dependent-descent-data-double-family-circleᵉ lᵉ Aᵉ Bᵉ) xᵉ =
  Bᵉ (base-free-loopᵉ lᵉ) (map-equiv-family-with-descent-data-circleᵉ Aᵉ xᵉ)
pr2ᵉ (dependent-descent-data-double-family-circleᵉ lᵉ Aᵉ Bᵉ) xᵉ =
  equiv-trᵉ
    ( ind-Σᵉ Bᵉ)
    ( eq-pair-Σᵉ
      ( loop-free-loopᵉ lᵉ)
      ( invᵉ (coherence-square-family-with-descent-data-circleᵉ Aᵉ xᵉ)))
```

### The identity type of dependent descent data for the circle

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : descent-data-circleᵉ l1ᵉ)
  where

  equiv-dependent-descent-data-circleᵉ :
    dependent-descent-data-circleᵉ l2ᵉ Pᵉ → dependent-descent-data-circleᵉ l3ᵉ Pᵉ →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  equiv-dependent-descent-data-circleᵉ =
    equiv-Dependent-Type-With-Automorphismᵉ Pᵉ

module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : descent-data-circleᵉ l1ᵉ)
  ( Qᵉ : dependent-descent-data-circleᵉ l2ᵉ Pᵉ)
  ( Tᵉ : dependent-descent-data-circleᵉ l3ᵉ Pᵉ)
  ( αᵉ : equiv-dependent-descent-data-circleᵉ Pᵉ Qᵉ Tᵉ)
  where

  equiv-equiv-dependent-descent-data-circleᵉ :
    equiv-famᵉ
      ( type-dependent-descent-data-circleᵉ Pᵉ Qᵉ)
      ( type-dependent-descent-data-circleᵉ Pᵉ Tᵉ)
  equiv-equiv-dependent-descent-data-circleᵉ =
    equiv-equiv-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ Tᵉ αᵉ

  map-equiv-dependent-descent-data-circleᵉ :
    { xᵉ : type-descent-data-circleᵉ Pᵉ} →
    ( type-dependent-descent-data-circleᵉ Pᵉ Qᵉ xᵉ) →
    ( type-dependent-descent-data-circleᵉ Pᵉ Tᵉ xᵉ)
  map-equiv-dependent-descent-data-circleᵉ =
    map-equiv-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ Tᵉ αᵉ

  coherence-square-equiv-dependent-descent-data-circleᵉ :
    ( xᵉ : type-descent-data-circleᵉ Pᵉ) →
    coherence-square-mapsᵉ
      ( map-equiv-dependent-descent-data-circleᵉ)
      ( map-dependent-descent-data-circleᵉ Pᵉ Qᵉ)
      ( map-dependent-descent-data-circleᵉ Pᵉ Tᵉ)
      ( map-equiv-dependent-descent-data-circleᵉ)
  coherence-square-equiv-dependent-descent-data-circleᵉ =
    coherence-square-equiv-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ Tᵉ αᵉ
```

### A dependent family over the circle with corresponding dependent descent data

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  where

  double-family-for-dependent-descent-data-circleᵉ :
    { l3ᵉ : Level} →
    dependent-descent-data-circleᵉ l3ᵉ
      ( descent-data-family-with-descent-data-circleᵉ Aᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  double-family-for-dependent-descent-data-circleᵉ {l3ᵉ} Qᵉ =
    Σᵉ ( (xᵉ : Sᵉ) → (family-family-with-descent-data-circleᵉ Aᵉ xᵉ) → UUᵉ l3ᵉ)
      ( λ Bᵉ →
        equiv-dependent-descent-data-circleᵉ
          ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
          ( Qᵉ)
          ( dependent-descent-data-double-family-circleᵉ lᵉ Aᵉ Bᵉ))

  dependent-descent-data-circle-for-double-familyᵉ :
    { l3ᵉ : Level} →
    ( (xᵉ : Sᵉ) → (family-family-with-descent-data-circleᵉ Aᵉ xᵉ) → UUᵉ l3ᵉ) →
    UUᵉ (l2ᵉ ⊔ lsuc l3ᵉ)
  dependent-descent-data-circle-for-double-familyᵉ {l3ᵉ} Bᵉ =
    Σᵉ ( dependent-descent-data-circleᵉ l3ᵉ
        ( descent-data-family-with-descent-data-circleᵉ Aᵉ))
      ( λ Qᵉ →
        equiv-dependent-descent-data-circleᵉ
          ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
          ( Qᵉ)
          ( dependent-descent-data-double-family-circleᵉ lᵉ Aᵉ Bᵉ))

  double-family-with-dependent-descent-data-circleᵉ :
    ( l3ᵉ : Level) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  double-family-with-dependent-descent-data-circleᵉ l3ᵉ =
    Σᵉ ( (xᵉ : Sᵉ) → (family-family-with-descent-data-circleᵉ Aᵉ xᵉ) → UUᵉ l3ᵉ)
      dependent-descent-data-circle-for-double-familyᵉ

module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {lᵉ : free-loopᵉ Sᵉ}
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  ( Bᵉ : double-family-with-dependent-descent-data-circleᵉ lᵉ Aᵉ l3ᵉ)
  where

  double-family-double-family-with-dependent-descent-data-circleᵉ :
    ( xᵉ : Sᵉ) → (family-family-with-descent-data-circleᵉ Aᵉ xᵉ) → UUᵉ l3ᵉ
  double-family-double-family-with-dependent-descent-data-circleᵉ = pr1ᵉ Bᵉ

  dependent-descent-data-for-double-family-with-dependent-descent-data-circleᵉ :
    dependent-descent-data-circle-for-double-familyᵉ lᵉ Aᵉ
      double-family-double-family-with-dependent-descent-data-circleᵉ
  dependent-descent-data-for-double-family-with-dependent-descent-data-circleᵉ =
    pr2ᵉ Bᵉ

  dependent-descent-data-double-family-with-dependent-descent-data-circleᵉ :
    dependent-descent-data-circleᵉ l3ᵉ
      ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
  dependent-descent-data-double-family-with-dependent-descent-data-circleᵉ =
    pr1ᵉ
      dependent-descent-data-for-double-family-with-dependent-descent-data-circleᵉ

  type-double-family-with-dependent-descent-data-circleᵉ :
    type-family-with-descent-data-circleᵉ Aᵉ → UUᵉ l3ᵉ
  type-double-family-with-dependent-descent-data-circleᵉ =
    type-dependent-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
      ( dependent-descent-data-double-family-with-dependent-descent-data-circleᵉ)

  dependent-automorphism-double-family-with-dependent-descent-data-circleᵉ :
    equiv-famᵉ
    ( type-double-family-with-dependent-descent-data-circleᵉ)
    ( type-double-family-with-dependent-descent-data-circleᵉ ∘ᵉ
      ( map-aut-family-with-descent-data-circleᵉ Aᵉ))
  dependent-automorphism-double-family-with-dependent-descent-data-circleᵉ =
    dependent-automorphism-dependent-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
      ( dependent-descent-data-double-family-with-dependent-descent-data-circleᵉ)

  map-dependent-automorphism-double-family-with-dependent-descent-data-circleᵉ :
    { xᵉ : type-family-with-descent-data-circleᵉ Aᵉ} →
    ( type-double-family-with-dependent-descent-data-circleᵉ xᵉ) →
    ( type-double-family-with-dependent-descent-data-circleᵉ
      ( map-aut-family-with-descent-data-circleᵉ Aᵉ xᵉ))
  map-dependent-automorphism-double-family-with-dependent-descent-data-circleᵉ =
    map-dependent-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
      ( dependent-descent-data-double-family-with-dependent-descent-data-circleᵉ)

  eq-double-family-with-dependent-descent-data-circleᵉ :
    equiv-dependent-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
      ( dependent-descent-data-double-family-with-dependent-descent-data-circleᵉ)
      ( dependent-descent-data-double-family-circleᵉ lᵉ Aᵉ
        ( double-family-double-family-with-dependent-descent-data-circleᵉ))
  eq-double-family-with-dependent-descent-data-circleᵉ =
    pr2ᵉ
      dependent-descent-data-for-double-family-with-dependent-descent-data-circleᵉ

  equiv-double-family-with-dependent-descent-data-circleᵉ :
    ( xᵉ : type-family-with-descent-data-circleᵉ Aᵉ) →
    ( type-double-family-with-dependent-descent-data-circleᵉ xᵉ) ≃ᵉ
    ( double-family-double-family-with-dependent-descent-data-circleᵉ
      ( base-free-loopᵉ lᵉ)
      ( map-equiv-family-with-descent-data-circleᵉ Aᵉ xᵉ))
  equiv-double-family-with-dependent-descent-data-circleᵉ =
    equiv-equiv-dependent-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
      ( dependent-descent-data-double-family-with-dependent-descent-data-circleᵉ)
      ( dependent-descent-data-double-family-circleᵉ lᵉ Aᵉ
        ( double-family-double-family-with-dependent-descent-data-circleᵉ))
      ( eq-double-family-with-dependent-descent-data-circleᵉ)

  map-equiv-double-family-with-dependent-descent-data-circleᵉ :
    ( xᵉ : type-family-with-descent-data-circleᵉ Aᵉ) →
    ( type-double-family-with-dependent-descent-data-circleᵉ xᵉ) →
    ( double-family-double-family-with-dependent-descent-data-circleᵉ
      ( base-free-loopᵉ lᵉ)
      ( map-equiv-family-with-descent-data-circleᵉ Aᵉ xᵉ))
  map-equiv-double-family-with-dependent-descent-data-circleᵉ xᵉ =
    map-equivᵉ (equiv-double-family-with-dependent-descent-data-circleᵉ xᵉ)

  coherence-square-double-family-with-dependent-descent-data-circleᵉ :
    ( xᵉ : type-family-with-descent-data-circleᵉ Aᵉ) →
    coherence-square-mapsᵉ
      ( map-equiv-double-family-with-dependent-descent-data-circleᵉ xᵉ)
      ( map-dependent-automorphism-double-family-with-dependent-descent-data-circleᵉ)
      ( trᵉ
        ( ind-Σᵉ
          ( double-family-double-family-with-dependent-descent-data-circleᵉ))
        ( eq-pair-Σᵉ
          ( loop-free-loopᵉ lᵉ)
          ( invᵉ (coherence-square-family-with-descent-data-circleᵉ Aᵉ xᵉ))))
      ( map-equiv-double-family-with-dependent-descent-data-circleᵉ
        ( map-aut-family-with-descent-data-circleᵉ Aᵉ xᵉ))
  coherence-square-double-family-with-dependent-descent-data-circleᵉ =
    coherence-square-equiv-dependent-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
      ( dependent-descent-data-double-family-with-dependent-descent-data-circleᵉ)
      ( dependent-descent-data-double-family-circleᵉ lᵉ Aᵉ
        ( double-family-double-family-with-dependent-descent-data-circleᵉ))
      ( eq-double-family-with-dependent-descent-data-circleᵉ)

  double-family-for-double-family-with-dependent-descent-data-circleᵉ :
    double-family-for-dependent-descent-data-circleᵉ lᵉ Aᵉ
      dependent-descent-data-double-family-with-dependent-descent-data-circleᵉ
  pr1ᵉ double-family-for-double-family-with-dependent-descent-data-circleᵉ =
    double-family-double-family-with-dependent-descent-data-circleᵉ
  pr2ᵉ double-family-for-double-family-with-dependent-descent-data-circleᵉ =
    eq-double-family-with-dependent-descent-data-circleᵉ
```

## Properties

### Characterization of the identity type of dependent descent data for the circle

```agda
module _
  { l1ᵉ l2ᵉ : Level} (Pᵉ : descent-data-circleᵉ l1ᵉ)
  where

  id-equiv-dependent-descent-data-circleᵉ :
    ( Qᵉ : dependent-descent-data-circleᵉ l2ᵉ Pᵉ) →
    equiv-dependent-descent-data-circleᵉ Pᵉ Qᵉ Qᵉ
  id-equiv-dependent-descent-data-circleᵉ =
    id-equiv-Dependent-Type-With-Automorphismᵉ Pᵉ

  equiv-eq-dependent-descent-data-circleᵉ :
    ( Qᵉ Tᵉ : dependent-descent-data-circleᵉ l2ᵉ Pᵉ) →
    Qᵉ ＝ᵉ Tᵉ → equiv-dependent-descent-data-circleᵉ Pᵉ Qᵉ Tᵉ
  equiv-eq-dependent-descent-data-circleᵉ =
    equiv-eq-Dependent-Type-With-Automorphismᵉ Pᵉ

  is-torsorial-equiv-dependent-descent-data-circleᵉ :
    ( Qᵉ : dependent-descent-data-circleᵉ l2ᵉ Pᵉ) →
    is-torsorialᵉ (equiv-dependent-descent-data-circleᵉ Pᵉ Qᵉ)
  is-torsorial-equiv-dependent-descent-data-circleᵉ =
    is-torsorial-equiv-Dependent-Type-With-Automorphismᵉ Pᵉ

  is-equiv-equiv-eq-dependent-descent-data-circleᵉ :
    ( Qᵉ Tᵉ : dependent-descent-data-circleᵉ l2ᵉ Pᵉ) →
    is-equivᵉ (equiv-eq-dependent-descent-data-circleᵉ Qᵉ Tᵉ)
  is-equiv-equiv-eq-dependent-descent-data-circleᵉ =
    is-equiv-equiv-eq-Dependent-Type-With-Automorphismᵉ Pᵉ

  extensionality-dependent-descent-data-circleᵉ :
    ( Qᵉ Tᵉ : dependent-descent-data-circleᵉ l2ᵉ Pᵉ) →
    (Qᵉ ＝ᵉ Tᵉ) ≃ᵉ equiv-dependent-descent-data-circleᵉ Pᵉ Qᵉ Tᵉ
  extensionality-dependent-descent-data-circleᵉ =
    extensionality-Dependent-Type-With-Automorphismᵉ Pᵉ

  eq-equiv-dependent-descent-data-circleᵉ :
    ( Qᵉ Tᵉ : dependent-descent-data-circleᵉ l2ᵉ Pᵉ) →
    equiv-dependent-descent-data-circleᵉ Pᵉ Qᵉ Tᵉ → Qᵉ ＝ᵉ Tᵉ
  eq-equiv-dependent-descent-data-circleᵉ =
    eq-equiv-Dependent-Type-With-Automorphismᵉ Pᵉ
```

### Uniqueness of dependent descent data characterizing a type family over a family over the circle

Givenᵉ aᵉ typeᵉ familyᵉ `Aᵉ : 𝕊¹ᵉ → U`ᵉ with correspondingᵉ descentᵉ data `(X,ᵉ e)`,ᵉ andᵉ aᵉ
typeᵉ familyᵉ `Rᵉ : Xᵉ → U`ᵉ overᵉ `X`ᵉ invariantᵉ underᵉ `e`ᵉ asᵉ witnessedᵉ byᵉ `k`,ᵉ thereᵉ
isᵉ aᵉ uniqueᵉ familyᵉ `Bᵉ : (tᵉ : 𝕊¹ᵉ) → Aᵉ tᵉ → U`ᵉ forᵉ whichᵉ `(R,ᵉ k)`ᵉ isᵉ dependentᵉ
descentᵉ data overᵉ `A`.ᵉ

Thisᵉ isᵉ soᵉ farᵉ aᵉ conjectureᵉ whichᵉ remainsᵉ to beᵉ shown.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  where

  unique-dependent-family-property-circleᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  unique-dependent-family-property-circleᵉ =
    ( Qᵉ :
      dependent-descent-data-circleᵉ l3ᵉ
        ( descent-data-family-with-descent-data-circleᵉ Aᵉ)) →
    is-contrᵉ (double-family-for-dependent-descent-data-circleᵉ lᵉ Aᵉ Qᵉ)
```