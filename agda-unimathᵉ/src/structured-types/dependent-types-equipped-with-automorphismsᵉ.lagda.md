# Dependent types equipped with automorphisms

```agda
module structured-types.dependent-types-equipped-with-automorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import structured-types.types-equipped-with-automorphismsᵉ
```

</details>

## Idea

Considerᵉ aᵉ
[typeᵉ equippedᵉ with anᵉ automorphism](structured-types.types-equipped-with-automorphisms.mdᵉ)
`(X,e)`.ᵉ Aᵉ **dependentᵉ typeᵉ equippedᵉ with anᵉ automorphism**ᵉ overᵉ `(X,e)`ᵉ
consistsᵉ ofᵉ aᵉ dependentᵉ typeᵉ `Y`ᵉ overᵉ `X`ᵉ andᵉ forᵉ eachᵉ `xᵉ : X`ᵉ anᵉ
[equivalence](foundation-core.equivalences.mdᵉ) `Yᵉ xᵉ ≃ᵉ Yᵉ (eᵉ x)`.ᵉ

## Definitions

### Dependent types equipped with automorphisms

```agda
Dependent-Type-With-Automorphismᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) →
  Type-With-Automorphismᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Dependent-Type-With-Automorphismᵉ l2ᵉ Pᵉ =
  Σᵉ ( type-Type-With-Automorphismᵉ Pᵉ → UUᵉ l2ᵉ)
    ( λ Rᵉ → equiv-famᵉ Rᵉ (Rᵉ ∘ᵉ (map-Type-With-Automorphismᵉ Pᵉ)))

module _
  { l1ᵉ l2ᵉ : Level} (Pᵉ : Type-With-Automorphismᵉ l1ᵉ)
  ( Qᵉ : Dependent-Type-With-Automorphismᵉ l2ᵉ Pᵉ)
  where

  family-Dependent-Type-With-Automorphismᵉ :
    type-Type-With-Automorphismᵉ Pᵉ → UUᵉ l2ᵉ
  family-Dependent-Type-With-Automorphismᵉ =
    pr1ᵉ Qᵉ

  dependent-automorphism-Dependent-Type-With-Automorphismᵉ :
    equiv-famᵉ
      ( family-Dependent-Type-With-Automorphismᵉ)
      ( family-Dependent-Type-With-Automorphismᵉ ∘ᵉ map-Type-With-Automorphismᵉ Pᵉ)
  dependent-automorphism-Dependent-Type-With-Automorphismᵉ = pr2ᵉ Qᵉ

  map-Dependent-Type-With-Automorphismᵉ :
    { xᵉ : type-Type-With-Automorphismᵉ Pᵉ} →
    ( family-Dependent-Type-With-Automorphismᵉ xᵉ) →
    ( family-Dependent-Type-With-Automorphismᵉ (map-Type-With-Automorphismᵉ Pᵉ xᵉ))
  map-Dependent-Type-With-Automorphismᵉ {xᵉ} =
    map-equivᵉ (dependent-automorphism-Dependent-Type-With-Automorphismᵉ xᵉ)
```

### Equivalences of dependent types equipped with automorphisms

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Type-With-Automorphismᵉ l1ᵉ)
  where

  equiv-Dependent-Type-With-Automorphismᵉ :
    Dependent-Type-With-Automorphismᵉ l2ᵉ Pᵉ →
    Dependent-Type-With-Automorphismᵉ l3ᵉ Pᵉ →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  equiv-Dependent-Type-With-Automorphismᵉ Qᵉ Tᵉ =
    Σᵉ ( equiv-famᵉ
        ( family-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ)
        ( family-Dependent-Type-With-Automorphismᵉ Pᵉ Tᵉ))
      ( λ Hᵉ →
        ( xᵉ : type-Type-With-Automorphismᵉ Pᵉ) →
        coherence-square-mapsᵉ
          ( map-equivᵉ (Hᵉ xᵉ))
          ( map-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ)
          ( map-Dependent-Type-With-Automorphismᵉ Pᵉ Tᵉ)
          ( map-equivᵉ (Hᵉ (map-Type-With-Automorphismᵉ Pᵉ xᵉ))))

module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Type-With-Automorphismᵉ l1ᵉ)
  ( Qᵉ : Dependent-Type-With-Automorphismᵉ l2ᵉ Pᵉ)
  ( Tᵉ : Dependent-Type-With-Automorphismᵉ l3ᵉ Pᵉ)
  ( αᵉ : equiv-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ Tᵉ)
  where

  equiv-equiv-Dependent-Type-With-Automorphismᵉ :
    equiv-famᵉ
      ( family-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ)
      ( family-Dependent-Type-With-Automorphismᵉ Pᵉ Tᵉ)
  equiv-equiv-Dependent-Type-With-Automorphismᵉ = pr1ᵉ αᵉ

  map-equiv-Dependent-Type-With-Automorphismᵉ :
    { xᵉ : type-Type-With-Automorphismᵉ Pᵉ} →
    ( family-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ xᵉ) →
    ( family-Dependent-Type-With-Automorphismᵉ Pᵉ Tᵉ xᵉ)
  map-equiv-Dependent-Type-With-Automorphismᵉ {xᵉ} =
    map-equivᵉ (equiv-equiv-Dependent-Type-With-Automorphismᵉ xᵉ)

  coherence-square-equiv-Dependent-Type-With-Automorphismᵉ :
    ( xᵉ : type-Type-With-Automorphismᵉ Pᵉ) →
    coherence-square-mapsᵉ
      ( map-equiv-Dependent-Type-With-Automorphismᵉ)
      ( map-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ)
      ( map-Dependent-Type-With-Automorphismᵉ Pᵉ Tᵉ)
      ( map-equiv-Dependent-Type-With-Automorphismᵉ)
  coherence-square-equiv-Dependent-Type-With-Automorphismᵉ = pr2ᵉ αᵉ
```

## Properties

### Characterization of the identity type of dependent descent data for the circle

```agda
module _
  { l1ᵉ l2ᵉ : Level} (Pᵉ : Type-With-Automorphismᵉ l1ᵉ)
  where

  id-equiv-Dependent-Type-With-Automorphismᵉ :
    ( Qᵉ : Dependent-Type-With-Automorphismᵉ l2ᵉ Pᵉ) →
    equiv-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ Qᵉ
  pr1ᵉ (id-equiv-Dependent-Type-With-Automorphismᵉ Qᵉ) =
    id-equiv-famᵉ (family-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ)
  pr2ᵉ (id-equiv-Dependent-Type-With-Automorphismᵉ Qᵉ) xᵉ = refl-htpyᵉ

  equiv-eq-Dependent-Type-With-Automorphismᵉ :
    ( Qᵉ Tᵉ : Dependent-Type-With-Automorphismᵉ l2ᵉ Pᵉ) →
    Qᵉ ＝ᵉ Tᵉ → equiv-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ Tᵉ
  equiv-eq-Dependent-Type-With-Automorphismᵉ Qᵉ .Qᵉ reflᵉ =
    id-equiv-Dependent-Type-With-Automorphismᵉ Qᵉ

  is-torsorial-equiv-Dependent-Type-With-Automorphismᵉ :
    ( Qᵉ : Dependent-Type-With-Automorphismᵉ l2ᵉ Pᵉ) →
    is-torsorialᵉ (equiv-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ)
  is-torsorial-equiv-Dependent-Type-With-Automorphismᵉ Qᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equiv-famᵉ (family-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ))
      ( family-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ ,ᵉ
        id-equiv-famᵉ (family-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ))
      ( is-torsorial-Eq-Πᵉ
        ( λ xᵉ →
          is-torsorial-htpy-equivᵉ
            ( dependent-automorphism-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ xᵉ)))

  is-equiv-equiv-eq-Dependent-Type-With-Automorphismᵉ :
    ( Qᵉ Tᵉ : Dependent-Type-With-Automorphismᵉ l2ᵉ Pᵉ) →
    is-equivᵉ (equiv-eq-Dependent-Type-With-Automorphismᵉ Qᵉ Tᵉ)
  is-equiv-equiv-eq-Dependent-Type-With-Automorphismᵉ Qᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-equiv-Dependent-Type-With-Automorphismᵉ Qᵉ)
      ( equiv-eq-Dependent-Type-With-Automorphismᵉ Qᵉ)

  extensionality-Dependent-Type-With-Automorphismᵉ :
    (Qᵉ Tᵉ : Dependent-Type-With-Automorphismᵉ l2ᵉ Pᵉ) →
    (Qᵉ ＝ᵉ Tᵉ) ≃ᵉ equiv-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ Tᵉ
  pr1ᵉ (extensionality-Dependent-Type-With-Automorphismᵉ Qᵉ Tᵉ) =
    equiv-eq-Dependent-Type-With-Automorphismᵉ Qᵉ Tᵉ
  pr2ᵉ (extensionality-Dependent-Type-With-Automorphismᵉ Qᵉ Tᵉ) =
    is-equiv-equiv-eq-Dependent-Type-With-Automorphismᵉ Qᵉ Tᵉ

  eq-equiv-Dependent-Type-With-Automorphismᵉ :
    ( Qᵉ Tᵉ : Dependent-Type-With-Automorphismᵉ l2ᵉ Pᵉ) →
    equiv-Dependent-Type-With-Automorphismᵉ Pᵉ Qᵉ Tᵉ → Qᵉ ＝ᵉ Tᵉ
  eq-equiv-Dependent-Type-With-Automorphismᵉ Qᵉ Tᵉ =
    map-inv-is-equivᵉ (is-equiv-equiv-eq-Dependent-Type-With-Automorphismᵉ Qᵉ Tᵉ)
```