# Binary functoriality of set quotients

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module foundation.binary-functoriality-set-quotientsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-homotopiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.exponents-set-quotientsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-set-quotientsᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.set-quotientsᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universal-property-set-quotientsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalence-relationsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Givenᵉ threeᵉ typesᵉ `A`,ᵉ `B`,ᵉ andᵉ `C`ᵉ equippedᵉ with equivalenceᵉ relationsᵉ `R`,ᵉ
`S`,ᵉ andᵉ `T`,ᵉ respectively,ᵉ anyᵉ binaryᵉ operationᵉ `fᵉ : Aᵉ → Bᵉ → C`ᵉ suchᵉ thatᵉ forᵉ
anyᵉ `xᵉ x'ᵉ : A`ᵉ suchᵉ thatᵉ `Rᵉ xᵉ x'`ᵉ holds,ᵉ andᵉ forᵉ anyᵉ `yᵉ y'ᵉ : B`ᵉ suchᵉ thatᵉ
`Sᵉ yᵉ y'`ᵉ holds,ᵉ theᵉ relationᵉ `Tᵉ (fᵉ xᵉ yᵉ) (fᵉ x'ᵉ y')`ᵉ holdsᵉ extendsᵉ uniquelyᵉ to aᵉ
binaryᵉ operationᵉ `gᵉ : A/Rᵉ → B/Sᵉ → C/T`ᵉ suchᵉ thatᵉ `gᵉ (qᵉ xᵉ) (qᵉ yᵉ) = qᵉ (fᵉ xᵉ y)`ᵉ forᵉ
allᵉ `xᵉ : A`ᵉ andᵉ `yᵉ : B`.ᵉ

## Definition

### Binary hom of equivalence relation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  {Cᵉ : UUᵉ l5ᵉ} (Tᵉ : equivalence-relationᵉ l6ᵉ Cᵉ)
  where

  preserves-sim-prop-binary-map-equivalence-relationᵉ :
    (Aᵉ → Bᵉ → Cᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l6ᵉ)
  preserves-sim-prop-binary-map-equivalence-relationᵉ fᵉ =
    implicit-Π-Propᵉ Aᵉ
      ( λ xᵉ →
        implicit-Π-Propᵉ Aᵉ
          ( λ x'ᵉ →
            implicit-Π-Propᵉ Bᵉ
              ( λ yᵉ →
                implicit-Π-Propᵉ Bᵉ
                  ( λ y'ᵉ →
                    function-Propᵉ
                      ( sim-equivalence-relationᵉ Rᵉ xᵉ x'ᵉ)
                      ( function-Propᵉ
                        ( sim-equivalence-relationᵉ Sᵉ yᵉ y'ᵉ)
                        ( prop-equivalence-relationᵉ Tᵉ (fᵉ xᵉ yᵉ) (fᵉ x'ᵉ y'ᵉ)))))))

  preserves-sim-binary-map-equivalence-relationᵉ :
    (Aᵉ → Bᵉ → Cᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l6ᵉ)
  preserves-sim-binary-map-equivalence-relationᵉ fᵉ =
    type-Propᵉ (preserves-sim-prop-binary-map-equivalence-relationᵉ fᵉ)

  is-prop-preserves-sim-binary-map-equivalence-relationᵉ :
    (fᵉ : Aᵉ → Bᵉ → Cᵉ) → is-propᵉ (preserves-sim-binary-map-equivalence-relationᵉ fᵉ)
  is-prop-preserves-sim-binary-map-equivalence-relationᵉ fᵉ =
    is-prop-type-Propᵉ (preserves-sim-prop-binary-map-equivalence-relationᵉ fᵉ)

  binary-hom-equivalence-relationᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  binary-hom-equivalence-relationᵉ =
    type-subtypeᵉ preserves-sim-prop-binary-map-equivalence-relationᵉ

  map-binary-hom-equivalence-relationᵉ :
    (fᵉ : binary-hom-equivalence-relationᵉ) → Aᵉ → Bᵉ → Cᵉ
  map-binary-hom-equivalence-relationᵉ = pr1ᵉ

  preserves-sim-binary-hom-equivalence-relationᵉ :
    (fᵉ : binary-hom-equivalence-relationᵉ) →
    preserves-sim-binary-map-equivalence-relationᵉ
      ( map-binary-hom-equivalence-relationᵉ fᵉ)
  preserves-sim-binary-hom-equivalence-relationᵉ = pr2ᵉ
```

## Properties

### Characterization of equality of `binary-hom-equivalence-relation`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  {Cᵉ : UUᵉ l5ᵉ} (Tᵉ : equivalence-relationᵉ l6ᵉ Cᵉ)
  where

  binary-htpy-hom-equivalence-relationᵉ :
    (fᵉ gᵉ : binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l5ᵉ)
  binary-htpy-hom-equivalence-relationᵉ fᵉ gᵉ =
    binary-htpyᵉ
      ( map-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ)
      ( map-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ gᵉ)

  refl-binary-htpy-hom-equivalence-relationᵉ :
    (fᵉ : binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ) →
    binary-htpy-hom-equivalence-relationᵉ fᵉ fᵉ
  refl-binary-htpy-hom-equivalence-relationᵉ fᵉ =
    refl-binary-htpyᵉ (map-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ)

  binary-htpy-eq-hom-equivalence-relationᵉ :
    (fᵉ gᵉ : binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ) →
    (fᵉ ＝ᵉ gᵉ) → binary-htpy-hom-equivalence-relationᵉ fᵉ gᵉ
  binary-htpy-eq-hom-equivalence-relationᵉ fᵉ .fᵉ reflᵉ =
    refl-binary-htpy-hom-equivalence-relationᵉ fᵉ

  is-torsorial-binary-htpy-hom-equivalence-relationᵉ :
    (fᵉ : binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ) →
    is-torsorialᵉ (binary-htpy-hom-equivalence-relationᵉ fᵉ)
  is-torsorial-binary-htpy-hom-equivalence-relationᵉ fᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-binary-htpyᵉ
        ( map-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ))
      ( is-prop-preserves-sim-binary-map-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ)
      ( map-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ)
      ( refl-binary-htpy-hom-equivalence-relationᵉ fᵉ)
      ( preserves-sim-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ)

  is-equiv-binary-htpy-eq-hom-equivalence-relationᵉ :
    (fᵉ gᵉ : binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ) →
    is-equivᵉ (binary-htpy-eq-hom-equivalence-relationᵉ fᵉ gᵉ)
  is-equiv-binary-htpy-eq-hom-equivalence-relationᵉ fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-binary-htpy-hom-equivalence-relationᵉ fᵉ)
      ( binary-htpy-eq-hom-equivalence-relationᵉ fᵉ)

  extensionality-binary-hom-equivalence-relationᵉ :
    (fᵉ gᵉ : binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ binary-htpy-hom-equivalence-relationᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-binary-hom-equivalence-relationᵉ fᵉ gᵉ) =
    binary-htpy-eq-hom-equivalence-relationᵉ fᵉ gᵉ
  pr2ᵉ (extensionality-binary-hom-equivalence-relationᵉ fᵉ gᵉ) =
    is-equiv-binary-htpy-eq-hom-equivalence-relationᵉ fᵉ gᵉ

  eq-binary-htpy-hom-equivalence-relationᵉ :
    (fᵉ gᵉ : binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ) →
    binary-htpy-hom-equivalence-relationᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-binary-htpy-hom-equivalence-relationᵉ fᵉ gᵉ =
    map-inv-equivᵉ (extensionality-binary-hom-equivalence-relationᵉ fᵉ gᵉ)
```

### The type `binary-hom-equivalence-relation R S T` is equivalent to the type `hom-equivalence-relation R (equivalence-relation-hom-equivalence-relation S T)`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  {Cᵉ : UUᵉ l5ᵉ} (Tᵉ : equivalence-relationᵉ l6ᵉ Cᵉ)
  where

  map-hom-binary-hom-equivalence-relationᵉ :
    binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ → Aᵉ → hom-equivalence-relationᵉ Sᵉ Tᵉ
  pr1ᵉ (map-hom-binary-hom-equivalence-relationᵉ fᵉ aᵉ) =
    map-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ aᵉ
  pr2ᵉ (map-hom-binary-hom-equivalence-relationᵉ fᵉ aᵉ) {xᵉ} {yᵉ} =
    preserves-sim-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ
      ( refl-equivalence-relationᵉ Rᵉ aᵉ)

  preserves-sim-hom-binary-hom-equivalence-relationᵉ :
    (fᵉ : binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ) →
    preserves-sim-equivalence-relationᵉ Rᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Sᵉ Tᵉ)
      ( map-hom-binary-hom-equivalence-relationᵉ fᵉ)
  preserves-sim-hom-binary-hom-equivalence-relationᵉ fᵉ rᵉ bᵉ =
    preserves-sim-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ rᵉ
      ( refl-equivalence-relationᵉ Sᵉ bᵉ)

  hom-binary-hom-equivalence-relationᵉ :
    binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ →
    hom-equivalence-relationᵉ Rᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Sᵉ Tᵉ)
  pr1ᵉ (hom-binary-hom-equivalence-relationᵉ fᵉ) =
    map-hom-binary-hom-equivalence-relationᵉ fᵉ
  pr2ᵉ (hom-binary-hom-equivalence-relationᵉ fᵉ) =
    preserves-sim-hom-binary-hom-equivalence-relationᵉ fᵉ

  map-binary-hom-hom-equivalence-relationᵉ :
    hom-equivalence-relationᵉ Rᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Sᵉ Tᵉ) →
    Aᵉ → Bᵉ → Cᵉ
  map-binary-hom-hom-equivalence-relationᵉ fᵉ xᵉ =
    map-hom-equivalence-relationᵉ Sᵉ Tᵉ
      ( map-hom-equivalence-relationᵉ Rᵉ
        ( equivalence-relation-hom-equivalence-relationᵉ Sᵉ Tᵉ)
        ( fᵉ)
        ( xᵉ))

  preserves-sim-binary-hom-hom-equivalence-relationᵉ :
    (fᵉ :
      hom-equivalence-relationᵉ Rᵉ
        ( equivalence-relation-hom-equivalence-relationᵉ Sᵉ Tᵉ)) →
    preserves-sim-binary-map-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ
      ( map-binary-hom-hom-equivalence-relationᵉ fᵉ)
  preserves-sim-binary-hom-hom-equivalence-relationᵉ fᵉ {xᵉ} {x'ᵉ} {yᵉ} {y'ᵉ} rᵉ sᵉ =
    transitive-equivalence-relationᵉ Tᵉ
      ( pr1ᵉ
        ( map-hom-equivalence-relationᵉ
            Rᵉ (equivalence-relation-hom-equivalence-relationᵉ Sᵉ Tᵉ) fᵉ xᵉ)
        ( yᵉ))
      ( pr1ᵉ
        ( map-hom-equivalence-relationᵉ
            Rᵉ (equivalence-relation-hom-equivalence-relationᵉ Sᵉ Tᵉ) fᵉ x'ᵉ) yᵉ)
      ( map-hom-equivalence-relationᵉ Sᵉ Tᵉ (pr1ᵉ fᵉ x'ᵉ) y'ᵉ)
      ( preserves-sim-hom-equivalence-relationᵉ Sᵉ Tᵉ
        ( map-hom-equivalence-relationᵉ
            Rᵉ (equivalence-relation-hom-equivalence-relationᵉ Sᵉ Tᵉ) fᵉ x'ᵉ)
        ( sᵉ))
      ( preserves-sim-hom-equivalence-relationᵉ
          Rᵉ (equivalence-relation-hom-equivalence-relationᵉ Sᵉ Tᵉ) fᵉ rᵉ yᵉ)

  binary-hom-hom-equivalence-relationᵉ :
    hom-equivalence-relationᵉ Rᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Sᵉ Tᵉ) →
    binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ
  pr1ᵉ (binary-hom-hom-equivalence-relationᵉ fᵉ) =
    map-binary-hom-hom-equivalence-relationᵉ fᵉ
  pr2ᵉ (binary-hom-hom-equivalence-relationᵉ fᵉ) =
    preserves-sim-binary-hom-hom-equivalence-relationᵉ fᵉ

  is-section-binary-hom-hom-equivalence-relationᵉ :
    ( hom-binary-hom-equivalence-relationᵉ ∘ᵉ
      binary-hom-hom-equivalence-relationᵉ) ~ᵉ
    idᵉ
  is-section-binary-hom-hom-equivalence-relationᵉ fᵉ =
    eq-htpy-hom-equivalence-relationᵉ Rᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Sᵉ Tᵉ)
      ( hom-binary-hom-equivalence-relationᵉ
        ( binary-hom-hom-equivalence-relationᵉ fᵉ))
      ( fᵉ)
      ( λ xᵉ →
        eq-htpy-hom-equivalence-relationᵉ Sᵉ Tᵉ
          ( map-hom-equivalence-relationᵉ Rᵉ
            ( equivalence-relation-hom-equivalence-relationᵉ Sᵉ Tᵉ)
            ( hom-binary-hom-equivalence-relationᵉ
              ( binary-hom-hom-equivalence-relationᵉ fᵉ))
            ( xᵉ))
          ( map-hom-equivalence-relationᵉ
              Rᵉ (equivalence-relation-hom-equivalence-relationᵉ Sᵉ Tᵉ) fᵉ xᵉ)
          ( refl-htpyᵉ))

  is-retraction-binary-hom-hom-equivalence-relationᵉ :
    ( binary-hom-hom-equivalence-relationᵉ ∘ᵉ
      hom-binary-hom-equivalence-relationᵉ) ~ᵉ
    idᵉ
  is-retraction-binary-hom-hom-equivalence-relationᵉ fᵉ =
    eq-binary-htpy-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ
      ( binary-hom-hom-equivalence-relationᵉ
        ( hom-binary-hom-equivalence-relationᵉ fᵉ))
      ( fᵉ)
      ( refl-binary-htpyᵉ (map-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ))

  is-equiv-hom-binary-hom-equivalence-relationᵉ :
    is-equivᵉ hom-binary-hom-equivalence-relationᵉ
  is-equiv-hom-binary-hom-equivalence-relationᵉ =
    is-equiv-is-invertibleᵉ
      binary-hom-hom-equivalence-relationᵉ
      is-section-binary-hom-hom-equivalence-relationᵉ
      is-retraction-binary-hom-hom-equivalence-relationᵉ

  equiv-hom-binary-hom-equivalence-relationᵉ :
    binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ ≃ᵉ
    hom-equivalence-relationᵉ Rᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Sᵉ Tᵉ)
  pr1ᵉ equiv-hom-binary-hom-equivalence-relationᵉ =
    hom-binary-hom-equivalence-relationᵉ
  pr2ᵉ equiv-hom-binary-hom-equivalence-relationᵉ =
    is-equiv-hom-binary-hom-equivalence-relationᵉ
```

### Binary functoriality of types that satisfy the universal property of set quotients

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  (QRᵉ : Setᵉ l3ᵉ) (qRᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ QRᵉ))
  {Bᵉ : UUᵉ l4ᵉ} (Sᵉ : equivalence-relationᵉ l5ᵉ Bᵉ)
  (QSᵉ : Setᵉ l6ᵉ) (qSᵉ : reflecting-map-equivalence-relationᵉ Sᵉ (type-Setᵉ QSᵉ))
  {Cᵉ : UUᵉ l7ᵉ} (Tᵉ : equivalence-relationᵉ l8ᵉ Cᵉ)
  (QTᵉ : Setᵉ l9ᵉ) (qTᵉ : reflecting-map-equivalence-relationᵉ Tᵉ (type-Setᵉ QTᵉ))
  (UqRᵉ : is-set-quotientᵉ Rᵉ QRᵉ qRᵉ)
  (UqSᵉ : is-set-quotientᵉ Sᵉ QSᵉ qSᵉ)
  (UqTᵉ : is-set-quotientᵉ Tᵉ QTᵉ qTᵉ)
  (fᵉ : binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ)
  where

  private
    pᵉ :
      (xᵉ : Aᵉ) (yᵉ : Bᵉ) →
      map-reflecting-map-equivalence-relationᵉ Tᵉ qTᵉ
        ( map-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ xᵉ yᵉ) ＝ᵉ
      inclusion-is-set-quotient-hom-equivalence-relationᵉ Sᵉ QSᵉ qSᵉ UqSᵉ Tᵉ QTᵉ qTᵉ UqTᵉ
        ( quotient-hom-equivalence-relation-Setᵉ Sᵉ Tᵉ)
        ( reflecting-map-quotient-map-hom-equivalence-relationᵉ Sᵉ Tᵉ)
        ( is-set-quotient-set-quotient-hom-equivalence-relationᵉ Sᵉ Tᵉ)
        ( quotient-map-hom-equivalence-relationᵉ Sᵉ Tᵉ
          ( map-hom-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ xᵉ))
        ( map-reflecting-map-equivalence-relationᵉ Sᵉ qSᵉ yᵉ)
    pᵉ xᵉ yᵉ =
      ( invᵉ
        ( coherence-square-map-is-set-quotientᵉ Sᵉ QSᵉ qSᵉ Tᵉ QTᵉ qTᵉ UqSᵉ UqTᵉ
          ( map-hom-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ xᵉ)
          ( yᵉ))) ∙ᵉ
      ( invᵉ
        ( htpy-eqᵉ
          ( triangle-inclusion-is-set-quotient-hom-equivalence-relationᵉ
            Sᵉ QSᵉ qSᵉ UqSᵉ Tᵉ QTᵉ qTᵉ UqTᵉ
            ( quotient-hom-equivalence-relation-Setᵉ Sᵉ Tᵉ)
            ( reflecting-map-quotient-map-hom-equivalence-relationᵉ Sᵉ Tᵉ)
            ( is-set-quotient-set-quotient-hom-equivalence-relationᵉ Sᵉ Tᵉ)
            ( map-hom-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ xᵉ))
          ( map-reflecting-map-equivalence-relationᵉ Sᵉ qSᵉ yᵉ)))

  unique-binary-map-is-set-quotientᵉ :
    is-contrᵉ
      ( Σᵉ ( type-Setᵉ QRᵉ → type-Setᵉ QSᵉ → type-Setᵉ QTᵉ)
          ( λ hᵉ →
            (xᵉ : Aᵉ) (yᵉ : Bᵉ) →
            ( hᵉ ( map-reflecting-map-equivalence-relationᵉ Rᵉ qRᵉ xᵉ)
                ( map-reflecting-map-equivalence-relationᵉ Sᵉ qSᵉ yᵉ)) ＝ᵉ
            ( map-reflecting-map-equivalence-relationᵉ Tᵉ qTᵉ
              ( map-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ xᵉ yᵉ))))
  unique-binary-map-is-set-quotientᵉ =
    is-contr-equivᵉ
      ( Σᵉ ( type-Setᵉ QRᵉ → set-quotient-hom-equivalence-relationᵉ Sᵉ Tᵉ)
          ( λ hᵉ →
            ( xᵉ : Aᵉ) →
            ( hᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qRᵉ xᵉ)) ＝ᵉ
            ( quotient-map-hom-equivalence-relationᵉ Sᵉ Tᵉ
              ( map-hom-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ xᵉ))))
      ( equiv-totᵉ
        ( λ hᵉ →
          ( equiv-inv-htpyᵉ
            ( ( quotient-map-hom-equivalence-relationᵉ Sᵉ Tᵉ) ∘ᵉ
              ( map-hom-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ))
            ( hᵉ ∘ᵉ map-reflecting-map-equivalence-relationᵉ Rᵉ qRᵉ))) ∘eᵉ
        ( ( inv-equivᵉ
            ( equiv-postcomp-extension-surjectionᵉ
              ( map-reflecting-map-equivalence-relationᵉ Rᵉ qRᵉ ,ᵉ
                is-surjective-is-set-quotientᵉ Rᵉ QRᵉ qRᵉ UqRᵉ)
              ( ( quotient-map-hom-equivalence-relationᵉ Sᵉ Tᵉ) ∘ᵉ
                ( map-hom-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ))
              ( emb-inclusion-is-set-quotient-hom-equivalence-relationᵉ
                Sᵉ QSᵉ qSᵉ UqSᵉ Tᵉ QTᵉ qTᵉ UqTᵉ
                ( quotient-hom-equivalence-relation-Setᵉ Sᵉ Tᵉ)
                ( reflecting-map-quotient-map-hom-equivalence-relationᵉ Sᵉ Tᵉ)
                ( is-set-quotient-set-quotient-hom-equivalence-relationᵉ
                    Sᵉ Tᵉ)))) ∘eᵉ
          ( equiv-totᵉ
            ( λ hᵉ →
              equiv-Π-equiv-familyᵉ
                ( λ xᵉ →
                  ( inv-equivᵉ equiv-funextᵉ) ∘eᵉ
                  ( inv-equivᵉ
                    ( equiv-dependent-universal-property-surjection-is-surjectiveᵉ
                      ( map-reflecting-map-equivalence-relationᵉ Sᵉ qSᵉ)
                      ( is-surjective-is-set-quotientᵉ Sᵉ QSᵉ qSᵉ UqSᵉ)
                      ( λ uᵉ →
                        Id-Propᵉ QTᵉ
                        ( inclusion-is-set-quotient-hom-equivalence-relationᵉ
                          Sᵉ QSᵉ qSᵉ UqSᵉ Tᵉ QTᵉ qTᵉ UqTᵉ
                          ( quotient-hom-equivalence-relation-Setᵉ Sᵉ Tᵉ)
                          ( reflecting-map-quotient-map-hom-equivalence-relationᵉ
                              Sᵉ Tᵉ)
                          ( is-set-quotient-set-quotient-hom-equivalence-relationᵉ
                              Sᵉ Tᵉ)
                          ( quotient-map-hom-equivalence-relationᵉ Sᵉ Tᵉ
                            ( map-hom-binary-hom-equivalence-relationᵉ
                                Rᵉ Sᵉ Tᵉ fᵉ xᵉ))
                          ( uᵉ))
                        ( hᵉ
                          ( map-reflecting-map-equivalence-relationᵉ Rᵉ qRᵉ xᵉ)
                          ( uᵉ)))) ∘eᵉ
                    ( equiv-Π-equiv-familyᵉ
                      ( λ yᵉ →
                        ( equiv-invᵉ _ _) ∘eᵉ
                        ( equiv-concat'ᵉ
                          ( hᵉ
                            ( map-reflecting-map-equivalence-relationᵉ Rᵉ qRᵉ xᵉ)
                            ( map-reflecting-map-equivalence-relationᵉ Sᵉ qSᵉ yᵉ))
                          ( pᵉ xᵉ yᵉ))))))))))
      ( unique-map-is-set-quotientᵉ Rᵉ QRᵉ qRᵉ
        ( equivalence-relation-hom-equivalence-relationᵉ Sᵉ Tᵉ)
        ( quotient-hom-equivalence-relation-Setᵉ Sᵉ Tᵉ)
        ( reflecting-map-quotient-map-hom-equivalence-relationᵉ Sᵉ Tᵉ)
        ( UqRᵉ)
        ( is-set-quotient-set-quotient-hom-equivalence-relationᵉ Sᵉ Tᵉ)
        ( hom-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ))

  binary-map-is-set-quotientᵉ : hom-Setᵉ QRᵉ (hom-set-Setᵉ QSᵉ QTᵉ)
  binary-map-is-set-quotientᵉ =
    pr1ᵉ (centerᵉ unique-binary-map-is-set-quotientᵉ)

  compute-binary-map-is-set-quotientᵉ :
    (xᵉ : Aᵉ) (yᵉ : Bᵉ) →
    binary-map-is-set-quotientᵉ
      ( map-reflecting-map-equivalence-relationᵉ Rᵉ qRᵉ xᵉ)
      ( map-reflecting-map-equivalence-relationᵉ Sᵉ qSᵉ yᵉ) ＝ᵉ
    map-reflecting-map-equivalence-relationᵉ
      Tᵉ qTᵉ (map-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ xᵉ yᵉ)
  compute-binary-map-is-set-quotientᵉ =
    pr2ᵉ (centerᵉ unique-binary-map-is-set-quotientᵉ)
```

### Binary functoriality of set quotients

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  {Cᵉ : UUᵉ l5ᵉ} (Tᵉ : equivalence-relationᵉ l6ᵉ Cᵉ)
  (fᵉ : binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ)
  where

  unique-binary-map-set-quotientᵉ :
    is-contrᵉ
      ( Σᵉ ( set-quotientᵉ Rᵉ → set-quotientᵉ Sᵉ → set-quotientᵉ Tᵉ)
          ( λ hᵉ →
            (xᵉ : Aᵉ) (yᵉ : Bᵉ) →
            ( hᵉ (quotient-mapᵉ Rᵉ xᵉ) (quotient-mapᵉ Sᵉ yᵉ)) ＝ᵉ
            ( quotient-mapᵉ Tᵉ
              ( map-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ xᵉ yᵉ))))
  unique-binary-map-set-quotientᵉ =
    unique-binary-map-is-set-quotientᵉ
      ( Rᵉ)
      ( quotient-Setᵉ Rᵉ)
      ( reflecting-map-quotient-mapᵉ Rᵉ)
      ( Sᵉ)
      ( quotient-Setᵉ Sᵉ)
      ( reflecting-map-quotient-mapᵉ Sᵉ)
      ( Tᵉ)
      ( quotient-Setᵉ Tᵉ)
      ( reflecting-map-quotient-mapᵉ Tᵉ)
      ( is-set-quotient-set-quotientᵉ Rᵉ)
      ( is-set-quotient-set-quotientᵉ Sᵉ)
      ( is-set-quotient-set-quotientᵉ Tᵉ)
      ( fᵉ)

  binary-map-set-quotientᵉ : set-quotientᵉ Rᵉ → set-quotientᵉ Sᵉ → set-quotientᵉ Tᵉ
  binary-map-set-quotientᵉ =
    pr1ᵉ (centerᵉ unique-binary-map-set-quotientᵉ)

  compute-binary-map-set-quotientᵉ :
    (xᵉ : Aᵉ) (yᵉ : Bᵉ) →
    ( binary-map-set-quotientᵉ (quotient-mapᵉ Rᵉ xᵉ) (quotient-mapᵉ Sᵉ yᵉ)) ＝ᵉ
    ( quotient-mapᵉ Tᵉ (map-binary-hom-equivalence-relationᵉ Rᵉ Sᵉ Tᵉ fᵉ xᵉ yᵉ))
  compute-binary-map-set-quotientᵉ =
    pr2ᵉ (centerᵉ unique-binary-map-set-quotientᵉ)
```