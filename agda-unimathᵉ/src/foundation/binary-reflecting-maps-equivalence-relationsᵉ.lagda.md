# Binary reflecting maps of equivalence relations

```agda
module foundation.binary-reflecting-maps-equivalence-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalence-relationsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Considerᵉ twoᵉ typesᵉ `A`ᵉ andᵉ `B`ᵉ equippedᵉ with equivalenceᵉ relationsᵉ `R`ᵉ andᵉ `S`.ᵉ
Aᵉ binaryᵉ reflectingᵉ mapᵉ fromᵉ `A`ᵉ to `B`ᵉ to `X`ᵉ isᵉ aᵉ binaryᵉ mapᵉ `fᵉ : Aᵉ → Bᵉ → X`ᵉ
suchᵉ thatᵉ forᵉ anyᵉ to `R`-relatedᵉ elementsᵉ `x`ᵉ andᵉ `x'`ᵉ in `A`ᵉ andᵉ anyᵉ twoᵉ
`S`-relatedᵉ elementsᵉ `y`ᵉ andᵉ `y'`ᵉ in `B`ᵉ weᵉ haveᵉ `fᵉ xᵉ yᵉ ＝ᵉ fᵉ x'ᵉ y'`ᵉ in `X`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (Rᵉ : equivalence-relationᵉ l3ᵉ Aᵉ) (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  where

  binary-reflects-equivalence-relationᵉ :
    {Xᵉ : UUᵉ l5ᵉ} (fᵉ : Aᵉ → Bᵉ → Xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  binary-reflects-equivalence-relationᵉ fᵉ =
    {xᵉ x'ᵉ : Aᵉ} {yᵉ y'ᵉ : Bᵉ} →
    sim-equivalence-relationᵉ Rᵉ xᵉ x'ᵉ → sim-equivalence-relationᵉ Sᵉ yᵉ y'ᵉ →
    fᵉ xᵉ yᵉ ＝ᵉ fᵉ x'ᵉ y'ᵉ

  binary-reflecting-map-equivalence-relationᵉ :
    (Xᵉ : UUᵉ l5ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  binary-reflecting-map-equivalence-relationᵉ Xᵉ =
    Σᵉ (Aᵉ → Bᵉ → Xᵉ) binary-reflects-equivalence-relationᵉ

  map-binary-reflecting-map-equivalence-relationᵉ :
    {Xᵉ : UUᵉ l5ᵉ} → binary-reflecting-map-equivalence-relationᵉ Xᵉ → Aᵉ → Bᵉ → Xᵉ
  map-binary-reflecting-map-equivalence-relationᵉ = pr1ᵉ

  reflects-binary-reflecting-map-equivalence-relationᵉ :
    {Xᵉ : UUᵉ l5ᵉ} (fᵉ : binary-reflecting-map-equivalence-relationᵉ Xᵉ) →
    binary-reflects-equivalence-relationᵉ
      ( map-binary-reflecting-map-equivalence-relationᵉ fᵉ)
  reflects-binary-reflecting-map-equivalence-relationᵉ = pr2ᵉ

  is-prop-binary-reflects-equivalence-relationᵉ :
    (Xᵉ : Setᵉ l5ᵉ) (fᵉ : Aᵉ → Bᵉ → type-Setᵉ Xᵉ) →
    is-propᵉ (binary-reflects-equivalence-relationᵉ fᵉ)
  is-prop-binary-reflects-equivalence-relationᵉ Xᵉ fᵉ =
    is-prop-implicit-Πᵉ
      ( λ xᵉ →
        is-prop-implicit-Πᵉ
          ( λ x'ᵉ →
            is-prop-implicit-Πᵉ
              ( λ yᵉ →
                is-prop-implicit-Πᵉ
                  ( λ y'ᵉ →
                    is-prop-function-typeᵉ
                      ( is-prop-function-typeᵉ
                        ( is-set-type-Setᵉ Xᵉ (fᵉ xᵉ yᵉ) (fᵉ x'ᵉ y'ᵉ)))))))

  binary-reflects-prop-equivalence-relationᵉ :
    (Xᵉ : Setᵉ l5ᵉ) (fᵉ : Aᵉ → Bᵉ → type-Setᵉ Xᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  pr1ᵉ (binary-reflects-prop-equivalence-relationᵉ Xᵉ fᵉ) =
    binary-reflects-equivalence-relationᵉ fᵉ
  pr2ᵉ (binary-reflects-prop-equivalence-relationᵉ Xᵉ fᵉ) =
    is-prop-binary-reflects-equivalence-relationᵉ Xᵉ fᵉ
```

### Characterizing the identity type of binary reflecting maps into sets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  (Cᵉ : Setᵉ l5ᵉ) (fᵉ : binary-reflecting-map-equivalence-relationᵉ Rᵉ Sᵉ (type-Setᵉ Cᵉ))
  where

  htpy-binary-reflecting-map-equivalence-relationᵉ :
    (gᵉ : binary-reflecting-map-equivalence-relationᵉ Rᵉ Sᵉ (type-Setᵉ Cᵉ)) →
    UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l5ᵉ)
  htpy-binary-reflecting-map-equivalence-relationᵉ gᵉ =
    (xᵉ : Aᵉ) (yᵉ : Bᵉ) →
    map-binary-reflecting-map-equivalence-relationᵉ Rᵉ Sᵉ fᵉ xᵉ yᵉ ＝ᵉ
    map-binary-reflecting-map-equivalence-relationᵉ Rᵉ Sᵉ gᵉ xᵉ yᵉ

  refl-htpy-binary-reflecting-map-equivalence-relationᵉ :
    htpy-binary-reflecting-map-equivalence-relationᵉ fᵉ
  refl-htpy-binary-reflecting-map-equivalence-relationᵉ xᵉ yᵉ = reflᵉ

  htpy-eq-binary-reflecting-map-equivalence-relationᵉ :
    (gᵉ : binary-reflecting-map-equivalence-relationᵉ Rᵉ Sᵉ (type-Setᵉ Cᵉ)) →
    (fᵉ ＝ᵉ gᵉ) → htpy-binary-reflecting-map-equivalence-relationᵉ gᵉ
  htpy-eq-binary-reflecting-map-equivalence-relationᵉ .fᵉ reflᵉ =
    refl-htpy-binary-reflecting-map-equivalence-relationᵉ

  is-torsorial-htpy-binary-reflecting-map-equivalence-relationᵉ :
    is-torsorialᵉ (htpy-binary-reflecting-map-equivalence-relationᵉ)
  is-torsorial-htpy-binary-reflecting-map-equivalence-relationᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-Eq-Πᵉ
        ( λ xᵉ →
          is-torsorial-htpyᵉ
            ( map-binary-reflecting-map-equivalence-relationᵉ Rᵉ Sᵉ fᵉ xᵉ)))
      ( is-prop-binary-reflects-equivalence-relationᵉ Rᵉ Sᵉ Cᵉ)
      ( map-binary-reflecting-map-equivalence-relationᵉ Rᵉ Sᵉ fᵉ)
      ( λ xᵉ → refl-htpyᵉ)
      ( reflects-binary-reflecting-map-equivalence-relationᵉ Rᵉ Sᵉ fᵉ)

  is-equiv-htpy-eq-binary-reflecting-map-equivalence-relationᵉ :
    (gᵉ : binary-reflecting-map-equivalence-relationᵉ Rᵉ Sᵉ (type-Setᵉ Cᵉ)) →
    is-equivᵉ (htpy-eq-binary-reflecting-map-equivalence-relationᵉ gᵉ)
  is-equiv-htpy-eq-binary-reflecting-map-equivalence-relationᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-htpy-binary-reflecting-map-equivalence-relationᵉ
      htpy-eq-binary-reflecting-map-equivalence-relationᵉ

  extensionality-binary-reflecting-map-equivalence-relationᵉ :
    (gᵉ : binary-reflecting-map-equivalence-relationᵉ Rᵉ Sᵉ (type-Setᵉ Cᵉ)) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-binary-reflecting-map-equivalence-relationᵉ gᵉ
  pr1ᵉ (extensionality-binary-reflecting-map-equivalence-relationᵉ gᵉ) =
    htpy-eq-binary-reflecting-map-equivalence-relationᵉ gᵉ
  pr2ᵉ (extensionality-binary-reflecting-map-equivalence-relationᵉ gᵉ) =
    is-equiv-htpy-eq-binary-reflecting-map-equivalence-relationᵉ gᵉ

  eq-htpy-binary-reflecting-map-equivalence-relationᵉ :
    (gᵉ : binary-reflecting-map-equivalence-relationᵉ Rᵉ Sᵉ (type-Setᵉ Cᵉ)) →
    htpy-binary-reflecting-map-equivalence-relationᵉ gᵉ → (fᵉ ＝ᵉ gᵉ)
  eq-htpy-binary-reflecting-map-equivalence-relationᵉ gᵉ =
    map-inv-equivᵉ (extensionality-binary-reflecting-map-equivalence-relationᵉ gᵉ)
```