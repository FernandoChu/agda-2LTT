# Nilpotent elements in semirings

```agda
module ring-theory.nilpotent-elements-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.binomial-theorem-semiringsᵉ
open import ring-theory.powers-of-elements-semiringsᵉ
open import ring-theory.semiringsᵉ
```

</details>

## Idea

Aᵉ nilpotentᵉ elementᵉ in aᵉ semiringᵉ isᵉ anᵉ elementᵉ `x`ᵉ forᵉ whichᵉ thereᵉ isᵉ aᵉ naturalᵉ
numberᵉ `n`ᵉ suchᵉ thatᵉ `x^nᵉ = 0`.ᵉ

## Definition

```agda
is-nilpotent-element-semiring-Propᵉ :
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ) → type-Semiringᵉ Rᵉ → Propᵉ lᵉ
is-nilpotent-element-semiring-Propᵉ Rᵉ xᵉ =
  exists-structure-Propᵉ ℕᵉ (λ nᵉ → power-Semiringᵉ Rᵉ nᵉ xᵉ ＝ᵉ zero-Semiringᵉ Rᵉ)

is-nilpotent-element-Semiringᵉ :
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ) → type-Semiringᵉ Rᵉ → UUᵉ lᵉ
is-nilpotent-element-Semiringᵉ Rᵉ xᵉ =
  type-Propᵉ (is-nilpotent-element-semiring-Propᵉ Rᵉ xᵉ)

is-prop-is-nilpotent-element-Semiringᵉ :
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ) (xᵉ : type-Semiringᵉ Rᵉ) →
  is-propᵉ (is-nilpotent-element-Semiringᵉ Rᵉ xᵉ)
is-prop-is-nilpotent-element-Semiringᵉ Rᵉ xᵉ =
  is-prop-type-Propᵉ (is-nilpotent-element-semiring-Propᵉ Rᵉ xᵉ)
```

## Properties

### Zero is nilpotent

```agda
is-nilpotent-zero-Semiringᵉ :
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ) →
  is-nilpotent-element-Semiringᵉ Rᵉ (zero-Semiringᵉ Rᵉ)
is-nilpotent-zero-Semiringᵉ Rᵉ = intro-existsᵉ 1 reflᵉ
```

### If `x` and `y` commute and are both nilpotent, then `x + y` is nilpotent

```agda
is-nilpotent-add-Semiringᵉ :
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ) →
  (xᵉ yᵉ : type-Semiringᵉ Rᵉ) → (mul-Semiringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Semiringᵉ Rᵉ yᵉ xᵉ) →
  is-nilpotent-element-Semiringᵉ Rᵉ xᵉ → is-nilpotent-element-Semiringᵉ Rᵉ yᵉ →
  is-nilpotent-element-Semiringᵉ Rᵉ (add-Semiringᵉ Rᵉ xᵉ yᵉ)
is-nilpotent-add-Semiringᵉ Rᵉ xᵉ yᵉ Hᵉ fᵉ hᵉ =
  apply-universal-property-trunc-Propᵉ fᵉ
    ( is-nilpotent-element-semiring-Propᵉ Rᵉ (add-Semiringᵉ Rᵉ xᵉ yᵉ))
    ( λ (nᵉ ,ᵉ pᵉ) →
      apply-universal-property-trunc-Propᵉ hᵉ
        ( is-nilpotent-element-semiring-Propᵉ Rᵉ (add-Semiringᵉ Rᵉ xᵉ yᵉ))
        ( λ (mᵉ ,ᵉ qᵉ) →
          intro-existsᵉ
            ( nᵉ +ℕᵉ mᵉ)
            ( ( is-linear-combination-power-add-Semiringᵉ Rᵉ nᵉ mᵉ xᵉ yᵉ Hᵉ) ∙ᵉ
              ( ( ap-add-Semiringᵉ Rᵉ
                  ( ( apᵉ (mul-Semiring'ᵉ Rᵉ _) qᵉ) ∙ᵉ
                    ( left-zero-law-mul-Semiringᵉ Rᵉ _))
                  ( ( apᵉ (mul-Semiring'ᵉ Rᵉ _) pᵉ) ∙ᵉ
                    ( left-zero-law-mul-Semiringᵉ Rᵉ _))) ∙ᵉ
                ( left-unit-law-add-Semiringᵉ Rᵉ (zero-Semiringᵉ Rᵉ))))))
```

### If `x` is nilpotent and `y` commutes with `x`, then `xy` is also nilpotent

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  is-nilpotent-element-mul-Semiringᵉ :
    (xᵉ yᵉ : type-Semiringᵉ Rᵉ) →
    mul-Semiringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Semiringᵉ Rᵉ yᵉ xᵉ →
    is-nilpotent-element-Semiringᵉ Rᵉ xᵉ →
    is-nilpotent-element-Semiringᵉ Rᵉ (mul-Semiringᵉ Rᵉ xᵉ yᵉ)
  is-nilpotent-element-mul-Semiringᵉ xᵉ yᵉ Hᵉ fᵉ =
    apply-universal-property-trunc-Propᵉ fᵉ
      ( is-nilpotent-element-semiring-Propᵉ Rᵉ (mul-Semiringᵉ Rᵉ xᵉ yᵉ))
      ( λ (nᵉ ,ᵉ pᵉ) →
        intro-existsᵉ nᵉ
          ( ( distributive-power-mul-Semiringᵉ Rᵉ nᵉ Hᵉ) ∙ᵉ
            ( ( apᵉ (mul-Semiring'ᵉ Rᵉ (power-Semiringᵉ Rᵉ nᵉ yᵉ)) pᵉ) ∙ᵉ
              ( left-zero-law-mul-Semiringᵉ Rᵉ
                ( power-Semiringᵉ Rᵉ nᵉ yᵉ)))))

  is-nilpotent-element-mul-Semiring'ᵉ :
    (xᵉ yᵉ : type-Semiringᵉ Rᵉ) →
    mul-Semiringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Semiringᵉ Rᵉ yᵉ xᵉ →
    is-nilpotent-element-Semiringᵉ Rᵉ xᵉ →
    is-nilpotent-element-Semiringᵉ Rᵉ (mul-Semiringᵉ Rᵉ yᵉ xᵉ)
  is-nilpotent-element-mul-Semiring'ᵉ xᵉ yᵉ Hᵉ fᵉ =
    is-closed-under-eq-subtypeᵉ
      ( is-nilpotent-element-semiring-Propᵉ Rᵉ)
      ( is-nilpotent-element-mul-Semiringᵉ xᵉ yᵉ Hᵉ fᵉ)
      ( Hᵉ)
```