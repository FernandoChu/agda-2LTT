# Nilpotent elements in rings

```agda
module ring-theory.nilpotent-elements-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.nilpotent-elements-semiringsᵉ
open import ring-theory.powers-of-elements-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.subsets-ringsᵉ
```

</details>

## Idea

Aᵉ nilpotentᵉ elementᵉ in aᵉ ringᵉ isᵉ anᵉ elementᵉ `x`ᵉ forᵉ whichᵉ thereᵉ isᵉ aᵉ naturalᵉ
numberᵉ `n`ᵉ suchᵉ thatᵉ `x^nᵉ = 0`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-nilpotent-element-ring-Propᵉ : type-Ringᵉ Rᵉ → Propᵉ lᵉ
  is-nilpotent-element-ring-Propᵉ =
    is-nilpotent-element-semiring-Propᵉ (semiring-Ringᵉ Rᵉ)

  is-nilpotent-element-Ringᵉ : type-Ringᵉ Rᵉ → UUᵉ lᵉ
  is-nilpotent-element-Ringᵉ = is-nilpotent-element-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  is-prop-is-nilpotent-element-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → is-propᵉ (is-nilpotent-element-Ringᵉ xᵉ)
  is-prop-is-nilpotent-element-Ringᵉ =
    is-prop-is-nilpotent-element-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

## Properties

### Zero is nilpotent

```agda
is-nilpotent-zero-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) → is-nilpotent-element-Ringᵉ Rᵉ (zero-Ringᵉ Rᵉ)
is-nilpotent-zero-Ringᵉ Rᵉ = is-nilpotent-zero-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### If `x` and `y` commute and are both nilpotent, then `x + y` is nilpotent

```agda
is-nilpotent-add-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) →
  (xᵉ yᵉ : type-Ringᵉ Rᵉ) → (mul-Ringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Ringᵉ Rᵉ yᵉ xᵉ) →
  is-nilpotent-element-Ringᵉ Rᵉ xᵉ → is-nilpotent-element-Ringᵉ Rᵉ yᵉ →
  is-nilpotent-element-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ xᵉ yᵉ)
is-nilpotent-add-Ringᵉ Rᵉ = is-nilpotent-add-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### If `x` is nilpotent, then so is `-x`

```agda
is-nilpotent-element-neg-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) →
  is-closed-under-negatives-subset-Ringᵉ Rᵉ (is-nilpotent-element-ring-Propᵉ Rᵉ)
is-nilpotent-element-neg-Ringᵉ Rᵉ {xᵉ} Hᵉ =
  apply-universal-property-trunc-Propᵉ Hᵉ
    ( is-nilpotent-element-ring-Propᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ))
    ( λ (nᵉ ,ᵉ pᵉ) →
      intro-existsᵉ nᵉ
        ( ( power-neg-Ringᵉ Rᵉ nᵉ xᵉ) ∙ᵉ
          ( ( apᵉ (mul-Ringᵉ Rᵉ (power-Ringᵉ Rᵉ nᵉ (neg-one-Ringᵉ Rᵉ))) pᵉ) ∙ᵉ
            ( right-zero-law-mul-Ringᵉ Rᵉ (power-Ringᵉ Rᵉ nᵉ (neg-one-Ringᵉ Rᵉ))))))
```

### If `x` is nilpotent and `y` commutes with `x`, then `xy` is also nilpotent

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-nilpotent-element-mul-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Ringᵉ Rᵉ yᵉ xᵉ →
    is-nilpotent-element-Ringᵉ Rᵉ xᵉ →
    is-nilpotent-element-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)
  is-nilpotent-element-mul-Ringᵉ =
    is-nilpotent-element-mul-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  is-nilpotent-element-mul-Ring'ᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Ringᵉ Rᵉ yᵉ xᵉ →
    is-nilpotent-element-Ringᵉ Rᵉ xᵉ →
    is-nilpotent-element-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ yᵉ xᵉ)
  is-nilpotent-element-mul-Ring'ᵉ =
    is-nilpotent-element-mul-Semiring'ᵉ (semiring-Ringᵉ Rᵉ)
```