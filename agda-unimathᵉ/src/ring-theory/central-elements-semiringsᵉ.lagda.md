# Central elements of semirings

```agda
module ring-theory.central-elements-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.central-elements-monoidsᵉ

open import ring-theory.semiringsᵉ
```

</details>

## Idea

Anᵉ elementᵉ `x`ᵉ ofᵉ aᵉ semiringᵉ `R`ᵉ isᵉ saidᵉ to beᵉ centralᵉ ifᵉ `xyᵉ ＝ᵉ yx`ᵉ forᵉ everyᵉ
`yᵉ : R`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  is-central-element-semiring-Propᵉ : type-Semiringᵉ Rᵉ → Propᵉ lᵉ
  is-central-element-semiring-Propᵉ =
    is-central-element-prop-Monoidᵉ
      ( multiplicative-monoid-Semiringᵉ Rᵉ)

  is-central-element-Semiringᵉ : type-Semiringᵉ Rᵉ → UUᵉ lᵉ
  is-central-element-Semiringᵉ =
    is-central-element-Monoidᵉ (multiplicative-monoid-Semiringᵉ Rᵉ)

  is-prop-is-central-element-Semiringᵉ :
    (xᵉ : type-Semiringᵉ Rᵉ) → is-propᵉ (is-central-element-Semiringᵉ xᵉ)
  is-prop-is-central-element-Semiringᵉ =
    is-prop-is-central-element-Monoidᵉ (multiplicative-monoid-Semiringᵉ Rᵉ)
```

## Properties

### The zero element is central

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  is-central-element-zero-Semiringᵉ :
    is-central-element-Semiringᵉ Rᵉ (zero-Semiringᵉ Rᵉ)
  is-central-element-zero-Semiringᵉ xᵉ =
    left-zero-law-mul-Semiringᵉ Rᵉ xᵉ ∙ᵉ invᵉ (right-zero-law-mul-Semiringᵉ Rᵉ xᵉ)
```

### The unit element is central

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  is-central-element-one-Semiringᵉ :
    is-central-element-Semiringᵉ Rᵉ (one-Semiringᵉ Rᵉ)
  is-central-element-one-Semiringᵉ =
    is-central-element-unit-Monoidᵉ (multiplicative-monoid-Semiringᵉ Rᵉ)
```

### The sum of two central elements is central

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  is-central-element-add-Semiringᵉ :
    (xᵉ yᵉ : type-Semiringᵉ Rᵉ) → is-central-element-Semiringᵉ Rᵉ xᵉ →
    is-central-element-Semiringᵉ Rᵉ yᵉ →
    is-central-element-Semiringᵉ Rᵉ (add-Semiringᵉ Rᵉ xᵉ yᵉ)
  is-central-element-add-Semiringᵉ xᵉ yᵉ Hᵉ Kᵉ zᵉ =
    ( right-distributive-mul-add-Semiringᵉ Rᵉ xᵉ yᵉ zᵉ) ∙ᵉ
    ( ( ap-add-Semiringᵉ Rᵉ (Hᵉ zᵉ) (Kᵉ zᵉ)) ∙ᵉ
      ( invᵉ (left-distributive-mul-add-Semiringᵉ Rᵉ zᵉ xᵉ yᵉ)))
```

### The product of two central elements is central

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  is-central-element-mul-Semiringᵉ :
    (xᵉ yᵉ : type-Semiringᵉ Rᵉ) →
    is-central-element-Semiringᵉ Rᵉ xᵉ → is-central-element-Semiringᵉ Rᵉ yᵉ →
    is-central-element-Semiringᵉ Rᵉ (mul-Semiringᵉ Rᵉ xᵉ yᵉ)
  is-central-element-mul-Semiringᵉ =
    is-central-element-mul-Monoidᵉ (multiplicative-monoid-Semiringᵉ Rᵉ)
```