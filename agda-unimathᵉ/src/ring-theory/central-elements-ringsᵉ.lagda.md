# Central elements of rings

```agda
module ring-theory.central-elements-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.central-elements-semiringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Anᵉ elementᵉ `x`ᵉ ofᵉ aᵉ ringᵉ `R`ᵉ isᵉ saidᵉ to beᵉ centralᵉ ifᵉ `xyᵉ ＝ᵉ yx`ᵉ forᵉ everyᵉ
`yᵉ : R`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-central-element-ring-Propᵉ : type-Ringᵉ Rᵉ → Propᵉ lᵉ
  is-central-element-ring-Propᵉ =
    is-central-element-semiring-Propᵉ (semiring-Ringᵉ Rᵉ)

  is-central-element-Ringᵉ : type-Ringᵉ Rᵉ → UUᵉ lᵉ
  is-central-element-Ringᵉ = is-central-element-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  is-prop-is-central-element-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → is-propᵉ (is-central-element-Ringᵉ xᵉ)
  is-prop-is-central-element-Ringᵉ =
    is-prop-is-central-element-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

## Properties

### The zero element is central

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-central-element-zero-Ringᵉ : is-central-element-Ringᵉ Rᵉ (zero-Ringᵉ Rᵉ)
  is-central-element-zero-Ringᵉ =
    is-central-element-zero-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### The unit element is central

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-central-element-one-Ringᵉ : is-central-element-Ringᵉ Rᵉ (one-Ringᵉ Rᵉ)
  is-central-element-one-Ringᵉ =
    is-central-element-one-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### The sum of two central elements is central

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-central-element-add-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) → is-central-element-Ringᵉ Rᵉ xᵉ →
    is-central-element-Ringᵉ Rᵉ yᵉ → is-central-element-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ xᵉ yᵉ)
  is-central-element-add-Ringᵉ =
    is-central-element-add-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### The negative of a central element is central

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-central-element-neg-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → is-central-element-Ringᵉ Rᵉ xᵉ →
    is-central-element-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ)
  is-central-element-neg-Ringᵉ xᵉ Hᵉ yᵉ =
    ( left-negative-law-mul-Ringᵉ Rᵉ xᵉ yᵉ) ∙ᵉ
    ( ( apᵉ (neg-Ringᵉ Rᵉ) (Hᵉ yᵉ)) ∙ᵉ
      ( invᵉ (right-negative-law-mul-Ringᵉ Rᵉ yᵉ xᵉ)))
```

### `-1` is a central element

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-central-element-neg-one-Ringᵉ :
    is-central-element-Ringᵉ Rᵉ (neg-one-Ringᵉ Rᵉ)
  is-central-element-neg-one-Ringᵉ =
    is-central-element-neg-Ringᵉ Rᵉ (one-Ringᵉ Rᵉ) (is-central-element-one-Ringᵉ Rᵉ)
```

### The product of two central elements is central

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-central-element-mul-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) → is-central-element-Ringᵉ Rᵉ xᵉ →
    is-central-element-Ringᵉ Rᵉ yᵉ → is-central-element-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)
  is-central-element-mul-Ringᵉ =
    is-central-element-mul-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```