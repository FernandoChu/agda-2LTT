# Central elements of monoids

```agda
module group-theory.central-elements-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.central-elements-semigroupsᵉ
open import group-theory.monoidsᵉ
```

</details>

## Idea

Anᵉ elementᵉ `x`ᵉ ofᵉ aᵉ monoidᵉ `M`ᵉ isᵉ saidᵉ to beᵉ centralᵉ ifᵉ `xyᵉ ＝ᵉ yx`ᵉ forᵉ everyᵉ
`yᵉ : M`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  is-central-element-prop-Monoidᵉ : type-Monoidᵉ Mᵉ → Propᵉ lᵉ
  is-central-element-prop-Monoidᵉ =
    is-central-element-prop-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)

  is-central-element-Monoidᵉ : type-Monoidᵉ Mᵉ → UUᵉ lᵉ
  is-central-element-Monoidᵉ =
    is-central-element-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)

  is-prop-is-central-element-Monoidᵉ :
    (xᵉ : type-Monoidᵉ Mᵉ) → is-propᵉ (is-central-element-Monoidᵉ xᵉ)
  is-prop-is-central-element-Monoidᵉ =
    is-prop-is-central-element-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)
```

## Properties

### The unit element is central

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  is-central-element-unit-Monoidᵉ : is-central-element-Monoidᵉ Mᵉ (unit-Monoidᵉ Mᵉ)
  is-central-element-unit-Monoidᵉ yᵉ =
    left-unit-law-mul-Monoidᵉ Mᵉ yᵉ ∙ᵉ invᵉ (right-unit-law-mul-Monoidᵉ Mᵉ yᵉ)
```

### The product of two central elements is central

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  is-central-element-mul-Monoidᵉ :
    (xᵉ yᵉ : type-Monoidᵉ Mᵉ) →
    is-central-element-Monoidᵉ Mᵉ xᵉ → is-central-element-Monoidᵉ Mᵉ yᵉ →
    is-central-element-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ)
  is-central-element-mul-Monoidᵉ =
    is-central-element-mul-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)
```