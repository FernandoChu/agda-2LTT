# Nil ideals of rings

```agda
module ring-theory.nil-ideals-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.ideals-ringsᵉ
open import ring-theory.left-ideals-ringsᵉ
open import ring-theory.nilpotent-elements-ringsᵉ
open import ring-theory.right-ideals-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Aᵉ nilᵉ idealᵉ in aᵉ ringᵉ isᵉ anᵉ idealᵉ in whichᵉ everyᵉ elementᵉ isᵉ nilpotentᵉ

## Definition

### Nil left ideals

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  is-nil-left-ideal-ring-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-nil-left-ideal-ring-Propᵉ =
    Π-Propᵉ
      ( type-left-ideal-Ringᵉ Rᵉ Iᵉ)
      ( λ xᵉ →
        is-nilpotent-element-ring-Propᵉ Rᵉ (inclusion-left-ideal-Ringᵉ Rᵉ Iᵉ xᵉ))

  is-nil-left-ideal-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-nil-left-ideal-Ringᵉ = type-Propᵉ is-nil-left-ideal-ring-Propᵉ

  is-prop-is-nil-left-ideal-Ringᵉ : is-propᵉ is-nil-left-ideal-Ringᵉ
  is-prop-is-nil-left-ideal-Ringᵉ =
    is-prop-type-Propᵉ is-nil-left-ideal-ring-Propᵉ
```

### Nil right ideals

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  is-nil-right-ideal-ring-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-nil-right-ideal-ring-Propᵉ =
    Π-Propᵉ
      ( type-right-ideal-Ringᵉ Rᵉ Iᵉ)
      ( λ xᵉ →
        is-nilpotent-element-ring-Propᵉ Rᵉ (inclusion-right-ideal-Ringᵉ Rᵉ Iᵉ xᵉ))

  is-nil-right-ideal-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-nil-right-ideal-Ringᵉ = type-Propᵉ is-nil-right-ideal-ring-Propᵉ

  is-prop-is-nil-right-ideal-Ringᵉ : is-propᵉ is-nil-right-ideal-Ringᵉ
  is-prop-is-nil-right-ideal-Ringᵉ =
    is-prop-type-Propᵉ is-nil-right-ideal-ring-Propᵉ
```

### Nil ideals

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  is-nil-ideal-ring-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-nil-ideal-ring-Propᵉ =
    Π-Propᵉ
      ( type-ideal-Ringᵉ Rᵉ Iᵉ)
      ( λ xᵉ →
        is-nilpotent-element-ring-Propᵉ Rᵉ (inclusion-ideal-Ringᵉ Rᵉ Iᵉ xᵉ))

  is-nil-ideal-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-nil-ideal-Ringᵉ = type-Propᵉ is-nil-ideal-ring-Propᵉ

  is-prop-is-nil-ideal-Ringᵉ : is-propᵉ is-nil-ideal-Ringᵉ
  is-prop-is-nil-ideal-Ringᵉ =
    is-prop-type-Propᵉ is-nil-ideal-ring-Propᵉ
```