# Locally finite posets

```agda
module order-theory.locally-finite-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.finite-posetsᵉ
open import order-theory.interval-subposetsᵉ
open import order-theory.posetsᵉ
```

</details>

## Idea

Aᵉ posetᵉ `X`ᵉ isᵉ saidᵉ to beᵉ **locallyᵉ finite**ᵉ ifᵉ forᵉ everyᵉ `x,ᵉ yᵉ ∈ᵉ X`,ᵉ theᵉ
[intervalᵉ subposet](order-theory.interval-subposets.mdᵉ) `[x,ᵉ y]`ᵉ consistingᵉ ofᵉ
`zᵉ : X`ᵉ suchᵉ thatᵉ `xᵉ ≤ᵉ zᵉ ≤ᵉ y`,ᵉ isᵉ finite.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  is-locally-finite-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-locally-finite-Poset-Propᵉ =
    Π-Propᵉ
      ( type-Posetᵉ Xᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( type-Posetᵉ Xᵉ)
          ( λ yᵉ →
            is-finite-Poset-Propᵉ (poset-interval-Subposetᵉ Xᵉ xᵉ yᵉ)))

  is-locally-finite-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-locally-finite-Posetᵉ = type-Propᵉ is-locally-finite-Poset-Propᵉ

  is-prop-is-locally-finite-Posetᵉ : is-propᵉ is-locally-finite-Posetᵉ
  is-prop-is-locally-finite-Posetᵉ =
    is-prop-type-Propᵉ is-locally-finite-Poset-Propᵉ
```