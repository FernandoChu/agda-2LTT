# Directed families in posets

```agda
module order-theory.directed-familiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.conjunctionᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.inhabited-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universal-quantificationᵉ
open import foundation.universe-levelsᵉ

open import order-theory.posetsᵉ
```

</details>

## Idea

Aᵉ **directedᵉ familyᵉ ofᵉ elements**ᵉ in aᵉ posetᵉ `P`ᵉ consistsᵉ ofᵉ anᵉ inhabitedᵉ typeᵉ
`I`ᵉ andᵉ aᵉ mapᵉ `xᵉ : Iᵉ → P`ᵉ suchᵉ thatᵉ forᵉ anyᵉ twoᵉ elementsᵉ `iᵉ jᵉ : I`ᵉ thereᵉ existsᵉ
anᵉ elementᵉ `kᵉ : I`ᵉ suchᵉ thatᵉ bothᵉ `xᵉ iᵉ ≤ᵉ xᵉ k`ᵉ andᵉ `xᵉ jᵉ ≤ᵉ xᵉ k`ᵉ hold.ᵉ

## Definition

```agda
is-directed-family-Poset-Propᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Iᵉ : Inhabited-Typeᵉ l3ᵉ)
  (xᵉ : type-Inhabited-Typeᵉ Iᵉ → type-Posetᵉ Pᵉ) → Propᵉ (l2ᵉ ⊔ l3ᵉ)
is-directed-family-Poset-Propᵉ Pᵉ Iᵉ xᵉ =
  ∀'ᵉ
    ( type-Inhabited-Typeᵉ Iᵉ)
    ( λ iᵉ →
      ∀'ᵉ
        ( type-Inhabited-Typeᵉ Iᵉ)
        ( λ jᵉ →
          ∃ᵉ ( type-Inhabited-Typeᵉ Iᵉ)
            ( λ kᵉ →
              leq-Poset-Propᵉ Pᵉ (xᵉ iᵉ) (xᵉ kᵉ) ∧ᵉ leq-Poset-Propᵉ Pᵉ (xᵉ jᵉ) (xᵉ kᵉ))))

is-directed-family-Posetᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Iᵉ : Inhabited-Typeᵉ l3ᵉ)
  (αᵉ : type-Inhabited-Typeᵉ Iᵉ → type-Posetᵉ Pᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
is-directed-family-Posetᵉ Pᵉ Iᵉ xᵉ = type-Propᵉ (is-directed-family-Poset-Propᵉ Pᵉ Iᵉ xᵉ)

directed-family-Posetᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) → Posetᵉ l1ᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
directed-family-Posetᵉ l3ᵉ Pᵉ =
  Σᵉ ( Inhabited-Typeᵉ l3ᵉ)
    ( λ Iᵉ →
      Σᵉ ( type-Inhabited-Typeᵉ Iᵉ → type-Posetᵉ Pᵉ)
        ( is-directed-family-Posetᵉ Pᵉ Iᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (xᵉ : directed-family-Posetᵉ l3ᵉ Pᵉ)
  where

  inhabited-type-directed-family-Posetᵉ : Inhabited-Typeᵉ l3ᵉ
  inhabited-type-directed-family-Posetᵉ = pr1ᵉ xᵉ

  type-directed-family-Posetᵉ : UUᵉ l3ᵉ
  type-directed-family-Posetᵉ =
    type-Inhabited-Typeᵉ inhabited-type-directed-family-Posetᵉ

  is-inhabited-type-directed-family-Posetᵉ :
    is-inhabitedᵉ type-directed-family-Posetᵉ
  is-inhabited-type-directed-family-Posetᵉ =
    is-inhabited-type-Inhabited-Typeᵉ inhabited-type-directed-family-Posetᵉ

  family-directed-family-Posetᵉ : type-directed-family-Posetᵉ → type-Posetᵉ Pᵉ
  family-directed-family-Posetᵉ = pr1ᵉ (pr2ᵉ xᵉ)

  is-directed-family-directed-family-Posetᵉ :
    is-directed-family-Posetᵉ Pᵉ
      ( inhabited-type-directed-family-Posetᵉ)
      ( family-directed-family-Posetᵉ)
  is-directed-family-directed-family-Posetᵉ = pr2ᵉ (pr2ᵉ xᵉ)
```