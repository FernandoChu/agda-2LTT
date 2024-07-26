# Multisubsets

```agda
module foundation.multisubsetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.imagesᵉ
open import foundation.negated-equalityᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.setsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ multisubsetᵉ ofᵉ aᵉ givenᵉ setᵉ `U`ᵉ isᵉ aᵉ typeᵉ `B`ᵉ equippedᵉ with aᵉ functionᵉ
`fᵉ : Bᵉ → U`ᵉ

## Definition

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level)
  where

  multisubsetᵉ : Setᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  multisubsetᵉ Uᵉ = Σᵉ (UUᵉ l2ᵉ) (λ Bᵉ → Bᵉ → type-Setᵉ Uᵉ)

  is-locally-finite-multisubsetᵉ :
    (Uᵉ : Setᵉ l1ᵉ) → multisubsetᵉ Uᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-locally-finite-multisubsetᵉ Uᵉ (pairᵉ Bᵉ fᵉ) =
    (xᵉ : type-Setᵉ Uᵉ) → is-finiteᵉ (fiberᵉ fᵉ xᵉ)

  is-finite-multisubsetᵉ :
    (Uᵉ : Setᵉ l1ᵉ) → multisubsetᵉ Uᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-finite-multisubsetᵉ Uᵉ (pairᵉ Bᵉ fᵉ) = is-finiteᵉ (imᵉ fᵉ)

module _
  {l1ᵉ : Level}
  where

  locally-finite-multisubsetᵉ : Setᵉ l1ᵉ → UUᵉ l1ᵉ
  locally-finite-multisubsetᵉ Uᵉ = type-Setᵉ Uᵉ → ℕᵉ

  support-locally-finite-multisubsetᵉ :
    (Uᵉ : Setᵉ l1ᵉ) → locally-finite-multisubsetᵉ Uᵉ → UUᵉ l1ᵉ
  support-locally-finite-multisubsetᵉ Uᵉ μᵉ =
    Σᵉ (type-Setᵉ Uᵉ) (λ xᵉ → μᵉ xᵉ ≠ᵉ 0ᵉ)

  is-finite-locally-finite-multisubsetᵉ :
    (Uᵉ : Setᵉ l1ᵉ) → locally-finite-multisubsetᵉ Uᵉ → UUᵉ l1ᵉ
  is-finite-locally-finite-multisubsetᵉ Uᵉ μᵉ =
    is-finiteᵉ (support-locally-finite-multisubsetᵉ Uᵉ μᵉ)
```