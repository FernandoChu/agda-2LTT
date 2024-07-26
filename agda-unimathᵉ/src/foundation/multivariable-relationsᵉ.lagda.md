# Multivariable relations

```agda
module foundation.multivariable-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.multivariable-correspondencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.subtypesᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ `n`-aryᵉ relationᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ subtypeᵉ ofᵉ `Finᵉ nᵉ → A`.ᵉ

## Definition

```agda
multivariable-relationᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (nᵉ : ℕᵉ) (Aᵉ : Finᵉ nᵉ → UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
multivariable-relationᵉ l2ᵉ nᵉ Aᵉ = subtypeᵉ l2ᵉ ((iᵉ : Finᵉ nᵉ) → Aᵉ iᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {nᵉ : ℕᵉ} {Aᵉ : Finᵉ nᵉ → UUᵉ l1ᵉ}
  (Rᵉ : multivariable-relationᵉ l2ᵉ nᵉ Aᵉ)
  where

  multivariable-correspondence-multivariable-relationᵉ :
    multivariable-correspondenceᵉ l2ᵉ nᵉ Aᵉ
  multivariable-correspondence-multivariable-relationᵉ =
    is-in-subtypeᵉ Rᵉ
```