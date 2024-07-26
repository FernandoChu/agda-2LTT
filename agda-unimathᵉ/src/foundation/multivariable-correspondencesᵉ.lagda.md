# Multivariable correspondences

```agda
module foundation.multivariable-correspondencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Considerᵉ aᵉ familyᵉ ofᵉ typesᵉ `A`ᵉ indexedᵉ byᵉ `Finᵉ n`.ᵉ Anᵉ `n`-aryᵉ correspondenceᵉ ofᵉ
tuplesᵉ `(x₁,...,x_n)`ᵉ where `x_iᵉ : A_i`ᵉ isᵉ aᵉ typeᵉ familyᵉ overᵉ
`(iᵉ : Finᵉ nᵉ) → Aᵉ i`.ᵉ

## Definition

```agda
multivariable-correspondenceᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (nᵉ : ℕᵉ) (Aᵉ : Finᵉ nᵉ → UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
multivariable-correspondenceᵉ l2ᵉ nᵉ Aᵉ = ((iᵉ : Finᵉ nᵉ) → Aᵉ iᵉ) → UUᵉ l2ᵉ
```