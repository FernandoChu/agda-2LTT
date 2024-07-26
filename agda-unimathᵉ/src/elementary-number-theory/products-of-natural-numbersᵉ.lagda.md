# Products of natural numbers

```agda
module elementary-number-theory.products-of-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.unit-typeᵉ

open import lists.listsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ productᵉ ofᵉ aᵉ listᵉ ofᵉ naturalᵉ numbersᵉ isᵉ definedᵉ byᵉ iteratedᵉ multiplication.ᵉ

## Definitions

### Products of lists of natural numbers

```agda
product-list-ℕᵉ : listᵉ ℕᵉ → ℕᵉ
product-list-ℕᵉ = fold-listᵉ 1 mul-ℕᵉ
```

### Products of families of natural numbers indexed by standard finite types

```agda
Π-ℕᵉ : (kᵉ : ℕᵉ) → (Finᵉ kᵉ → ℕᵉ) → ℕᵉ
Π-ℕᵉ zero-ℕᵉ xᵉ = 1
Π-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ = (Π-ℕᵉ kᵉ (λ iᵉ → xᵉ (inlᵉ iᵉ))) *ℕᵉ (xᵉ (inrᵉ starᵉ))
```