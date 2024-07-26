# Equivalences between standard finite types

```agda
module univalent-combinatorics.equivalences-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.exponentiation-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.contractible-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-coproduct-typesᵉ
open import foundation.universal-property-empty-typeᵉ
open import foundation.universal-property-unit-typeᵉ

open import univalent-combinatorics.cartesian-product-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Weᵉ constructᵉ **equivalences**ᵉ betweenᵉ (typesᵉ builtᵉ outᵉ ofᵉ)
[standardᵉ finiteᵉ types](univalent-combinatorics.standard-finite-types.md).ᵉ

### The standard finite types are closed under function types

```agda
function-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) → (Finᵉ kᵉ → Finᵉ lᵉ) ≃ᵉ Finᵉ (exp-ℕᵉ lᵉ kᵉ)
function-Finᵉ zero-ℕᵉ lᵉ =
  ( inv-left-unit-law-coproductᵉ unitᵉ) ∘eᵉ
  ( equiv-is-contrᵉ (universal-property-empty'ᵉ (Finᵉ lᵉ)) is-contr-unitᵉ)
function-Finᵉ (succ-ℕᵉ kᵉ) lᵉ =
  ( product-Finᵉ (exp-ℕᵉ lᵉ kᵉ) lᵉ) ∘eᵉ
  ( equiv-productᵉ (function-Finᵉ kᵉ lᵉ) (equiv-universal-property-unitᵉ (Finᵉ lᵉ))) ∘eᵉ
  ( equiv-universal-property-coproductᵉ (Finᵉ lᵉ))

Fin-exp-ℕᵉ : (kᵉ lᵉ : ℕᵉ) → Finᵉ (exp-ℕᵉ lᵉ kᵉ) ≃ᵉ (Finᵉ kᵉ → Finᵉ lᵉ)
Fin-exp-ℕᵉ kᵉ lᵉ = inv-equivᵉ (function-Finᵉ kᵉ lᵉ)
```