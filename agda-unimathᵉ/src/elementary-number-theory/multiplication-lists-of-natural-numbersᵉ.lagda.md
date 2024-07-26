# Multiplication of the elements of a list of natural numbers

```agda
module elementary-number-theory.multiplication-lists-of-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.permutations-standard-finite-typesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.identity-typesᵉ

open import lists.concatenation-listsᵉ
open import lists.listsᵉ
open import lists.permutation-listsᵉ
```

</details>

## Idea

Givenᵉ aᵉ listᵉ ofᵉ naturalᵉ numberᵉ `l`,ᵉ weᵉ defineᵉ theᵉ productᵉ ofᵉ theᵉ elementᵉ ofᵉ theᵉ
list.ᵉ

## Definition

```agda
mul-list-ℕᵉ :
  listᵉ ℕᵉ → ℕᵉ
mul-list-ℕᵉ = fold-listᵉ 1 mul-ℕᵉ
```

## Properties

### `mul-list-ℕ` is invariant by permutation

```agda
invariant-permutation-mul-list-ℕᵉ :
  (lᵉ : listᵉ ℕᵉ) (tᵉ : Permutationᵉ (length-listᵉ lᵉ)) →
  mul-list-ℕᵉ lᵉ ＝ᵉ mul-list-ℕᵉ (permute-listᵉ lᵉ tᵉ)
invariant-permutation-mul-list-ℕᵉ =
  invariant-permutation-fold-listᵉ
    ( 1ᵉ)
    ( mul-ℕᵉ)
    ( λ a1ᵉ a2ᵉ bᵉ →
      ( invᵉ (associative-mul-ℕᵉ a1ᵉ a2ᵉ bᵉ) ∙ᵉ
        ( apᵉ (λ nᵉ → nᵉ *ℕᵉ bᵉ) (commutative-mul-ℕᵉ a1ᵉ a2ᵉ) ∙ᵉ
          ( associative-mul-ℕᵉ a2ᵉ a1ᵉ bᵉ))))
```

### `mul-list-ℕ` of a concatenation of lists

```agda
eq-mul-list-concat-list-ℕᵉ :
  (pᵉ qᵉ : listᵉ ℕᵉ) →
  (mul-list-ℕᵉ (concat-listᵉ pᵉ qᵉ)) ＝ᵉ (mul-list-ℕᵉ pᵉ) *ℕᵉ (mul-list-ℕᵉ qᵉ)
eq-mul-list-concat-list-ℕᵉ nilᵉ qᵉ = invᵉ (left-unit-law-add-ℕᵉ (mul-list-ℕᵉ qᵉ))
eq-mul-list-concat-list-ℕᵉ (consᵉ xᵉ pᵉ) qᵉ =
  apᵉ (mul-ℕᵉ xᵉ) (eq-mul-list-concat-list-ℕᵉ pᵉ qᵉ) ∙ᵉ
  invᵉ (associative-mul-ℕᵉ xᵉ (mul-list-ℕᵉ pᵉ) (mul-list-ℕᵉ qᵉ))
```