# The group of integers

```agda
module elementary-number-theory.group-of-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.integersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ integers,ᵉ equippedᵉ with aᵉ zero-element,ᵉ addition,ᵉ andᵉ negatives,ᵉ
formsᵉ aᵉ group.ᵉ

## Definition

```agda
ℤ-Semigroupᵉ : Semigroupᵉ lzero
pr1ᵉ ℤ-Semigroupᵉ = ℤ-Setᵉ
pr1ᵉ (pr2ᵉ ℤ-Semigroupᵉ) = add-ℤᵉ
pr2ᵉ (pr2ᵉ ℤ-Semigroupᵉ) = associative-add-ℤᵉ

ℤ-Groupᵉ : Groupᵉ lzero
pr1ᵉ ℤ-Groupᵉ = ℤ-Semigroupᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ ℤ-Groupᵉ)) = zero-ℤᵉ
pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ ℤ-Groupᵉ))) = left-unit-law-add-ℤᵉ
pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ ℤ-Groupᵉ))) = right-unit-law-add-ℤᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ ℤ-Groupᵉ)) = neg-ℤᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ℤ-Groupᵉ))) = left-inverse-law-add-ℤᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ℤ-Groupᵉ))) = right-inverse-law-add-ℤᵉ

ℤ-Abᵉ : Abᵉ lzero
pr1ᵉ ℤ-Abᵉ = ℤ-Groupᵉ
pr2ᵉ ℤ-Abᵉ = commutative-add-ℤᵉ
```