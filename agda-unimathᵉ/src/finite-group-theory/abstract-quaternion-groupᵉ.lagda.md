# The abstract quaternion group of order `8`

```agda
module finite-group-theory.abstract-quaternion-groupᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.semigroupsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ abstract quaternionᵉ groupᵉ ofᵉ orderᵉ 8 isᵉ theᵉ groupᵉ ofᵉ theᵉ quaternionsᵉ `1`,ᵉ
`-1`,ᵉ `i`,ᵉ `-i`,ᵉ `j`,ᵉ `-j`,ᵉ `k`,ᵉ andᵉ `-k`.ᵉ

## Definition

```agda
data Q8ᵉ : UUᵉ lzero where
  e-Q8ᵉ : Q8ᵉ
  -e-Q8ᵉ : Q8ᵉ
  i-Q8ᵉ : Q8ᵉ
  -i-Q8ᵉ : Q8ᵉ
  j-Q8ᵉ : Q8ᵉ
  -j-Q8ᵉ : Q8ᵉ
  k-Q8ᵉ : Q8ᵉ
  -k-Q8ᵉ : Q8ᵉ

mul-Q8ᵉ : Q8ᵉ → Q8ᵉ → Q8ᵉ
mul-Q8ᵉ e-Q8ᵉ e-Q8ᵉ = e-Q8ᵉ
mul-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ = -e-Q8ᵉ
mul-Q8ᵉ e-Q8ᵉ i-Q8ᵉ = i-Q8ᵉ
mul-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ = -i-Q8ᵉ
mul-Q8ᵉ e-Q8ᵉ j-Q8ᵉ = j-Q8ᵉ
mul-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ = -j-Q8ᵉ
mul-Q8ᵉ e-Q8ᵉ k-Q8ᵉ = k-Q8ᵉ
mul-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ = -k-Q8ᵉ
mul-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ = -e-Q8ᵉ
mul-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ = e-Q8ᵉ
mul-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ = -i-Q8ᵉ
mul-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ = i-Q8ᵉ
mul-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ = -j-Q8ᵉ
mul-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ = j-Q8ᵉ
mul-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ = -k-Q8ᵉ
mul-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ = k-Q8ᵉ
mul-Q8ᵉ i-Q8ᵉ e-Q8ᵉ = i-Q8ᵉ
mul-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ = -i-Q8ᵉ
mul-Q8ᵉ i-Q8ᵉ i-Q8ᵉ = -e-Q8ᵉ
mul-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ = e-Q8ᵉ
mul-Q8ᵉ i-Q8ᵉ j-Q8ᵉ = k-Q8ᵉ
mul-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ = -k-Q8ᵉ
mul-Q8ᵉ i-Q8ᵉ k-Q8ᵉ = -j-Q8ᵉ
mul-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ = j-Q8ᵉ
mul-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ = -i-Q8ᵉ
mul-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ = i-Q8ᵉ
mul-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ = e-Q8ᵉ
mul-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ = -e-Q8ᵉ
mul-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ = -k-Q8ᵉ
mul-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ = k-Q8ᵉ
mul-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ = j-Q8ᵉ
mul-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ = -j-Q8ᵉ
mul-Q8ᵉ j-Q8ᵉ e-Q8ᵉ = j-Q8ᵉ
mul-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ = -j-Q8ᵉ
mul-Q8ᵉ j-Q8ᵉ i-Q8ᵉ = -k-Q8ᵉ
mul-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ = k-Q8ᵉ
mul-Q8ᵉ j-Q8ᵉ j-Q8ᵉ = -e-Q8ᵉ
mul-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ = e-Q8ᵉ
mul-Q8ᵉ j-Q8ᵉ k-Q8ᵉ = i-Q8ᵉ
mul-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ = -i-Q8ᵉ
mul-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ = -j-Q8ᵉ
mul-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ = j-Q8ᵉ
mul-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ = k-Q8ᵉ
mul-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ = -k-Q8ᵉ
mul-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ = e-Q8ᵉ
mul-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ = -e-Q8ᵉ
mul-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ = -i-Q8ᵉ
mul-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ = i-Q8ᵉ
mul-Q8ᵉ k-Q8ᵉ e-Q8ᵉ = k-Q8ᵉ
mul-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ = -k-Q8ᵉ
mul-Q8ᵉ k-Q8ᵉ i-Q8ᵉ = j-Q8ᵉ
mul-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ = -j-Q8ᵉ
mul-Q8ᵉ k-Q8ᵉ j-Q8ᵉ = -i-Q8ᵉ
mul-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ = i-Q8ᵉ
mul-Q8ᵉ k-Q8ᵉ k-Q8ᵉ = -e-Q8ᵉ
mul-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ = e-Q8ᵉ
mul-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ = -k-Q8ᵉ
mul-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ = k-Q8ᵉ
mul-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ = -j-Q8ᵉ
mul-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ = j-Q8ᵉ
mul-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ = i-Q8ᵉ
mul-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ = -i-Q8ᵉ
mul-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ = e-Q8ᵉ
mul-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ = -e-Q8ᵉ

inv-Q8ᵉ : Q8ᵉ → Q8ᵉ
inv-Q8ᵉ e-Q8ᵉ = e-Q8ᵉ
inv-Q8ᵉ -e-Q8ᵉ = -e-Q8ᵉ
inv-Q8ᵉ i-Q8ᵉ = -i-Q8ᵉ
inv-Q8ᵉ -i-Q8ᵉ = i-Q8ᵉ
inv-Q8ᵉ j-Q8ᵉ = -j-Q8ᵉ
inv-Q8ᵉ -j-Q8ᵉ = j-Q8ᵉ
inv-Q8ᵉ k-Q8ᵉ = -k-Q8ᵉ
inv-Q8ᵉ -k-Q8ᵉ = k-Q8ᵉ

left-unit-law-mul-Q8ᵉ : (xᵉ : Q8ᵉ) → Idᵉ (mul-Q8ᵉ e-Q8ᵉ xᵉ) xᵉ
left-unit-law-mul-Q8ᵉ e-Q8ᵉ = reflᵉ
left-unit-law-mul-Q8ᵉ -e-Q8ᵉ = reflᵉ
left-unit-law-mul-Q8ᵉ i-Q8ᵉ = reflᵉ
left-unit-law-mul-Q8ᵉ -i-Q8ᵉ = reflᵉ
left-unit-law-mul-Q8ᵉ j-Q8ᵉ = reflᵉ
left-unit-law-mul-Q8ᵉ -j-Q8ᵉ = reflᵉ
left-unit-law-mul-Q8ᵉ k-Q8ᵉ = reflᵉ
left-unit-law-mul-Q8ᵉ -k-Q8ᵉ = reflᵉ

right-unit-law-mul-Q8ᵉ : (xᵉ : Q8ᵉ) → Idᵉ (mul-Q8ᵉ xᵉ e-Q8ᵉ) xᵉ
right-unit-law-mul-Q8ᵉ e-Q8ᵉ = reflᵉ
right-unit-law-mul-Q8ᵉ -e-Q8ᵉ = reflᵉ
right-unit-law-mul-Q8ᵉ i-Q8ᵉ = reflᵉ
right-unit-law-mul-Q8ᵉ -i-Q8ᵉ = reflᵉ
right-unit-law-mul-Q8ᵉ j-Q8ᵉ = reflᵉ
right-unit-law-mul-Q8ᵉ -j-Q8ᵉ = reflᵉ
right-unit-law-mul-Q8ᵉ k-Q8ᵉ = reflᵉ
right-unit-law-mul-Q8ᵉ -k-Q8ᵉ = reflᵉ

associative-mul-Q8ᵉ :
  (xᵉ yᵉ zᵉ : Q8ᵉ) → Idᵉ (mul-Q8ᵉ (mul-Q8ᵉ xᵉ yᵉ) zᵉ) (mul-Q8ᵉ xᵉ (mul-Q8ᵉ yᵉ zᵉ))
associative-mul-Q8ᵉ e-Q8ᵉ e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ = reflᵉ
associative-mul-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ = reflᵉ

left-inverse-law-mul-Q8ᵉ : (xᵉ : Q8ᵉ) → Idᵉ (mul-Q8ᵉ (inv-Q8ᵉ xᵉ) xᵉ) e-Q8ᵉ
left-inverse-law-mul-Q8ᵉ e-Q8ᵉ = reflᵉ
left-inverse-law-mul-Q8ᵉ -e-Q8ᵉ = reflᵉ
left-inverse-law-mul-Q8ᵉ i-Q8ᵉ = reflᵉ
left-inverse-law-mul-Q8ᵉ -i-Q8ᵉ = reflᵉ
left-inverse-law-mul-Q8ᵉ j-Q8ᵉ = reflᵉ
left-inverse-law-mul-Q8ᵉ -j-Q8ᵉ = reflᵉ
left-inverse-law-mul-Q8ᵉ k-Q8ᵉ = reflᵉ
left-inverse-law-mul-Q8ᵉ -k-Q8ᵉ = reflᵉ

right-inverse-law-mul-Q8ᵉ : (xᵉ : Q8ᵉ) → Idᵉ (mul-Q8ᵉ xᵉ (inv-Q8ᵉ xᵉ)) e-Q8ᵉ
right-inverse-law-mul-Q8ᵉ e-Q8ᵉ = reflᵉ
right-inverse-law-mul-Q8ᵉ -e-Q8ᵉ = reflᵉ
right-inverse-law-mul-Q8ᵉ i-Q8ᵉ = reflᵉ
right-inverse-law-mul-Q8ᵉ -i-Q8ᵉ = reflᵉ
right-inverse-law-mul-Q8ᵉ j-Q8ᵉ = reflᵉ
right-inverse-law-mul-Q8ᵉ -j-Q8ᵉ = reflᵉ
right-inverse-law-mul-Q8ᵉ k-Q8ᵉ = reflᵉ
right-inverse-law-mul-Q8ᵉ -k-Q8ᵉ = reflᵉ

Eq-Q8ᵉ : Q8ᵉ → Q8ᵉ → UUᵉ lzero
Eq-Q8ᵉ e-Q8ᵉ e-Q8ᵉ = unitᵉ
Eq-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ e-Q8ᵉ i-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ e-Q8ᵉ j-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ e-Q8ᵉ k-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ = unitᵉ
Eq-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ i-Q8ᵉ e-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ i-Q8ᵉ i-Q8ᵉ = unitᵉ
Eq-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ i-Q8ᵉ j-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ i-Q8ᵉ k-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ = unitᵉ
Eq-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ j-Q8ᵉ e-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ j-Q8ᵉ i-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ j-Q8ᵉ j-Q8ᵉ = unitᵉ
Eq-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ j-Q8ᵉ k-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ = unitᵉ
Eq-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ k-Q8ᵉ e-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ k-Q8ᵉ i-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ k-Q8ᵉ j-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ k-Q8ᵉ k-Q8ᵉ = unitᵉ
Eq-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ = emptyᵉ
Eq-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ = unitᵉ

refl-Eq-Q8ᵉ : (xᵉ : Q8ᵉ) → Eq-Q8ᵉ xᵉ xᵉ
refl-Eq-Q8ᵉ e-Q8ᵉ = starᵉ
refl-Eq-Q8ᵉ -e-Q8ᵉ = starᵉ
refl-Eq-Q8ᵉ i-Q8ᵉ = starᵉ
refl-Eq-Q8ᵉ -i-Q8ᵉ = starᵉ
refl-Eq-Q8ᵉ j-Q8ᵉ = starᵉ
refl-Eq-Q8ᵉ -j-Q8ᵉ = starᵉ
refl-Eq-Q8ᵉ k-Q8ᵉ = starᵉ
refl-Eq-Q8ᵉ -k-Q8ᵉ = starᵉ

Eq-eq-Q8ᵉ : {xᵉ yᵉ : Q8ᵉ} → Idᵉ xᵉ yᵉ → Eq-Q8ᵉ xᵉ yᵉ
Eq-eq-Q8ᵉ {xᵉ} reflᵉ = refl-Eq-Q8ᵉ xᵉ

eq-Eq-Q8ᵉ : (xᵉ yᵉ : Q8ᵉ) → Eq-Q8ᵉ xᵉ yᵉ → Idᵉ xᵉ yᵉ
eq-Eq-Q8ᵉ e-Q8ᵉ e-Q8ᵉ eᵉ = reflᵉ
eq-Eq-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ eᵉ = reflᵉ
eq-Eq-Q8ᵉ i-Q8ᵉ i-Q8ᵉ eᵉ = reflᵉ
eq-Eq-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ eᵉ = reflᵉ
eq-Eq-Q8ᵉ j-Q8ᵉ j-Q8ᵉ eᵉ = reflᵉ
eq-Eq-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ eᵉ = reflᵉ
eq-Eq-Q8ᵉ k-Q8ᵉ k-Q8ᵉ eᵉ = reflᵉ
eq-Eq-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ eᵉ = reflᵉ

is-decidable-Eq-Q8ᵉ : (xᵉ yᵉ : Q8ᵉ) → is-decidableᵉ (Eq-Q8ᵉ xᵉ yᵉ)
is-decidable-Eq-Q8ᵉ e-Q8ᵉ e-Q8ᵉ = is-decidable-unitᵉ
is-decidable-Eq-Q8ᵉ e-Q8ᵉ -e-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ e-Q8ᵉ i-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ e-Q8ᵉ -i-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ e-Q8ᵉ j-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ e-Q8ᵉ -j-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ e-Q8ᵉ k-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ e-Q8ᵉ -k-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -e-Q8ᵉ e-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -e-Q8ᵉ -e-Q8ᵉ = is-decidable-unitᵉ
is-decidable-Eq-Q8ᵉ -e-Q8ᵉ i-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -e-Q8ᵉ -i-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -e-Q8ᵉ j-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -e-Q8ᵉ -j-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -e-Q8ᵉ k-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -e-Q8ᵉ -k-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ i-Q8ᵉ e-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ i-Q8ᵉ -e-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ i-Q8ᵉ i-Q8ᵉ = is-decidable-unitᵉ
is-decidable-Eq-Q8ᵉ i-Q8ᵉ -i-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ i-Q8ᵉ j-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ i-Q8ᵉ -j-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ i-Q8ᵉ k-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ i-Q8ᵉ -k-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -i-Q8ᵉ e-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -i-Q8ᵉ -e-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -i-Q8ᵉ i-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -i-Q8ᵉ -i-Q8ᵉ = is-decidable-unitᵉ
is-decidable-Eq-Q8ᵉ -i-Q8ᵉ j-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -i-Q8ᵉ -j-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -i-Q8ᵉ k-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -i-Q8ᵉ -k-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ j-Q8ᵉ e-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ j-Q8ᵉ -e-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ j-Q8ᵉ i-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ j-Q8ᵉ -i-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ j-Q8ᵉ j-Q8ᵉ = is-decidable-unitᵉ
is-decidable-Eq-Q8ᵉ j-Q8ᵉ -j-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ j-Q8ᵉ k-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ j-Q8ᵉ -k-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -j-Q8ᵉ e-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -j-Q8ᵉ -e-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -j-Q8ᵉ i-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -j-Q8ᵉ -i-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -j-Q8ᵉ j-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -j-Q8ᵉ -j-Q8ᵉ = is-decidable-unitᵉ
is-decidable-Eq-Q8ᵉ -j-Q8ᵉ k-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -j-Q8ᵉ -k-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ k-Q8ᵉ e-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ k-Q8ᵉ -e-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ k-Q8ᵉ i-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ k-Q8ᵉ -i-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ k-Q8ᵉ j-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ k-Q8ᵉ -j-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ k-Q8ᵉ k-Q8ᵉ = is-decidable-unitᵉ
is-decidable-Eq-Q8ᵉ k-Q8ᵉ -k-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -k-Q8ᵉ e-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -k-Q8ᵉ -e-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -k-Q8ᵉ i-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -k-Q8ᵉ -i-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -k-Q8ᵉ j-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -k-Q8ᵉ -j-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -k-Q8ᵉ k-Q8ᵉ = is-decidable-emptyᵉ
is-decidable-Eq-Q8ᵉ -k-Q8ᵉ -k-Q8ᵉ = is-decidable-unitᵉ

has-decidable-equality-Q8ᵉ : has-decidable-equalityᵉ Q8ᵉ
has-decidable-equality-Q8ᵉ xᵉ yᵉ =
  is-decidable-iffᵉ
    ( eq-Eq-Q8ᵉ xᵉ yᵉ)
    ( Eq-eq-Q8ᵉ)
    ( is-decidable-Eq-Q8ᵉ xᵉ yᵉ)

is-set-Q8ᵉ : is-setᵉ Q8ᵉ
is-set-Q8ᵉ = is-set-has-decidable-equalityᵉ has-decidable-equality-Q8ᵉ

Q8-Setᵉ : Setᵉ lzero
Q8-Setᵉ = pairᵉ Q8ᵉ is-set-Q8ᵉ

Q8-Semigroupᵉ : Semigroupᵉ lzero
Q8-Semigroupᵉ = pairᵉ Q8-Setᵉ (pairᵉ mul-Q8ᵉ associative-mul-Q8ᵉ)

Q8-Groupᵉ : Groupᵉ lzero
Q8-Groupᵉ =
  pairᵉ
    Q8-Semigroupᵉ
    ( pairᵉ
      ( pairᵉ e-Q8ᵉ
        ( pairᵉ left-unit-law-mul-Q8ᵉ right-unit-law-mul-Q8ᵉ))
      ( pairᵉ inv-Q8ᵉ (pairᵉ left-inverse-law-mul-Q8ᵉ right-inverse-law-mul-Q8ᵉ)))

is-noncommutative-mul-Q8ᵉ :
  ¬ᵉ ((xᵉ yᵉ : Q8ᵉ) → Idᵉ (mul-Q8ᵉ xᵉ yᵉ) (mul-Q8ᵉ yᵉ xᵉ))
is-noncommutative-mul-Q8ᵉ fᵉ = Eq-eq-Q8ᵉ (fᵉ i-Q8ᵉ j-Q8ᵉ)

map-equiv-count-Q8ᵉ : Finᵉ 8 → Q8ᵉ
map-equiv-count-Q8ᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inrᵉ _)))))))) = e-Q8ᵉ
map-equiv-count-Q8ᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inrᵉ _))))))) = -e-Q8ᵉ
map-equiv-count-Q8ᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inrᵉ _)))))) = i-Q8ᵉ
map-equiv-count-Q8ᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inrᵉ _))))) = -i-Q8ᵉ
map-equiv-count-Q8ᵉ (inlᵉ (inlᵉ (inlᵉ (inrᵉ _)))) = j-Q8ᵉ
map-equiv-count-Q8ᵉ (inlᵉ (inlᵉ (inrᵉ _))) = -j-Q8ᵉ
map-equiv-count-Q8ᵉ (inlᵉ (inrᵉ _)) = k-Q8ᵉ
map-equiv-count-Q8ᵉ (inrᵉ _) = -k-Q8ᵉ

map-inv-equiv-count-Q8ᵉ : Q8ᵉ → Finᵉ 8
map-inv-equiv-count-Q8ᵉ e-Q8ᵉ = inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))))))
map-inv-equiv-count-Q8ᵉ -e-Q8ᵉ = inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ))))))
map-inv-equiv-count-Q8ᵉ i-Q8ᵉ = inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))))
map-inv-equiv-count-Q8ᵉ -i-Q8ᵉ = inlᵉ (inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ))))
map-inv-equiv-count-Q8ᵉ j-Q8ᵉ = inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))
map-inv-equiv-count-Q8ᵉ -j-Q8ᵉ = inlᵉ (inlᵉ (inrᵉ starᵉ))
map-inv-equiv-count-Q8ᵉ k-Q8ᵉ = inlᵉ (inrᵉ starᵉ)
map-inv-equiv-count-Q8ᵉ -k-Q8ᵉ = inrᵉ starᵉ

is-section-map-inv-equiv-count-Q8ᵉ :
  ( map-equiv-count-Q8ᵉ ∘ᵉ map-inv-equiv-count-Q8ᵉ) ~ᵉ idᵉ
is-section-map-inv-equiv-count-Q8ᵉ e-Q8ᵉ = reflᵉ
is-section-map-inv-equiv-count-Q8ᵉ -e-Q8ᵉ = reflᵉ
is-section-map-inv-equiv-count-Q8ᵉ i-Q8ᵉ = reflᵉ
is-section-map-inv-equiv-count-Q8ᵉ -i-Q8ᵉ = reflᵉ
is-section-map-inv-equiv-count-Q8ᵉ j-Q8ᵉ = reflᵉ
is-section-map-inv-equiv-count-Q8ᵉ -j-Q8ᵉ = reflᵉ
is-section-map-inv-equiv-count-Q8ᵉ k-Q8ᵉ = reflᵉ
is-section-map-inv-equiv-count-Q8ᵉ -k-Q8ᵉ = reflᵉ

is-retraction-map-inv-equiv-count-Q8ᵉ :
  ( map-inv-equiv-count-Q8ᵉ ∘ᵉ map-equiv-count-Q8ᵉ) ~ᵉ idᵉ
is-retraction-map-inv-equiv-count-Q8ᵉ
  (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inrᵉ _)))))))) = reflᵉ
is-retraction-map-inv-equiv-count-Q8ᵉ
  (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inrᵉ _))))))) = reflᵉ
is-retraction-map-inv-equiv-count-Q8ᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inrᵉ _)))))) =
  reflᵉ
is-retraction-map-inv-equiv-count-Q8ᵉ (inlᵉ (inlᵉ (inlᵉ (inlᵉ (inrᵉ _))))) = reflᵉ
is-retraction-map-inv-equiv-count-Q8ᵉ (inlᵉ (inlᵉ (inlᵉ (inrᵉ _)))) = reflᵉ
is-retraction-map-inv-equiv-count-Q8ᵉ (inlᵉ (inlᵉ (inrᵉ _))) = reflᵉ
is-retraction-map-inv-equiv-count-Q8ᵉ (inlᵉ (inrᵉ _)) = reflᵉ
is-retraction-map-inv-equiv-count-Q8ᵉ (inrᵉ _) = reflᵉ

is-equiv-map-equiv-count-Q8ᵉ : is-equivᵉ map-equiv-count-Q8ᵉ
is-equiv-map-equiv-count-Q8ᵉ =
  is-equiv-is-invertibleᵉ
    map-inv-equiv-count-Q8ᵉ
    is-section-map-inv-equiv-count-Q8ᵉ
    is-retraction-map-inv-equiv-count-Q8ᵉ

equiv-count-Q8ᵉ : Finᵉ 8 ≃ᵉ Q8ᵉ
equiv-count-Q8ᵉ = pairᵉ map-equiv-count-Q8ᵉ is-equiv-map-equiv-count-Q8ᵉ

count-Q8ᵉ : countᵉ Q8ᵉ
count-Q8ᵉ = pairᵉ 8 equiv-count-Q8ᵉ

is-finite-Q8ᵉ : is-finiteᵉ Q8ᵉ
is-finite-Q8ᵉ = unit-trunc-Propᵉ count-Q8ᵉ

Q8-𝔽ᵉ : 𝔽ᵉ lzero
Q8-𝔽ᵉ = pairᵉ Q8ᵉ is-finite-Q8ᵉ

has-cardinality-eight-Q8ᵉ : has-cardinalityᵉ 8 Q8ᵉ
has-cardinality-eight-Q8ᵉ = unit-trunc-Propᵉ equiv-count-Q8ᵉ

Q8-UU-Fin-8ᵉ : UU-Finᵉ lzero 8
Q8-UU-Fin-8ᵉ = pairᵉ Q8ᵉ has-cardinality-eight-Q8ᵉ

has-finite-cardinality-Q8ᵉ : has-finite-cardinalityᵉ Q8ᵉ
has-finite-cardinality-Q8ᵉ = pairᵉ 8 has-cardinality-eight-Q8ᵉ
```