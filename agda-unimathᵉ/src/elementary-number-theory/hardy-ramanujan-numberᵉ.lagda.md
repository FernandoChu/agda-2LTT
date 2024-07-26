# The Hardy-Ramanujan number

```agda
module elementary-number-theory.hardy-ramanujan-numberᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.taxicab-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "Hardy-Ramanujanᵉ number"ᵉ Agda=Hardy-Ramanujan-ℕᵉ WD="1729"ᵉ WDID=Q825176ᵉ}}
isᵉ theᵉ numberᵉ `1729`.ᵉ Thisᵉ numberᵉ isᵉ theᵉ secondᵉ
[taxicabᵉ number](elementary-number-theory.taxicab-numbers.md),ᵉ i.e.,ᵉ itᵉ isᵉ theᵉ
leastᵉ naturalᵉ numberᵉ thatᵉ canᵉ beᵉ writtenᵉ asᵉ aᵉ sumᵉ ofᵉ cubesᵉ ofᵉ positiveᵉ naturalᵉ
numbersᵉ in exactlyᵉ twoᵉ distinctᵉ ways.ᵉ Specifically,ᵉ weᵉ haveᵉ theᵉ identificationsᵉ

```text
  1³ᵉ +ᵉ 12³ᵉ ＝ᵉ 1729    andᵉ    9³ᵉ +ᵉ 10³ᵉ ＝ᵉ 1729.ᵉ
```

## Definition

### The Hardy-Ramanujan number

```agda
Hardy-Ramanujan-ℕᵉ : ℕᵉ
Hardy-Ramanujan-ℕᵉ = 1729
```

## Properties

### Two decompositions of the Hardy-Ramanujan number into sums of cubes of two positive natural numbers

```agda
first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕᵉ :
  sum-of-cubes-decomposition-ℕᵉ Hardy-Ramanujan-ℕᵉ
pr1ᵉ first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕᵉ =
  (1ᵉ ,ᵉ is-nonzero-one-ℕᵉ)
pr1ᵉ (pr2ᵉ first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕᵉ) =
  (12ᵉ ,ᵉ is-nonzero-succ-ℕᵉ 11ᵉ)
pr1ᵉ (pr2ᵉ (pr2ᵉ first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕᵉ)) =
  starᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕᵉ)) =
  reflᵉ

second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕᵉ :
  sum-of-cubes-decomposition-ℕᵉ Hardy-Ramanujan-ℕᵉ
pr1ᵉ second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕᵉ =
  (9ᵉ ,ᵉ is-nonzero-succ-ℕᵉ 8ᵉ)
pr1ᵉ (pr2ᵉ second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕᵉ) =
  (10ᵉ ,ᵉ is-nonzero-succ-ℕᵉ 9ᵉ)
pr1ᵉ (pr2ᵉ (pr2ᵉ second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕᵉ)) =
  starᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕᵉ)) =
  reflᵉ
```

## External links

-ᵉ [1729ᵉ (number)](<https://en.wikipedia.org/wiki/1729_(number)>ᵉ) atᵉ Wikipediaᵉ