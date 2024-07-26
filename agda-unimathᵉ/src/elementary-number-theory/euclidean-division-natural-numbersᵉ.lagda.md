# Euclidean division on the natural numbers

```agda
module elementary-number-theory.euclidean-division-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.congruence-natural-numbersᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Euclideanᵉ divisionᵉ isᵉ divisionᵉ with remainder,ᵉ i.e.,ᵉ theᵉ Euclideanᵉ divisionᵉ ofᵉ
`n`ᵉ byᵉ `d`ᵉ isᵉ theᵉ largestᵉ naturalᵉ numberᵉ `kᵉ ≤ᵉ n/d`,ᵉ andᵉ theᵉ remainderᵉ isᵉ theᵉ
uniqueᵉ naturalᵉ numberᵉ `rᵉ <ᵉ d`ᵉ suchᵉ thatᵉ `kdᵉ +ᵉ rᵉ = n`.ᵉ

## Definitions

### Euclidean division via an array of natural numbers

Theᵉ followingᵉ definitionᵉ producesᵉ forᵉ eachᵉ `kᵉ : ℕ`ᵉ aᵉ sequenceᵉ ofᵉ sequencesᵉ asᵉ
followsᵉ:

```text
    Thisᵉ isᵉ columnᵉ kᵉ
      ↓ᵉ
  0,…,0,0,0,0,0,0,0,…ᵉ  --ᵉ Theᵉ sequenceᵉ atᵉ rowᵉ 0 isᵉ theᵉ constantᵉ sequenceᵉ
  1,0,…,0,0,0,0,0,0,…ᵉ  --ᵉ Weᵉ appendᵉ 1'sᵉ atᵉ theᵉ startᵉ
      ⋮ᵉ
  1,…,1,0,…,0,0,0,0,…ᵉ  --ᵉ Thisᵉ isᵉ rowᵉ k+1ᵉ
  2,1,…,1,0,0,0,0,0,…ᵉ  --ᵉ Afterᵉ k+1ᵉ stepsᵉ weᵉ appendᵉ 2'sᵉ atᵉ theᵉ startᵉ
      ⋮ᵉ
  2,…,2,1,…,1,0,…,0,…ᵉ  --ᵉ Thisᵉ isᵉ rowᵉ 2(k+1ᵉ)
  3,2,…,2,1,…,1,0,0,…ᵉ  --ᵉ Afterᵉ anotherᵉ k+1ᵉ stepsᵉ weᵉ appendᵉ 3'sᵉ atᵉ theᵉ startᵉ
      ⋮ᵉ
```

Thisᵉ producesᵉ anᵉ arrayᵉ ofᵉ naturalᵉ numbers.ᵉ Weᵉ findᵉ theᵉ quotientᵉ ofᵉ theᵉ euclideanᵉ
divisionᵉ ofᵉ `n`ᵉ byᵉ `k+1`ᵉ in theᵉ `k`-thᵉ columnᵉ ofᵉ theᵉ `n`-thᵉ rowᵉ ofᵉ thisᵉ array.ᵉ
Weᵉ willᵉ arbitrarilyᵉ setᵉ theᵉ quotientᵉ ofᵉ theᵉ euclideanᵉ divisionᵉ ofᵉ `n`ᵉ byᵉ `0`ᵉ to
`0`ᵉ in thisᵉ definition.ᵉ

```agda
array-quotient-euclidean-division-ℕᵉ : ℕᵉ → ℕᵉ → ℕᵉ → ℕᵉ
array-quotient-euclidean-division-ℕᵉ kᵉ zero-ℕᵉ mᵉ = zero-ℕᵉ
array-quotient-euclidean-division-ℕᵉ kᵉ (succ-ℕᵉ nᵉ) zero-ℕᵉ =
  succ-ℕᵉ (array-quotient-euclidean-division-ℕᵉ kᵉ nᵉ kᵉ)
array-quotient-euclidean-division-ℕᵉ kᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ mᵉ) =
  array-quotient-euclidean-division-ℕᵉ kᵉ nᵉ mᵉ

quotient-euclidean-division-ℕ'ᵉ : ℕᵉ → ℕᵉ → ℕᵉ
quotient-euclidean-division-ℕ'ᵉ zero-ℕᵉ nᵉ = zero-ℕᵉ
quotient-euclidean-division-ℕ'ᵉ (succ-ℕᵉ kᵉ) nᵉ =
  array-quotient-euclidean-division-ℕᵉ kᵉ nᵉ kᵉ
```

### Euclidean division via modular arithmetic

```agda
euclidean-division-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) → Σᵉ ℕᵉ (λ rᵉ → (cong-ℕᵉ kᵉ xᵉ rᵉ) ×ᵉ (is-nonzero-ℕᵉ kᵉ → le-ℕᵉ rᵉ kᵉ))
pr1ᵉ (euclidean-division-ℕᵉ zero-ℕᵉ xᵉ) = xᵉ
pr1ᵉ (pr2ᵉ (euclidean-division-ℕᵉ zero-ℕᵉ xᵉ)) = refl-cong-ℕᵉ zero-ℕᵉ xᵉ
pr2ᵉ (pr2ᵉ (euclidean-division-ℕᵉ zero-ℕᵉ xᵉ)) fᵉ = ex-falsoᵉ (fᵉ reflᵉ)
pr1ᵉ (euclidean-division-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ) = nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ)
pr1ᵉ (pr2ᵉ (euclidean-division-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ)) =
  symmetric-cong-ℕᵉ
    ( succ-ℕᵉ kᵉ)
    ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))
    ( xᵉ)
    ( cong-nat-mod-succ-ℕᵉ kᵉ xᵉ)
pr2ᵉ (pr2ᵉ (euclidean-division-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ)) fᵉ =
  strict-upper-bound-nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ)

remainder-euclidean-division-ℕᵉ : ℕᵉ → ℕᵉ → ℕᵉ
remainder-euclidean-division-ℕᵉ kᵉ xᵉ =
  pr1ᵉ (euclidean-division-ℕᵉ kᵉ xᵉ)

cong-euclidean-division-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) → cong-ℕᵉ kᵉ xᵉ (remainder-euclidean-division-ℕᵉ kᵉ xᵉ)
cong-euclidean-division-ℕᵉ kᵉ xᵉ =
  pr1ᵉ (pr2ᵉ (euclidean-division-ℕᵉ kᵉ xᵉ))

strict-upper-bound-remainder-euclidean-division-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) → is-nonzero-ℕᵉ kᵉ → le-ℕᵉ (remainder-euclidean-division-ℕᵉ kᵉ xᵉ) kᵉ
strict-upper-bound-remainder-euclidean-division-ℕᵉ kᵉ xᵉ =
  pr2ᵉ (pr2ᵉ (euclidean-division-ℕᵉ kᵉ xᵉ))

quotient-euclidean-division-ℕᵉ : ℕᵉ → ℕᵉ → ℕᵉ
quotient-euclidean-division-ℕᵉ kᵉ xᵉ =
  pr1ᵉ (cong-euclidean-division-ℕᵉ kᵉ xᵉ)

eq-quotient-euclidean-division-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) →
  ( (quotient-euclidean-division-ℕᵉ kᵉ xᵉ) *ℕᵉ kᵉ) ＝ᵉ
  ( dist-ℕᵉ xᵉ (remainder-euclidean-division-ℕᵉ kᵉ xᵉ))
eq-quotient-euclidean-division-ℕᵉ kᵉ xᵉ =
  pr2ᵉ (cong-euclidean-division-ℕᵉ kᵉ xᵉ)

eq-euclidean-division-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) →
  ( add-ℕᵉ
    ( (quotient-euclidean-division-ℕᵉ kᵉ xᵉ) *ℕᵉ kᵉ)
    ( remainder-euclidean-division-ℕᵉ kᵉ xᵉ)) ＝ᵉ
  ( xᵉ)
eq-euclidean-division-ℕᵉ zero-ℕᵉ xᵉ =
  ( invᵉ
    ( apᵉ
      ( _+ℕᵉ xᵉ)
      ( right-zero-law-mul-ℕᵉ (quotient-euclidean-division-ℕᵉ zero-ℕᵉ xᵉ)))) ∙ᵉ
  ( left-unit-law-add-ℕᵉ xᵉ)
eq-euclidean-division-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ =
  ( apᵉ
    ( _+ℕᵉ (remainder-euclidean-division-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ))
    ( ( pr2ᵉ (cong-euclidean-division-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ)) ∙ᵉ
      ( symmetric-dist-ℕᵉ xᵉ
        ( remainder-euclidean-division-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ)))) ∙ᵉ
  ( is-difference-dist-ℕ'ᵉ (remainder-euclidean-division-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ) xᵉ
    ( leq-nat-mod-succ-ℕᵉ kᵉ xᵉ))
```

```agda
map-extended-euclidean-algorithmᵉ : ℕᵉ ×ᵉ ℕᵉ → ℕᵉ ×ᵉ ℕᵉ
pr1ᵉ (map-extended-euclidean-algorithmᵉ (pairᵉ xᵉ yᵉ)) = yᵉ
pr2ᵉ (map-extended-euclidean-algorithmᵉ (pairᵉ xᵉ yᵉ)) =
  remainder-euclidean-division-ℕᵉ yᵉ xᵉ
```