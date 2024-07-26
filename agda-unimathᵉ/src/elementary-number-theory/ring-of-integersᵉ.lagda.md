# The ring of integers

```agda
module elementary-number-theory.ring-of-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.group-of-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.nonzero-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.free-groups-with-one-generatorᵉ
open import group-theory.homomorphisms-groupsᵉ

open import ring-theory.homomorphisms-ringsᵉ
open import ring-theory.initial-ringsᵉ
open import ring-theory.integer-multiples-of-elements-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.trivial-ringsᵉ
```

</details>

## Definition

```agda
ℤ-Ringᵉ : Ringᵉ lzero
pr1ᵉ ℤ-Ringᵉ = ℤ-Abᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ ℤ-Ringᵉ)) = mul-ℤᵉ
pr2ᵉ (pr1ᵉ (pr2ᵉ ℤ-Ringᵉ)) = associative-mul-ℤᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ ℤ-Ringᵉ))) = one-ℤᵉ
pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ ℤ-Ringᵉ)))) = left-unit-law-mul-ℤᵉ
pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ ℤ-Ringᵉ)))) = right-unit-law-mul-ℤᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ℤ-Ringᵉ))) = left-distributive-mul-add-ℤᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ℤ-Ringᵉ))) = right-distributive-mul-add-ℤᵉ

ℤ-Commutative-Ringᵉ : Commutative-Ringᵉ lzero
pr1ᵉ ℤ-Commutative-Ringᵉ = ℤ-Ringᵉ
pr2ᵉ ℤ-Commutative-Ringᵉ = commutative-mul-ℤᵉ
```

## Properties

### The ring of integers is nontrivial

```agda
is-nontrivial-ℤ-Ringᵉ : is-nontrivial-Ringᵉ ℤ-Ringᵉ
is-nontrivial-ℤ-Ringᵉ Hᵉ = is-nonzero-one-ℤᵉ (invᵉ Hᵉ)
```

### The integer multiples in `ℤ-Ring` coincide with multiplication in `ℤ`

```agda
is-mul-integer-multiple-ℤ-Ringᵉ :
  (kᵉ lᵉ : ℤᵉ) → integer-multiple-Ringᵉ ℤ-Ringᵉ kᵉ lᵉ ＝ᵉ mul-ℤᵉ kᵉ lᵉ
is-mul-integer-multiple-ℤ-Ringᵉ (inlᵉ zero-ℕᵉ) lᵉ =
  ( integer-multiple-neg-one-Ringᵉ ℤ-Ringᵉ lᵉ) ∙ᵉ
  ( invᵉ (left-neg-unit-law-mul-ℤᵉ lᵉ))
is-mul-integer-multiple-ℤ-Ringᵉ (inlᵉ (succ-ℕᵉ kᵉ)) lᵉ =
  ( integer-multiple-pred-Ringᵉ ℤ-Ringᵉ (inlᵉ kᵉ) lᵉ) ∙ᵉ
  ( apᵉ
    ( λ tᵉ → right-subtraction-Ringᵉ ℤ-Ringᵉ tᵉ lᵉ)
    ( is-mul-integer-multiple-ℤ-Ringᵉ (inlᵉ kᵉ) lᵉ)) ∙ᵉ
  ( commutative-add-ℤᵉ (mul-ℤᵉ (inlᵉ kᵉ) lᵉ) (neg-ℤᵉ lᵉ)) ∙ᵉ
  ( invᵉ (left-predecessor-law-mul-ℤᵉ (inlᵉ kᵉ) lᵉ))
is-mul-integer-multiple-ℤ-Ringᵉ (inrᵉ (inlᵉ _)) lᵉ =
  ( integer-multiple-zero-Ringᵉ ℤ-Ringᵉ lᵉ) ∙ᵉ
  ( invᵉ (left-zero-law-mul-ℤᵉ lᵉ))
is-mul-integer-multiple-ℤ-Ringᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) lᵉ =
  ( integer-multiple-one-Ringᵉ ℤ-Ringᵉ lᵉ) ∙ᵉ
  ( invᵉ (left-unit-law-mul-ℤᵉ lᵉ))
is-mul-integer-multiple-ℤ-Ringᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ))) lᵉ =
  ( integer-multiple-succ-Ringᵉ ℤ-Ringᵉ (inrᵉ (inrᵉ kᵉ)) lᵉ) ∙ᵉ
  ( apᵉ (add-ℤ'ᵉ lᵉ) (is-mul-integer-multiple-ℤ-Ringᵉ (inrᵉ (inrᵉ kᵉ)) lᵉ)) ∙ᵉ
  ( commutative-add-ℤᵉ _ lᵉ) ∙ᵉ
  ( invᵉ (left-successor-law-mul-ℤᵉ (inrᵉ (inrᵉ kᵉ)) lᵉ))

is-integer-multiple-ℤᵉ :
  (kᵉ : ℤᵉ) → integer-multiple-Ringᵉ ℤ-Ringᵉ kᵉ one-ℤᵉ ＝ᵉ kᵉ
is-integer-multiple-ℤᵉ kᵉ =
  ( is-mul-integer-multiple-ℤ-Ringᵉ kᵉ one-ℤᵉ) ∙ᵉ
  ( right-unit-law-mul-ℤᵉ kᵉ)
```

### The ring of integers is the initial ring

#### The homomorphism from `ℤ` to a ring

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  hom-group-initial-hom-Ringᵉ : hom-Groupᵉ ℤ-Groupᵉ (group-Ringᵉ Rᵉ)
  hom-group-initial-hom-Ringᵉ = hom-element-Groupᵉ (group-Ringᵉ Rᵉ) (one-Ringᵉ Rᵉ)

  map-initial-hom-Ringᵉ : ℤᵉ → type-Ringᵉ Rᵉ
  map-initial-hom-Ringᵉ =
    map-hom-Groupᵉ ℤ-Groupᵉ (group-Ringᵉ Rᵉ) hom-group-initial-hom-Ringᵉ

  preserves-add-initial-hom-Ringᵉ :
    (kᵉ lᵉ : ℤᵉ) →
    map-initial-hom-Ringᵉ (add-ℤᵉ kᵉ lᵉ) ＝ᵉ
    add-Ringᵉ Rᵉ (map-initial-hom-Ringᵉ kᵉ) (map-initial-hom-Ringᵉ lᵉ)
  preserves-add-initial-hom-Ringᵉ kᵉ lᵉ =
    preserves-mul-hom-Groupᵉ
      ( ℤ-Groupᵉ)
      ( group-Ringᵉ Rᵉ)
      ( hom-group-initial-hom-Ringᵉ)
      { kᵉ}
      { lᵉ}

  preserves-one-initial-hom-Ringᵉ : map-initial-hom-Ringᵉ one-ℤᵉ ＝ᵉ one-Ringᵉ Rᵉ
  preserves-one-initial-hom-Ringᵉ = integer-multiple-one-Ringᵉ Rᵉ (one-Ringᵉ Rᵉ)

  preserves-mul-initial-hom-Ringᵉ :
    (kᵉ lᵉ : ℤᵉ) →
    map-initial-hom-Ringᵉ (mul-ℤᵉ kᵉ lᵉ) ＝ᵉ
    mul-Ringᵉ Rᵉ (map-initial-hom-Ringᵉ kᵉ) (map-initial-hom-Ringᵉ lᵉ)
  preserves-mul-initial-hom-Ringᵉ kᵉ lᵉ =
    ( apᵉ map-initial-hom-Ringᵉ (commutative-mul-ℤᵉ kᵉ lᵉ)) ∙ᵉ
    ( integer-multiple-mul-Ringᵉ Rᵉ lᵉ kᵉ (one-Ringᵉ Rᵉ)) ∙ᵉ
    ( apᵉ (integer-multiple-Ringᵉ Rᵉ lᵉ) (invᵉ (right-unit-law-mul-Ringᵉ Rᵉ _))) ∙ᵉ
    ( invᵉ (right-integer-multiple-law-mul-Ringᵉ Rᵉ lᵉ _ _))

  initial-hom-Ringᵉ : hom-Ringᵉ ℤ-Ringᵉ Rᵉ
  pr1ᵉ initial-hom-Ringᵉ = hom-group-initial-hom-Ringᵉ
  pr1ᵉ (pr2ᵉ initial-hom-Ringᵉ) {xᵉ} {yᵉ} = preserves-mul-initial-hom-Ringᵉ xᵉ yᵉ
  pr2ᵉ (pr2ᵉ initial-hom-Ringᵉ) = preserves-one-initial-hom-Ringᵉ
```

#### Any ring homomorphisms from `ℤ` to `R` is equal to the homomorphism `initial-hom-Ring`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  htpy-initial-hom-Ringᵉ :
    (fᵉ : hom-Ringᵉ ℤ-Ringᵉ Rᵉ) → htpy-hom-Ringᵉ ℤ-Ringᵉ Rᵉ (initial-hom-Ringᵉ Rᵉ) fᵉ
  htpy-initial-hom-Ringᵉ fᵉ kᵉ =
    ( invᵉ
      ( ( preserves-integer-multiples-hom-Ringᵉ ℤ-Ringᵉ Rᵉ fᵉ kᵉ one-ℤᵉ) ∙ᵉ
        ( apᵉ
          ( integer-multiple-Ringᵉ Rᵉ kᵉ)
          ( preserves-one-hom-Ringᵉ ℤ-Ringᵉ Rᵉ fᵉ)))) ∙ᵉ
    ( apᵉ (map-hom-Ringᵉ ℤ-Ringᵉ Rᵉ fᵉ) (is-integer-multiple-ℤᵉ kᵉ))

  contraction-initial-hom-Ringᵉ :
    (fᵉ : hom-Ringᵉ ℤ-Ringᵉ Rᵉ) → initial-hom-Ringᵉ Rᵉ ＝ᵉ fᵉ
  contraction-initial-hom-Ringᵉ fᵉ =
    eq-htpy-hom-Ringᵉ ℤ-Ringᵉ Rᵉ (initial-hom-Ringᵉ Rᵉ) fᵉ (htpy-initial-hom-Ringᵉ fᵉ)
```

#### The ring of integers is the initial ring

```agda
is-initial-ℤ-Ringᵉ : is-initial-Ringᵉ ℤ-Ringᵉ
pr1ᵉ (is-initial-ℤ-Ringᵉ Sᵉ) = initial-hom-Ringᵉ Sᵉ
pr2ᵉ (is-initial-ℤ-Ringᵉ Sᵉ) fᵉ = contraction-initial-hom-Ringᵉ Sᵉ fᵉ
```

### Integer multiplication in the ring of integers coincides with multiplication of integers

```agda
integer-multiple-one-ℤ-Ringᵉ :
  (kᵉ : ℤᵉ) → integer-multiple-Ringᵉ ℤ-Ringᵉ kᵉ one-ℤᵉ ＝ᵉ kᵉ
integer-multiple-one-ℤ-Ringᵉ (inlᵉ zero-ℕᵉ) = reflᵉ
integer-multiple-one-ℤ-Ringᵉ (inlᵉ (succ-ℕᵉ nᵉ)) =
  apᵉ pred-ℤᵉ (integer-multiple-one-ℤ-Ringᵉ (inlᵉ nᵉ))
integer-multiple-one-ℤ-Ringᵉ (inrᵉ (inlᵉ _)) = reflᵉ
integer-multiple-one-ℤ-Ringᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) = reflᵉ
integer-multiple-one-ℤ-Ringᵉ (inrᵉ (inrᵉ (succ-ℕᵉ nᵉ))) =
  apᵉ succ-ℤᵉ (integer-multiple-one-ℤ-Ringᵉ (inrᵉ (inrᵉ nᵉ)))

compute-integer-multiple-ℤ-Ringᵉ :
  (kᵉ lᵉ : ℤᵉ) → integer-multiple-Ringᵉ ℤ-Ringᵉ kᵉ lᵉ ＝ᵉ mul-ℤᵉ kᵉ lᵉ
compute-integer-multiple-ℤ-Ringᵉ kᵉ lᵉ =
  equational-reasoningᵉ
    integer-multiple-Ringᵉ ℤ-Ringᵉ kᵉ lᵉ
    ＝ᵉ integer-multiple-Ringᵉ ℤ-Ringᵉ kᵉ (integer-multiple-Ringᵉ ℤ-Ringᵉ lᵉ one-ℤᵉ)
      byᵉ
      apᵉ
        ( integer-multiple-Ringᵉ ℤ-Ringᵉ kᵉ)
        ( invᵉ (integer-multiple-one-ℤ-Ringᵉ lᵉ))
    ＝ᵉ integer-multiple-Ringᵉ ℤ-Ringᵉ (mul-ℤᵉ kᵉ lᵉ) one-ℤᵉ
      byᵉ
      invᵉ (integer-multiple-mul-Ringᵉ ℤ-Ringᵉ kᵉ lᵉ one-ℤᵉ)
    ＝ᵉ mul-ℤᵉ kᵉ lᵉ
      byᵉ
      integer-multiple-one-ℤ-Ringᵉ _
```