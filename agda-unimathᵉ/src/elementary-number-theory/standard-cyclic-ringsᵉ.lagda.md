# The standard cyclic rings

```agda
module elementary-number-theory.standard-cyclic-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.modular-arithmeticᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.ring-of-integersᵉ
open import elementary-number-theory.standard-cyclic-groupsᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.cyclic-groupsᵉ
open import group-theory.generating-elements-groupsᵉ

open import ring-theory.cyclic-ringsᵉ
open import ring-theory.integer-multiples-of-elements-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Theᵉ **standardᵉ cyclicᵉ rings**ᵉ `ℤ/n`ᵉ areᵉ theᵉ [rings](ring-theory.rings.mdᵉ) ofᵉ
[integers](elementary-number-theory.integers.mdᵉ)
[moduloᵉ `n`](elementary-number-theory.modular-arithmetic.md).ᵉ

## Definitions

### The standard cyclic rings

```agda
ℤ-Mod-Ringᵉ : ℕᵉ → Ringᵉ lzero
pr1ᵉ (ℤ-Mod-Ringᵉ nᵉ) = ℤ-Mod-Abᵉ nᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ (ℤ-Mod-Ringᵉ nᵉ))) = mul-ℤ-Modᵉ nᵉ
pr2ᵉ (pr1ᵉ (pr2ᵉ (ℤ-Mod-Ringᵉ nᵉ))) = associative-mul-ℤ-Modᵉ nᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (ℤ-Mod-Ringᵉ nᵉ)))) = one-ℤ-Modᵉ nᵉ
pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (ℤ-Mod-Ringᵉ nᵉ))))) = left-unit-law-mul-ℤ-Modᵉ nᵉ
pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (ℤ-Mod-Ringᵉ nᵉ))))) = right-unit-law-mul-ℤ-Modᵉ nᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (ℤ-Mod-Ringᵉ nᵉ)))) = left-distributive-mul-add-ℤ-Modᵉ nᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (ℤ-Mod-Ringᵉ nᵉ)))) = right-distributive-mul-add-ℤ-Modᵉ nᵉ

ℤ-Mod-Commutative-Ringᵉ : ℕᵉ → Commutative-Ringᵉ lzero
pr1ᵉ (ℤ-Mod-Commutative-Ringᵉ nᵉ) = ℤ-Mod-Ringᵉ nᵉ
pr2ᵉ (ℤ-Mod-Commutative-Ringᵉ nᵉ) = commutative-mul-ℤ-Modᵉ nᵉ
```

### Integer multiplication in the standard cyclic rings

```agda
integer-multiple-ℤ-Modᵉ :
  (nᵉ : ℕᵉ) → ℤᵉ → ℤ-Modᵉ nᵉ → ℤ-Modᵉ nᵉ
integer-multiple-ℤ-Modᵉ nᵉ kᵉ xᵉ = integer-multiple-Ringᵉ (ℤ-Mod-Ringᵉ nᵉ) kᵉ xᵉ
```

## Properties

### The negative-one element of the ring `ℤ/n` coincides with the element `neg-one-ℤ-Mod n`

```agda
is-neg-one-neg-one-ℤ-Modᵉ :
  ( nᵉ : ℕᵉ) → neg-one-Ringᵉ (ℤ-Mod-Ringᵉ nᵉ) ＝ᵉ neg-one-ℤ-Modᵉ nᵉ
is-neg-one-neg-one-ℤ-Modᵉ zero-ℕᵉ = reflᵉ
is-neg-one-neg-one-ℤ-Modᵉ (succ-ℕᵉ nᵉ) = is-neg-one-neg-one-Finᵉ nᵉ
```

### The integer multiple `k · 1` is equal to `[k] : ℤ-Mod n`

```agda
integer-multiplication-by-one-preserves-succ-ℤᵉ :
  (nᵉ : ℕᵉ) (xᵉ : ℤᵉ) →
  integer-multiple-ℤ-Modᵉ nᵉ (succ-ℤᵉ xᵉ) (one-ℤ-Modᵉ nᵉ) ＝ᵉ
  succ-ℤ-Modᵉ nᵉ (integer-multiple-ℤ-Modᵉ nᵉ xᵉ (one-ℤ-Modᵉ nᵉ))
integer-multiplication-by-one-preserves-succ-ℤᵉ nᵉ xᵉ =
  ( integer-multiple-succ-Ringᵉ (ℤ-Mod-Ringᵉ nᵉ) xᵉ (one-ℤ-Modᵉ nᵉ)) ∙ᵉ
  ( invᵉ
    ( is-left-add-one-succ-ℤ-Mod'ᵉ
      ( nᵉ)
      ( integer-multiple-Ringᵉ (ℤ-Mod-Ringᵉ nᵉ) xᵉ (one-ℤ-Modᵉ nᵉ))))

integer-multiplication-by-one-preserves-pred-ℤᵉ :
  (nᵉ : ℕᵉ) (xᵉ : ℤᵉ) →
  integer-multiple-ℤ-Modᵉ nᵉ (pred-ℤᵉ xᵉ) (one-ℤ-Modᵉ nᵉ) ＝ᵉ
  pred-ℤ-Modᵉ nᵉ (integer-multiple-ℤ-Modᵉ nᵉ xᵉ (one-ℤ-Modᵉ nᵉ))
integer-multiplication-by-one-preserves-pred-ℤᵉ nᵉ xᵉ =
  ( apᵉ
    ( λ kᵉ → integer-multiple-ℤ-Modᵉ nᵉ kᵉ (one-ℤ-Modᵉ nᵉ))
    ( is-right-add-neg-one-pred-ℤᵉ xᵉ)) ∙ᵉ
  ( distributive-integer-multiple-add-Ringᵉ
    ( ℤ-Mod-Ringᵉ nᵉ)
    ( one-ℤ-Modᵉ nᵉ)
    ( xᵉ)
    ( neg-one-ℤᵉ)) ∙ᵉ
  ( apᵉ
    ( λ kᵉ →
      add-ℤ-Modᵉ nᵉ
      ( integer-multiple-ℤ-Modᵉ nᵉ xᵉ (one-ℤ-Modᵉ nᵉ))
      ( kᵉ))
    ( integer-multiple-neg-one-Ringᵉ (ℤ-Mod-Ringᵉ nᵉ) (one-ℤ-Modᵉ nᵉ))) ∙ᵉ
  ( apᵉ
    ( λ kᵉ →
      add-ℤ-Modᵉ nᵉ
      ( integer-multiple-ℤ-Modᵉ nᵉ xᵉ (one-ℤ-Modᵉ nᵉ))
      ( kᵉ))
    ( is-neg-one-neg-one-ℤ-Modᵉ nᵉ)) ∙ᵉ
    ( invᵉ
      ( is-left-add-neg-one-pred-ℤ-Mod'ᵉ
        ( nᵉ)
        ( integer-multiple-ℤ-Modᵉ nᵉ xᵉ (one-ℤ-Modᵉ nᵉ))))

compute-integer-multiple-one-ℤ-Modᵉ :
  ( nᵉ : ℕᵉ) → (λ kᵉ → integer-multiple-ℤ-Modᵉ nᵉ kᵉ (one-ℤ-Modᵉ nᵉ)) ~ᵉ mod-ℤᵉ nᵉ
compute-integer-multiple-one-ℤ-Modᵉ zero-ℕᵉ xᵉ = integer-multiple-one-ℤ-Ringᵉ xᵉ
compute-integer-multiple-one-ℤ-Modᵉ (succ-ℕᵉ nᵉ) (inlᵉ zero-ℕᵉ) =
  ( integer-multiple-neg-one-Ringᵉ
    ( ℤ-Mod-Ringᵉ (succ-ℕᵉ nᵉ))
    ( one-ℤ-Modᵉ (succ-ℕᵉ nᵉ))) ∙ᵉ
  ( is-neg-one-neg-one-ℤ-Modᵉ (succ-ℕᵉ nᵉ)) ∙ᵉ
  ( invᵉ (mod-neg-one-ℤᵉ (succ-ℕᵉ nᵉ)))
compute-integer-multiple-one-ℤ-Modᵉ (succ-ℕᵉ nᵉ) (inlᵉ (succ-ℕᵉ xᵉ)) =
  ( integer-multiplication-by-one-preserves-pred-ℤᵉ
    ( succ-ℕᵉ nᵉ)
    ( inlᵉ xᵉ)) ∙ᵉ
  ( apᵉ
    ( pred-ℤ-Modᵉ (succ-ℕᵉ nᵉ))
    ( compute-integer-multiple-one-ℤ-Modᵉ (succ-ℕᵉ nᵉ) (inlᵉ xᵉ))) ∙ᵉ
  ( invᵉ (preserves-predecessor-mod-ℤᵉ (succ-ℕᵉ nᵉ) (inlᵉ xᵉ)))
compute-integer-multiple-one-ℤ-Modᵉ (succ-ℕᵉ nᵉ) (inrᵉ (inlᵉ _)) = reflᵉ
compute-integer-multiple-one-ℤ-Modᵉ (succ-ℕᵉ nᵉ) (inrᵉ (inrᵉ zero-ℕᵉ)) =
  ( integer-multiple-one-Ringᵉ
    ( ℤ-Mod-Ringᵉ (succ-ℕᵉ nᵉ))
    ( one-ℤ-Modᵉ (succ-ℕᵉ nᵉ))) ∙ᵉ
  ( invᵉ (mod-one-ℤᵉ (succ-ℕᵉ nᵉ)))
compute-integer-multiple-one-ℤ-Modᵉ (succ-ℕᵉ nᵉ) (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) =
  ( integer-multiplication-by-one-preserves-succ-ℤᵉ
    ( succ-ℕᵉ nᵉ)
    ( inrᵉ (inrᵉ xᵉ))) ∙ᵉ
  ( apᵉ
    ( succ-ℤ-Modᵉ (succ-ℕᵉ nᵉ))
    ( compute-integer-multiple-one-ℤ-Modᵉ (succ-ℕᵉ nᵉ) (inrᵉ (inrᵉ xᵉ)))) ∙ᵉ
  ( invᵉ (preserves-successor-mod-ℤᵉ (succ-ℕᵉ nᵉ) (inrᵉ (inrᵉ xᵉ))))
```

### The standard cyclic rings are cyclic

```agda
is-surjective-hom-element-one-ℤ-Modᵉ :
  ( nᵉ : ℕᵉ) → is-surjective-hom-element-Groupᵉ (ℤ-Mod-Groupᵉ nᵉ) (one-ℤ-Modᵉ nᵉ)
is-surjective-hom-element-one-ℤ-Modᵉ nᵉ =
  is-surjective-htpyᵉ
    ( compute-integer-multiple-one-ℤ-Modᵉ nᵉ)
    ( is-surjective-mod-ℤᵉ nᵉ)

is-generating-element-one-ℤ-Modᵉ :
  ( nᵉ : ℕᵉ) → is-generating-element-Groupᵉ (ℤ-Mod-Groupᵉ nᵉ) (one-ℤ-Modᵉ nᵉ)
is-generating-element-one-ℤ-Modᵉ nᵉ =
  is-generating-element-is-surjective-hom-element-Groupᵉ
    ( ℤ-Mod-Groupᵉ nᵉ)
    ( one-ℤ-Modᵉ nᵉ)
    ( is-surjective-hom-element-one-ℤ-Modᵉ nᵉ)

is-cyclic-ℤ-Mod-Groupᵉ :
  ( nᵉ : ℕᵉ) → is-cyclic-Groupᵉ (ℤ-Mod-Groupᵉ nᵉ)
is-cyclic-ℤ-Mod-Groupᵉ nᵉ =
  intro-existsᵉ
    ( one-ℤ-Modᵉ nᵉ)
    ( is-generating-element-one-ℤ-Modᵉ nᵉ)

is-cyclic-ℤ-Mod-Ringᵉ :
  ( nᵉ : ℕᵉ) → is-cyclic-Ringᵉ (ℤ-Mod-Ringᵉ nᵉ)
is-cyclic-ℤ-Mod-Ringᵉ =
  is-cyclic-ℤ-Mod-Groupᵉ
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}