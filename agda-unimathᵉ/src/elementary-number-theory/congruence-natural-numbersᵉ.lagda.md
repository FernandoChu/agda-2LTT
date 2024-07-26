# The congruence relations on the natural numbers

```agda
module elementary-number-theory.congruence-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Properties

### The congruence relations on the natural numbers

```agda
cong-ℕᵉ :
  ℕᵉ → ℕᵉ → ℕᵉ → UUᵉ lzero
cong-ℕᵉ kᵉ xᵉ yᵉ = div-ℕᵉ kᵉ (dist-ℕᵉ xᵉ yᵉ)

_≡_modᵉ_ : ℕᵉ → ℕᵉ → ℕᵉ → UUᵉ lzero
xᵉ ≡ᵉ yᵉ modᵉ kᵉ = cong-ℕᵉ kᵉ xᵉ yᵉ

concatenate-eq-cong-eq-ℕᵉ :
  (kᵉ : ℕᵉ) {x1ᵉ x2ᵉ x3ᵉ x4ᵉ : ℕᵉ} →
  x1ᵉ ＝ᵉ x2ᵉ → cong-ℕᵉ kᵉ x2ᵉ x3ᵉ → x3ᵉ ＝ᵉ x4ᵉ → cong-ℕᵉ kᵉ x1ᵉ x4ᵉ
concatenate-eq-cong-eq-ℕᵉ kᵉ reflᵉ Hᵉ reflᵉ = Hᵉ

concatenate-eq-cong-ℕᵉ :
  (kᵉ : ℕᵉ) {x1ᵉ x2ᵉ x3ᵉ : ℕᵉ} →
  x1ᵉ ＝ᵉ x2ᵉ → cong-ℕᵉ kᵉ x2ᵉ x3ᵉ → cong-ℕᵉ kᵉ x1ᵉ x3ᵉ
concatenate-eq-cong-ℕᵉ kᵉ reflᵉ Hᵉ = Hᵉ

concatenate-cong-eq-ℕᵉ :
  (kᵉ : ℕᵉ) {x1ᵉ x2ᵉ x3ᵉ : ℕᵉ} →
  cong-ℕᵉ kᵉ x1ᵉ x2ᵉ → x2ᵉ ＝ᵉ x3ᵉ → cong-ℕᵉ kᵉ x1ᵉ x3ᵉ
concatenate-cong-eq-ℕᵉ kᵉ Hᵉ reflᵉ = Hᵉ

is-indiscrete-cong-one-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → cong-ℕᵉ 1 xᵉ yᵉ
is-indiscrete-cong-one-ℕᵉ xᵉ yᵉ = div-one-ℕᵉ (dist-ℕᵉ xᵉ yᵉ)

is-discrete-cong-zero-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → cong-ℕᵉ zero-ℕᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
is-discrete-cong-zero-ℕᵉ xᵉ yᵉ (pairᵉ kᵉ pᵉ) =
  eq-dist-ℕᵉ xᵉ yᵉ ((invᵉ pᵉ) ∙ᵉ (right-zero-law-mul-ℕᵉ kᵉ))

cong-zero-ℕᵉ :
  (kᵉ : ℕᵉ) → cong-ℕᵉ kᵉ kᵉ zero-ℕᵉ
pr1ᵉ (cong-zero-ℕᵉ kᵉ) = 1
pr2ᵉ (cong-zero-ℕᵉ kᵉ) =
  (left-unit-law-mul-ℕᵉ kᵉ) ∙ᵉ (invᵉ (right-unit-law-dist-ℕᵉ kᵉ))

refl-cong-ℕᵉ : (kᵉ : ℕᵉ) → is-reflexiveᵉ (cong-ℕᵉ kᵉ)
pr1ᵉ (refl-cong-ℕᵉ kᵉ xᵉ) = zero-ℕᵉ
pr2ᵉ (refl-cong-ℕᵉ kᵉ xᵉ) =
  (left-zero-law-mul-ℕᵉ (succ-ℕᵉ kᵉ)) ∙ᵉ (invᵉ (dist-eq-ℕᵉ xᵉ xᵉ reflᵉ))

cong-identification-ℕᵉ :
  (kᵉ : ℕᵉ) {xᵉ yᵉ : ℕᵉ} → xᵉ ＝ᵉ yᵉ → cong-ℕᵉ kᵉ xᵉ yᵉ
cong-identification-ℕᵉ kᵉ {xᵉ} reflᵉ = refl-cong-ℕᵉ kᵉ xᵉ

symmetric-cong-ℕᵉ : (kᵉ : ℕᵉ) → is-symmetricᵉ (cong-ℕᵉ kᵉ)
pr1ᵉ (symmetric-cong-ℕᵉ kᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) = dᵉ
pr2ᵉ (symmetric-cong-ℕᵉ kᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) = pᵉ ∙ᵉ (symmetric-dist-ℕᵉ xᵉ yᵉ)

cong-zero-ℕ'ᵉ : (kᵉ : ℕᵉ) → cong-ℕᵉ kᵉ zero-ℕᵉ kᵉ
cong-zero-ℕ'ᵉ kᵉ =
  symmetric-cong-ℕᵉ kᵉ kᵉ zero-ℕᵉ (cong-zero-ℕᵉ kᵉ)

transitive-cong-ℕᵉ : (kᵉ : ℕᵉ) → is-transitiveᵉ (cong-ℕᵉ kᵉ)
transitive-cong-ℕᵉ kᵉ xᵉ yᵉ zᵉ eᵉ dᵉ with is-total-dist-ℕᵉ xᵉ yᵉ zᵉ
transitive-cong-ℕᵉ kᵉ xᵉ yᵉ zᵉ eᵉ dᵉ | inlᵉ αᵉ =
  concatenate-div-eq-ℕᵉ (div-add-ℕᵉ kᵉ (dist-ℕᵉ xᵉ yᵉ) (dist-ℕᵉ yᵉ zᵉ) dᵉ eᵉ) αᵉ
transitive-cong-ℕᵉ kᵉ xᵉ yᵉ zᵉ eᵉ dᵉ | inrᵉ (inlᵉ αᵉ) =
  div-right-summand-ℕᵉ kᵉ (dist-ℕᵉ yᵉ zᵉ) (dist-ℕᵉ xᵉ zᵉ) eᵉ
    ( concatenate-div-eq-ℕᵉ dᵉ (invᵉ αᵉ))
transitive-cong-ℕᵉ kᵉ xᵉ yᵉ zᵉ eᵉ dᵉ | inrᵉ (inrᵉ αᵉ) =
  div-left-summand-ℕᵉ kᵉ (dist-ℕᵉ xᵉ zᵉ) (dist-ℕᵉ xᵉ yᵉ) dᵉ
    ( concatenate-div-eq-ℕᵉ eᵉ (invᵉ αᵉ))

concatenate-cong-eq-cong-ℕᵉ :
  {kᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ : ℕᵉ} →
  cong-ℕᵉ kᵉ x1ᵉ x2ᵉ → x2ᵉ ＝ᵉ x3ᵉ → cong-ℕᵉ kᵉ x3ᵉ x4ᵉ → cong-ℕᵉ kᵉ x1ᵉ x4ᵉ
concatenate-cong-eq-cong-ℕᵉ {kᵉ} {xᵉ} {yᵉ} {.yᵉ} {zᵉ} Hᵉ reflᵉ Kᵉ =
  transitive-cong-ℕᵉ kᵉ xᵉ yᵉ zᵉ Kᵉ Hᵉ

concatenate-eq-cong-eq-cong-eq-ℕᵉ :
  (kᵉ : ℕᵉ) {x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ : ℕᵉ} →
  x1ᵉ ＝ᵉ x2ᵉ → cong-ℕᵉ kᵉ x2ᵉ x3ᵉ → x3ᵉ ＝ᵉ x4ᵉ →
  cong-ℕᵉ kᵉ x4ᵉ x5ᵉ → x5ᵉ ＝ᵉ x6ᵉ → cong-ℕᵉ kᵉ x1ᵉ x6ᵉ
concatenate-eq-cong-eq-cong-eq-ℕᵉ kᵉ
  {xᵉ} {.xᵉ} {yᵉ} {.yᵉ} {zᵉ} {.zᵉ} reflᵉ Hᵉ reflᵉ Kᵉ reflᵉ =
  transitive-cong-ℕᵉ kᵉ xᵉ yᵉ zᵉ Kᵉ Hᵉ
```

```agda
eq-cong-le-dist-ℕᵉ :
  (kᵉ xᵉ yᵉ : ℕᵉ) → le-ℕᵉ (dist-ℕᵉ xᵉ yᵉ) kᵉ → cong-ℕᵉ kᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
eq-cong-le-dist-ℕᵉ kᵉ xᵉ yᵉ Hᵉ Kᵉ =
  eq-dist-ℕᵉ xᵉ yᵉ (is-zero-div-ℕᵉ kᵉ (dist-ℕᵉ xᵉ yᵉ) Hᵉ Kᵉ)
```

```agda
eq-cong-le-ℕᵉ :
  (kᵉ xᵉ yᵉ : ℕᵉ) → le-ℕᵉ xᵉ kᵉ → le-ℕᵉ yᵉ kᵉ → cong-ℕᵉ kᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
eq-cong-le-ℕᵉ kᵉ xᵉ yᵉ Hᵉ Kᵉ =
  eq-cong-le-dist-ℕᵉ kᵉ xᵉ yᵉ (strict-upper-bound-dist-ℕᵉ kᵉ xᵉ yᵉ Hᵉ Kᵉ)
```

```agda
eq-cong-nat-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) → cong-ℕᵉ kᵉ (nat-Finᵉ kᵉ xᵉ) (nat-Finᵉ kᵉ yᵉ) → xᵉ ＝ᵉ yᵉ
eq-cong-nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ Hᵉ =
  is-injective-nat-Finᵉ (succ-ℕᵉ kᵉ)
    ( eq-cong-le-ℕᵉ (succ-ℕᵉ kᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ)
      ( strict-upper-bound-nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
      ( strict-upper-bound-nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ)
      ( Hᵉ))
```

```agda
cong-is-zero-nat-zero-Finᵉ :
  {kᵉ : ℕᵉ} → cong-ℕᵉ (succ-ℕᵉ kᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ)) zero-ℕᵉ
cong-is-zero-nat-zero-Finᵉ {kᵉ} =
  cong-identification-ℕᵉ (succ-ℕᵉ kᵉ) (is-zero-nat-zero-Finᵉ {kᵉ})
```

```agda
eq-cong-zero-ℕᵉ : (xᵉ yᵉ : ℕᵉ) → cong-ℕᵉ zero-ℕᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
eq-cong-zero-ℕᵉ xᵉ yᵉ Hᵉ =
  eq-dist-ℕᵉ xᵉ yᵉ (is-zero-div-zero-ℕᵉ (dist-ℕᵉ xᵉ yᵉ) Hᵉ)

is-one-cong-succ-ℕᵉ : {kᵉ : ℕᵉ} (xᵉ : ℕᵉ) → cong-ℕᵉ kᵉ xᵉ (succ-ℕᵉ xᵉ) → is-one-ℕᵉ kᵉ
is-one-cong-succ-ℕᵉ {kᵉ} xᵉ Hᵉ =
  is-one-div-one-ℕᵉ kᵉ (trᵉ (div-ℕᵉ kᵉ) (is-one-dist-succ-ℕᵉ xᵉ) Hᵉ)
```

### Congruence is invariant under scalar multiplication

```agda
scalar-invariant-cong-ℕᵉ :
  (kᵉ xᵉ yᵉ zᵉ : ℕᵉ) → cong-ℕᵉ kᵉ xᵉ yᵉ → cong-ℕᵉ kᵉ (zᵉ *ℕᵉ xᵉ) (zᵉ *ℕᵉ yᵉ)
pr1ᵉ (scalar-invariant-cong-ℕᵉ kᵉ xᵉ yᵉ zᵉ (pairᵉ dᵉ pᵉ)) = zᵉ *ℕᵉ dᵉ
pr2ᵉ (scalar-invariant-cong-ℕᵉ kᵉ xᵉ yᵉ zᵉ (pairᵉ dᵉ pᵉ)) =
  ( associative-mul-ℕᵉ zᵉ dᵉ kᵉ) ∙ᵉ
    ( ( apᵉ (zᵉ *ℕᵉ_) pᵉ) ∙ᵉ
      ( left-distributive-mul-dist-ℕᵉ xᵉ yᵉ zᵉ))

scalar-invariant-cong-ℕ'ᵉ :
  (kᵉ xᵉ yᵉ zᵉ : ℕᵉ) → cong-ℕᵉ kᵉ xᵉ yᵉ → cong-ℕᵉ kᵉ (xᵉ *ℕᵉ zᵉ) (yᵉ *ℕᵉ zᵉ)
scalar-invariant-cong-ℕ'ᵉ kᵉ xᵉ yᵉ zᵉ Hᵉ =
  concatenate-eq-cong-eq-ℕᵉ kᵉ
    ( commutative-mul-ℕᵉ xᵉ zᵉ)
    ( scalar-invariant-cong-ℕᵉ kᵉ xᵉ yᵉ zᵉ Hᵉ)
    ( commutative-mul-ℕᵉ zᵉ yᵉ)
```

### Multiplication respects the congruence relation

```agda
congruence-mul-ℕᵉ :
  (kᵉ : ℕᵉ) {xᵉ yᵉ x'ᵉ y'ᵉ : ℕᵉ} →
  cong-ℕᵉ kᵉ xᵉ x'ᵉ → cong-ℕᵉ kᵉ yᵉ y'ᵉ → cong-ℕᵉ kᵉ (xᵉ *ℕᵉ yᵉ) (x'ᵉ *ℕᵉ y'ᵉ)
congruence-mul-ℕᵉ kᵉ {xᵉ} {yᵉ} {x'ᵉ} {y'ᵉ} Hᵉ Kᵉ =
  transitive-cong-ℕᵉ kᵉ (xᵉ *ℕᵉ yᵉ) (xᵉ *ℕᵉ y'ᵉ) (x'ᵉ *ℕᵉ y'ᵉ)
    ( scalar-invariant-cong-ℕ'ᵉ kᵉ xᵉ x'ᵉ y'ᵉ Hᵉ)
    ( scalar-invariant-cong-ℕᵉ kᵉ yᵉ y'ᵉ xᵉ Kᵉ)
```

### The congruence is translation invariant

```agda
translation-invariant-cong-ℕᵉ :
  (kᵉ xᵉ yᵉ zᵉ : ℕᵉ) → cong-ℕᵉ kᵉ xᵉ yᵉ → cong-ℕᵉ kᵉ (zᵉ +ℕᵉ xᵉ) (zᵉ +ℕᵉ yᵉ)
pr1ᵉ (translation-invariant-cong-ℕᵉ kᵉ xᵉ yᵉ zᵉ (pairᵉ dᵉ pᵉ)) = dᵉ
pr2ᵉ (translation-invariant-cong-ℕᵉ kᵉ xᵉ yᵉ zᵉ (pairᵉ dᵉ pᵉ)) =
  pᵉ ∙ᵉ invᵉ (translation-invariant-dist-ℕᵉ zᵉ xᵉ yᵉ)

translation-invariant-cong-ℕ'ᵉ :
  (kᵉ xᵉ yᵉ zᵉ : ℕᵉ) → cong-ℕᵉ kᵉ xᵉ yᵉ → cong-ℕᵉ kᵉ (xᵉ +ℕᵉ zᵉ) (yᵉ +ℕᵉ zᵉ)
translation-invariant-cong-ℕ'ᵉ kᵉ xᵉ yᵉ zᵉ Hᵉ =
  concatenate-eq-cong-eq-ℕᵉ kᵉ
    ( commutative-add-ℕᵉ xᵉ zᵉ)
    ( translation-invariant-cong-ℕᵉ kᵉ xᵉ yᵉ zᵉ Hᵉ)
    ( commutative-add-ℕᵉ zᵉ yᵉ)

step-invariant-cong-ℕᵉ :
  (kᵉ xᵉ yᵉ : ℕᵉ) → cong-ℕᵉ kᵉ xᵉ yᵉ → cong-ℕᵉ kᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ)
step-invariant-cong-ℕᵉ kᵉ xᵉ yᵉ = translation-invariant-cong-ℕ'ᵉ kᵉ xᵉ yᵉ 1

reflects-cong-add-ℕᵉ :
  {kᵉ : ℕᵉ} (xᵉ : ℕᵉ) {yᵉ zᵉ : ℕᵉ} → cong-ℕᵉ kᵉ (xᵉ +ℕᵉ yᵉ) (xᵉ +ℕᵉ zᵉ) → cong-ℕᵉ kᵉ yᵉ zᵉ
pr1ᵉ (reflects-cong-add-ℕᵉ {kᵉ} xᵉ {yᵉ} {zᵉ} (pairᵉ dᵉ pᵉ)) = dᵉ
pr2ᵉ (reflects-cong-add-ℕᵉ {kᵉ} xᵉ {yᵉ} {zᵉ} (pairᵉ dᵉ pᵉ)) =
  pᵉ ∙ᵉ translation-invariant-dist-ℕᵉ xᵉ yᵉ zᵉ

reflects-cong-add-ℕ'ᵉ :
  {kᵉ : ℕᵉ} (xᵉ : ℕᵉ) {yᵉ zᵉ : ℕᵉ} → cong-ℕᵉ kᵉ (add-ℕ'ᵉ xᵉ yᵉ) (add-ℕ'ᵉ xᵉ zᵉ) → cong-ℕᵉ kᵉ yᵉ zᵉ
reflects-cong-add-ℕ'ᵉ {kᵉ} xᵉ {yᵉ} {zᵉ} Hᵉ =
  reflects-cong-add-ℕᵉ xᵉ {yᵉ} {zᵉ}
    ( concatenate-eq-cong-eq-ℕᵉ kᵉ
      ( commutative-add-ℕᵉ xᵉ yᵉ)
      ( Hᵉ)
      ( commutative-add-ℕᵉ zᵉ xᵉ))
```