# The natural numbers base `k`

```agda
module elementary-number-theory.finitary-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.congruence-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Definition

### The finitary natural numbers

```agda
data based-ℕᵉ : ℕᵉ → UUᵉ lzero where
  constant-based-ℕᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → based-ℕᵉ kᵉ
  unary-op-based-ℕᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → based-ℕᵉ kᵉ → based-ℕᵉ kᵉ
```

### Converting a `k`-ary natural number to a natural number

```agda
constant-ℕᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → ℕᵉ
constant-ℕᵉ kᵉ xᵉ = nat-Finᵉ kᵉ xᵉ

unary-op-ℕᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → ℕᵉ → ℕᵉ
unary-op-ℕᵉ kᵉ xᵉ nᵉ = (kᵉ *ℕᵉ (succ-ℕᵉ nᵉ)) +ℕᵉ (nat-Finᵉ kᵉ xᵉ)

convert-based-ℕᵉ : (kᵉ : ℕᵉ) → based-ℕᵉ kᵉ → ℕᵉ
convert-based-ℕᵉ kᵉ (constant-based-ℕᵉ .kᵉ xᵉ) =
  constant-ℕᵉ kᵉ xᵉ
convert-based-ℕᵉ kᵉ (unary-op-based-ℕᵉ .kᵉ xᵉ nᵉ) =
  unary-op-ℕᵉ kᵉ xᵉ (convert-based-ℕᵉ kᵉ nᵉ)
```

### The type of `0`-ary natural numbers is empty

```agda
is-empty-based-zero-ℕᵉ : is-emptyᵉ (based-ℕᵉ zero-ℕᵉ)
is-empty-based-zero-ℕᵉ (constant-based-ℕᵉ .zero-ℕᵉ ())
is-empty-based-zero-ℕᵉ (unary-op-based-ℕᵉ .zero-ℕᵉ () nᵉ)
```

### The function `convert-based-ℕ` is injective

```agda
cong-unary-op-ℕᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) (nᵉ : ℕᵉ) →
  cong-ℕᵉ kᵉ (unary-op-ℕᵉ kᵉ xᵉ nᵉ) (nat-Finᵉ kᵉ xᵉ)
cong-unary-op-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ nᵉ =
  concatenate-cong-eq-ℕᵉ
    ( succ-ℕᵉ kᵉ)
    { unary-op-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ nᵉ}
    ( translation-invariant-cong-ℕ'ᵉ
      ( succ-ℕᵉ kᵉ)
      ( (succ-ℕᵉ kᵉ) *ℕᵉ (succ-ℕᵉ nᵉ))
      ( zero-ℕᵉ)
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
      ( pairᵉ (succ-ℕᵉ nᵉ) (commutative-mul-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ kᵉ))))
    ( left-unit-law-add-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))
```

### Any natural number of the form `constant-ℕ k x` is strictly less than any natural number of the form `unary-op-ℕ k y m`

```agda
le-constant-unary-op-ℕᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) (mᵉ : ℕᵉ) → le-ℕᵉ (constant-ℕᵉ kᵉ xᵉ) (unary-op-ℕᵉ kᵉ yᵉ mᵉ)
le-constant-unary-op-ℕᵉ kᵉ xᵉ yᵉ mᵉ =
  concatenate-le-leq-ℕᵉ {nat-Finᵉ kᵉ xᵉ} {kᵉ} {unary-op-ℕᵉ kᵉ yᵉ mᵉ}
    ( strict-upper-bound-nat-Finᵉ kᵉ xᵉ)
    ( transitive-leq-ℕᵉ
      ( kᵉ)
      ( kᵉ *ℕᵉ (succ-ℕᵉ mᵉ))
      ( unary-op-ℕᵉ kᵉ yᵉ mᵉ)
      ( leq-add-ℕᵉ (kᵉ *ℕᵉ (succ-ℕᵉ mᵉ)) (nat-Finᵉ kᵉ yᵉ))
      ( leq-mul-ℕᵉ mᵉ kᵉ))

is-injective-convert-based-ℕᵉ :
  (kᵉ : ℕᵉ) → is-injectiveᵉ (convert-based-ℕᵉ kᵉ)
is-injective-convert-based-ℕᵉ
  ( succ-ℕᵉ kᵉ)
  { constant-based-ℕᵉ .(succ-ℕᵉ kᵉ) xᵉ}
  { constant-based-ℕᵉ .(succ-ℕᵉ kᵉ) yᵉ} pᵉ =
  apᵉ (constant-based-ℕᵉ (succ-ℕᵉ kᵉ)) (is-injective-nat-Finᵉ (succ-ℕᵉ kᵉ) pᵉ)
is-injective-convert-based-ℕᵉ
  ( succ-ℕᵉ kᵉ)
  { constant-based-ℕᵉ .(succ-ℕᵉ kᵉ) xᵉ}
  { unary-op-based-ℕᵉ .(succ-ℕᵉ kᵉ) yᵉ mᵉ} pᵉ =
  ex-falsoᵉ
    ( neq-le-ℕᵉ
      ( le-constant-unary-op-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ (convert-based-ℕᵉ (succ-ℕᵉ kᵉ) mᵉ))
      ( pᵉ))
is-injective-convert-based-ℕᵉ
  ( succ-ℕᵉ kᵉ)
  { unary-op-based-ℕᵉ .(succ-ℕᵉ kᵉ) xᵉ nᵉ}
  { constant-based-ℕᵉ .(succ-ℕᵉ kᵉ) yᵉ} pᵉ =
  ex-falsoᵉ
    ( neq-le-ℕᵉ
      ( le-constant-unary-op-ℕᵉ (succ-ℕᵉ kᵉ) yᵉ xᵉ (convert-based-ℕᵉ (succ-ℕᵉ kᵉ) nᵉ))
      ( invᵉ pᵉ))
is-injective-convert-based-ℕᵉ
  ( succ-ℕᵉ kᵉ)
  { unary-op-based-ℕᵉ .(succ-ℕᵉ kᵉ) xᵉ nᵉ}
  { unary-op-based-ℕᵉ .(succ-ℕᵉ kᵉ) yᵉ mᵉ} pᵉ with
  is-injective-nat-Finᵉ (succ-ℕᵉ kᵉ) {xᵉ} {yᵉ}
    ( eq-cong-le-ℕᵉ
      ( succ-ℕᵉ kᵉ)
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ)
      ( strict-upper-bound-nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
      ( strict-upper-bound-nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ)
      ( concatenate-cong-eq-cong-ℕᵉ
        { succ-ℕᵉ kᵉ}
        { nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ}
        { unary-op-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ (convert-based-ℕᵉ (succ-ℕᵉ kᵉ) nᵉ)}
        { unary-op-ℕᵉ (succ-ℕᵉ kᵉ) yᵉ (convert-based-ℕᵉ (succ-ℕᵉ kᵉ) mᵉ)}
        { nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ}
        ( symmetric-cong-ℕᵉ
          ( succ-ℕᵉ kᵉ)
          ( unary-op-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ (convert-based-ℕᵉ (succ-ℕᵉ kᵉ) nᵉ))
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
          ( cong-unary-op-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ (convert-based-ℕᵉ (succ-ℕᵉ kᵉ) nᵉ)))
        ( pᵉ)
        ( cong-unary-op-ℕᵉ (succ-ℕᵉ kᵉ) yᵉ (convert-based-ℕᵉ (succ-ℕᵉ kᵉ) mᵉ))))
... | reflᵉ =
  apᵉ
    ( unary-op-based-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ)
    ( is-injective-convert-based-ℕᵉ (succ-ℕᵉ kᵉ)
      ( is-injective-succ-ℕᵉ
        ( is-injective-left-mul-succ-ℕᵉ kᵉ
          ( is-injective-right-add-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) pᵉ))))
```

### The zero-element of the `k+1`-ary natural numbers

```agda
zero-based-ℕᵉ : (kᵉ : ℕᵉ) → based-ℕᵉ (succ-ℕᵉ kᵉ)
zero-based-ℕᵉ kᵉ = constant-based-ℕᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ)
```

### The successor function on the `k`-ary natural numbers

```agda
succ-based-ℕᵉ : (kᵉ : ℕᵉ) → based-ℕᵉ kᵉ → based-ℕᵉ kᵉ
succ-based-ℕᵉ (succ-ℕᵉ kᵉ) (constant-based-ℕᵉ .(succ-ℕᵉ kᵉ) (inlᵉ xᵉ)) =
  constant-based-ℕᵉ (succ-ℕᵉ kᵉ) (succ-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ))
succ-based-ℕᵉ (succ-ℕᵉ kᵉ) (constant-based-ℕᵉ .(succ-ℕᵉ kᵉ) (inrᵉ _)) =
  unary-op-based-ℕᵉ
    (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ) (constant-based-ℕᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ))
succ-based-ℕᵉ (succ-ℕᵉ kᵉ) (unary-op-based-ℕᵉ .(succ-ℕᵉ kᵉ) (inlᵉ xᵉ) nᵉ) =
  unary-op-based-ℕᵉ (succ-ℕᵉ kᵉ) (succ-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ)) nᵉ
succ-based-ℕᵉ (succ-ℕᵉ kᵉ) (unary-op-based-ℕᵉ .(succ-ℕᵉ kᵉ) (inrᵉ xᵉ) nᵉ) =
  unary-op-based-ℕᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ) (succ-based-ℕᵉ (succ-ℕᵉ kᵉ) nᵉ)
```

### The inverse map of `convert-based-ℕ`

```agda
inv-convert-based-ℕᵉ : (kᵉ : ℕᵉ) → ℕᵉ → based-ℕᵉ (succ-ℕᵉ kᵉ)
inv-convert-based-ℕᵉ kᵉ zero-ℕᵉ =
  zero-based-ℕᵉ kᵉ
inv-convert-based-ℕᵉ kᵉ (succ-ℕᵉ nᵉ) =
  succ-based-ℕᵉ (succ-ℕᵉ kᵉ) (inv-convert-based-ℕᵉ kᵉ nᵉ)

convert-based-succ-based-ℕᵉ :
  (kᵉ : ℕᵉ) (xᵉ : based-ℕᵉ kᵉ) →
  convert-based-ℕᵉ kᵉ (succ-based-ℕᵉ kᵉ xᵉ) ＝ᵉ succ-ℕᵉ (convert-based-ℕᵉ kᵉ xᵉ)
convert-based-succ-based-ℕᵉ (succ-ℕᵉ kᵉ) (constant-based-ℕᵉ .(succ-ℕᵉ kᵉ) (inlᵉ xᵉ)) =
  nat-succ-Finᵉ kᵉ xᵉ
convert-based-succ-based-ℕᵉ
  ( succ-ℕᵉ kᵉ) (constant-based-ℕᵉ .(succ-ℕᵉ kᵉ) (inrᵉ _)) =
  ( apᵉ
    ( λ tᵉ → ((succ-ℕᵉ kᵉ) *ℕᵉ (succ-ℕᵉ tᵉ)) +ℕᵉ tᵉ)
    ( is-zero-nat-zero-Finᵉ {kᵉ})) ∙ᵉ
  ( right-unit-law-mul-ℕᵉ (succ-ℕᵉ kᵉ))
convert-based-succ-based-ℕᵉ (succ-ℕᵉ kᵉ) (unary-op-based-ℕᵉ .(succ-ℕᵉ kᵉ) (inlᵉ xᵉ) nᵉ) =
  apᵉ
    ( ((succ-ℕᵉ kᵉ) *ℕᵉ (succ-ℕᵉ (convert-based-ℕᵉ (succ-ℕᵉ kᵉ) nᵉ))) +ℕᵉ_)
    ( nat-succ-Finᵉ kᵉ xᵉ)
convert-based-succ-based-ℕᵉ
  (succ-ℕᵉ kᵉ) (unary-op-based-ℕᵉ .(succ-ℕᵉ kᵉ) (inrᵉ _) nᵉ) =
  ( apᵉ
    ( ( ( succ-ℕᵉ kᵉ) *ℕᵉ
        ( succ-ℕᵉ (convert-based-ℕᵉ (succ-ℕᵉ kᵉ) (succ-based-ℕᵉ (succ-ℕᵉ kᵉ) nᵉ))))
          +ℕᵉ_)
    ( is-zero-nat-zero-Finᵉ {kᵉ})) ∙ᵉ
  ( ( apᵉ
      ( ((succ-ℕᵉ kᵉ) *ℕᵉ_) ∘ᵉ succ-ℕᵉ)
      ( convert-based-succ-based-ℕᵉ (succ-ℕᵉ kᵉ) nᵉ)) ∙ᵉ
    ( ( right-successor-law-mul-ℕᵉ
        ( succ-ℕᵉ kᵉ)
        ( succ-ℕᵉ (convert-based-ℕᵉ (succ-ℕᵉ kᵉ) nᵉ))) ∙ᵉ
      ( commutative-add-ℕᵉ
        ( succ-ℕᵉ kᵉ)
        ( (succ-ℕᵉ kᵉ) *ℕᵉ (succ-ℕᵉ (convert-based-ℕᵉ (succ-ℕᵉ kᵉ) nᵉ))))))

is-section-inv-convert-based-ℕᵉ :
  (kᵉ nᵉ : ℕᵉ) → convert-based-ℕᵉ (succ-ℕᵉ kᵉ) (inv-convert-based-ℕᵉ kᵉ nᵉ) ＝ᵉ nᵉ
is-section-inv-convert-based-ℕᵉ kᵉ zero-ℕᵉ = is-zero-nat-zero-Finᵉ {kᵉ}
is-section-inv-convert-based-ℕᵉ kᵉ (succ-ℕᵉ nᵉ) =
  ( convert-based-succ-based-ℕᵉ (succ-ℕᵉ kᵉ) (inv-convert-based-ℕᵉ kᵉ nᵉ)) ∙ᵉ
  ( apᵉ succ-ℕᵉ (is-section-inv-convert-based-ℕᵉ kᵉ nᵉ))

is-retraction-inv-convert-based-ℕᵉ :
  (kᵉ : ℕᵉ) (xᵉ : based-ℕᵉ (succ-ℕᵉ kᵉ)) →
  inv-convert-based-ℕᵉ kᵉ (convert-based-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ) ＝ᵉ xᵉ
is-retraction-inv-convert-based-ℕᵉ kᵉ xᵉ =
  is-injective-convert-based-ℕᵉ
    ( succ-ℕᵉ kᵉ)
    ( is-section-inv-convert-based-ℕᵉ kᵉ (convert-based-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ))
```