# Squares in the natural numbers

```agda
module elementary-number-theory.squares-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.decidable-typesᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "square"ᵉ Disambiguation="naturalᵉ number"ᵉ Agda=square-ℕᵉ}} `n²`ᵉ ofᵉ
aᵉ [naturalᵉ number](elementary-number-theory.natural-numbers.mdᵉ) `n`ᵉ isᵉ theᵉ
[product](elementary-number-theory.multiplication-natural-numbers.mdᵉ)

```text
  n²ᵉ :=ᵉ nᵉ *ᵉ nᵉ
```

ofᵉ `n`ᵉ with itself.ᵉ

## Definition

### Squares of natural numbers

```agda
square-ℕᵉ : ℕᵉ → ℕᵉ
square-ℕᵉ nᵉ = mul-ℕᵉ nᵉ nᵉ
```

### The predicate of being a square of a natural number

```agda
is-square-ℕᵉ : ℕᵉ → UUᵉ lzero
is-square-ℕᵉ nᵉ = Σᵉ ℕᵉ (λ xᵉ → nᵉ ＝ᵉ square-ℕᵉ xᵉ)
```

### The square root of a square natural number

```agda
square-root-ℕᵉ : (nᵉ : ℕᵉ) → is-square-ℕᵉ nᵉ → ℕᵉ
square-root-ℕᵉ _ (rootᵉ ,ᵉ _) = rootᵉ
```

## Properties

### Squares of successors

```agda
square-succ-ℕᵉ :
  (nᵉ : ℕᵉ) →
  square-ℕᵉ (succ-ℕᵉ nᵉ) ＝ᵉ succ-ℕᵉ ((succ-ℕᵉ (succ-ℕᵉ nᵉ)) *ℕᵉ nᵉ)
square-succ-ℕᵉ nᵉ =
  ( right-successor-law-mul-ℕᵉ (succ-ℕᵉ nᵉ) nᵉ) ∙ᵉ
  ( commutative-add-ℕᵉ (succ-ℕᵉ nᵉ) ((succ-ℕᵉ nᵉ) *ℕᵉ nᵉ))

square-succ-succ-ℕᵉ :
  (nᵉ : ℕᵉ) →
  square-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) ＝ᵉ square-ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ +ℕᵉ 4
square-succ-succ-ℕᵉ nᵉ =
  equational-reasoningᵉ
  square-ℕᵉ (nᵉ +ℕᵉ 2ᵉ)
  ＝ᵉ (nᵉ +ℕᵉ 2ᵉ) *ℕᵉ nᵉ +ℕᵉ (nᵉ +ℕᵉ 2ᵉ) *ℕᵉ 2
    byᵉ (left-distributive-mul-add-ℕᵉ (nᵉ +ℕᵉ 2ᵉ) nᵉ 2ᵉ)
  ＝ᵉ square-ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ (nᵉ +ℕᵉ 2ᵉ)
    byᵉ
      ( ap-add-ℕᵉ {(nᵉ +ℕᵉ 2ᵉ) *ℕᵉ nᵉ} {(nᵉ +ℕᵉ 2ᵉ) *ℕᵉ 2ᵉ}
        ( right-distributive-mul-add-ℕᵉ nᵉ 2 nᵉ)
        ( commutative-mul-ℕᵉ (nᵉ +ℕᵉ 2ᵉ) 2ᵉ))
  ＝ᵉ square-ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ +ℕᵉ 4
    byᵉ
      ( ap-add-ℕᵉ {square-ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ} {2ᵉ *ℕᵉ (nᵉ +ℕᵉ 2ᵉ)}
        ( reflᵉ)
        ( left-distributive-mul-add-ℕᵉ 2 nᵉ 2ᵉ))
```

### `n > √n` for `n > 1`

Theᵉ ideaᵉ isᵉ to assumeᵉ `nᵉ = mᵉ +ᵉ 2 ≤ᵉ sqrt(mᵉ +ᵉ 2)`ᵉ forᵉ someᵉ `mᵉ : ℕ`ᵉ andᵉ deriveᵉ aᵉ
contradictionᵉ byᵉ squaringᵉ bothᵉ sidesᵉ ofᵉ theᵉ inequalityᵉ

```agda
greater-than-square-root-ℕᵉ :
  (nᵉ rootᵉ : ℕᵉ) → ¬ᵉ ((nᵉ +ℕᵉ 2 ≤-ℕᵉ rootᵉ) ×ᵉ (nᵉ +ℕᵉ 2 ＝ᵉ square-ℕᵉ rootᵉ))
greater-than-square-root-ℕᵉ nᵉ rootᵉ (pf-leqᵉ ,ᵉ pf-eqᵉ) =
  reflects-leq-left-add-ℕᵉ
    ( square-ℕᵉ rootᵉ)
    ( square-ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ +ℕᵉ nᵉ +ℕᵉ 2ᵉ)
    ( 0ᵉ)
    ( trᵉ
      ( leq-ℕᵉ (square-ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ +ℕᵉ nᵉ +ℕᵉ 2 +ℕᵉ square-ℕᵉ rootᵉ))
      ( invᵉ (left-unit-law-add-ℕᵉ (square-ℕᵉ rootᵉ)))
      ( concatenate-eq-leq-ℕᵉ
        ( square-ℕᵉ rootᵉ)
        ( invᵉ
          ( lemmaᵉ ∙ᵉ
            ( ap-add-ℕᵉ {square-ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ +ℕᵉ nᵉ +ℕᵉ 2ᵉ} {nᵉ +ℕᵉ 2ᵉ}
              ( reflᵉ)
              ( pf-eqᵉ))))
        ( preserves-leq-mul-ℕᵉ (nᵉ +ℕᵉ 2ᵉ) rootᵉ (nᵉ +ℕᵉ 2ᵉ) rootᵉ pf-leqᵉ pf-leqᵉ)))
  where
  lemmaᵉ : square-ℕᵉ (nᵉ +ℕᵉ 2ᵉ) ＝ᵉ square-ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ +ℕᵉ nᵉ +ℕᵉ 2 +ℕᵉ nᵉ +ℕᵉ 2
  lemmaᵉ =
    equational-reasoningᵉ
    square-ℕᵉ (nᵉ +ℕᵉ 2ᵉ)
    ＝ᵉ square-ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ +ℕᵉ 4
      byᵉ (square-succ-succ-ℕᵉ nᵉ)
    ＝ᵉ square-ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ +ℕᵉ (nᵉ +ℕᵉ 2 +ℕᵉ nᵉ +ℕᵉ 2ᵉ)
      byᵉ
        ( ap-add-ℕᵉ {square-ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ} {2ᵉ *ℕᵉ nᵉ +ℕᵉ 4ᵉ}
          ( reflᵉ)
          ( equational-reasoningᵉ
            2 *ℕᵉ nᵉ +ℕᵉ 4
            ＝ᵉ nᵉ +ℕᵉ nᵉ +ℕᵉ 2 +ℕᵉ 2
              byᵉ
                ( ap-add-ℕᵉ {2ᵉ *ℕᵉ nᵉ} {4ᵉ}
                  ( left-two-law-mul-ℕᵉ nᵉ)
                  ( reflᵉ))
            ＝ᵉ nᵉ +ℕᵉ 2 +ℕᵉ 2 +ℕᵉ nᵉ
              byᵉ (commutative-add-ℕᵉ nᵉ (nᵉ +ℕᵉ 2 +ℕᵉ 2ᵉ))
            ＝ᵉ nᵉ +ℕᵉ 2 +ℕᵉ (2ᵉ +ℕᵉ nᵉ)
              byᵉ (associative-add-ℕᵉ (nᵉ +ℕᵉ 2ᵉ) 2 nᵉ)
            ＝ᵉ nᵉ +ℕᵉ 2 +ℕᵉ (nᵉ +ℕᵉ 2ᵉ)
              byᵉ
                ( ap-add-ℕᵉ {nᵉ +ℕᵉ 2ᵉ} {2ᵉ +ℕᵉ nᵉ}
                  ( reflᵉ)
                  ( commutative-add-ℕᵉ 2 nᵉ))))
    ＝ᵉ square-ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ +ℕᵉ nᵉ +ℕᵉ 2 +ℕᵉ nᵉ +ℕᵉ 2
      byᵉ
        ( invᵉ
          ( associative-add-ℕᵉ
            ( square-ℕᵉ nᵉ +ℕᵉ 2 *ℕᵉ nᵉ)
            ( nᵉ +ℕᵉ 2ᵉ)
            ( nᵉ +ℕᵉ 2ᵉ)))
```

### Squareness in ℕ is decidable

```agda
is-decidable-big-rootᵉ :
  (nᵉ : ℕᵉ) → is-decidableᵉ (Σᵉ ℕᵉ (λ rootᵉ → (nᵉ ≤-ℕᵉ rootᵉ) ×ᵉ (nᵉ ＝ᵉ square-ℕᵉ rootᵉ)))
is-decidable-big-rootᵉ 0 = inlᵉ (0ᵉ ,ᵉ starᵉ ,ᵉ reflᵉ)
is-decidable-big-rootᵉ 1 = inlᵉ (1ᵉ ,ᵉ starᵉ ,ᵉ reflᵉ)
is-decidable-big-rootᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) =
  inrᵉ (λ Hᵉ → greater-than-square-root-ℕᵉ nᵉ (pr1ᵉ Hᵉ) (pr2ᵉ Hᵉ))

is-decidable-is-square-ℕᵉ : (nᵉ : ℕᵉ) → is-decidableᵉ (is-square-ℕᵉ nᵉ)
is-decidable-is-square-ℕᵉ nᵉ =
  is-decidable-Σ-ℕᵉ nᵉ
    ( λ xᵉ → nᵉ ＝ᵉ square-ℕᵉ xᵉ)
    ( λ xᵉ → has-decidable-equality-ℕᵉ nᵉ (square-ℕᵉ xᵉ))
    ( is-decidable-big-rootᵉ nᵉ)
```

## See also

-ᵉ [Cubesᵉ ofᵉ naturalᵉ numbers](elementary-number-theory.cubes-natural-numbers.mdᵉ)