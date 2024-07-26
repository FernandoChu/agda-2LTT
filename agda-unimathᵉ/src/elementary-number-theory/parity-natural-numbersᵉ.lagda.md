# Parity of the natural numbers

```agda
module elementary-number-theory.parity-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Parityᵉ partitionsᵉ theᵉ naturalᵉ numbersᵉ intoᵉ twoᵉ classesᵉ: theᵉ evenᵉ andᵉ theᵉ oddᵉ
naturalᵉ numbers.ᵉ Evenᵉ naturalᵉ numbersᵉ areᵉ thoseᵉ thatᵉ areᵉ divisibleᵉ byᵉ two,ᵉ andᵉ
oddᵉ naturalᵉ numbersᵉ areᵉ thoseᵉ thatᵉ aren't.ᵉ

## Definition

```agda
is-even-ℕᵉ : ℕᵉ → UUᵉ lzero
is-even-ℕᵉ nᵉ = div-ℕᵉ 2 nᵉ

is-odd-ℕᵉ : ℕᵉ → UUᵉ lzero
is-odd-ℕᵉ nᵉ = ¬ᵉ (is-even-ℕᵉ nᵉ)
```

## Properties

### Being even or odd is decidable

```agda
is-decidable-is-even-ℕᵉ : (xᵉ : ℕᵉ) → is-decidableᵉ (is-even-ℕᵉ xᵉ)
is-decidable-is-even-ℕᵉ xᵉ = is-decidable-div-ℕᵉ 2 xᵉ

is-decidable-is-odd-ℕᵉ : (xᵉ : ℕᵉ) → is-decidableᵉ (is-odd-ℕᵉ xᵉ)
is-decidable-is-odd-ℕᵉ xᵉ = is-decidable-negᵉ (is-decidable-is-even-ℕᵉ xᵉ)
```

### `0` is an even natural number

```agda
is-even-zero-ℕᵉ : is-even-ℕᵉ 0
is-even-zero-ℕᵉ = div-zero-ℕᵉ 2

is-odd-one-ℕᵉ : is-odd-ℕᵉ 1
is-odd-one-ℕᵉ Hᵉ = Eq-eq-ℕᵉ (is-one-div-one-ℕᵉ 2 Hᵉ)
```

### A natural number `x` is even if and only if `x + 2` is even

```agda
is-even-is-even-succ-succ-ℕᵉ :
  (nᵉ : ℕᵉ) → is-even-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) → is-even-ℕᵉ nᵉ
pr1ᵉ (is-even-is-even-succ-succ-ℕᵉ nᵉ (succ-ℕᵉ dᵉ ,ᵉ pᵉ)) = dᵉ
pr2ᵉ (is-even-is-even-succ-succ-ℕᵉ nᵉ (succ-ℕᵉ dᵉ ,ᵉ pᵉ)) =
  is-injective-succ-ℕᵉ (is-injective-succ-ℕᵉ pᵉ)

is-even-succ-succ-is-even-ℕᵉ :
  (nᵉ : ℕᵉ) → is-even-ℕᵉ nᵉ → is-even-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))
pr1ᵉ (is-even-succ-succ-is-even-ℕᵉ nᵉ (dᵉ ,ᵉ pᵉ)) = succ-ℕᵉ dᵉ
pr2ᵉ (is-even-succ-succ-is-even-ℕᵉ nᵉ (dᵉ ,ᵉ pᵉ)) = apᵉ (succ-ℕᵉ ∘ᵉ succ-ℕᵉ) pᵉ
```

### A natural number `x` is odd if and only if `x + 2` is odd

```agda
is-odd-is-odd-succ-succ-ℕᵉ :
  (nᵉ : ℕᵉ) → is-odd-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) → is-odd-ℕᵉ nᵉ
is-odd-is-odd-succ-succ-ℕᵉ nᵉ = map-negᵉ (is-even-succ-succ-is-even-ℕᵉ nᵉ)

is-odd-succ-succ-is-odd-ℕᵉ :
  (nᵉ : ℕᵉ) → is-odd-ℕᵉ nᵉ → is-odd-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))
is-odd-succ-succ-is-odd-ℕᵉ nᵉ = map-negᵉ (is-even-is-even-succ-succ-ℕᵉ nᵉ)
```

### If a natural number `x` is odd, then `x + 1` is even

```agda
is-even-succ-is-odd-ℕᵉ :
  (nᵉ : ℕᵉ) → is-odd-ℕᵉ nᵉ → is-even-ℕᵉ (succ-ℕᵉ nᵉ)
is-even-succ-is-odd-ℕᵉ zero-ℕᵉ pᵉ = ex-falsoᵉ (pᵉ is-even-zero-ℕᵉ)
is-even-succ-is-odd-ℕᵉ (succ-ℕᵉ zero-ℕᵉ) pᵉ = (1ᵉ ,ᵉ reflᵉ)
is-even-succ-is-odd-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) pᵉ =
  is-even-succ-succ-is-even-ℕᵉ
    ( succ-ℕᵉ nᵉ)
    ( is-even-succ-is-odd-ℕᵉ nᵉ (is-odd-is-odd-succ-succ-ℕᵉ nᵉ pᵉ))
```

### If a natural number `x` is even, then `x + 1` is odd

```agda
is-odd-succ-is-even-ℕᵉ :
  (nᵉ : ℕᵉ) → is-even-ℕᵉ nᵉ → is-odd-ℕᵉ (succ-ℕᵉ nᵉ)
is-odd-succ-is-even-ℕᵉ zero-ℕᵉ pᵉ = is-odd-one-ℕᵉ
is-odd-succ-is-even-ℕᵉ (succ-ℕᵉ zero-ℕᵉ) pᵉ = ex-falsoᵉ (is-odd-one-ℕᵉ pᵉ)
is-odd-succ-is-even-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) pᵉ =
  is-odd-succ-succ-is-odd-ℕᵉ
    ( succ-ℕᵉ nᵉ)
    ( is-odd-succ-is-even-ℕᵉ nᵉ (is-even-is-even-succ-succ-ℕᵉ nᵉ pᵉ))
```

### If a natural number `x + 1` is odd, then `x` is even

```agda
is-even-is-odd-succ-ℕᵉ :
  (nᵉ : ℕᵉ) → is-odd-ℕᵉ (succ-ℕᵉ nᵉ) → is-even-ℕᵉ nᵉ
is-even-is-odd-succ-ℕᵉ nᵉ pᵉ =
  is-even-is-even-succ-succ-ℕᵉ
    ( nᵉ)
    ( is-even-succ-is-odd-ℕᵉ (succ-ℕᵉ nᵉ) pᵉ)
```

### If a natural number `x + 1` is even, then `x` is odd

```agda
is-odd-is-even-succ-ℕᵉ :
  (nᵉ : ℕᵉ) → is-even-ℕᵉ (succ-ℕᵉ nᵉ) → is-odd-ℕᵉ nᵉ
is-odd-is-even-succ-ℕᵉ nᵉ pᵉ =
  is-odd-is-odd-succ-succ-ℕᵉ
    ( nᵉ)
    ( is-odd-succ-is-even-ℕᵉ (succ-ℕᵉ nᵉ) pᵉ)
```

### A natural number `x` is odd if and only if there is a natural number `y` such that `succ-ℕ (y *ℕ 2) ＝ x`

```agda
has-odd-expansionᵉ : ℕᵉ → UUᵉ lzero
has-odd-expansionᵉ xᵉ = Σᵉ ℕᵉ (λ yᵉ → (succ-ℕᵉ (yᵉ *ℕᵉ 2ᵉ)) ＝ᵉ xᵉ)

is-odd-has-odd-expansionᵉ : (nᵉ : ℕᵉ) → has-odd-expansionᵉ nᵉ → is-odd-ℕᵉ nᵉ
is-odd-has-odd-expansionᵉ .(succ-ℕᵉ (mᵉ *ℕᵉ 2ᵉ)) (mᵉ ,ᵉ reflᵉ) =
  is-odd-succ-is-even-ℕᵉ (mᵉ *ℕᵉ 2ᵉ) (mᵉ ,ᵉ reflᵉ)

has-odd-expansion-is-oddᵉ : (nᵉ : ℕᵉ) → is-odd-ℕᵉ nᵉ → has-odd-expansionᵉ nᵉ
has-odd-expansion-is-oddᵉ zero-ℕᵉ pᵉ = ex-falsoᵉ (pᵉ is-even-zero-ℕᵉ)
has-odd-expansion-is-oddᵉ (succ-ℕᵉ zero-ℕᵉ) pᵉ = 0 ,ᵉ reflᵉ
has-odd-expansion-is-oddᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) pᵉ =
  ( succ-ℕᵉ (pr1ᵉ sᵉ)) ,ᵉ apᵉ (succ-ℕᵉ ∘ᵉ succ-ℕᵉ) (pr2ᵉ sᵉ)
  where
  sᵉ : has-odd-expansionᵉ nᵉ
  sᵉ = has-odd-expansion-is-oddᵉ nᵉ (is-odd-is-odd-succ-succ-ℕᵉ nᵉ pᵉ)
```