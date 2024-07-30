# The type of natural numbers

```agda
module elementary-number-theory.natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.empty-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.negationᵉ
```

</details>

## Idea

The **natural numbers** is an inductively generated type by the zero element and
the successor function. The induction principle for the natural numbers works to
construct sections of type families over the natural numbers.

## Definitions

### The inductive definition of the type of natural numbers

```agda
data ℕᵉ : UUᵉ lzero where
  zero-ℕᵉ : ℕᵉ
  succ-ℕᵉ : ℕᵉ → ℕᵉ

pattern 0ᵉ = zero-ℕᵉ

1ᵉ : ℕᵉ
1ᵉ = succ-ℕᵉ zero-ℕᵉ

2ᵉ : ℕᵉ
2ᵉ = succ-ℕᵉ 1ᵉ

3ᵉ : ℕᵉ
3ᵉ = succ-ℕᵉ 2ᵉ

4ᵉ : ℕᵉ
4ᵉ = succ-ℕᵉ 3ᵉ

5ᵉ : ℕᵉ
5ᵉ = succ-ℕᵉ 4ᵉ

6ᵉ : ℕᵉ
6ᵉ = succ-ℕᵉ 5ᵉ

7ᵉ : ℕᵉ
7ᵉ = succ-ℕᵉ 6ᵉ

8ᵉ : ℕᵉ
8ᵉ = succ-ℕᵉ 7ᵉ

9ᵉ : ℕᵉ
9ᵉ = succ-ℕᵉ 8ᵉ

10ᵉ : ℕᵉ
10ᵉ = succ-ℕᵉ 9ᵉ

11ᵉ : ℕᵉ
11ᵉ = succ-ℕᵉ 10ᵉ

12ᵉ : ℕᵉ
12ᵉ = succ-ℕᵉ 11ᵉ

13ᵉ : ℕᵉ
13ᵉ = succ-ℕᵉ 12ᵉ

14ᵉ : ℕᵉ
14ᵉ = succ-ℕᵉ 13ᵉ

15ᵉ : ℕᵉ
15ᵉ = succ-ℕᵉ 14ᵉ

16ᵉ : ℕᵉ
16ᵉ = succ-ℕᵉ 15ᵉ

17ᵉ : ℕᵉ
17ᵉ = succ-ℕᵉ 16ᵉ

18ᵉ : ℕᵉ
18ᵉ = succ-ℕᵉ 17ᵉ

second-succ-ℕᵉ : ℕᵉ → ℕᵉ
second-succ-ℕᵉ = succ-ℕᵉ ∘ᵉ succ-ℕᵉ

third-succ-ℕᵉ : ℕᵉ → ℕᵉ
third-succ-ℕᵉ = succ-ℕᵉ ∘ᵉ second-succ-ℕᵉ

fourth-succ-ℕᵉ : ℕᵉ → ℕᵉ
fourth-succ-ℕᵉ = succ-ℕᵉ ∘ᵉ third-succ-ℕᵉ
```

### Useful predicates on the natural numbers

These predicates can of course be asserted directly without much trouble.
However, using the defined predicates ensures uniformity, and helps naming
definitions.

```agda
is-zero-ℕᵉ : ℕᵉ → UUᵉ lzero
is-zero-ℕᵉ nᵉ = (nᵉ ＝ᵉ zero-ℕᵉ)

is-zero-ℕ'ᵉ : ℕᵉ → UUᵉ lzero
is-zero-ℕ'ᵉ nᵉ = (zero-ℕᵉ ＝ᵉ nᵉ)

is-successor-ℕᵉ : ℕᵉ → UUᵉ lzero
is-successor-ℕᵉ nᵉ = Σᵉ ℕᵉ (λ yᵉ → nᵉ ＝ᵉ succ-ℕᵉ yᵉ)

is-nonzero-ℕᵉ : ℕᵉ → UUᵉ lzero
is-nonzero-ℕᵉ nᵉ = ¬ᵉ (is-zero-ℕᵉ nᵉ)

is-one-ℕᵉ : ℕᵉ → UUᵉ lzero
is-one-ℕᵉ nᵉ = (nᵉ ＝ᵉ 1ᵉ)

is-one-ℕ'ᵉ : ℕᵉ → UUᵉ lzero
is-one-ℕ'ᵉ nᵉ = (1ᵉ ＝ᵉ nᵉ)

is-not-one-ℕᵉ : ℕᵉ → UUᵉ lzero
is-not-one-ℕᵉ nᵉ = ¬ᵉ (is-one-ℕᵉ nᵉ)

is-not-one-ℕ'ᵉ : ℕᵉ → UUᵉ lzero
is-not-one-ℕ'ᵉ nᵉ = ¬ᵉ (is-one-ℕ'ᵉ nᵉ)
```

## Properties

### The induction principle of ℕ

```agda
ind-ℕᵉ :
  {lᵉ : Level} {Pᵉ : ℕᵉ → UUᵉ lᵉ} →
  Pᵉ 0ᵉ → ((nᵉ : ℕᵉ) → Pᵉ nᵉ → Pᵉ (succ-ℕᵉ nᵉ)) → ((nᵉ : ℕᵉ) → Pᵉ nᵉ)
ind-ℕᵉ p-zeroᵉ p-succᵉ 0ᵉ = p-zeroᵉ
ind-ℕᵉ p-zeroᵉ p-succᵉ (succ-ℕᵉ nᵉ) = p-succᵉ nᵉ (ind-ℕᵉ p-zeroᵉ p-succᵉ nᵉ)
```

### The recursion principle of ℕ

```agda
rec-ℕᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → Aᵉ → (ℕᵉ → Aᵉ → Aᵉ) → (ℕᵉ → Aᵉ)
rec-ℕᵉ = ind-ℕᵉ
```

### The successor function on ℕ is injective

```agda
is-injective-succ-ℕᵉ : is-injectiveᵉ succ-ℕᵉ
is-injective-succ-ℕᵉ reflᵉ = reflᵉ
```

### Successors are nonzero

```agda
is-nonzero-succ-ℕᵉ : (xᵉ : ℕᵉ) → is-nonzero-ℕᵉ (succ-ℕᵉ xᵉ)
is-nonzero-succ-ℕᵉ xᵉ ()

is-nonzero-is-successor-ℕᵉ : {xᵉ : ℕᵉ} → is-successor-ℕᵉ xᵉ → is-nonzero-ℕᵉ xᵉ
is-nonzero-is-successor-ℕᵉ (xᵉ ,ᵉ reflᵉ) ()

is-successor-is-nonzero-ℕᵉ : {xᵉ : ℕᵉ} → is-nonzero-ℕᵉ xᵉ → is-successor-ℕᵉ xᵉ
is-successor-is-nonzero-ℕᵉ {zero-ℕᵉ} Hᵉ = ex-falsoᵉ (Hᵉ reflᵉ)
pr1ᵉ (is-successor-is-nonzero-ℕᵉ {succ-ℕᵉ xᵉ} Hᵉ) = xᵉ
pr2ᵉ (is-successor-is-nonzero-ℕᵉ {succ-ℕᵉ xᵉ} Hᵉ) = reflᵉ

has-no-fixed-points-succ-ℕᵉ : (xᵉ : ℕᵉ) → ¬ᵉ (succ-ℕᵉ xᵉ ＝ᵉ xᵉ)
has-no-fixed-points-succ-ℕᵉ xᵉ ()
```

### Basic nonequalities

```agda
is-nonzero-one-ℕᵉ : is-nonzero-ℕᵉ 1ᵉ
is-nonzero-one-ℕᵉ ()

is-not-one-zero-ℕᵉ : is-not-one-ℕᵉ zero-ℕᵉ
is-not-one-zero-ℕᵉ ()

is-nonzero-two-ℕᵉ : is-nonzero-ℕᵉ 2ᵉ
is-nonzero-two-ℕᵉ ()

is-not-one-two-ℕᵉ : is-not-one-ℕᵉ 2ᵉ
is-not-one-two-ℕᵉ ()
```

## See also

- The based induction principle is defined in
  [`based-induction-natural-numbers`](elementary-number-theory.based-induction-natural-numbers.md).
- The strong induction principle is defined in
  [`strong-induction-natural-numbers`](elementary-number-theory.strong-induction-natural-numbers.md).
- The based strong induction principle is defined in
  [`based-strong-induction-natural-numbers`](elementary-number-theory.based-strong-induction-natural-numbers.md).
