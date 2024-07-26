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

Theᵉ **naturalᵉ numbers**ᵉ isᵉ anᵉ inductivelyᵉ generatedᵉ typeᵉ byᵉ theᵉ zeroᵉ elementᵉ andᵉ
theᵉ successorᵉ function.ᵉ Theᵉ inductionᵉ principleᵉ forᵉ theᵉ naturalᵉ numbersᵉ worksᵉ to
constructᵉ sectionsᵉ ofᵉ typeᵉ familiesᵉ overᵉ theᵉ naturalᵉ numbers.ᵉ

## Definitions

### The inductive definition of the type of natural numbers

```agda
data ℕᵉ : UUᵉ lzero where
  zero-ℕᵉ : ℕᵉ
  succ-ℕᵉ : ℕᵉ → ℕᵉ

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

second-succ-ℕᵉ : ℕᵉ → ℕᵉ
second-succ-ℕᵉ = succ-ℕᵉ ∘ᵉ succ-ℕᵉ

third-succ-ℕᵉ : ℕᵉ → ℕᵉ
third-succ-ℕᵉ = succ-ℕᵉ ∘ᵉ second-succ-ℕᵉ

fourth-succ-ℕᵉ : ℕᵉ → ℕᵉ
fourth-succ-ℕᵉ = succ-ℕᵉ ∘ᵉ third-succ-ℕᵉ
```

### Useful predicates on the natural numbers

Theseᵉ predicatesᵉ canᵉ ofᵉ courseᵉ beᵉ assertedᵉ directlyᵉ withoutᵉ muchᵉ trouble.ᵉ
However,ᵉ using theᵉ definedᵉ predicatesᵉ ensuresᵉ uniformity,ᵉ andᵉ helpsᵉ namingᵉ
definitions.ᵉ

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
  Pᵉ zero-ℕᵉ → ((nᵉ : ℕᵉ) → Pᵉ nᵉ → Pᵉ (succ-ℕᵉ nᵉ)) → ((nᵉ : ℕᵉ) → Pᵉ nᵉ)
ind-ℕᵉ p-zeroᵉ p-succᵉ zero-ℕᵉ = p-zeroᵉ
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

-ᵉ Theᵉ basedᵉ inductionᵉ principleᵉ isᵉ definedᵉ in
  [`based-induction-natural-numbers`](elementary-number-theory.based-induction-natural-numbers.md).ᵉ
-ᵉ Theᵉ strongᵉ inductionᵉ principleᵉ isᵉ definedᵉ in
  [`strong-induction-natural-numbers`](elementary-number-theory.strong-induction-natural-numbers.md).ᵉ
-ᵉ Theᵉ basedᵉ strongᵉ inductionᵉ principleᵉ isᵉ definedᵉ in
  [`based-strong-induction-natural-numbers`](elementary-number-theory.based-strong-induction-natural-numbers.md).ᵉ
