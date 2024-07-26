# Truncation levels

```agda
module foundation-core.truncation-levelsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ **truncationᵉ levels**ᵉ isᵉ aᵉ typeᵉ similarᵉ to theᵉ typeᵉ ofᵉ
[naturalᵉ numbers](elementary-number-theory.natural-numbers.md),ᵉ butᵉ startingᵉ theᵉ
countᵉ atᵉ -2,ᵉ soᵉ thatᵉ [sets](foundation-core.sets.mdᵉ) haveᵉ
[truncation](foundation-core.truncated-types.mdᵉ) levelᵉ 0.ᵉ

## Definitions

### The type of truncation levels

```agda
data 𝕋ᵉ : UUᵉ lzero where
  neg-two-𝕋ᵉ : 𝕋ᵉ
  succ-𝕋ᵉ : 𝕋ᵉ → 𝕋ᵉ
```

### Aliases for common truncation levels

```agda
neg-one-𝕋ᵉ : 𝕋ᵉ
neg-one-𝕋ᵉ = succ-𝕋ᵉ neg-two-𝕋ᵉ

zero-𝕋ᵉ : 𝕋ᵉ
zero-𝕋ᵉ = succ-𝕋ᵉ neg-one-𝕋ᵉ

one-𝕋ᵉ : 𝕋ᵉ
one-𝕋ᵉ = succ-𝕋ᵉ zero-𝕋ᵉ

two-𝕋ᵉ : 𝕋ᵉ
two-𝕋ᵉ = succ-𝕋ᵉ one-𝕋ᵉ
```