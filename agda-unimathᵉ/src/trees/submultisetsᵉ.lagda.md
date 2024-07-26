# Submultisets

```agda
module trees.submultisetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ

open import trees.multisetsᵉ
```

</details>

## Idea

Givenᵉ twoᵉ multisetsᵉ `x`ᵉ andᵉ `y`,ᵉ weᵉ sayᵉ thatᵉ `x`ᵉ isᵉ aᵉ **submultiset**ᵉ ofᵉ `y`ᵉ ifᵉ
forᵉ everyᵉ `zᵉ ∈-𝕍ᵉ x`ᵉ weᵉ haveᵉ `zᵉ ∈-𝕍ᵉ xᵉ ↪ᵉ zᵉ ∈-𝕍ᵉ y`.ᵉ

## Definition

### Submultisets

```agda
is-submultiset-𝕍ᵉ : {lᵉ : Level} → 𝕍ᵉ lᵉ → 𝕍ᵉ lᵉ → UUᵉ (lsuc lᵉ)
is-submultiset-𝕍ᵉ {lᵉ} yᵉ xᵉ = (zᵉ : 𝕍ᵉ lᵉ) → zᵉ ∈-𝕍ᵉ xᵉ → (zᵉ ∈-𝕍ᵉ xᵉ) ↪ᵉ (zᵉ ∈-𝕍ᵉ yᵉ)

infix 6 _⊆-𝕍ᵉ_
_⊆-𝕍ᵉ_ : {lᵉ : Level} → 𝕍ᵉ lᵉ → 𝕍ᵉ lᵉ → UUᵉ (lsuc lᵉ)
xᵉ ⊆-𝕍ᵉ yᵉ = is-submultiset-𝕍ᵉ yᵉ xᵉ
```

### Full submultisets

```agda
is-full-submultiset-𝕍ᵉ : {lᵉ : Level} → 𝕍ᵉ lᵉ → 𝕍ᵉ lᵉ → UUᵉ (lsuc lᵉ)
is-full-submultiset-𝕍ᵉ {lᵉ} yᵉ xᵉ = (zᵉ : 𝕍ᵉ lᵉ) → zᵉ ∈-𝕍ᵉ xᵉ → (zᵉ ∈-𝕍ᵉ xᵉ) ≃ᵉ (zᵉ ∈-𝕍ᵉ yᵉ)

_⊑-𝕍ᵉ_ : {lᵉ : Level} → 𝕍ᵉ lᵉ → 𝕍ᵉ lᵉ → UUᵉ (lsuc lᵉ)
xᵉ ⊑-𝕍ᵉ yᵉ = is-full-submultiset-𝕍ᵉ yᵉ xᵉ
```