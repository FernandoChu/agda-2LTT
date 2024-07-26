# Transitive multisets

```agda
module trees.transitive-multisetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import trees.multisetsᵉ
open import trees.submultisetsᵉ
```

</details>

## Idea

Aᵉ multisetᵉ `x`ᵉ isᵉ saidᵉ to beᵉ **transitive**ᵉ ifᵉ `yᵉ ⊑-𝕍ᵉ x`ᵉ forᵉ everyᵉ `yᵉ ∈-𝕍ᵉ x`.ᵉ
Thatᵉ is,ᵉ `x`ᵉ isᵉ transitiveᵉ ifᵉ forᵉ everyᵉ `zᵉ ∈-𝕍ᵉ yᵉ ∈-𝕍ᵉ x`ᵉ weᵉ haveᵉ
`zᵉ ∈-𝕍ᵉ yᵉ ≃ᵉ zᵉ ∈-𝕍ᵉ x`.ᵉ

Similarly,ᵉ weᵉ sayᵉ thatᵉ `x`ᵉ isᵉ **weaklyᵉ transitive**ᵉ ifᵉ `yᵉ ⊆-𝕍ᵉ x`ᵉ forᵉ everyᵉ
`yᵉ ∈-𝕍ᵉ x`.ᵉ Thatᵉ is,ᵉ `x`ᵉ isᵉ weaklyᵉ transitiveᵉ ifᵉ forᵉ everyᵉ `zᵉ ∈-𝕍ᵉ yᵉ ∈-𝕍ᵉ x`ᵉ weᵉ
haveᵉ `zᵉ ∈-𝕍ᵉ yᵉ ↪ᵉ zᵉ ∈-𝕍ᵉ x`.ᵉ

## Definition

### Transitive multisets

```agda
is-transitive-𝕍ᵉ : {lᵉ : Level} → 𝕍ᵉ lᵉ → UUᵉ (lsuc lᵉ)
is-transitive-𝕍ᵉ {lᵉ} xᵉ = (yᵉ : 𝕍ᵉ lᵉ) → yᵉ ∈-𝕍ᵉ xᵉ → yᵉ ⊑-𝕍ᵉ xᵉ
```

### Wealky transitive multisets

```agda
is-weakly-transitive-𝕍ᵉ : {lᵉ : Level} → 𝕍ᵉ lᵉ → UUᵉ (lsuc lᵉ)
is-weakly-transitive-𝕍ᵉ {lᵉ} xᵉ = (yᵉ : 𝕍ᵉ lᵉ) → yᵉ ∈-𝕍ᵉ xᵉ → yᵉ ⊆-𝕍ᵉ xᵉ
```