# Bands

```agda
module foundation.bandsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.set-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
```

</details>

## Idea

Aᵉ **band**ᵉ fromᵉ $X$ᵉ to $Y$ᵉ isᵉ anᵉ elementᵉ ofᵉ theᵉ
[set-truncation](foundation.set-truncations.mdᵉ) ofᵉ theᵉ typeᵉ ofᵉ
[equivalences](foundation-core.equivalences.mdᵉ) fromᵉ $X$ᵉ to $Y$.ᵉ

## Definition

```agda
bandᵉ : {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
bandᵉ Aᵉ Bᵉ = type-trunc-Setᵉ (Aᵉ ≃ᵉ Bᵉ)

unit-bandᵉ : {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ ≃ᵉ Bᵉ) → bandᵉ Aᵉ Bᵉ
unit-bandᵉ = unit-trunc-Setᵉ

refl-bandᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → bandᵉ Aᵉ Aᵉ
refl-bandᵉ Aᵉ = unit-bandᵉ id-equivᵉ
```