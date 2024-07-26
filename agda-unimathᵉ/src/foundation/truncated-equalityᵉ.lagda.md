# Truncated equality

```agda
module foundation.truncated-equalityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Definition

```agda
trunc-eqᵉ : {lᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ lᵉ} → Aᵉ → Aᵉ → Truncated-Typeᵉ lᵉ kᵉ
trunc-eqᵉ kᵉ xᵉ yᵉ = truncᵉ kᵉ (xᵉ ＝ᵉ yᵉ)
```