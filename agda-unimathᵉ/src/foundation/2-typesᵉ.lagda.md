# `2`-Types

```agda
module foundation.2-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Definition

Aᵉ 2-typeᵉ isᵉ aᵉ typeᵉ thatᵉ isᵉ 2-truncatedᵉ

```agda
is-2-typeᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
is-2-typeᵉ = is-truncᵉ (two-𝕋ᵉ)

UU-2-Typeᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
UU-2-Typeᵉ lᵉ = Σᵉ (UUᵉ lᵉ) is-2-typeᵉ

type-2-Typeᵉ :
  {lᵉ : Level} → UU-2-Typeᵉ lᵉ → UUᵉ lᵉ
type-2-Typeᵉ = pr1ᵉ

abstract
  is-2-type-type-2-Typeᵉ :
    {lᵉ : Level} (Aᵉ : UU-2-Typeᵉ lᵉ) → is-2-typeᵉ (type-2-Typeᵉ Aᵉ)
  is-2-type-type-2-Typeᵉ = pr2ᵉ
```