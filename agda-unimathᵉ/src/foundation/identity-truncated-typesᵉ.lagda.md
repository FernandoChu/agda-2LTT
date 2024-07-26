# Identity types of truncated types

```agda
module foundation.identity-truncated-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

### The type of identity of truncated types is truncated

```agda
module _
  {lᵉ : Level} {Aᵉ Bᵉ : UUᵉ lᵉ}
  where

  is-trunc-id-is-truncᵉ :
    (kᵉ : 𝕋ᵉ) → is-truncᵉ kᵉ Aᵉ → is-truncᵉ kᵉ Bᵉ → is-truncᵉ kᵉ (Aᵉ ＝ᵉ Bᵉ)
  is-trunc-id-is-truncᵉ kᵉ is-trunc-Aᵉ is-trunc-Bᵉ =
    is-trunc-equivᵉ kᵉ
      ( Aᵉ ≃ᵉ Bᵉ)
      ( equiv-univalenceᵉ)
      ( is-trunc-equiv-is-truncᵉ kᵉ is-trunc-Aᵉ is-trunc-Bᵉ)
```