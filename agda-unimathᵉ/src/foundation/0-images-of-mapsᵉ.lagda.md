# `0`-Images of maps

```agda
module foundation.0-images-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.truncation-images-of-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Theᵉ 0-imageᵉ ofᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ theᵉ typeᵉ
`0-imᵉ fᵉ :=ᵉ Σᵉ (bᵉ : B),ᵉ type-trunc-Setᵉ (fiberᵉ fᵉ b)`.ᵉ Theᵉ mapᵉ `Aᵉ → 0-imᵉ f`ᵉ isᵉ
0-connectedᵉ andᵉ theᵉ mapᵉ `0-imᵉ fᵉ → B`ᵉ isᵉ `0`-truncated.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  0-imᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  0-imᵉ = trunc-imᵉ zero-𝕋ᵉ fᵉ

  unit-0-imᵉ : Aᵉ → 0-imᵉ
  unit-0-imᵉ = unit-trunc-imᵉ zero-𝕋ᵉ fᵉ

  projection-0-imᵉ : 0-imᵉ → Bᵉ
  projection-0-imᵉ = projection-trunc-imᵉ zero-𝕋ᵉ fᵉ
```

## Properties

### Characterization of the identity type of `0-im f`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  Eq-unit-0-imᵉ : Aᵉ → Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  Eq-unit-0-imᵉ = Eq-unit-trunc-imᵉ neg-one-𝕋ᵉ fᵉ
```