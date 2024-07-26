# Fixed points of endofunctions

```agda
module foundation.fixed-points-endofunctionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Givenᵉ anᵉ [endofunction](foundation-core.endomorphisms.mdᵉ) `fᵉ : Aᵉ → A`,ᵉ theᵉ typeᵉ
ofᵉ {{#conceptᵉ "fixedᵉ points"ᵉ}} isᵉ theᵉ typeᵉ ofᵉ elementsᵉ `xᵉ : A`ᵉ suchᵉ thatᵉ
`fᵉ xᵉ ＝ᵉ x`.ᵉ

## Definitions

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (fᵉ : Aᵉ → Aᵉ)
  where

  fixed-pointᵉ : UUᵉ lᵉ
  fixed-pointᵉ = Σᵉ Aᵉ (λ xᵉ → fᵉ xᵉ ＝ᵉ xᵉ)

  fixed-point'ᵉ : UUᵉ lᵉ
  fixed-point'ᵉ = Σᵉ Aᵉ (λ xᵉ → xᵉ ＝ᵉ fᵉ xᵉ)
```