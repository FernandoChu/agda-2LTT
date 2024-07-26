# Faithful pointed maps

```agda
module structured-types.faithful-pointed-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.faithful-mapsᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ faithfulᵉ pointedᵉ mapᵉ fromᵉ `A`ᵉ to `B`ᵉ isᵉ aᵉ pointedᵉ mapᵉ fromᵉ `A`ᵉ to `B`ᵉ ofᵉ whichᵉ
theᵉ underlyingᵉ mapᵉ isᵉ faithful.ᵉ

## Definition

```agda
faithful-pointed-mapᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
faithful-pointed-mapᵉ Aᵉ Bᵉ =
  Σᵉ (Aᵉ →∗ᵉ Bᵉ) (λ fᵉ → is-faithfulᵉ (map-pointed-mapᵉ fᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  (fᵉ : faithful-pointed-mapᵉ Aᵉ Bᵉ)
  where

  pointed-map-faithful-pointed-mapᵉ : Aᵉ →∗ᵉ Bᵉ
  pointed-map-faithful-pointed-mapᵉ = pr1ᵉ fᵉ

  map-faithful-pointed-mapᵉ : type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Bᵉ
  map-faithful-pointed-mapᵉ =
    map-pointed-mapᵉ pointed-map-faithful-pointed-mapᵉ

  preserves-point-faithful-pointed-mapᵉ :
    map-faithful-pointed-mapᵉ (point-Pointed-Typeᵉ Aᵉ) ＝ᵉ point-Pointed-Typeᵉ Bᵉ
  preserves-point-faithful-pointed-mapᵉ =
    preserves-point-pointed-mapᵉ pointed-map-faithful-pointed-mapᵉ

  is-faithful-faithful-pointed-mapᵉ : is-faithfulᵉ map-faithful-pointed-mapᵉ
  is-faithful-faithful-pointed-mapᵉ = pr2ᵉ fᵉ
```