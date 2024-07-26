# The pointed unit type

```agda
module structured-types.pointed-unit-typeᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Theᵉ pointedᵉ unitᵉ typeᵉ isᵉ theᵉ initialᵉ pointedᵉ type.ᵉ

## Definition

```agda
unit-Pointed-Typeᵉ : Pointed-Typeᵉ lzero
pr1ᵉ unit-Pointed-Typeᵉ = unitᵉ
pr2ᵉ unit-Pointed-Typeᵉ = starᵉ
```

## Properties

```agda
module _
  {lᵉ : Level} (Xᵉ : Pointed-Typeᵉ lᵉ)
  where

  terminal-pointed-mapᵉ : Xᵉ →∗ᵉ unit-Pointed-Typeᵉ
  pr1ᵉ terminal-pointed-mapᵉ _ = starᵉ
  pr2ᵉ terminal-pointed-mapᵉ = reflᵉ

  map-terminal-pointed-mapᵉ : type-Pointed-Typeᵉ Xᵉ → unitᵉ
  map-terminal-pointed-mapᵉ =
    map-pointed-mapᵉ {Aᵉ = Xᵉ} {Bᵉ = unit-Pointed-Typeᵉ}
      terminal-pointed-mapᵉ

  inclusion-point-Pointed-Typeᵉ :
    unit-Pointed-Typeᵉ →∗ᵉ Xᵉ
  pr1ᵉ inclusion-point-Pointed-Typeᵉ = pointᵉ (point-Pointed-Typeᵉ Xᵉ)
  pr2ᵉ inclusion-point-Pointed-Typeᵉ = reflᵉ

  is-initial-unit-Pointed-Typeᵉ :
    ( fᵉ : unit-Pointed-Typeᵉ →∗ᵉ Xᵉ) → fᵉ ~∗ᵉ inclusion-point-Pointed-Typeᵉ
  pr1ᵉ (is-initial-unit-Pointed-Typeᵉ fᵉ) _ = preserves-point-pointed-mapᵉ fᵉ
  pr2ᵉ (is-initial-unit-Pointed-Typeᵉ fᵉ) = invᵉ right-unitᵉ
```