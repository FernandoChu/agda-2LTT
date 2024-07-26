# Constant pointed maps

```agda
module structured-types.constant-pointed-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Givenᵉ twoᵉ [pointedᵉ types](structured-types.pointed-types.mdᵉ) `A`ᵉ andᵉ `B`ᵉ theᵉ
{{#conceptᵉ "constantᵉ pointedᵉ map"ᵉ Agda=constant-pointed-mapᵉ}} fromᵉ `A`ᵉ to `B`ᵉ isᵉ
theᵉ [pointedᵉ map](structured-types.pointed-maps.mdᵉ)
`constant-pointed-mapᵉ : Aᵉ →∗ᵉ B`ᵉ mappingᵉ everyᵉ elementᵉ in `A`ᵉ to theᵉ baseᵉ pointᵉ
ofᵉ `B`.ᵉ

## Definitions

### Constant pointed maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ)
  where

  map-constant-pointed-mapᵉ : type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Bᵉ
  map-constant-pointed-mapᵉ =
    constᵉ (type-Pointed-Typeᵉ Aᵉ) (point-Pointed-Typeᵉ Bᵉ)

  preserves-point-constant-pointed-mapᵉ :
    map-constant-pointed-mapᵉ (point-Pointed-Typeᵉ Aᵉ) ＝ᵉ point-Pointed-Typeᵉ Bᵉ
  preserves-point-constant-pointed-mapᵉ = reflᵉ

  constant-pointed-mapᵉ : Aᵉ →∗ᵉ Bᵉ
  pr1ᵉ constant-pointed-mapᵉ = map-constant-pointed-mapᵉ
  pr2ᵉ constant-pointed-mapᵉ = preserves-point-constant-pointed-mapᵉ
```

### The pointed type of pointed maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ)
  where

  pointed-map-Pointed-Typeᵉ : Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ pointed-map-Pointed-Typeᵉ = Aᵉ →∗ᵉ Bᵉ
  pr2ᵉ pointed-map-Pointed-Typeᵉ = constant-pointed-mapᵉ Aᵉ Bᵉ
```

## See also

-ᵉ [Constantᵉ maps](foundation.constant-maps.mdᵉ)