# Pointed maps

```agda
module structured-types.pointed-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.constant-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-dependent-functionsᵉ
open import structured-types.pointed-families-of-typesᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ pointedᵉ mapᵉ fromᵉ aᵉ pointedᵉ typeᵉ `A`ᵉ to aᵉ pointedᵉ typeᵉ `B`ᵉ isᵉ aᵉ baseᵉ pointᵉ
preservingᵉ functionᵉ fromᵉ `A`ᵉ to `B`.ᵉ

Theᵉ typeᵉ `Aᵉ →∗ᵉ B`ᵉ ofᵉ pointedᵉ mapsᵉ fromᵉ `A`ᵉ to `B`ᵉ isᵉ itselfᵉ pointedᵉ byᵉ theᵉ
[constantᵉ pointedᵉ map](structured-types.constant-pointed-maps.md).ᵉ

## Definitions

### Pointed maps

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  where

  pointed-mapᵉ : Pointed-Typeᵉ l1ᵉ → Pointed-Typeᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  pointed-mapᵉ Aᵉ Bᵉ = pointed-Πᵉ Aᵉ (constant-Pointed-Famᵉ Aᵉ Bᵉ)

  infixr 5 _→∗ᵉ_
  _→∗ᵉ_ = pointed-mapᵉ
```

**Note**ᵉ: theᵉ subscriptᵉ asteriskᵉ symbolᵉ usedᵉ forᵉ theᵉ pointedᵉ mapᵉ typeᵉ `_→∗_`,ᵉ
andᵉ pointedᵉ typeᵉ constructionsᵉ in general,ᵉ isᵉ theᵉ
[asteriskᵉ operator](https://codepoints.net/U+2217ᵉ) `∗`ᵉ (agda-inputᵉ: `\ast`),ᵉ notᵉ
theᵉ [asterisk](https://codepoints.net/U+002Aᵉ) `*`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  where

  map-pointed-mapᵉ : Aᵉ →∗ᵉ Bᵉ → type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Bᵉ
  map-pointed-mapᵉ = pr1ᵉ

  preserves-point-pointed-mapᵉ :
    (fᵉ : Aᵉ →∗ᵉ Bᵉ) →
    map-pointed-mapᵉ fᵉ (point-Pointed-Typeᵉ Aᵉ) ＝ᵉ point-Pointed-Typeᵉ Bᵉ
  preserves-point-pointed-mapᵉ = pr2ᵉ
```

### Precomposing pointed maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  (Cᵉ : Pointed-Famᵉ l3ᵉ Bᵉ) (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  precomp-Pointed-Famᵉ : Pointed-Famᵉ l3ᵉ Aᵉ
  pr1ᵉ precomp-Pointed-Famᵉ = fam-Pointed-Famᵉ Bᵉ Cᵉ ∘ᵉ map-pointed-mapᵉ fᵉ
  pr2ᵉ precomp-Pointed-Famᵉ =
    trᵉ
      ( fam-Pointed-Famᵉ Bᵉ Cᵉ)
      ( invᵉ (preserves-point-pointed-mapᵉ fᵉ))
      ( point-Pointed-Famᵉ Bᵉ Cᵉ)

  precomp-pointed-Πᵉ : pointed-Πᵉ Bᵉ Cᵉ → pointed-Πᵉ Aᵉ precomp-Pointed-Famᵉ
  pr1ᵉ (precomp-pointed-Πᵉ gᵉ) xᵉ =
    function-pointed-Πᵉ gᵉ (map-pointed-mapᵉ fᵉ xᵉ)
  pr2ᵉ (precomp-pointed-Πᵉ gᵉ) =
    ( invᵉ
      ( apdᵉ
        ( function-pointed-Πᵉ gᵉ)
        ( invᵉ (preserves-point-pointed-mapᵉ fᵉ)))) ∙ᵉ
    ( apᵉ
      ( trᵉ
        ( fam-Pointed-Famᵉ Bᵉ Cᵉ)
        ( invᵉ (preserves-point-pointed-mapᵉ fᵉ)))
      ( preserves-point-function-pointed-Πᵉ gᵉ))
```

### Composing pointed maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} {Cᵉ : Pointed-Typeᵉ l3ᵉ}
  where

  map-comp-pointed-mapᵉ :
    Bᵉ →∗ᵉ Cᵉ → Aᵉ →∗ᵉ Bᵉ → type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Cᵉ
  map-comp-pointed-mapᵉ gᵉ fᵉ =
    map-pointed-mapᵉ gᵉ ∘ᵉ map-pointed-mapᵉ fᵉ

  preserves-point-comp-pointed-mapᵉ :
    (gᵉ : Bᵉ →∗ᵉ Cᵉ) (fᵉ : Aᵉ →∗ᵉ Bᵉ) →
    (map-comp-pointed-mapᵉ gᵉ fᵉ (point-Pointed-Typeᵉ Aᵉ)) ＝ᵉ point-Pointed-Typeᵉ Cᵉ
  preserves-point-comp-pointed-mapᵉ gᵉ fᵉ =
    ( apᵉ (map-pointed-mapᵉ gᵉ) (preserves-point-pointed-mapᵉ fᵉ)) ∙ᵉ
    ( preserves-point-pointed-mapᵉ gᵉ)

  comp-pointed-mapᵉ : Bᵉ →∗ᵉ Cᵉ → Aᵉ →∗ᵉ Bᵉ → Aᵉ →∗ᵉ Cᵉ
  pr1ᵉ (comp-pointed-mapᵉ gᵉ fᵉ) = map-comp-pointed-mapᵉ gᵉ fᵉ
  pr2ᵉ (comp-pointed-mapᵉ gᵉ fᵉ) = preserves-point-comp-pointed-mapᵉ gᵉ fᵉ

  infixr 15 _∘∗ᵉ_

  _∘∗ᵉ_ : Bᵉ →∗ᵉ Cᵉ → Aᵉ →∗ᵉ Bᵉ → Aᵉ →∗ᵉ Cᵉ
  _∘∗ᵉ_ = comp-pointed-mapᵉ
```

### The identity pointed map

```agda
module _
  {l1ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ}
  where

  id-pointed-mapᵉ : Aᵉ →∗ᵉ Aᵉ
  pr1ᵉ id-pointed-mapᵉ = idᵉ
  pr2ᵉ id-pointed-mapᵉ = reflᵉ
```

## See also

-ᵉ [Constantᵉ pointedᵉ maps](structured-types.constant-pointed-maps.mdᵉ)
-ᵉ [Precompositionᵉ ofᵉ pointedᵉ maps](structured-types.precomposition-pointed-maps.mdᵉ)