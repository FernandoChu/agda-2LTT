# Maps between large globular types

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module structured-types.maps-large-globular-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.globular-typesᵉ
open import structured-types.large-globular-typesᵉ
open import structured-types.maps-globular-typesᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "map"ᵉ Disambiguation="largeᵉ globularᵉ types"ᵉ Agda=map-Large-Globular-Typeᵉ}}
`f`ᵉ betweenᵉ [largeᵉ globularᵉ types](structured-types.large-globular-types.mdᵉ) `A`ᵉ
andᵉ `B`ᵉ isᵉ aᵉ mapᵉ `F₀`ᵉ ofᵉ $0$-cells,ᵉ andᵉ forᵉ everyᵉ pairᵉ ofᵉ $n$-cellsᵉ `x`ᵉ andᵉ `y`,ᵉ
aᵉ mapᵉ ofᵉ $(n+1)$-cellsᵉ

```text
  Fₙ₊₁ᵉ : (𝑛+1)-Cellᵉ Aᵉ xᵉ yᵉ → (𝑛+1)-Cellᵉ Bᵉ (Fₙᵉ xᵉ) (Fₙᵉ y).ᵉ
```

## Definitions

### Maps between large globular types

```agda
record
  map-Large-Globular-Typeᵉ
  {α1ᵉ α2ᵉ : Level → Level} {β1ᵉ β2ᵉ : Level → Level → Level} (δᵉ : Level → Level)
  (Aᵉ : Large-Globular-Typeᵉ α1ᵉ β1ᵉ) (Bᵉ : Large-Globular-Typeᵉ α2ᵉ β2ᵉ) : UUωᵉ
  where
  field
    0-cell-map-Large-Globular-Typeᵉ :
      {lᵉ : Level} →
      0-cell-Large-Globular-Typeᵉ Aᵉ lᵉ → 0-cell-Large-Globular-Typeᵉ Bᵉ (δᵉ lᵉ)

    globular-type-1-cell-map-Large-Globular-Typeᵉ :
      {l1ᵉ l2ᵉ : Level}
      {xᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l1ᵉ}
      {yᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l2ᵉ} →
      map-Globular-Typeᵉ
        ( globular-type-1-cell-Large-Globular-Typeᵉ Aᵉ xᵉ yᵉ)
        ( globular-type-1-cell-Large-Globular-Typeᵉ Bᵉ
          ( 0-cell-map-Large-Globular-Typeᵉ xᵉ)
          ( 0-cell-map-Large-Globular-Typeᵉ yᵉ))

open map-Large-Globular-Typeᵉ public

module _
  {α1ᵉ α2ᵉ : Level → Level} {β1ᵉ β2ᵉ : Level → Level → Level} {δᵉ : Level → Level}
  {Aᵉ : Large-Globular-Typeᵉ α1ᵉ β1ᵉ} {Bᵉ : Large-Globular-Typeᵉ α2ᵉ β2ᵉ}
  (Fᵉ : map-Large-Globular-Typeᵉ δᵉ Aᵉ Bᵉ)
  where

  1-cell-map-Large-Globular-Typeᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l1ᵉ}
    {yᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l2ᵉ} →
    1-cell-Large-Globular-Typeᵉ Aᵉ xᵉ yᵉ →
    1-cell-Large-Globular-Typeᵉ Bᵉ
      ( 0-cell-map-Large-Globular-Typeᵉ Fᵉ xᵉ)
      ( 0-cell-map-Large-Globular-Typeᵉ Fᵉ yᵉ)
  1-cell-map-Large-Globular-Typeᵉ =
    0-cell-map-Globular-Typeᵉ (globular-type-1-cell-map-Large-Globular-Typeᵉ Fᵉ)

module _
  {α1ᵉ α2ᵉ : Level → Level} {β1ᵉ β2ᵉ : Level → Level → Level} {δᵉ : Level → Level}
  {Aᵉ : Large-Globular-Typeᵉ α1ᵉ β1ᵉ} {Bᵉ : Large-Globular-Typeᵉ α2ᵉ β2ᵉ}
  (Fᵉ : map-Large-Globular-Typeᵉ δᵉ Aᵉ Bᵉ)
  where

  2-cell-map-Large-Globular-Typeᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l1ᵉ}
    {yᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l2ᵉ} →
    {fᵉ gᵉ : 1-cell-Large-Globular-Typeᵉ Aᵉ xᵉ yᵉ} →
    2-cell-Large-Globular-Typeᵉ Aᵉ fᵉ gᵉ →
    2-cell-Large-Globular-Typeᵉ Bᵉ
      ( 1-cell-map-Large-Globular-Typeᵉ Fᵉ fᵉ)
      ( 1-cell-map-Large-Globular-Typeᵉ Fᵉ gᵉ)
  2-cell-map-Large-Globular-Typeᵉ =
    1-cell-map-Globular-Typeᵉ (globular-type-1-cell-map-Large-Globular-Typeᵉ Fᵉ)

module _
  {α1ᵉ α2ᵉ : Level → Level} {β1ᵉ β2ᵉ : Level → Level → Level} {δᵉ : Level → Level}
  {Aᵉ : Large-Globular-Typeᵉ α1ᵉ β1ᵉ} {Bᵉ : Large-Globular-Typeᵉ α2ᵉ β2ᵉ}
  (Fᵉ : map-Large-Globular-Typeᵉ δᵉ Aᵉ Bᵉ)
  where

  3-cell-map-Large-Globular-Typeᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l1ᵉ}
    {yᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l2ᵉ} →
    {fᵉ gᵉ : 1-cell-Large-Globular-Typeᵉ Aᵉ xᵉ yᵉ} →
    {Hᵉ Kᵉ : 2-cell-Large-Globular-Typeᵉ Aᵉ fᵉ gᵉ} →
    3-cell-Large-Globular-Typeᵉ Aᵉ Hᵉ Kᵉ →
    3-cell-Large-Globular-Typeᵉ Bᵉ
      ( 2-cell-map-Large-Globular-Typeᵉ Fᵉ Hᵉ)
      ( 2-cell-map-Large-Globular-Typeᵉ Fᵉ Kᵉ)
  3-cell-map-Large-Globular-Typeᵉ =
    2-cell-map-Globular-Typeᵉ (globular-type-1-cell-map-Large-Globular-Typeᵉ Fᵉ)
```