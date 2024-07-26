# Maps between globular types

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module structured-types.maps-globular-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.globular-typesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "map"ᵉ Disambiguation="globularᵉ types"ᵉ Agda=map-Globular-Typeᵉ}} `f`ᵉ
betweenᵉ [globularᵉ types](structured-types.globular-types.mdᵉ) `A`ᵉ andᵉ `B`ᵉ isᵉ aᵉ
mapᵉ `F₀`ᵉ ofᵉ $0$-cells,ᵉ andᵉ forᵉ everyᵉ pairᵉ ofᵉ $n$-cellsᵉ `x`ᵉ andᵉ `y`,ᵉ aᵉ mapᵉ ofᵉ
$(n+1)$-cellsᵉ

```text
  Fₙ₊₁ᵉ : (𝑛+1)-Cellᵉ Aᵉ xᵉ yᵉ → (𝑛+1)-Cellᵉ Bᵉ (Fₙᵉ xᵉ) (Fₙᵉ y).ᵉ
```

## Definitions

### Maps between globular types

```agda
record
  map-Globular-Typeᵉ
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Globular-Typeᵉ l1ᵉ l2ᵉ) (Bᵉ : Globular-Typeᵉ l3ᵉ l4ᵉ)
  : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  where
  coinductiveᵉ
  field
    0-cell-map-Globular-Typeᵉ :
      0-cell-Globular-Typeᵉ Aᵉ → 0-cell-Globular-Typeᵉ Bᵉ

    globular-type-1-cell-map-Globular-Typeᵉ :
      {xᵉ yᵉ : 0-cell-Globular-Typeᵉ Aᵉ} →
      map-Globular-Typeᵉ
        ( globular-type-1-cell-Globular-Typeᵉ Aᵉ xᵉ yᵉ)
        ( globular-type-1-cell-Globular-Typeᵉ Bᵉ
          ( 0-cell-map-Globular-Typeᵉ xᵉ)
          ( 0-cell-map-Globular-Typeᵉ yᵉ))

open map-Globular-Typeᵉ public

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : Globular-Typeᵉ l1ᵉ l2ᵉ} {Bᵉ : Globular-Typeᵉ l3ᵉ l4ᵉ}
  (Fᵉ : map-Globular-Typeᵉ Aᵉ Bᵉ)
  where

  1-cell-map-Globular-Typeᵉ :
    {xᵉ yᵉ : 0-cell-Globular-Typeᵉ Aᵉ} →
    1-cell-Globular-Typeᵉ Aᵉ xᵉ yᵉ →
    1-cell-Globular-Typeᵉ Bᵉ
      ( 0-cell-map-Globular-Typeᵉ Fᵉ xᵉ)
      ( 0-cell-map-Globular-Typeᵉ Fᵉ yᵉ)
  1-cell-map-Globular-Typeᵉ =
    0-cell-map-Globular-Typeᵉ (globular-type-1-cell-map-Globular-Typeᵉ Fᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : Globular-Typeᵉ l1ᵉ l2ᵉ} {Bᵉ : Globular-Typeᵉ l3ᵉ l4ᵉ}
  (Fᵉ : map-Globular-Typeᵉ Aᵉ Bᵉ)
  where

  2-cell-map-Globular-Typeᵉ :
    {xᵉ yᵉ : 0-cell-Globular-Typeᵉ Aᵉ}
    {fᵉ gᵉ : 1-cell-Globular-Typeᵉ Aᵉ xᵉ yᵉ} →
    2-cell-Globular-Typeᵉ Aᵉ fᵉ gᵉ →
    2-cell-Globular-Typeᵉ Bᵉ
      ( 1-cell-map-Globular-Typeᵉ Fᵉ fᵉ)
      ( 1-cell-map-Globular-Typeᵉ Fᵉ gᵉ)
  2-cell-map-Globular-Typeᵉ =
    1-cell-map-Globular-Typeᵉ (globular-type-1-cell-map-Globular-Typeᵉ Fᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : Globular-Typeᵉ l1ᵉ l2ᵉ} {Bᵉ : Globular-Typeᵉ l3ᵉ l4ᵉ}
  (Fᵉ : map-Globular-Typeᵉ Aᵉ Bᵉ)
  where

  3-cell-map-Globular-Typeᵉ :
    {xᵉ yᵉ : 0-cell-Globular-Typeᵉ Aᵉ}
    {fᵉ gᵉ : 1-cell-Globular-Typeᵉ Aᵉ xᵉ yᵉ} →
    {Hᵉ Kᵉ : 2-cell-Globular-Typeᵉ Aᵉ fᵉ gᵉ} →
    3-cell-Globular-Typeᵉ Aᵉ Hᵉ Kᵉ →
    3-cell-Globular-Typeᵉ Bᵉ
      ( 2-cell-map-Globular-Typeᵉ Fᵉ Hᵉ)
      ( 2-cell-map-Globular-Typeᵉ Fᵉ Kᵉ)
  3-cell-map-Globular-Typeᵉ =
    2-cell-map-Globular-Typeᵉ (globular-type-1-cell-map-Globular-Typeᵉ Fᵉ)
```

### The identity map on a globular type

```agda
id-map-Globular-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Globular-Typeᵉ l1ᵉ l2ᵉ) → map-Globular-Typeᵉ Aᵉ Aᵉ
id-map-Globular-Typeᵉ Aᵉ =
  λ where
  .0-cell-map-Globular-Typeᵉ → idᵉ
  .globular-type-1-cell-map-Globular-Typeᵉ {xᵉ} {yᵉ} →
    id-map-Globular-Typeᵉ (globular-type-1-cell-Globular-Typeᵉ Aᵉ xᵉ yᵉ)
```

### Composition of maps of globular types

```agda
comp-map-Globular-Typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : Globular-Typeᵉ l1ᵉ l2ᵉ}
  {Bᵉ : Globular-Typeᵉ l3ᵉ l4ᵉ}
  {Cᵉ : Globular-Typeᵉ l5ᵉ l6ᵉ} →
  map-Globular-Typeᵉ Bᵉ Cᵉ → map-Globular-Typeᵉ Aᵉ Bᵉ → map-Globular-Typeᵉ Aᵉ Cᵉ
comp-map-Globular-Typeᵉ gᵉ fᵉ =
  λ where
  .0-cell-map-Globular-Typeᵉ →
    0-cell-map-Globular-Typeᵉ gᵉ ∘ᵉ 0-cell-map-Globular-Typeᵉ fᵉ
  .globular-type-1-cell-map-Globular-Typeᵉ →
    comp-map-Globular-Typeᵉ
      ( globular-type-1-cell-map-Globular-Typeᵉ gᵉ)
      ( globular-type-1-cell-map-Globular-Typeᵉ fᵉ)
```