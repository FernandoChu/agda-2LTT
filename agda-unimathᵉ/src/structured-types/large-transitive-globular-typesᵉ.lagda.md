# Large transitive globular types

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module structured-types.large-transitive-globular-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import structured-types.large-globular-typesᵉ
open import structured-types.transitive-globular-typesᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "largeᵉ transitiveᵉ globularᵉ type"ᵉ Agda=Large-Transitive-Globular-Typeᵉ}}
isᵉ aᵉ [largeᵉ globularᵉ type](structured-types.large-globular-types.mdᵉ) `A`ᵉ
[equipped](foundation.structure.mdᵉ) with aᵉ binaryᵉ operatorᵉ

```text
  -ᵉ *ᵉ -ᵉ : (𝑛+1)-Cellᵉ Aᵉ yᵉ zᵉ → (𝑛+1)-Cellᵉ Aᵉ xᵉ yᵉ → (𝑛+1)-Cellᵉ Aᵉ xᵉ zᵉ
```

atᵉ everyᵉ levelᵉ $n$.ᵉ

## Definition

### The structure transitivitiy on a large globular type

```agda
record
  is-transitive-large-globular-structureᵉ
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)}
  (Gᵉ : large-globular-structureᵉ βᵉ Aᵉ) : UUωᵉ
  where

  field
    comp-1-cell-is-transitive-large-globular-structureᵉ :
      {l1ᵉ l2ᵉ l3ᵉ : Level} {xᵉ : Aᵉ l1ᵉ} {yᵉ : Aᵉ l2ᵉ} {zᵉ : Aᵉ l3ᵉ} →
      1-cell-large-globular-structureᵉ Gᵉ yᵉ zᵉ →
      1-cell-large-globular-structureᵉ Gᵉ xᵉ yᵉ →
      1-cell-large-globular-structureᵉ Gᵉ xᵉ zᵉ

    is-transitive-globular-structure-1-cell-is-transitive-large-globular-structureᵉ :
      {l1ᵉ l2ᵉ : Level} (xᵉ : Aᵉ l1ᵉ) (yᵉ : Aᵉ l2ᵉ) →
      is-transitive-globular-structureᵉ
        ( globular-structure-1-cell-large-globular-structureᵉ Gᵉ xᵉ yᵉ)

open is-transitive-large-globular-structureᵉ public

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)}
  {Gᵉ : large-globular-structureᵉ βᵉ Aᵉ}
  (rᵉ : is-transitive-large-globular-structureᵉ Gᵉ)
  where

  comp-2-cell-is-transitive-large-globular-structureᵉ :
    {l1ᵉ l2ᵉ : Level} {xᵉ : Aᵉ l1ᵉ} {yᵉ : Aᵉ l2ᵉ}
    {fᵉ gᵉ hᵉ : 1-cell-large-globular-structureᵉ Gᵉ xᵉ yᵉ} →
    2-cell-large-globular-structureᵉ Gᵉ gᵉ hᵉ →
    2-cell-large-globular-structureᵉ Gᵉ fᵉ gᵉ →
    2-cell-large-globular-structureᵉ Gᵉ fᵉ hᵉ
  comp-2-cell-is-transitive-large-globular-structureᵉ {xᵉ = xᵉ} {yᵉ} =
    comp-1-cell-is-transitive-globular-structureᵉ
      ( is-transitive-globular-structure-1-cell-is-transitive-large-globular-structureᵉ
        ( rᵉ)
        ( xᵉ)
        ( yᵉ))

  comp-3-cell-is-transitive-large-globular-structureᵉ :
    {l1ᵉ l2ᵉ : Level} {xᵉ : Aᵉ l1ᵉ} {yᵉ : Aᵉ l2ᵉ}
    {fᵉ gᵉ : 1-cell-large-globular-structureᵉ Gᵉ xᵉ yᵉ}
    {Hᵉ Kᵉ Lᵉ : 2-cell-large-globular-structureᵉ Gᵉ fᵉ gᵉ} →
    3-cell-large-globular-structureᵉ Gᵉ Kᵉ Lᵉ →
    3-cell-large-globular-structureᵉ Gᵉ Hᵉ Kᵉ →
    3-cell-large-globular-structureᵉ Gᵉ Hᵉ Lᵉ
  comp-3-cell-is-transitive-large-globular-structureᵉ {xᵉ = xᵉ} {yᵉ} =
    comp-2-cell-is-transitive-globular-structureᵉ
      ( is-transitive-globular-structure-1-cell-is-transitive-large-globular-structureᵉ
        ( rᵉ)
        ( xᵉ)
        ( yᵉ))
```

### The type of transitive globular structures on a large type

```agda
record
  large-transitive-globular-structureᵉ
  {αᵉ : Level → Level} (βᵉ : Level → Level → Level) (Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ))
  : UUωᵉ
  where

  field
    large-globular-structure-large-transitive-globular-structureᵉ :
      large-globular-structureᵉ βᵉ Aᵉ

    is-transitive-large-globular-structure-large-transitive-globular-structureᵉ :
      is-transitive-large-globular-structureᵉ
        ( large-globular-structure-large-transitive-globular-structureᵉ)

open large-transitive-globular-structureᵉ public
```

### The type of large transitive globular types

```agda
record
  Large-Transitive-Globular-Typeᵉ
  (αᵉ : Level → Level) (βᵉ : Level → Level → Level) : UUωᵉ
  where

  field
    0-cell-Large-Transitive-Globular-Typeᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)

    transitive-globular-structure-0-cell-Large-Transitive-Globular-Typeᵉ :
      large-transitive-globular-structureᵉ
        ( βᵉ)
        ( 0-cell-Large-Transitive-Globular-Typeᵉ)

open Large-Transitive-Globular-Typeᵉ public
```