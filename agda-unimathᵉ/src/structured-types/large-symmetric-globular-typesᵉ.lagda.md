# Large symmetric globular types

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module structured-types.large-symmetric-globular-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relationsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.large-globular-typesᵉ
open import structured-types.symmetric-globular-typesᵉ
```

</details>

## Idea

Weᵉ sayᵉ aᵉ [largeᵉ globularᵉ type](structured-types.large-globular-types.mdᵉ) isᵉ
{{#conceptᵉ "symmetric"ᵉ Disambiguation="largeᵉ globularᵉ type"ᵉ Agda=is-symmetric-large-globular-structureᵉ}}
ifᵉ thereᵉ isᵉ aᵉ symmetryᵉ actionᵉ onᵉ itsᵉ $n$-cellsᵉ forᵉ positiveᵉ $n$,ᵉ mappingᵉ
$n$-cellsᵉ fromᵉ `x`ᵉ to `y`ᵉ to $n$-cellsᵉ fromᵉ `y`ᵉ to `x`.ᵉ

## Definition

### Symmetry structure on a large globular structure

```agda
record
  is-symmetric-large-globular-structureᵉ
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)}
  (Gᵉ : large-globular-structureᵉ βᵉ Aᵉ) : UUωᵉ
  where
  field
    is-symmetric-1-cell-is-symmetric-large-globular-structureᵉ :
      is-symmetric-Large-Relationᵉ Aᵉ (1-cell-large-globular-structureᵉ Gᵉ)
    is-symmetric-globular-structure-1-cell-is-symmetric-large-globular-structureᵉ :
      {l1ᵉ l2ᵉ : Level} (xᵉ : Aᵉ l1ᵉ) (yᵉ : Aᵉ l2ᵉ) →
      is-symmetric-globular-structureᵉ
        ( globular-structure-1-cell-large-globular-structureᵉ Gᵉ xᵉ yᵉ)

open is-symmetric-large-globular-structureᵉ public

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)}
  (Gᵉ : large-globular-structureᵉ βᵉ Aᵉ)
  (rᵉ : is-symmetric-large-globular-structureᵉ Gᵉ)
  where

  sym-1-cell-is-symmetric-large-globular-structureᵉ :
    {l1ᵉ l2ᵉ : Level} {xᵉ : Aᵉ l1ᵉ} {yᵉ : Aᵉ l2ᵉ} →
    1-cell-large-globular-structureᵉ Gᵉ xᵉ yᵉ →
    1-cell-large-globular-structureᵉ Gᵉ yᵉ xᵉ
  sym-1-cell-is-symmetric-large-globular-structureᵉ {xᵉ = xᵉ} {yᵉ} =
    is-symmetric-1-cell-is-symmetric-large-globular-structureᵉ rᵉ xᵉ yᵉ

  sym-2-cell-is-symmetric-large-globular-structureᵉ :
    {l1ᵉ l2ᵉ : Level} {xᵉ : Aᵉ l1ᵉ} {yᵉ : Aᵉ l2ᵉ}
    {fᵉ gᵉ : 1-cell-large-globular-structureᵉ Gᵉ xᵉ yᵉ} →
    2-cell-large-globular-structureᵉ Gᵉ fᵉ gᵉ →
    2-cell-large-globular-structureᵉ Gᵉ gᵉ fᵉ
  sym-2-cell-is-symmetric-large-globular-structureᵉ {xᵉ = xᵉ} {yᵉ} {fᵉ} {gᵉ} =
    is-symmetric-1-cell-is-symmetric-globular-structureᵉ
      ( is-symmetric-globular-structure-1-cell-is-symmetric-large-globular-structureᵉ
        ( rᵉ)
        ( xᵉ)
        ( yᵉ))
      ( fᵉ)
      ( gᵉ)
```