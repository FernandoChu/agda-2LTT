# Large reflexive globular types

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module structured-types.large-reflexive-globular-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relationsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.large-globular-typesᵉ
open import structured-types.reflexive-globular-typesᵉ
```

</details>

## Idea

Aᵉ [largeᵉ globularᵉ type](structured-types.large-globular-types.mdᵉ) isᵉ
{{#conceptᵉ "reflexive"ᵉ Disambiguation="largeᵉ globularᵉ type"ᵉ Agda=is-reflexive-large-globular-structureᵉ}}
ifᵉ everyᵉ $n$-cellᵉ `x`ᵉ comesᵉ with aᵉ choiceᵉ ofᵉ $(n+1)$-cellᵉ fromᵉ `x`ᵉ to `x`.ᵉ

## Definition

### Reflexivity structure on a large globular structure

```agda
record
  is-reflexive-large-globular-structureᵉ
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)}
  (Gᵉ : large-globular-structureᵉ βᵉ Aᵉ) : UUωᵉ
  where

  field
    is-reflexive-1-cell-is-reflexive-large-globular-structureᵉ :
      is-reflexive-Large-Relationᵉ Aᵉ (1-cell-large-globular-structureᵉ Gᵉ)

    is-reflexive-globular-structure-1-cell-is-reflexive-large-globular-structureᵉ :
      {l1ᵉ l2ᵉ : Level} (xᵉ : Aᵉ l1ᵉ) (yᵉ : Aᵉ l2ᵉ) →
      is-reflexive-globular-structureᵉ
        ( globular-structure-1-cell-large-globular-structureᵉ Gᵉ xᵉ yᵉ)

open is-reflexive-large-globular-structureᵉ public

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)}
  {Gᵉ : large-globular-structureᵉ βᵉ Aᵉ}
  (rᵉ : is-reflexive-large-globular-structureᵉ Gᵉ)
  where

  refl-1-cell-is-reflexive-large-globular-structureᵉ :
    {lᵉ : Level} {xᵉ : Aᵉ lᵉ} → 1-cell-large-globular-structureᵉ Gᵉ xᵉ xᵉ
  refl-1-cell-is-reflexive-large-globular-structureᵉ {xᵉ = xᵉ} =
    is-reflexive-1-cell-is-reflexive-large-globular-structureᵉ rᵉ xᵉ

  refl-2-cell-is-reflexive-large-globular-structureᵉ :
    {l1ᵉ l2ᵉ : Level} {xᵉ : Aᵉ l1ᵉ} {yᵉ : Aᵉ l2ᵉ}
    {fᵉ : 1-cell-large-globular-structureᵉ Gᵉ xᵉ yᵉ} →
    2-cell-large-globular-structureᵉ Gᵉ fᵉ fᵉ
  refl-2-cell-is-reflexive-large-globular-structureᵉ {xᵉ = xᵉ} {yᵉ} {fᵉ} =
    is-reflexive-1-cell-is-reflexive-globular-structureᵉ
      ( is-reflexive-globular-structure-1-cell-is-reflexive-large-globular-structureᵉ
        ( rᵉ)
        ( xᵉ)
        ( yᵉ))
      ( fᵉ)

  refl-3-cell-is-reflexive-large-globular-structureᵉ :
    {l1ᵉ l2ᵉ : Level} {xᵉ : Aᵉ l1ᵉ} {yᵉ : Aᵉ l2ᵉ}
    {fᵉ gᵉ : 1-cell-large-globular-structureᵉ Gᵉ xᵉ yᵉ} →
    {Hᵉ : 2-cell-large-globular-structureᵉ Gᵉ fᵉ gᵉ} →
    3-cell-large-globular-structureᵉ Gᵉ Hᵉ Hᵉ
  refl-3-cell-is-reflexive-large-globular-structureᵉ {xᵉ = xᵉ} {yᵉ} =
    refl-2-cell-is-reflexive-globular-structureᵉ
      ( is-reflexive-globular-structure-1-cell-is-reflexive-large-globular-structureᵉ
        ( rᵉ)
        ( xᵉ)
        ( yᵉ))
```