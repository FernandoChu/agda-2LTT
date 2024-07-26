# Reflexive globular types

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module structured-types.reflexive-globular-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.globular-typesᵉ
```

</details>

## Idea

Aᵉ [globularᵉ type](structured-types.globular-types.mdᵉ) isᵉ
{{#conceptᵉ "reflexive"ᵉ Disambiguation="globularᵉ type"ᵉ Agda=is-reflexive-globular-structureᵉ}}
ifᵉ everyᵉ $n$-cellᵉ `x`ᵉ comesᵉ with aᵉ choiceᵉ ofᵉ $(n+1)$-cellᵉ fromᵉ `x`ᵉ to `x`.ᵉ

## Definition

### Reflexivity structure on a globular structure

```agda
record
  is-reflexive-globular-structureᵉ
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Gᵉ : globular-structureᵉ l2ᵉ Aᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  where
  coinductiveᵉ
  field
    is-reflexive-1-cell-is-reflexive-globular-structureᵉ :
      is-reflexiveᵉ (1-cell-globular-structureᵉ Gᵉ)
    is-reflexive-globular-structure-1-cell-is-reflexive-globular-structureᵉ :
      (xᵉ yᵉ : Aᵉ) →
      is-reflexive-globular-structureᵉ
        ( globular-structure-1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ)

open is-reflexive-globular-structureᵉ public

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Gᵉ : globular-structureᵉ l2ᵉ Aᵉ}
  (rᵉ : is-reflexive-globular-structureᵉ Gᵉ)
  where

  refl-1-cell-is-reflexive-globular-structureᵉ :
    {xᵉ : Aᵉ} → 1-cell-globular-structureᵉ Gᵉ xᵉ xᵉ
  refl-1-cell-is-reflexive-globular-structureᵉ {xᵉ} =
    is-reflexive-1-cell-is-reflexive-globular-structureᵉ rᵉ xᵉ

  refl-2-cell-is-reflexive-globular-structureᵉ :
    {xᵉ yᵉ : Aᵉ} {fᵉ : 1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ} →
    2-cell-globular-structureᵉ Gᵉ fᵉ fᵉ
  refl-2-cell-is-reflexive-globular-structureᵉ {xᵉ} {yᵉ} {fᵉ} =
    is-reflexive-1-cell-is-reflexive-globular-structureᵉ
      ( is-reflexive-globular-structure-1-cell-is-reflexive-globular-structureᵉ
        ( rᵉ)
        ( xᵉ)
        ( yᵉ))
      ( fᵉ)

  is-reflexive-globular-structure-2-cell-is-reflexive-globular-structureᵉ :
    {xᵉ yᵉ : Aᵉ}
    (fᵉ gᵉ : 1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ) →
    is-reflexive-globular-structureᵉ
      ( globular-structure-2-cell-globular-structureᵉ Gᵉ fᵉ gᵉ)
  is-reflexive-globular-structure-2-cell-is-reflexive-globular-structureᵉ
    { xᵉ} {yᵉ} =
    is-reflexive-globular-structure-1-cell-is-reflexive-globular-structureᵉ
      ( is-reflexive-globular-structure-1-cell-is-reflexive-globular-structureᵉ
        ( rᵉ)
        ( xᵉ)
        ( yᵉ))

  refl-3-cell-is-reflexive-globular-structureᵉ :
    {xᵉ yᵉ : Aᵉ}
    {fᵉ gᵉ : 1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ}
    {Hᵉ : 2-cell-globular-structureᵉ Gᵉ fᵉ gᵉ} →
    3-cell-globular-structureᵉ Gᵉ Hᵉ Hᵉ
  refl-3-cell-is-reflexive-globular-structureᵉ {xᵉ} {yᵉ} {fᵉ} {gᵉ} {Hᵉ} =
    is-reflexive-1-cell-is-reflexive-globular-structureᵉ
      ( is-reflexive-globular-structure-2-cell-is-reflexive-globular-structureᵉ
        ( fᵉ)
        ( gᵉ))
      ( Hᵉ)
```

### The type of reflexive globular structures

```agda
reflexive-globular-structureᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
reflexive-globular-structureᵉ l2ᵉ Aᵉ =
  Σᵉ (globular-structureᵉ l2ᵉ Aᵉ) (is-reflexive-globular-structureᵉ)
```

## Examples

### The reflexive globular structure on a type given by its identity types

```agda
is-reflexive-globular-structure-Idᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
  is-reflexive-globular-structureᵉ (globular-structure-Idᵉ Aᵉ)
is-reflexive-globular-structure-Idᵉ Aᵉ =
  λ where
  .is-reflexive-1-cell-is-reflexive-globular-structureᵉ xᵉ →
    reflᵉ
  .is-reflexive-globular-structure-1-cell-is-reflexive-globular-structureᵉ xᵉ yᵉ →
    is-reflexive-globular-structure-Idᵉ (xᵉ ＝ᵉ yᵉ)
```