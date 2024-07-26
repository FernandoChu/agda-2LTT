# Symmetric globular types

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module structured-types.symmetric-globular-typesᵉ where
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

Weᵉ sayᵉ aᵉ [globularᵉ type](structured-types.globular-types.mdᵉ) isᵉ
{{#conceptᵉ "symmetric"ᵉ Disambiguation="globularᵉ type"ᵉ Agda=is-symmetric-globular-structureᵉ}}
ifᵉ thereᵉ isᵉ aᵉ symmetryᵉ actionᵉ onᵉ itsᵉ $n$-cellsᵉ forᵉ positiveᵉ $n$,ᵉ mappingᵉ
$n$-cellsᵉ fromᵉ `x`ᵉ to `y`ᵉ to $n$-cellsᵉ fromᵉ `y`ᵉ to `x`.ᵉ

## Definition

### Symmetry structure on a globular structure

```agda
record
  is-symmetric-globular-structureᵉ
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Gᵉ : globular-structureᵉ l2ᵉ Aᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  where
  coinductiveᵉ
  field
    is-symmetric-1-cell-is-symmetric-globular-structureᵉ :
      is-symmetricᵉ (1-cell-globular-structureᵉ Gᵉ)
    is-symmetric-globular-structure-1-cell-is-symmetric-globular-structureᵉ :
      (xᵉ yᵉ : Aᵉ) →
      is-symmetric-globular-structureᵉ
        ( globular-structure-1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ)

open is-symmetric-globular-structureᵉ public

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Gᵉ : globular-structureᵉ l2ᵉ Aᵉ}
  (rᵉ : is-symmetric-globular-structureᵉ Gᵉ)
  where

  sym-1-cell-is-symmetric-globular-structureᵉ :
    {xᵉ yᵉ : Aᵉ} →
    1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ → 1-cell-globular-structureᵉ Gᵉ yᵉ xᵉ
  sym-1-cell-is-symmetric-globular-structureᵉ {xᵉ} {yᵉ} =
    is-symmetric-1-cell-is-symmetric-globular-structureᵉ rᵉ xᵉ yᵉ

  sym-2-cell-is-symmetric-globular-structureᵉ :
    {xᵉ yᵉ : Aᵉ} {fᵉ gᵉ : 1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ} →
    2-cell-globular-structureᵉ Gᵉ fᵉ gᵉ →
    2-cell-globular-structureᵉ Gᵉ gᵉ fᵉ
  sym-2-cell-is-symmetric-globular-structureᵉ {xᵉ} {yᵉ} {fᵉ} {gᵉ} =
    is-symmetric-1-cell-is-symmetric-globular-structureᵉ
      ( is-symmetric-globular-structure-1-cell-is-symmetric-globular-structureᵉ
        ( rᵉ)
        ( xᵉ)
        ( yᵉ))
      ( fᵉ)
      ( gᵉ)
```

### The type of symmetric globular structures

```agda
symmetric-globular-structureᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
symmetric-globular-structureᵉ l2ᵉ Aᵉ =
  Σᵉ (globular-structureᵉ l2ᵉ Aᵉ) (is-symmetric-globular-structureᵉ)
```

## Examples

### The symmetric globular structure on a type given by its identity types

```agda
is-symmetric-globular-structure-Idᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
  is-symmetric-globular-structureᵉ (globular-structure-Idᵉ Aᵉ)
is-symmetric-globular-structure-Idᵉ Aᵉ =
  λ where
  .is-symmetric-1-cell-is-symmetric-globular-structureᵉ xᵉ yᵉ →
    invᵉ
  .is-symmetric-globular-structure-1-cell-is-symmetric-globular-structureᵉ xᵉ yᵉ →
    is-symmetric-globular-structure-Idᵉ (xᵉ ＝ᵉ yᵉ)
```