# Transitive globular types

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module structured-types.transitive-globular-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.globular-typesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "transitiveᵉ globularᵉ type"ᵉ Agda=Transitive-Globular-Typeᵉ}} isᵉ aᵉ
[globularᵉ type](structured-types.globular-types.mdᵉ) `A`ᵉ
[equipped](foundation.structure.mdᵉ) with aᵉ binaryᵉ operatorᵉ

```text
  -ᵉ *ᵉ -ᵉ : (𝑛+1)-Cellᵉ Aᵉ yᵉ zᵉ → (𝑛+1)-Cellᵉ Aᵉ xᵉ yᵉ → (𝑛+1)-Cellᵉ Aᵉ xᵉ zᵉ
```

atᵉ everyᵉ levelᵉ $n$.ᵉ

**Note.**ᵉ Thisᵉ isᵉ notᵉ establishedᵉ terminologyᵉ andᵉ mayᵉ change.ᵉ

## Definition

### Transitivity structure on a globular type

```agda
record
  is-transitive-globular-structureᵉ
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Gᵉ : globular-structureᵉ l2ᵉ Aᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  where
  coinductiveᵉ
  field
    comp-1-cell-is-transitive-globular-structureᵉ :
      {xᵉ yᵉ zᵉ : Aᵉ} →
      1-cell-globular-structureᵉ Gᵉ yᵉ zᵉ →
      1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ →
      1-cell-globular-structureᵉ Gᵉ xᵉ zᵉ

    is-transitive-globular-structure-1-cell-is-transitive-globular-structureᵉ :
      (xᵉ yᵉ : Aᵉ) →
      is-transitive-globular-structureᵉ
        ( globular-structure-1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ)

open is-transitive-globular-structureᵉ public

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Gᵉ : globular-structureᵉ l2ᵉ Aᵉ}
  (rᵉ : is-transitive-globular-structureᵉ Gᵉ)
  where

  comp-2-cell-is-transitive-globular-structureᵉ :
    {xᵉ yᵉ : Aᵉ} {fᵉ gᵉ hᵉ : 1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ} →
    2-cell-globular-structureᵉ Gᵉ gᵉ hᵉ →
    2-cell-globular-structureᵉ Gᵉ fᵉ gᵉ →
    2-cell-globular-structureᵉ Gᵉ fᵉ hᵉ
  comp-2-cell-is-transitive-globular-structureᵉ {xᵉ} {yᵉ} =
    comp-1-cell-is-transitive-globular-structureᵉ
      ( is-transitive-globular-structure-1-cell-is-transitive-globular-structureᵉ
        ( rᵉ)
        ( xᵉ)
        ( yᵉ))

  is-transitive-globular-structure-2-cell-is-transitive-globular-structureᵉ :
    {xᵉ yᵉ : Aᵉ} (fᵉ gᵉ : 1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ) →
    is-transitive-globular-structureᵉ
      ( globular-structure-2-cell-globular-structureᵉ Gᵉ fᵉ gᵉ)
  is-transitive-globular-structure-2-cell-is-transitive-globular-structureᵉ
    { xᵉ} {yᵉ} =
    is-transitive-globular-structure-1-cell-is-transitive-globular-structureᵉ
      ( is-transitive-globular-structure-1-cell-is-transitive-globular-structureᵉ
        ( rᵉ)
        ( xᵉ)
        ( yᵉ))

  comp-3-cell-is-transitive-globular-structureᵉ :
    {xᵉ yᵉ : Aᵉ} {fᵉ gᵉ : 1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ}
    {Hᵉ Kᵉ Lᵉ : 2-cell-globular-structureᵉ Gᵉ fᵉ gᵉ} →
    3-cell-globular-structureᵉ Gᵉ Kᵉ Lᵉ →
    3-cell-globular-structureᵉ Gᵉ Hᵉ Kᵉ →
    3-cell-globular-structureᵉ Gᵉ Hᵉ Lᵉ
  comp-3-cell-is-transitive-globular-structureᵉ {xᵉ} {yᵉ} {fᵉ} {gᵉ} =
    comp-1-cell-is-transitive-globular-structureᵉ
      ( is-transitive-globular-structure-2-cell-is-transitive-globular-structureᵉ
        ( fᵉ)
        ( gᵉ))
```

### The type of transitive globular structures on a type

```agda
transitive-globular-structureᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
transitive-globular-structureᵉ l2ᵉ Aᵉ =
  Σᵉ (globular-structureᵉ l2ᵉ Aᵉ) (is-transitive-globular-structureᵉ)
```

### The type of transitive globular types

```agda
Transitive-Globular-Typeᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Transitive-Globular-Typeᵉ l1ᵉ l2ᵉ = Σᵉ (UUᵉ l1ᵉ) (transitive-globular-structureᵉ l2ᵉ)
```

## Examples

### The transitive globular structure on a type given by its identity types

```agda
is-transitive-globular-structure-Idᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
  is-transitive-globular-structureᵉ (globular-structure-Idᵉ Aᵉ)
is-transitive-globular-structure-Idᵉ Aᵉ =
  λ where
  .comp-1-cell-is-transitive-globular-structureᵉ
    pᵉ qᵉ →
    qᵉ ∙ᵉ pᵉ
  .is-transitive-globular-structure-1-cell-is-transitive-globular-structureᵉ
    xᵉ yᵉ →
    is-transitive-globular-structure-Idᵉ (xᵉ ＝ᵉ yᵉ)

transitive-globular-structure-Idᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → transitive-globular-structureᵉ lᵉ Aᵉ
transitive-globular-structure-Idᵉ Aᵉ =
  ( globular-structure-Idᵉ Aᵉ ,ᵉ is-transitive-globular-structure-Idᵉ Aᵉ)
```