# Large globular types

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module structured-types.large-globular-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.globular-typesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "largeᵉ globularᵉ type"ᵉ Agda=Large-Globular-Typeᵉ}} isᵉ aᵉ hierarchyᵉ ofᵉ
typesᵉ indexedᵉ byᵉ universeᵉ levels,ᵉ [equipped](foundation.structure.mdᵉ) with aᵉ
[largeᵉ binaryᵉ relation](foundation.large-binary-relations.mdᵉ) valuedᵉ in
[globularᵉ types](structured-types.globular-types.md).ᵉ

Thus,ᵉ aᵉ largeᵉ globularᵉ typeᵉ consistsᵉ ofᵉ aᵉ baseᵉ hierarchyᵉ ofᵉ typesᵉ indexedᵉ byᵉ
universeᵉ levelsᵉ `A`ᵉ calledᵉ theᵉ _$0$-cells_,ᵉ andᵉ forᵉ everyᵉ pairᵉ ofᵉ $0$-cells,ᵉ aᵉ
typeᵉ ofᵉ $1$-cells,ᵉ andᵉ forᵉ everyᵉ pairᵉ ofᵉ $1$-cellsᵉ aᵉ typeᵉ ofᵉ $2$-cells,ᵉ andᵉ soᵉ
onᵉ _adᵉ infinitum_.ᵉ Forᵉ everyᵉ pairᵉ ofᵉ $n$-cellsᵉ `s`ᵉ andᵉ `t`,ᵉ thereᵉ isᵉ aᵉ typeᵉ ofᵉ
$(n+1)$-cellsᵉ _fromᵉ `s`ᵉ to `t`_,ᵉ andᵉ weᵉ sayᵉ theᵉ $(n+1)$-cellsᵉ haveᵉ _sourceᵉ_ `s`ᵉ
andᵉ _targetᵉ_ `t`.ᵉ

Theᵉ standardᵉ interpretationᵉ ofᵉ theᵉ higherᵉ cellsᵉ ofᵉ aᵉ globularᵉ typeᵉ isᵉ asᵉ arrowsᵉ
fromᵉ theirᵉ sourceᵉ to theirᵉ target.ᵉ Forᵉ instance,ᵉ givenᵉ twoᵉ $0$-cellsᵉ `x`ᵉ andᵉ
`y`,ᵉ twoᵉ $1$-cellsᵉ `f`ᵉ andᵉ `g`ᵉ fromᵉ `x`ᵉ to `y`,ᵉ twoᵉ $2$-cellsᵉ `H`ᵉ andᵉ `K`ᵉ fromᵉ
`f`ᵉ to `g`,ᵉ andᵉ aᵉ $3$-cellᵉ `α`ᵉ fromᵉ `H`ᵉ to `K`,ᵉ aᵉ commonᵉ depictionᵉ wouldᵉ beᵉ

```text
            fᵉ
       -----------ᵉ
     /ᵉ  //ᵉ     \\ᵉ  \ᵉ
    /ᵉ  //ᵉ   αᵉ   \\ᵉ  ∨ᵉ
   xᵉ  H||ᵉ ≡≡≡≡>ᵉ ||Kᵉ  y.ᵉ
    \ᵉ  \\ᵉ       //ᵉ  ∧ᵉ
     \ᵉ  Vᵉ       Vᵉ  /ᵉ
       -----------ᵉ
            gᵉ
```

## Definitions

### The structure of a large globular type

```agda
record
  large-globular-structureᵉ
  {αᵉ : Level → Level} (βᵉ : Level → Level → Level) (Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ))
  : UUωᵉ
  where
  field
    1-cell-large-globular-structureᵉ :
      {l1ᵉ l2ᵉ : Level} (xᵉ : Aᵉ l1ᵉ) (yᵉ : Aᵉ l2ᵉ) → UUᵉ (βᵉ l1ᵉ l2ᵉ)
    globular-structure-1-cell-large-globular-structureᵉ :
      {l1ᵉ l2ᵉ : Level} (xᵉ : Aᵉ l1ᵉ) (yᵉ : Aᵉ l2ᵉ) →
      globular-structureᵉ (βᵉ l1ᵉ l2ᵉ) (1-cell-large-globular-structureᵉ xᵉ yᵉ)

open large-globular-structureᵉ public
```

#### Iterated projections for large globular structures

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)}
  (Gᵉ : large-globular-structureᵉ βᵉ Aᵉ)
  {l1ᵉ l2ᵉ : Level} {xᵉ : Aᵉ l1ᵉ} {yᵉ : Aᵉ l2ᵉ}
  (fᵉ gᵉ : 1-cell-large-globular-structureᵉ Gᵉ xᵉ yᵉ)
  where

  2-cell-large-globular-structureᵉ : UUᵉ (βᵉ l1ᵉ l2ᵉ)
  2-cell-large-globular-structureᵉ =
    1-cell-globular-structureᵉ
      ( globular-structure-1-cell-large-globular-structureᵉ Gᵉ xᵉ yᵉ) fᵉ gᵉ

  globular-structure-2-cell-large-globular-structureᵉ :
    globular-structureᵉ (βᵉ l1ᵉ l2ᵉ) 2-cell-large-globular-structureᵉ
  globular-structure-2-cell-large-globular-structureᵉ =
    globular-structure-1-cell-globular-structureᵉ
      ( globular-structure-1-cell-large-globular-structureᵉ Gᵉ xᵉ yᵉ) fᵉ gᵉ

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)}
  (Gᵉ : large-globular-structureᵉ βᵉ Aᵉ)
  {l1ᵉ l2ᵉ : Level} {xᵉ : Aᵉ l1ᵉ} {yᵉ : Aᵉ l2ᵉ}
  {fᵉ gᵉ : 1-cell-large-globular-structureᵉ Gᵉ xᵉ yᵉ}
  (pᵉ qᵉ : 2-cell-large-globular-structureᵉ Gᵉ fᵉ gᵉ)
  where

  3-cell-large-globular-structureᵉ : UUᵉ (βᵉ l1ᵉ l2ᵉ)
  3-cell-large-globular-structureᵉ =
    1-cell-globular-structureᵉ
      ( globular-structure-2-cell-large-globular-structureᵉ Gᵉ fᵉ gᵉ) pᵉ qᵉ

  globular-structure-3-cell-large-globular-structureᵉ :
    globular-structureᵉ (βᵉ l1ᵉ l2ᵉ) 3-cell-large-globular-structureᵉ
  globular-structure-3-cell-large-globular-structureᵉ =
    globular-structure-1-cell-globular-structureᵉ
      ( globular-structure-2-cell-large-globular-structureᵉ Gᵉ fᵉ gᵉ) pᵉ qᵉ

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)}
  (Gᵉ : large-globular-structureᵉ βᵉ Aᵉ)
  {l1ᵉ l2ᵉ : Level} {xᵉ : Aᵉ l1ᵉ} {yᵉ : Aᵉ l2ᵉ}
  {fᵉ gᵉ : 1-cell-large-globular-structureᵉ Gᵉ xᵉ yᵉ}
  {pᵉ qᵉ : 2-cell-large-globular-structureᵉ Gᵉ fᵉ gᵉ}
  (Hᵉ Kᵉ : 3-cell-large-globular-structureᵉ Gᵉ pᵉ qᵉ)
  where

  4-cell-large-globular-structureᵉ : UUᵉ (βᵉ l1ᵉ l2ᵉ)
  4-cell-large-globular-structureᵉ =
    1-cell-globular-structureᵉ
      ( globular-structure-3-cell-large-globular-structureᵉ Gᵉ pᵉ qᵉ) Hᵉ Kᵉ

  globular-structure-4-cell-large-globular-structureᵉ :
    globular-structureᵉ (βᵉ l1ᵉ l2ᵉ) 4-cell-large-globular-structureᵉ
  globular-structure-4-cell-large-globular-structureᵉ =
    globular-structure-1-cell-globular-structureᵉ
      ( globular-structure-3-cell-large-globular-structureᵉ Gᵉ pᵉ qᵉ) Hᵉ Kᵉ
```

### The type of large globular types

```agda
record
  Large-Globular-Typeᵉ (αᵉ : Level → Level) (βᵉ : Level → Level → Level) : UUωᵉ
  where
  field
    0-cell-Large-Globular-Typeᵉ :
      (lᵉ : Level) → UUᵉ (αᵉ lᵉ)
    globular-structure-0-cell-Large-Globular-Typeᵉ :
      large-globular-structureᵉ βᵉ 0-cell-Large-Globular-Typeᵉ

open Large-Globular-Typeᵉ public

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Aᵉ : Large-Globular-Typeᵉ αᵉ βᵉ)
  where

  1-cell-Large-Globular-Typeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l1ᵉ)
    (yᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l2ᵉ) →
    UUᵉ (βᵉ l1ᵉ l2ᵉ)
  1-cell-Large-Globular-Typeᵉ =
    1-cell-large-globular-structureᵉ
      ( globular-structure-0-cell-Large-Globular-Typeᵉ Aᵉ)

  globular-structure-1-cell-Large-Globular-Typeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l1ᵉ)
    (yᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l2ᵉ) →
    globular-structureᵉ (βᵉ l1ᵉ l2ᵉ) (1-cell-Large-Globular-Typeᵉ xᵉ yᵉ)
  globular-structure-1-cell-Large-Globular-Typeᵉ =
    globular-structure-1-cell-large-globular-structureᵉ
      ( globular-structure-0-cell-Large-Globular-Typeᵉ Aᵉ)

  globular-type-1-cell-Large-Globular-Typeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l1ᵉ)
    (yᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l2ᵉ) →
    Globular-Typeᵉ (βᵉ l1ᵉ l2ᵉ) (βᵉ l1ᵉ l2ᵉ)
  globular-type-1-cell-Large-Globular-Typeᵉ xᵉ yᵉ =
    ( 1-cell-Large-Globular-Typeᵉ xᵉ yᵉ ,ᵉ
      globular-structure-1-cell-Large-Globular-Typeᵉ xᵉ yᵉ)

  2-cell-Large-Globular-Typeᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l1ᵉ}
    {yᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l2ᵉ}
    (pᵉ qᵉ : 1-cell-Large-Globular-Typeᵉ xᵉ yᵉ) → UUᵉ (βᵉ l1ᵉ l2ᵉ)
  2-cell-Large-Globular-Typeᵉ {xᵉ = xᵉ} {yᵉ} =
    1-cell-globular-structureᵉ
      ( globular-structure-1-cell-Large-Globular-Typeᵉ xᵉ yᵉ)

  globular-structure-2-cell-Large-Globular-Typeᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l1ᵉ}
    {yᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l2ᵉ}
    (fᵉ gᵉ : 1-cell-Large-Globular-Typeᵉ xᵉ yᵉ) →
    globular-structureᵉ (βᵉ l1ᵉ l2ᵉ) (2-cell-Large-Globular-Typeᵉ fᵉ gᵉ)
  globular-structure-2-cell-Large-Globular-Typeᵉ =
    globular-structure-2-cell-large-globular-structureᵉ
      ( globular-structure-0-cell-Large-Globular-Typeᵉ Aᵉ)

  globular-type-2-cell-Large-Globular-Typeᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l1ᵉ}
    {yᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l2ᵉ}
    (fᵉ gᵉ : 1-cell-Large-Globular-Typeᵉ xᵉ yᵉ) →
    Globular-Typeᵉ (βᵉ l1ᵉ l2ᵉ) (βᵉ l1ᵉ l2ᵉ)
  globular-type-2-cell-Large-Globular-Typeᵉ fᵉ gᵉ =
    ( 2-cell-Large-Globular-Typeᵉ fᵉ gᵉ ,ᵉ
      globular-structure-2-cell-Large-Globular-Typeᵉ fᵉ gᵉ)

  3-cell-Large-Globular-Typeᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l1ᵉ}
    {yᵉ : 0-cell-Large-Globular-Typeᵉ Aᵉ l2ᵉ}
    {pᵉ qᵉ : 1-cell-Large-Globular-Typeᵉ xᵉ yᵉ}
    (Hᵉ Kᵉ : 2-cell-Large-Globular-Typeᵉ pᵉ qᵉ) → UUᵉ (βᵉ l1ᵉ l2ᵉ)
  3-cell-Large-Globular-Typeᵉ {xᵉ = xᵉ} {yᵉ} =
    2-cell-globular-structureᵉ
      ( globular-structure-1-cell-Large-Globular-Typeᵉ xᵉ yᵉ)
```