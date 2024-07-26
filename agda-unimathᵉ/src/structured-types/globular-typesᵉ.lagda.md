# Globular types

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module structured-types.globular-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "globularᵉ type"ᵉ Agda=Globular-Typeᵉ}} isᵉ aᵉ typeᵉ equippedᵉ with aᵉ
[binaryᵉ relation](foundation.binary-relations.mdᵉ) valuedᵉ in globularᵉ types.ᵉ

Thus,ᵉ aᵉ globularᵉ typeᵉ consistsᵉ ofᵉ aᵉ baseᵉ typeᵉ `A`ᵉ whichᵉ isᵉ calledᵉ theᵉ typeᵉ ofᵉ
$0$-cells,ᵉ andᵉ forᵉ everyᵉ pairᵉ ofᵉ $0$-cells,ᵉ aᵉ typeᵉ ofᵉ $1$-cells,ᵉ andᵉ forᵉ everyᵉ
pairᵉ ofᵉ $1$-cellsᵉ aᵉ typeᵉ ofᵉ $2$-cells,ᵉ andᵉ soᵉ onᵉ _adᵉ infinitum_.ᵉ Forᵉ everyᵉ pairᵉ
ofᵉ $n$-cellsᵉ `s`ᵉ andᵉ `t`,ᵉ thereᵉ isᵉ aᵉ typeᵉ ofᵉ $(n+1)$-cellsᵉ _fromᵉ `s`ᵉ to `t`_,ᵉ
andᵉ weᵉ sayᵉ theᵉ $(n+1)$-cellsᵉ haveᵉ _sourceᵉ_ `s`ᵉ andᵉ _targetᵉ_ `t`.ᵉ

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

Weᵉ followᵉ theᵉ conventionalᵉ approachᵉ ofᵉ theᵉ libraryᵉ andᵉ startᵉ byᵉ definingᵉ theᵉ
globularᵉ [structure](foundation.structure.mdᵉ) onᵉ aᵉ type,ᵉ andᵉ thenᵉ defineᵉ aᵉ
globularᵉ typeᵉ to beᵉ aᵉ typeᵉ equippedᵉ with suchᵉ structure.ᵉ Noteᵉ thatᵉ weᵉ couldᵉ
equivalentlyᵉ haveᵉ startedᵉ byᵉ definingᵉ globularᵉ types,ᵉ andᵉ thenᵉ defineᵉ globularᵉ
structuresᵉ onᵉ aᵉ typeᵉ asᵉ binaryᵉ familiesᵉ ofᵉ globularᵉ typesᵉ onᵉ it,ᵉ butᵉ thisᵉ isᵉ aᵉ
specialᵉ propertyᵉ ofᵉ globularᵉ types.ᵉ

## Definitions

### The structure of a globular type

**Comment.**ᵉ Theᵉ choiceᵉ to addᵉ aᵉ secondᵉ universeᵉ levelᵉ in theᵉ definitionᵉ ofᵉ aᵉ
globularᵉ structureᵉ mayᵉ seemᵉ ratherᵉ arbitrary,ᵉ butᵉ makesᵉ theᵉ conceptᵉ applicableᵉ
in particularᵉ extraᵉ casesᵉ thatᵉ areᵉ ofᵉ useᵉ to usᵉ whenᵉ workingᵉ with
[largeᵉ globularᵉ structures](structured-types.large-globular-types.md).ᵉ

```agda
record
  globular-structureᵉ {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  where
  coinductiveᵉ
  field
    1-cell-globular-structureᵉ :
      (xᵉ yᵉ : Aᵉ) → UUᵉ l2ᵉ
    globular-structure-1-cell-globular-structureᵉ :
      (xᵉ yᵉ : Aᵉ) → globular-structureᵉ l2ᵉ (1-cell-globular-structureᵉ xᵉ yᵉ)

open globular-structureᵉ public
```

#### Iterated projections for globular structures

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Gᵉ : globular-structureᵉ l2ᵉ Aᵉ)
  {xᵉ yᵉ : Aᵉ} (fᵉ gᵉ : 1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ)
  where

  2-cell-globular-structureᵉ : UUᵉ l2ᵉ
  2-cell-globular-structureᵉ =
    1-cell-globular-structureᵉ
      ( globular-structure-1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ) fᵉ gᵉ

  globular-structure-2-cell-globular-structureᵉ :
    globular-structureᵉ l2ᵉ 2-cell-globular-structureᵉ
  globular-structure-2-cell-globular-structureᵉ =
    globular-structure-1-cell-globular-structureᵉ
      ( globular-structure-1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ) fᵉ gᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Gᵉ : globular-structureᵉ l2ᵉ Aᵉ)
  {xᵉ yᵉ : Aᵉ} {fᵉ gᵉ : 1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ}
  (pᵉ qᵉ : 2-cell-globular-structureᵉ Gᵉ fᵉ gᵉ)
  where

  3-cell-globular-structureᵉ : UUᵉ l2ᵉ
  3-cell-globular-structureᵉ =
    1-cell-globular-structureᵉ
      ( globular-structure-2-cell-globular-structureᵉ Gᵉ fᵉ gᵉ) pᵉ qᵉ

  globular-structure-3-cell-globular-structureᵉ :
    globular-structureᵉ l2ᵉ 3-cell-globular-structureᵉ
  globular-structure-3-cell-globular-structureᵉ =
    globular-structure-1-cell-globular-structureᵉ
      ( globular-structure-2-cell-globular-structureᵉ Gᵉ fᵉ gᵉ) pᵉ qᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Gᵉ : globular-structureᵉ l2ᵉ Aᵉ)
  {xᵉ yᵉ : Aᵉ} {fᵉ gᵉ : 1-cell-globular-structureᵉ Gᵉ xᵉ yᵉ}
  {pᵉ qᵉ : 2-cell-globular-structureᵉ Gᵉ fᵉ gᵉ}
  (Hᵉ Kᵉ : 3-cell-globular-structureᵉ Gᵉ pᵉ qᵉ)
  where

  4-cell-globular-structureᵉ : UUᵉ l2ᵉ
  4-cell-globular-structureᵉ =
    1-cell-globular-structureᵉ
      ( globular-structure-3-cell-globular-structureᵉ Gᵉ pᵉ qᵉ) Hᵉ Kᵉ

  globular-structure-4-cell-globular-structureᵉ :
    globular-structureᵉ l2ᵉ 4-cell-globular-structureᵉ
  globular-structure-4-cell-globular-structureᵉ =
    globular-structure-1-cell-globular-structureᵉ
      ( globular-structure-3-cell-globular-structureᵉ Gᵉ pᵉ qᵉ) Hᵉ Kᵉ
```

### The type of globular types

```agda
Globular-Typeᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Globular-Typeᵉ l1ᵉ l2ᵉ = Σᵉ (UUᵉ l1ᵉ) (globular-structureᵉ l2ᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Globular-Typeᵉ l1ᵉ l2ᵉ)
  where

  0-cell-Globular-Typeᵉ : UUᵉ l1ᵉ
  0-cell-Globular-Typeᵉ = pr1ᵉ Aᵉ

  globular-structure-0-cell-Globular-Typeᵉ :
    globular-structureᵉ l2ᵉ 0-cell-Globular-Typeᵉ
  globular-structure-0-cell-Globular-Typeᵉ = pr2ᵉ Aᵉ

  1-cell-Globular-Typeᵉ : (xᵉ yᵉ : 0-cell-Globular-Typeᵉ) → UUᵉ l2ᵉ
  1-cell-Globular-Typeᵉ =
    1-cell-globular-structureᵉ globular-structure-0-cell-Globular-Typeᵉ

  globular-structure-1-cell-Globular-Typeᵉ :
    (xᵉ yᵉ : 0-cell-Globular-Typeᵉ) →
    globular-structureᵉ l2ᵉ (1-cell-Globular-Typeᵉ xᵉ yᵉ)
  globular-structure-1-cell-Globular-Typeᵉ =
    globular-structure-1-cell-globular-structureᵉ
      ( globular-structure-0-cell-Globular-Typeᵉ)

  globular-type-1-cell-Globular-Typeᵉ :
    (xᵉ yᵉ : 0-cell-Globular-Typeᵉ) → Globular-Typeᵉ l2ᵉ l2ᵉ
  globular-type-1-cell-Globular-Typeᵉ xᵉ yᵉ =
    ( 1-cell-Globular-Typeᵉ xᵉ yᵉ ,ᵉ globular-structure-1-cell-Globular-Typeᵉ xᵉ yᵉ)

  2-cell-Globular-Typeᵉ :
    {xᵉ yᵉ : 0-cell-Globular-Typeᵉ} (fᵉ gᵉ : 1-cell-Globular-Typeᵉ xᵉ yᵉ) → UUᵉ l2ᵉ
  2-cell-Globular-Typeᵉ =
    2-cell-globular-structureᵉ globular-structure-0-cell-Globular-Typeᵉ

  globular-structure-2-cell-Globular-Typeᵉ :
    {xᵉ yᵉ : 0-cell-Globular-Typeᵉ} (fᵉ gᵉ : 1-cell-Globular-Typeᵉ xᵉ yᵉ) →
    globular-structureᵉ l2ᵉ (2-cell-Globular-Typeᵉ fᵉ gᵉ)
  globular-structure-2-cell-Globular-Typeᵉ =
    globular-structure-2-cell-globular-structureᵉ
      ( globular-structure-0-cell-Globular-Typeᵉ)

  globular-type-2-cell-Globular-Typeᵉ :
    {xᵉ yᵉ : 0-cell-Globular-Typeᵉ} (fᵉ gᵉ : 1-cell-Globular-Typeᵉ xᵉ yᵉ) →
    Globular-Typeᵉ l2ᵉ l2ᵉ
  globular-type-2-cell-Globular-Typeᵉ fᵉ gᵉ =
    ( 2-cell-Globular-Typeᵉ fᵉ gᵉ ,ᵉ globular-structure-2-cell-Globular-Typeᵉ fᵉ gᵉ)

  3-cell-Globular-Typeᵉ :
    {xᵉ yᵉ : 0-cell-Globular-Typeᵉ} {fᵉ gᵉ : 1-cell-Globular-Typeᵉ xᵉ yᵉ}
    (Hᵉ Kᵉ : 2-cell-Globular-Typeᵉ fᵉ gᵉ) → UUᵉ l2ᵉ
  3-cell-Globular-Typeᵉ =
    3-cell-globular-structureᵉ globular-structure-0-cell-Globular-Typeᵉ

  4-cell-Globular-Typeᵉ :
    {xᵉ yᵉ : 0-cell-Globular-Typeᵉ} {fᵉ gᵉ : 1-cell-Globular-Typeᵉ xᵉ yᵉ}
    {Hᵉ Kᵉ : 2-cell-Globular-Typeᵉ fᵉ gᵉ} (αᵉ βᵉ : 3-cell-Globular-Typeᵉ Hᵉ Kᵉ) → UUᵉ l2ᵉ
  4-cell-Globular-Typeᵉ =
    4-cell-globular-structureᵉ globular-structure-0-cell-Globular-Typeᵉ
```

## Examples

### The globular structure on a type given by its identity types

```agda
globular-structure-Idᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → globular-structureᵉ lᵉ Aᵉ
globular-structure-Idᵉ Aᵉ =
  λ where
  .1-cell-globular-structureᵉ xᵉ yᵉ →
    xᵉ ＝ᵉ yᵉ
  .globular-structure-1-cell-globular-structureᵉ xᵉ yᵉ →
    globular-structure-Idᵉ (xᵉ ＝ᵉ yᵉ)
```