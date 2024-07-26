# Noncoherent large wild higher precategories

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module wild-category-theory.noncoherent-large-wild-higher-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.globular-typesᵉ
open import structured-types.large-globular-typesᵉ
open import structured-types.large-reflexive-globular-typesᵉ
open import structured-types.large-transitive-globular-typesᵉ

open import wild-category-theory.noncoherent-wild-higher-precategoriesᵉ
```

</details>

## Idea

Itᵉ isᵉ anᵉ importantᵉ open problemᵉ knownᵉ asᵉ theᵉ _coherenceᵉ problemᵉ_ to defineᵉ aᵉ
fullyᵉ coherentᵉ notionᵉ ofᵉ $∞$-categoryᵉ in univalentᵉ typeᵉ theory.ᵉ Theᵉ subjectᵉ ofᵉ
_wildᵉ categoryᵉ theoryᵉ_ attemptsᵉ to recoverᵉ someᵉ ofᵉ theᵉ benefitsᵉ ofᵉ $∞$-categoryᵉ
theoryᵉ withoutᵉ tacklingᵉ thisᵉ problem.ᵉ Weᵉ introduce,ᵉ asᵉ oneᵉ ofᵉ ourᵉ basicᵉ buildingᵉ
blocksᵉ in thisᵉ subject,ᵉ theᵉ notionᵉ ofᵉ aᵉ _largeᵉ noncoherentᵉ wildᵉ higherᵉ
precategory_.ᵉ

Aᵉ _largeᵉ noncoherentᵉ wildᵉ higherᵉ precategoryᵉ_ `𝒞`ᵉ isᵉ aᵉ structureᵉ thatᵉ attemptsᵉ
atᵉ capturingᵉ theᵉ structureᵉ ofᵉ aᵉ largeᵉ higherᵉ precategoryᵉ to theᵉ $0$'thᵉ order.ᵉ Itᵉ
consistsᵉ ofᵉ in someᵉ senseᵉ allᵉ ofᵉ theᵉ operationsᵉ andᵉ noneᵉ ofᵉ theᵉ coherenceᵉ ofᵉ aᵉ
largeᵉ higherᵉ precategory.ᵉ Thus,ᵉ itᵉ isᵉ definedᵉ asᵉ aᵉ
[largeᵉ globularᵉ type](structured-types.large-globular-types.mdᵉ) with familiesᵉ ofᵉ
$n$-morphismsᵉ labeledᵉ asᵉ "identities"ᵉ

```text
  id-homᵉ : (xᵉ : 𝑛-Cellᵉ 𝒞ᵉ) → (𝑛+1)-Cellᵉ 𝒞ᵉ xᵉ xᵉ
```

andᵉ aᵉ compositionᵉ operationᵉ atᵉ everyᵉ dimensionᵉ

```text
  comp-homᵉ :
    {xᵉ yᵉ zᵉ : 𝑛-Cellᵉ 𝒞ᵉ} → (𝑛+1)-Cellᵉ 𝒞ᵉ yᵉ zᵉ → (𝑛+1)-Cellᵉ 𝒞ᵉ xᵉ yᵉ → (𝑛+1)-Cellᵉ 𝒞ᵉ xᵉ z.ᵉ
```

Entirelyᵉ concretely,ᵉ weᵉ defineᵉ aᵉ
{{#conceptᵉ "noncoherentᵉ largeᵉ wildᵉ higherᵉ precategory"ᵉ Agda=Noncoherent-Large-Wild-Higher-Precategoryᵉ}}
to beᵉ aᵉ [reflexive](structured-types.reflexive-globular-types.mdᵉ) andᵉ
[transitive](structured-types.transitive-globular-types.mdᵉ) largeᵉ globularᵉ type.ᵉ
Weᵉ callᵉ theᵉ 0-cellsᵉ theᵉ _objects_,ᵉ theᵉ 1-cellsᵉ theᵉ _morphismsᵉ_ andᵉ theᵉ higherᵉ
cellsᵉ theᵉ _$n$-morphisms_.ᵉ Theᵉ reflexivitiesᵉ areᵉ calledᵉ theᵉ _identityᵉ
morphisms_,ᵉ andᵉ theᵉ transitivityᵉ operationsᵉ areᵉ brandedᵉ asᵉ _compositionᵉ ofᵉ
morphisms_.ᵉ

## Definitions

### Noncoherent large wild higher precategories

```agda
record
  Noncoherent-Large-Wild-Higher-Precategoryᵉ
  (αᵉ : Level → Level) (βᵉ : Level → Level → Level) : UUωᵉ
  where

  field
    obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)

    hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      large-globular-structureᵉ βᵉ obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ

    id-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      is-reflexive-large-globular-structureᵉ
        ( hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

    comp-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      is-transitive-large-globular-structureᵉ
        ( hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  large-globular-type-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    Large-Globular-Typeᵉ αᵉ βᵉ
  large-globular-type-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    λ where
    .0-cell-Large-Globular-Typeᵉ →
      obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ
    .globular-structure-0-cell-Large-Globular-Typeᵉ →
      hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ
```

Weᵉ record someᵉ commonᵉ projectionsᵉ forᵉ noncoherentᵉ largeᵉ wildᵉ higherᵉ
precategories.ᵉ

```agda
  hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level} →
    obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l1ᵉ →
    obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l2ᵉ →
    UUᵉ (βᵉ l1ᵉ l2ᵉ)
  hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    1-cell-large-globular-structureᵉ
      ( hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  id-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {lᵉ : Level} {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ lᵉ} →
    hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ xᵉ
  id-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    refl-1-cell-is-reflexive-large-globular-structureᵉ
      ( id-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  comp-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l1ᵉ}
    {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l2ᵉ}
    {zᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l3ᵉ} →
    hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ yᵉ zᵉ →
    hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ yᵉ →
    hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ zᵉ
  comp-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    comp-1-cell-is-transitive-large-globular-structureᵉ
      ( comp-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  hom-globular-type-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l1ᵉ)
    (yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l2ᵉ) →
    Globular-Typeᵉ (βᵉ l1ᵉ l2ᵉ) (βᵉ l1ᵉ l2ᵉ)
  pr1ᵉ (hom-globular-type-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ yᵉ) =
    hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ yᵉ
  pr2ᵉ (hom-globular-type-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ yᵉ) =
    globular-structure-1-cell-large-globular-structureᵉ
      ( hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
      ( xᵉ)
      ( yᵉ)

  hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l1ᵉ)
    (yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l2ᵉ) →
    Noncoherent-Wild-Higher-Precategoryᵉ (βᵉ l1ᵉ l2ᵉ) (βᵉ l1ᵉ l2ᵉ)
  hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategoryᵉ
    xᵉ yᵉ =
    make-Noncoherent-Wild-Higher-Precategoryᵉ
      ( hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ yᵉ)
      ( globular-structure-1-cell-large-globular-structureᵉ
        ( hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
        ( xᵉ)
        ( yᵉ))
      ( is-reflexive-globular-structure-1-cell-is-reflexive-large-globular-structureᵉ
        ( id-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
        ( xᵉ)
        ( yᵉ))
      ( is-transitive-globular-structure-1-cell-is-transitive-large-globular-structureᵉ
        ( comp-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
        ( xᵉ)
        ( yᵉ))
```

```agda
  2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l1ᵉ}
    {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l2ᵉ} →
    hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ yᵉ →
    hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ yᵉ →
    UUᵉ (βᵉ l1ᵉ l2ᵉ)
  2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    2-cell-large-globular-structureᵉ
      ( hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  id-2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l1ᵉ}
    {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l2ᵉ}
    {fᵉ : hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ yᵉ} →
    2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ fᵉ fᵉ
  id-2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    refl-2-cell-is-reflexive-large-globular-structureᵉ
      ( id-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  comp-2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l1ᵉ}
    {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l2ᵉ}
    {fᵉ gᵉ hᵉ : hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ yᵉ} →
    2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ gᵉ hᵉ →
    2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ fᵉ gᵉ →
    2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ fᵉ hᵉ
  comp-2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    comp-2-cell-is-transitive-large-globular-structureᵉ
      ( comp-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
```

```agda
  3-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l1ᵉ}
    {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l2ᵉ}
    {fᵉ gᵉ : hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ yᵉ} →
    2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ fᵉ gᵉ →
    2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ fᵉ gᵉ →
    UUᵉ (βᵉ l1ᵉ l2ᵉ)
  3-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    3-cell-large-globular-structureᵉ
      ( hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  id-3-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l1ᵉ}
    {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l2ᵉ}
    {fᵉ gᵉ : hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ yᵉ}
    {Hᵉ : 2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ fᵉ gᵉ} →
    3-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ Hᵉ Hᵉ
  id-3-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    refl-3-cell-is-reflexive-large-globular-structureᵉ
      ( id-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  comp-3-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l1ᵉ}
    {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ l2ᵉ}
    {fᵉ gᵉ : hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ yᵉ}
    {Hᵉ Kᵉ Lᵉ : 2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ fᵉ gᵉ} →
    3-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ Kᵉ Lᵉ →
    3-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ Hᵉ Kᵉ →
    3-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ Hᵉ Lᵉ
  comp-3-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    comp-3-cell-is-transitive-large-globular-structureᵉ
      ( comp-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
```

```agda
open Noncoherent-Large-Wild-Higher-Precategoryᵉ public
```