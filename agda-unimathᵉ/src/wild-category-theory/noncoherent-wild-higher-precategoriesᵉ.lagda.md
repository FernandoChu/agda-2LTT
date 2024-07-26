# Noncoherent wild higher precategories

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module wild-category-theory.noncoherent-wild-higher-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.globular-typesᵉ
open import structured-types.reflexive-globular-typesᵉ
open import structured-types.transitive-globular-typesᵉ
```

</details>

## Idea

Itᵉ isᵉ anᵉ importantᵉ open problemᵉ knownᵉ asᵉ theᵉ _coherenceᵉ problemᵉ_ to defineᵉ aᵉ
fullyᵉ coherentᵉ notionᵉ ofᵉ $∞$-categoryᵉ in univalentᵉ typeᵉ theory.ᵉ Theᵉ subjectᵉ ofᵉ
_wildᵉ categoryᵉ theoryᵉ_ attemptsᵉ to recoverᵉ someᵉ ofᵉ theᵉ benefitsᵉ ofᵉ $∞$-categoryᵉ
theoryᵉ withoutᵉ tacklingᵉ thisᵉ problem.ᵉ Weᵉ introduce,ᵉ asᵉ oneᵉ ofᵉ ourᵉ basicᵉ buildingᵉ
blocksᵉ in thisᵉ subject,ᵉ theᵉ notionᵉ ofᵉ aᵉ _noncoherentᵉ wildᵉ higherᵉ precategory_.ᵉ

Aᵉ _noncoherentᵉ wildᵉ higherᵉ precategoryᵉ_ `𝒞`ᵉ isᵉ aᵉ structureᵉ thatᵉ attemptsᵉ atᵉ
capturingᵉ theᵉ structureᵉ ofᵉ aᵉ higherᵉ precategoryᵉ to theᵉ $0$'thᵉ order.ᵉ Itᵉ consistsᵉ
ofᵉ in someᵉ senseᵉ allᵉ ofᵉ theᵉ operationsᵉ andᵉ noneᵉ ofᵉ theᵉ coherenceᵉ ofᵉ aᵉ higherᵉ
precategory.ᵉ Thus,ᵉ itᵉ isᵉ definedᵉ asᵉ aᵉ
[globularᵉ type](structured-types.globular-types.mdᵉ) with familiesᵉ ofᵉ
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
{{#conceptᵉ "noncoherentᵉ wildᵉ higherᵉ precategory"ᵉ Agda=Noncoherent-Wild-Higher-Precategoryᵉ}}
to beᵉ aᵉ [reflexive](structured-types.reflexive-globular-types.mdᵉ) andᵉ
[transitive](structured-types.transitive-globular-types.mdᵉ) globularᵉ type.ᵉ Weᵉ
callᵉ theᵉ 0-cellsᵉ theᵉ _objects_,ᵉ theᵉ 1-cellsᵉ theᵉ _morphismsᵉ_ andᵉ theᵉ higherᵉ cellsᵉ
theᵉ _$n$-morphisms_.ᵉ Theᵉ reflexivitiesᵉ areᵉ calledᵉ theᵉ _identityᵉ morphisms_,ᵉ andᵉ
theᵉ transitivityᵉ operationsᵉ areᵉ brandedᵉ asᵉ _compositionᵉ ofᵉ morphisms_.ᵉ

## Definitions

### Noncoherent wild higher precategories

```agda
Noncoherent-Wild-Higher-Precategoryᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Noncoherent-Wild-Higher-Precategoryᵉ l1ᵉ l2ᵉ =
  Σᵉ ( UUᵉ l1ᵉ)
    ( λ obj-Noncoherent-Wild-Higher-Precategoryᵉ →
      Σᵉ ( globular-structureᵉ l2ᵉ obj-Noncoherent-Wild-Higher-Precategoryᵉ)
        ( λ hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ →
          ( is-reflexive-globular-structureᵉ
            ( hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)) ×ᵉ
          ( is-transitive-globular-structureᵉ
            ( hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ))))

make-Noncoherent-Wild-Higher-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} →
  (obj-Noncoherent-Wild-Higher-Precategoryᵉ : UUᵉ l1ᵉ)
  (hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ :
    globular-structureᵉ l2ᵉ obj-Noncoherent-Wild-Higher-Precategoryᵉ) →
  ( is-reflexive-globular-structureᵉ
    hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ) →
  ( is-transitive-globular-structureᵉ
    hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ) →
  Noncoherent-Wild-Higher-Precategoryᵉ l1ᵉ l2ᵉ
make-Noncoherent-Wild-Higher-Precategoryᵉ objᵉ homᵉ idᵉ compᵉ =
  ( objᵉ ,ᵉ homᵉ ,ᵉ idᵉ ,ᵉ compᵉ)

{-# INLINE make-Noncoherent-Wild-Higher-Precategoryᵉ #-}

module _
  {l1ᵉ l2ᵉ : Level} (𝒞ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l1ᵉ l2ᵉ)
  where

  obj-Noncoherent-Wild-Higher-Precategoryᵉ : UUᵉ l1ᵉ
  obj-Noncoherent-Wild-Higher-Precategoryᵉ = pr1ᵉ 𝒞ᵉ

  hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ :
    globular-structureᵉ l2ᵉ obj-Noncoherent-Wild-Higher-Precategoryᵉ
  hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ = pr1ᵉ (pr2ᵉ 𝒞ᵉ)

  id-hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ :
    is-reflexive-globular-structureᵉ
      ( hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)
  id-hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ =
    pr1ᵉ (pr2ᵉ (pr2ᵉ 𝒞ᵉ))

  comp-hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ :
    is-transitive-globular-structureᵉ
      ( hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)
  comp-hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ =
    pr2ᵉ (pr2ᵉ (pr2ᵉ 𝒞ᵉ))

  globular-type-Noncoherent-Wild-Higher-Precategoryᵉ : Globular-Typeᵉ l1ᵉ l2ᵉ
  pr1ᵉ globular-type-Noncoherent-Wild-Higher-Precategoryᵉ =
    obj-Noncoherent-Wild-Higher-Precategoryᵉ
  pr2ᵉ globular-type-Noncoherent-Wild-Higher-Precategoryᵉ =
    hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ
```

Weᵉ record someᵉ commonᵉ projectionsᵉ forᵉ noncoherentᵉ wildᵉ higherᵉ precategories.ᵉ

```agda
  hom-Noncoherent-Wild-Higher-Precategoryᵉ :
    obj-Noncoherent-Wild-Higher-Precategoryᵉ →
    obj-Noncoherent-Wild-Higher-Precategoryᵉ →
    UUᵉ l2ᵉ
  hom-Noncoherent-Wild-Higher-Precategoryᵉ =
    1-cell-globular-structureᵉ
      ( hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)

  id-hom-Noncoherent-Wild-Higher-Precategoryᵉ :
    {xᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ} →
    hom-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ xᵉ
  id-hom-Noncoherent-Wild-Higher-Precategoryᵉ =
    refl-1-cell-is-reflexive-globular-structureᵉ
      ( id-hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)

  comp-hom-Noncoherent-Wild-Higher-Precategoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ} →
    hom-Noncoherent-Wild-Higher-Precategoryᵉ yᵉ zᵉ →
    hom-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ yᵉ →
    hom-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ zᵉ
  comp-hom-Noncoherent-Wild-Higher-Precategoryᵉ =
    comp-1-cell-is-transitive-globular-structureᵉ
      ( comp-hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)

  hom-globular-type-Noncoherent-Wild-Higher-Precategoryᵉ :
    (xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ) →
    Globular-Typeᵉ l2ᵉ l2ᵉ
  pr1ᵉ (hom-globular-type-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ yᵉ) =
    hom-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ yᵉ
  pr2ᵉ (hom-globular-type-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ yᵉ) =
    globular-structure-1-cell-globular-structureᵉ
      ( hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)
      ( xᵉ)
      ( yᵉ)

  hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategoryᵉ :
    (xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ) →
    Noncoherent-Wild-Higher-Precategoryᵉ l2ᵉ l2ᵉ
  hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategoryᵉ
    xᵉ yᵉ =
    make-Noncoherent-Wild-Higher-Precategoryᵉ
      ( hom-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ yᵉ)
      ( globular-structure-1-cell-globular-structureᵉ
        ( hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)
        ( xᵉ)
        ( yᵉ))
      ( is-reflexive-globular-structure-1-cell-is-reflexive-globular-structureᵉ
        ( id-hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)
        ( xᵉ)
        ( yᵉ))
      ( is-transitive-globular-structure-1-cell-is-transitive-globular-structureᵉ
        ( comp-hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)
        ( xᵉ)
        ( yᵉ))
```

```agda
  2-hom-Noncoherent-Wild-Higher-Precategoryᵉ :
    {xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ} →
    hom-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ yᵉ →
    hom-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ yᵉ →
    UUᵉ l2ᵉ
  2-hom-Noncoherent-Wild-Higher-Precategoryᵉ =
    2-cell-globular-structureᵉ
      ( hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)

  id-2-hom-Noncoherent-Wild-Higher-Precategoryᵉ :
    {xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ}
    {fᵉ : hom-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ yᵉ} →
    2-hom-Noncoherent-Wild-Higher-Precategoryᵉ fᵉ fᵉ
  id-2-hom-Noncoherent-Wild-Higher-Precategoryᵉ =
    refl-2-cell-is-reflexive-globular-structureᵉ
      ( id-hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)

  comp-2-hom-Noncoherent-Wild-Higher-Precategoryᵉ :
    {xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ}
    {fᵉ gᵉ hᵉ : hom-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ yᵉ} →
    2-hom-Noncoherent-Wild-Higher-Precategoryᵉ gᵉ hᵉ →
    2-hom-Noncoherent-Wild-Higher-Precategoryᵉ fᵉ gᵉ →
    2-hom-Noncoherent-Wild-Higher-Precategoryᵉ fᵉ hᵉ
  comp-2-hom-Noncoherent-Wild-Higher-Precategoryᵉ =
    comp-2-cell-is-transitive-globular-structureᵉ
      ( comp-hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)
```

```agda
  3-hom-Noncoherent-Wild-Higher-Precategoryᵉ :
    {xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ}
    {fᵉ gᵉ : hom-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ yᵉ} →
    2-hom-Noncoherent-Wild-Higher-Precategoryᵉ fᵉ gᵉ →
    2-hom-Noncoherent-Wild-Higher-Precategoryᵉ fᵉ gᵉ →
    UUᵉ l2ᵉ
  3-hom-Noncoherent-Wild-Higher-Precategoryᵉ =
    3-cell-globular-structureᵉ
      ( hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)

  id-3-hom-Noncoherent-Wild-Higher-Precategoryᵉ :
    {xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ}
    {fᵉ gᵉ : hom-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ yᵉ}
    {Hᵉ : 2-hom-Noncoherent-Wild-Higher-Precategoryᵉ fᵉ gᵉ} →
    3-hom-Noncoherent-Wild-Higher-Precategoryᵉ Hᵉ Hᵉ
  id-3-hom-Noncoherent-Wild-Higher-Precategoryᵉ =
    refl-3-cell-is-reflexive-globular-structureᵉ
      ( id-hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)

  comp-3-hom-Noncoherent-Wild-Higher-Precategoryᵉ :
    {xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ}
    {fᵉ gᵉ : hom-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ yᵉ}
    {Hᵉ Kᵉ Lᵉ : 2-hom-Noncoherent-Wild-Higher-Precategoryᵉ fᵉ gᵉ} →
    3-hom-Noncoherent-Wild-Higher-Precategoryᵉ Kᵉ Lᵉ →
    3-hom-Noncoherent-Wild-Higher-Precategoryᵉ Hᵉ Kᵉ →
    3-hom-Noncoherent-Wild-Higher-Precategoryᵉ Hᵉ Lᵉ
  comp-3-hom-Noncoherent-Wild-Higher-Precategoryᵉ =
    comp-3-cell-is-transitive-globular-structureᵉ
      ( comp-hom-globular-structure-Noncoherent-Wild-Higher-Precategoryᵉ)
```