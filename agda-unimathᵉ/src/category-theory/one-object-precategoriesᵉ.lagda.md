# One object precategories

```agda
module category-theory.one-object-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.endomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import group-theory.monoidsᵉ
```

</details>

## Definition

```agda
is-one-object-prop-Precategoryᵉ : {l1ᵉ l2ᵉ : Level} → Precategoryᵉ l1ᵉ l2ᵉ → Propᵉ l1ᵉ
is-one-object-prop-Precategoryᵉ Pᵉ = is-contr-Propᵉ (obj-Precategoryᵉ Pᵉ)

is-one-object-Precategoryᵉ : {l1ᵉ l2ᵉ : Level} → Precategoryᵉ l1ᵉ l2ᵉ → UUᵉ l1ᵉ
is-one-object-Precategoryᵉ Pᵉ = type-Propᵉ (is-one-object-prop-Precategoryᵉ Pᵉ)

One-Object-Precategoryᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
One-Object-Precategoryᵉ l1ᵉ l2ᵉ = Σᵉ (Precategoryᵉ l1ᵉ l2ᵉ) (is-one-object-Precategoryᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : One-Object-Precategoryᵉ l1ᵉ l2ᵉ)
  where

  precategory-One-Object-Precategoryᵉ : Precategoryᵉ l1ᵉ l2ᵉ
  precategory-One-Object-Precategoryᵉ = pr1ᵉ Pᵉ

  is-one-object-precategory-One-Object-Precategoryᵉ :
    is-one-object-Precategoryᵉ precategory-One-Object-Precategoryᵉ
  is-one-object-precategory-One-Object-Precategoryᵉ = pr2ᵉ Pᵉ

  object-One-Object-Precategoryᵉ :
    obj-Precategoryᵉ precategory-One-Object-Precategoryᵉ
  object-One-Object-Precategoryᵉ =
    centerᵉ is-one-object-precategory-One-Object-Precategoryᵉ
```

## Properties

### Monoids are one-object precategories

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  hom-set-one-object-precategory-Monoidᵉ :
    unitᵉ → unitᵉ → Setᵉ lᵉ
  hom-set-one-object-precategory-Monoidᵉ _ _ = set-Monoidᵉ Mᵉ

  hom-one-object-precategory-Monoidᵉ :
    unitᵉ → unitᵉ → UUᵉ lᵉ
  hom-one-object-precategory-Monoidᵉ xᵉ yᵉ =
    type-Setᵉ (hom-set-one-object-precategory-Monoidᵉ xᵉ yᵉ)

  comp-hom-one-object-precategory-Monoidᵉ :
    {xᵉ yᵉ zᵉ : unitᵉ} →
    hom-one-object-precategory-Monoidᵉ yᵉ zᵉ →
    hom-one-object-precategory-Monoidᵉ xᵉ yᵉ →
    hom-one-object-precategory-Monoidᵉ xᵉ zᵉ
  comp-hom-one-object-precategory-Monoidᵉ =
    mul-Monoidᵉ Mᵉ

  associative-comp-hom-one-object-precategory-Monoidᵉ :
    {xᵉ yᵉ zᵉ wᵉ : unitᵉ} →
    (hᵉ : hom-one-object-precategory-Monoidᵉ zᵉ wᵉ)
    (gᵉ : hom-one-object-precategory-Monoidᵉ yᵉ zᵉ)
    (fᵉ : hom-one-object-precategory-Monoidᵉ xᵉ yᵉ) →
    comp-hom-one-object-precategory-Monoidᵉ
      ( comp-hom-one-object-precategory-Monoidᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-one-object-precategory-Monoidᵉ
      ( hᵉ)
      ( comp-hom-one-object-precategory-Monoidᵉ gᵉ fᵉ)
  associative-comp-hom-one-object-precategory-Monoidᵉ =
    associative-mul-Monoidᵉ Mᵉ

  id-hom-one-object-precategory-Monoidᵉ :
    (xᵉ : unitᵉ) → hom-one-object-precategory-Monoidᵉ xᵉ xᵉ
  id-hom-one-object-precategory-Monoidᵉ _ = unit-Monoidᵉ Mᵉ

  left-unit-law-comp-hom-one-object-precategory-Monoidᵉ :
    {xᵉ yᵉ : unitᵉ} (fᵉ : hom-one-object-precategory-Monoidᵉ xᵉ yᵉ) →
    comp-hom-one-object-precategory-Monoidᵉ
      ( id-hom-one-object-precategory-Monoidᵉ yᵉ)
      ( fᵉ) ＝ᵉ
    fᵉ
  left-unit-law-comp-hom-one-object-precategory-Monoidᵉ =
    left-unit-law-mul-Monoidᵉ Mᵉ

  right-unit-law-comp-hom-one-object-precategory-Monoidᵉ :
    {xᵉ yᵉ : unitᵉ} (fᵉ : hom-one-object-precategory-Monoidᵉ xᵉ yᵉ) →
    comp-hom-one-object-precategory-Monoidᵉ
      ( fᵉ)
      ( id-hom-one-object-precategory-Monoidᵉ xᵉ) ＝ᵉ
    fᵉ
  right-unit-law-comp-hom-one-object-precategory-Monoidᵉ =
    right-unit-law-mul-Monoidᵉ Mᵉ

  precategory-one-object-precategory-Monoidᵉ : Precategoryᵉ lzero lᵉ
  precategory-one-object-precategory-Monoidᵉ =
    make-Precategoryᵉ
      ( unitᵉ)
      ( hom-set-one-object-precategory-Monoidᵉ)
      ( comp-hom-one-object-precategory-Monoidᵉ)
      ( id-hom-one-object-precategory-Monoidᵉ)
      ( associative-comp-hom-one-object-precategory-Monoidᵉ)
      ( left-unit-law-comp-hom-one-object-precategory-Monoidᵉ)
      ( right-unit-law-comp-hom-one-object-precategory-Monoidᵉ)

  one-object-precategory-Monoidᵉ : One-Object-Precategoryᵉ lzero lᵉ
  pr1ᵉ one-object-precategory-Monoidᵉ = precategory-one-object-precategory-Monoidᵉ
  pr2ᵉ one-object-precategory-Monoidᵉ = is-contr-unitᵉ
```

### Monoids from one-object precategories

```agda
monoid-One-Object-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} → One-Object-Precategoryᵉ l1ᵉ l2ᵉ → Monoidᵉ l2ᵉ
monoid-One-Object-Precategoryᵉ Pᵉ =
  monoid-endo-Precategoryᵉ
    ( precategory-One-Object-Precategoryᵉ Pᵉ)
    ( object-One-Object-Precategoryᵉ Pᵉ)
```