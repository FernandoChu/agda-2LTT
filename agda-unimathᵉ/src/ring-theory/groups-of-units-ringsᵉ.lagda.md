# The group of multiplicative units of a ring

```agda
module ring-theory.groups-of-units-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategoriesᵉ

open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.cores-monoidsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.homomorphisms-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.precategory-of-groupsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.submonoidsᵉ

open import ring-theory.homomorphisms-ringsᵉ
open import ring-theory.invertible-elements-ringsᵉ
open import ring-theory.precategory-of-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Theᵉ **groupᵉ ofᵉ units**ᵉ ofᵉ aᵉ [ring](ring-theory.rings.mdᵉ) `R`ᵉ isᵉ theᵉ
[group](group-theory.groups.mdᵉ) consistingᵉ ofᵉ allᵉ theᵉ
[invertibleᵉ elements](ring-theory.invertible-elements-rings.mdᵉ) in `R`.ᵉ
Equivalently,ᵉ theᵉ groupᵉ ofᵉ unitsᵉ ofᵉ `R`ᵉ isᵉ theᵉ
[core](group-theory.cores-monoids.mdᵉ) ofᵉ theᵉ multiplicativeᵉ
[monoid](group-theory.monoids.mdᵉ) ofᵉ `R`.ᵉ

## Definitions

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  subtype-group-of-units-Ringᵉ : type-Ringᵉ Rᵉ → Propᵉ lᵉ
  subtype-group-of-units-Ringᵉ = is-invertible-element-prop-Ringᵉ Rᵉ

  submonoid-group-of-units-Ringᵉ : Submonoidᵉ lᵉ (multiplicative-monoid-Ringᵉ Rᵉ)
  submonoid-group-of-units-Ringᵉ =
    submonoid-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  monoid-group-of-units-Ringᵉ : Monoidᵉ lᵉ
  monoid-group-of-units-Ringᵉ =
    monoid-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  semigroup-group-of-units-Ringᵉ : Semigroupᵉ lᵉ
  semigroup-group-of-units-Ringᵉ =
    semigroup-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  type-group-of-units-Ringᵉ : UUᵉ lᵉ
  type-group-of-units-Ringᵉ =
    type-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  mul-group-of-units-Ringᵉ :
    (xᵉ yᵉ : type-group-of-units-Ringᵉ) → type-group-of-units-Ringᵉ
  mul-group-of-units-Ringᵉ =
    mul-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  associative-mul-group-of-units-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-group-of-units-Ringᵉ) →
    mul-group-of-units-Ringᵉ (mul-group-of-units-Ringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-group-of-units-Ringᵉ xᵉ (mul-group-of-units-Ringᵉ yᵉ zᵉ)
  associative-mul-group-of-units-Ringᵉ =
    associative-mul-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  unit-group-of-units-Ringᵉ : type-group-of-units-Ringᵉ
  unit-group-of-units-Ringᵉ =
    unit-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  left-unit-law-mul-group-of-units-Ringᵉ :
    (xᵉ : type-group-of-units-Ringᵉ) →
    mul-group-of-units-Ringᵉ unit-group-of-units-Ringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-group-of-units-Ringᵉ =
    left-unit-law-mul-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  right-unit-law-mul-group-of-units-Ringᵉ :
    (xᵉ : type-group-of-units-Ringᵉ) →
    mul-group-of-units-Ringᵉ xᵉ unit-group-of-units-Ringᵉ ＝ᵉ xᵉ
  right-unit-law-mul-group-of-units-Ringᵉ =
    right-unit-law-mul-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  is-unital-group-of-units-Ringᵉ :
    is-unital-Semigroupᵉ semigroup-group-of-units-Ringᵉ
  is-unital-group-of-units-Ringᵉ =
    is-unital-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  inv-group-of-units-Ringᵉ : type-group-of-units-Ringᵉ → type-group-of-units-Ringᵉ
  inv-group-of-units-Ringᵉ =
    inv-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  left-inverse-law-mul-group-of-units-Ringᵉ :
    (xᵉ : type-group-of-units-Ringᵉ) →
    mul-group-of-units-Ringᵉ (inv-group-of-units-Ringᵉ xᵉ) xᵉ ＝ᵉ
    unit-group-of-units-Ringᵉ
  left-inverse-law-mul-group-of-units-Ringᵉ =
    left-inverse-law-mul-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  right-inverse-law-mul-group-of-units-Ringᵉ :
    (xᵉ : type-group-of-units-Ringᵉ) →
    mul-group-of-units-Ringᵉ xᵉ (inv-group-of-units-Ringᵉ xᵉ) ＝ᵉ
    unit-group-of-units-Ringᵉ
  right-inverse-law-mul-group-of-units-Ringᵉ =
    right-inverse-law-mul-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  is-group-group-of-units-Ring'ᵉ :
    is-group-is-unital-Semigroupᵉ
      ( semigroup-group-of-units-Ringᵉ)
      ( is-unital-group-of-units-Ringᵉ)
  is-group-group-of-units-Ring'ᵉ =
    is-group-core-Monoid'ᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  is-group-group-of-units-Ringᵉ :
    is-group-Semigroupᵉ semigroup-group-of-units-Ringᵉ
  is-group-group-of-units-Ringᵉ =
    is-group-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  group-of-units-Ringᵉ : Groupᵉ lᵉ
  group-of-units-Ringᵉ = core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  inclusion-group-of-units-Ringᵉ :
    type-group-of-units-Ringᵉ → type-Ringᵉ Rᵉ
  inclusion-group-of-units-Ringᵉ =
    inclusion-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  preserves-mul-inclusion-group-of-units-Ringᵉ :
    {xᵉ yᵉ : type-group-of-units-Ringᵉ} →
    inclusion-group-of-units-Ringᵉ (mul-group-of-units-Ringᵉ xᵉ yᵉ) ＝ᵉ
    mul-Ringᵉ Rᵉ
      ( inclusion-group-of-units-Ringᵉ xᵉ)
      ( inclusion-group-of-units-Ringᵉ yᵉ)
  preserves-mul-inclusion-group-of-units-Ringᵉ {xᵉ} {yᵉ} =
    preserves-mul-inclusion-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ) {xᵉ} {yᵉ}

  hom-inclusion-group-of-units-Ringᵉ :
    hom-Monoidᵉ monoid-group-of-units-Ringᵉ (multiplicative-monoid-Ringᵉ Rᵉ)
  hom-inclusion-group-of-units-Ringᵉ =
    hom-inclusion-core-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)
```

## Properties

### The group of units of a ring is a functor from rings to groups

#### The functorial action of `group-of-units-Ring`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (fᵉ : hom-Ringᵉ Rᵉ Sᵉ)
  where

  map-group-of-units-hom-Ringᵉ :
    type-group-of-units-Ringᵉ Rᵉ → type-group-of-units-Ringᵉ Sᵉ
  map-group-of-units-hom-Ringᵉ =
    map-core-hom-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( multiplicative-monoid-Ringᵉ Sᵉ)
      ( hom-multiplicative-monoid-hom-Ringᵉ Rᵉ Sᵉ fᵉ)

  preserves-mul-hom-group-of-units-hom-Ringᵉ :
    {xᵉ yᵉ : type-group-of-units-Ringᵉ Rᵉ} →
    map-group-of-units-hom-Ringᵉ (mul-group-of-units-Ringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
    mul-group-of-units-Ringᵉ Sᵉ
      ( map-group-of-units-hom-Ringᵉ xᵉ)
      ( map-group-of-units-hom-Ringᵉ yᵉ)
  preserves-mul-hom-group-of-units-hom-Ringᵉ =
    preserves-mul-hom-core-hom-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( multiplicative-monoid-Ringᵉ Sᵉ)
      ( hom-multiplicative-monoid-hom-Ringᵉ Rᵉ Sᵉ fᵉ)

  hom-group-of-units-hom-Ringᵉ :
    hom-Groupᵉ (group-of-units-Ringᵉ Rᵉ) (group-of-units-Ringᵉ Sᵉ)
  hom-group-of-units-hom-Ringᵉ =
    hom-core-hom-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( multiplicative-monoid-Ringᵉ Sᵉ)
      ( hom-multiplicative-monoid-hom-Ringᵉ Rᵉ Sᵉ fᵉ)

  preserves-unit-hom-group-of-units-hom-Ringᵉ :
    map-group-of-units-hom-Ringᵉ (unit-group-of-units-Ringᵉ Rᵉ) ＝ᵉ
    unit-group-of-units-Ringᵉ Sᵉ
  preserves-unit-hom-group-of-units-hom-Ringᵉ =
    preserves-unit-hom-core-hom-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( multiplicative-monoid-Ringᵉ Sᵉ)
      ( hom-multiplicative-monoid-hom-Ringᵉ Rᵉ Sᵉ fᵉ)

  preserves-inv-hom-group-of-units-hom-Ringᵉ :
    {xᵉ : type-group-of-units-Ringᵉ Rᵉ} →
    map-group-of-units-hom-Ringᵉ (inv-group-of-units-Ringᵉ Rᵉ xᵉ) ＝ᵉ
    inv-group-of-units-Ringᵉ Sᵉ (map-group-of-units-hom-Ringᵉ xᵉ)
  preserves-inv-hom-group-of-units-hom-Ringᵉ =
    preserves-inv-hom-core-hom-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( multiplicative-monoid-Ringᵉ Sᵉ)
      ( hom-multiplicative-monoid-hom-Ringᵉ Rᵉ Sᵉ fᵉ)
```

#### The functorial laws of `group-of-units-Ring`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  preserves-id-hom-group-of-units-hom-Ringᵉ :
    hom-group-of-units-hom-Ringᵉ Rᵉ Rᵉ (id-hom-Ringᵉ Rᵉ) ＝ᵉ
    id-hom-Groupᵉ (group-of-units-Ringᵉ Rᵉ)
  preserves-id-hom-group-of-units-hom-Ringᵉ =
    preserves-id-hom-core-hom-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Tᵉ : Ringᵉ l3ᵉ)
  where

  preserves-comp-hom-group-of-units-hom-Ringᵉ :
    (gᵉ : hom-Ringᵉ Sᵉ Tᵉ) (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) →
    hom-group-of-units-hom-Ringᵉ Rᵉ Tᵉ (comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ gᵉ fᵉ) ＝ᵉ
    comp-hom-Groupᵉ
      ( group-of-units-Ringᵉ Rᵉ)
      ( group-of-units-Ringᵉ Sᵉ)
      ( group-of-units-Ringᵉ Tᵉ)
      ( hom-group-of-units-hom-Ringᵉ Sᵉ Tᵉ gᵉ)
      ( hom-group-of-units-hom-Ringᵉ Rᵉ Sᵉ fᵉ)
  preserves-comp-hom-group-of-units-hom-Ringᵉ gᵉ fᵉ =
    preserves-comp-hom-core-hom-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( multiplicative-monoid-Ringᵉ Sᵉ)
      ( multiplicative-monoid-Ringᵉ Tᵉ)
      ( hom-multiplicative-monoid-hom-Ringᵉ Sᵉ Tᵉ gᵉ)
      ( hom-multiplicative-monoid-hom-Ringᵉ Rᵉ Sᵉ fᵉ)
```

#### The functor `group-of-units-Ring`

```agda
group-of-units-ring-functor-Large-Precategoryᵉ :
  functor-Large-Precategoryᵉ
    ( λ lᵉ → lᵉ)
    ( Ring-Large-Precategoryᵉ)
    ( Group-Large-Precategoryᵉ)
obj-functor-Large-Precategoryᵉ
  group-of-units-ring-functor-Large-Precategoryᵉ =
  group-of-units-Ringᵉ
hom-functor-Large-Precategoryᵉ
  group-of-units-ring-functor-Large-Precategoryᵉ {Xᵉ = Rᵉ} {Yᵉ = Sᵉ} =
  hom-group-of-units-hom-Ringᵉ Rᵉ Sᵉ
preserves-comp-functor-Large-Precategoryᵉ
  group-of-units-ring-functor-Large-Precategoryᵉ {Xᵉ = Rᵉ} {Yᵉ = Sᵉ} {Zᵉ = Tᵉ} =
  preserves-comp-hom-group-of-units-hom-Ringᵉ Rᵉ Sᵉ Tᵉ
preserves-id-functor-Large-Precategoryᵉ
  group-of-units-ring-functor-Large-Precategoryᵉ {Xᵉ = Rᵉ} =
  preserves-id-hom-group-of-units-hom-Ringᵉ Rᵉ
```