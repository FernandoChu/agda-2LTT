# The group of multiplicative units of a commutative ring

```agda
module commutative-algebra.groups-of-units-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategoriesᵉ

open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.homomorphisms-commutative-ringsᵉ
open import commutative-algebra.precategory-of-commutative-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.category-of-abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.homomorphisms-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.submonoidsᵉ

open import ring-theory.groups-of-units-ringsᵉ
```

</details>

## Idea

Theᵉ **groupᵉ ofᵉ units**ᵉ ofᵉ aᵉ
[commutativeᵉ ring](commutative-algebra.commutative-rings.mdᵉ) `A`ᵉ isᵉ theᵉ
[abelianᵉ group](group-theory.abelian-groups.mdᵉ) consistingᵉ ofᵉ allᵉ theᵉ
[invertibleᵉ elements](commutative-algebra.invertible-elements-commutative-rings.mdᵉ)
in `A`.ᵉ Equivalently,ᵉ theᵉ groupᵉ ofᵉ unitsᵉ ofᵉ `A`ᵉ isᵉ theᵉ
[core](group-theory.cores-monoids.mdᵉ) ofᵉ theᵉ multiplicativeᵉ
[monoid](group-theory.monoids.mdᵉ) ofᵉ `A`.ᵉ

## Definitions

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  subtype-group-of-units-Commutative-Ringᵉ :
    type-Commutative-Ringᵉ Aᵉ → Propᵉ lᵉ
  subtype-group-of-units-Commutative-Ringᵉ =
    subtype-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  submonoid-group-of-units-Commutative-Ringᵉ :
    Submonoidᵉ lᵉ (multiplicative-monoid-Commutative-Ringᵉ Aᵉ)
  submonoid-group-of-units-Commutative-Ringᵉ =
    submonoid-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  monoid-group-of-units-Commutative-Ringᵉ : Monoidᵉ lᵉ
  monoid-group-of-units-Commutative-Ringᵉ =
    monoid-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  semigroup-group-of-units-Commutative-Ringᵉ : Semigroupᵉ lᵉ
  semigroup-group-of-units-Commutative-Ringᵉ =
    semigroup-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  type-group-of-units-Commutative-Ringᵉ : UUᵉ lᵉ
  type-group-of-units-Commutative-Ringᵉ =
    type-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  mul-group-of-units-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-group-of-units-Commutative-Ringᵉ) →
    type-group-of-units-Commutative-Ringᵉ
  mul-group-of-units-Commutative-Ringᵉ =
    mul-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  associative-mul-group-of-units-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-group-of-units-Commutative-Ringᵉ) →
    mul-group-of-units-Commutative-Ringᵉ
      ( mul-group-of-units-Commutative-Ringᵉ xᵉ yᵉ)
      ( zᵉ) ＝ᵉ
    mul-group-of-units-Commutative-Ringᵉ xᵉ
      ( mul-group-of-units-Commutative-Ringᵉ yᵉ zᵉ)
  associative-mul-group-of-units-Commutative-Ringᵉ =
    associative-mul-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  unit-group-of-units-Commutative-Ringᵉ :
    type-group-of-units-Commutative-Ringᵉ
  unit-group-of-units-Commutative-Ringᵉ =
    unit-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  left-unit-law-mul-group-of-units-Commutative-Ringᵉ :
    (xᵉ : type-group-of-units-Commutative-Ringᵉ) →
    mul-group-of-units-Commutative-Ringᵉ
      ( unit-group-of-units-Commutative-Ringᵉ)
      ( xᵉ) ＝ᵉ
    xᵉ
  left-unit-law-mul-group-of-units-Commutative-Ringᵉ =
    left-unit-law-mul-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  right-unit-law-mul-group-of-units-Commutative-Ringᵉ :
    (xᵉ : type-group-of-units-Commutative-Ringᵉ) →
    mul-group-of-units-Commutative-Ringᵉ
      ( xᵉ)
      ( unit-group-of-units-Commutative-Ringᵉ) ＝ᵉ
    xᵉ
  right-unit-law-mul-group-of-units-Commutative-Ringᵉ =
    right-unit-law-mul-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-unital-group-of-units-Commutative-Ringᵉ :
    is-unital-Semigroupᵉ semigroup-group-of-units-Commutative-Ringᵉ
  is-unital-group-of-units-Commutative-Ringᵉ =
    is-unital-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  inv-group-of-units-Commutative-Ringᵉ :
    type-group-of-units-Commutative-Ringᵉ →
    type-group-of-units-Commutative-Ringᵉ
  inv-group-of-units-Commutative-Ringᵉ =
    inv-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  left-inverse-law-mul-group-of-units-Commutative-Ringᵉ :
    (xᵉ : type-group-of-units-Commutative-Ringᵉ) →
    mul-group-of-units-Commutative-Ringᵉ
      ( inv-group-of-units-Commutative-Ringᵉ xᵉ)
      ( xᵉ) ＝ᵉ
    unit-group-of-units-Commutative-Ringᵉ
  left-inverse-law-mul-group-of-units-Commutative-Ringᵉ =
    left-inverse-law-mul-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  right-inverse-law-mul-group-of-units-Commutative-Ringᵉ :
    (xᵉ : type-group-of-units-Commutative-Ringᵉ) →
    mul-group-of-units-Commutative-Ringᵉ
      ( xᵉ)
      ( inv-group-of-units-Commutative-Ringᵉ xᵉ) ＝ᵉ
    unit-group-of-units-Commutative-Ringᵉ
  right-inverse-law-mul-group-of-units-Commutative-Ringᵉ =
    right-inverse-law-mul-group-of-units-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)

  commutative-mul-group-of-units-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-group-of-units-Commutative-Ringᵉ) →
    mul-group-of-units-Commutative-Ringᵉ xᵉ yᵉ ＝ᵉ
    mul-group-of-units-Commutative-Ringᵉ yᵉ xᵉ
  commutative-mul-group-of-units-Commutative-Ringᵉ xᵉ yᵉ =
    eq-type-subtypeᵉ
      ( subtype-group-of-units-Commutative-Ringᵉ)
      ( commutative-mul-Commutative-Ringᵉ Aᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ))

  is-group-group-of-units-Commutative-Ring'ᵉ :
    is-group-is-unital-Semigroupᵉ
      ( semigroup-group-of-units-Commutative-Ringᵉ)
      ( is-unital-group-of-units-Commutative-Ringᵉ)
  is-group-group-of-units-Commutative-Ring'ᵉ =
    is-group-group-of-units-Ring'ᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-group-group-of-units-Commutative-Ringᵉ :
    is-group-Semigroupᵉ semigroup-group-of-units-Commutative-Ringᵉ
  is-group-group-of-units-Commutative-Ringᵉ =
    is-group-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  group-of-units-Commutative-Ringᵉ : Groupᵉ lᵉ
  group-of-units-Commutative-Ringᵉ =
    group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  abelian-group-of-units-Commutative-Ringᵉ : Abᵉ lᵉ
  pr1ᵉ abelian-group-of-units-Commutative-Ringᵉ =
    group-of-units-Commutative-Ringᵉ
  pr2ᵉ abelian-group-of-units-Commutative-Ringᵉ =
    commutative-mul-group-of-units-Commutative-Ringᵉ

  inclusion-group-of-units-Commutative-Ringᵉ :
    type-group-of-units-Commutative-Ringᵉ → type-Commutative-Ringᵉ Aᵉ
  inclusion-group-of-units-Commutative-Ringᵉ =
    inclusion-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  preserves-mul-inclusion-group-of-units-Commutative-Ringᵉ :
    {xᵉ yᵉ : type-group-of-units-Commutative-Ringᵉ} →
    inclusion-group-of-units-Commutative-Ringᵉ
      ( mul-group-of-units-Commutative-Ringᵉ xᵉ yᵉ) ＝ᵉ
    mul-Commutative-Ringᵉ Aᵉ
      ( inclusion-group-of-units-Commutative-Ringᵉ xᵉ)
      ( inclusion-group-of-units-Commutative-Ringᵉ yᵉ)
  preserves-mul-inclusion-group-of-units-Commutative-Ringᵉ {xᵉ} {yᵉ} =
    preserves-mul-inclusion-group-of-units-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      { xᵉ}
      { yᵉ}

  hom-inclusion-group-of-units-Commutative-Ringᵉ :
    hom-Monoidᵉ monoid-group-of-units-Commutative-Ringᵉ
      ( multiplicative-monoid-Commutative-Ringᵉ Aᵉ)
  hom-inclusion-group-of-units-Commutative-Ringᵉ =
    hom-inclusion-group-of-units-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

## Properties

### The group of units of a commutative ring is a functor from commutative rings to abelian groups

#### The functorial action of `group-of-units-Commutative-Ring`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Bᵉ : Commutative-Ringᵉ l2ᵉ)
  (fᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ)
  where

  map-group-of-units-hom-Commutative-Ringᵉ :
    type-group-of-units-Commutative-Ringᵉ Aᵉ →
    type-group-of-units-Commutative-Ringᵉ Bᵉ
  map-group-of-units-hom-Commutative-Ringᵉ =
    map-group-of-units-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

  preserves-mul-hom-group-of-units-hom-Commutative-Ringᵉ :
    {xᵉ yᵉ : type-group-of-units-Commutative-Ringᵉ Aᵉ} →
    map-group-of-units-hom-Commutative-Ringᵉ
      ( mul-group-of-units-Commutative-Ringᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
    mul-group-of-units-Commutative-Ringᵉ Bᵉ
      ( map-group-of-units-hom-Commutative-Ringᵉ xᵉ)
      ( map-group-of-units-hom-Commutative-Ringᵉ yᵉ)
  preserves-mul-hom-group-of-units-hom-Commutative-Ringᵉ =
    preserves-mul-hom-group-of-units-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

  hom-group-of-units-hom-Commutative-Ringᵉ :
    hom-Groupᵉ
      ( group-of-units-Commutative-Ringᵉ Aᵉ)
      ( group-of-units-Commutative-Ringᵉ Bᵉ)
  hom-group-of-units-hom-Commutative-Ringᵉ =
    hom-group-of-units-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

  preserves-unit-hom-group-of-units-hom-Commutative-Ringᵉ :
    map-group-of-units-hom-Commutative-Ringᵉ
      ( unit-group-of-units-Commutative-Ringᵉ Aᵉ) ＝ᵉ
    unit-group-of-units-Commutative-Ringᵉ Bᵉ
  preserves-unit-hom-group-of-units-hom-Commutative-Ringᵉ =
    preserves-unit-hom-group-of-units-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

  preserves-inv-hom-group-of-units-hom-Commutative-Ringᵉ :
    {xᵉ : type-group-of-units-Commutative-Ringᵉ Aᵉ} →
    map-group-of-units-hom-Commutative-Ringᵉ
      ( inv-group-of-units-Commutative-Ringᵉ Aᵉ xᵉ) ＝ᵉ
    inv-group-of-units-Commutative-Ringᵉ Bᵉ
      ( map-group-of-units-hom-Commutative-Ringᵉ xᵉ)
  preserves-inv-hom-group-of-units-hom-Commutative-Ringᵉ =
    preserves-inv-hom-group-of-units-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)
```

#### The functorial laws of `group-of-units-Commutative-Ring`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  preserves-id-hom-group-of-units-hom-Commutative-Ringᵉ :
    hom-group-of-units-hom-Commutative-Ringᵉ Aᵉ Aᵉ (id-hom-Commutative-Ringᵉ Aᵉ) ＝ᵉ
    id-hom-Groupᵉ (group-of-units-Commutative-Ringᵉ Aᵉ)
  preserves-id-hom-group-of-units-hom-Commutative-Ringᵉ =
    preserves-id-hom-group-of-units-hom-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Bᵉ : Commutative-Ringᵉ l2ᵉ) (Cᵉ : Commutative-Ringᵉ l3ᵉ)
  where

  preserves-comp-hom-group-of-units-hom-Commutative-Ringᵉ :
    (gᵉ : hom-Commutative-Ringᵉ Bᵉ Cᵉ) (fᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ) →
    hom-group-of-units-hom-Commutative-Ringᵉ Aᵉ Cᵉ
      ( comp-hom-Commutative-Ringᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ) ＝ᵉ
    comp-hom-Groupᵉ
      ( group-of-units-Commutative-Ringᵉ Aᵉ)
      ( group-of-units-Commutative-Ringᵉ Bᵉ)
      ( group-of-units-Commutative-Ringᵉ Cᵉ)
      ( hom-group-of-units-hom-Commutative-Ringᵉ Bᵉ Cᵉ gᵉ)
      ( hom-group-of-units-hom-Commutative-Ringᵉ Aᵉ Bᵉ fᵉ)
  preserves-comp-hom-group-of-units-hom-Commutative-Ringᵉ gᵉ fᵉ =
    preserves-comp-hom-group-of-units-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( ring-Commutative-Ringᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)
```

#### The functor `group-of-units-Commutative-Ring`

```agda
group-of-units-commutative-ring-functor-Large-Precategoryᵉ :
  functor-Large-Precategoryᵉ (λ lᵉ → lᵉ)
    ( Commutative-Ring-Large-Precategoryᵉ)
    ( Ab-Large-Precategoryᵉ)
obj-functor-Large-Precategoryᵉ
  group-of-units-commutative-ring-functor-Large-Precategoryᵉ =
  abelian-group-of-units-Commutative-Ringᵉ
hom-functor-Large-Precategoryᵉ
  group-of-units-commutative-ring-functor-Large-Precategoryᵉ {Xᵉ = Aᵉ} {Yᵉ = Bᵉ} =
  hom-group-of-units-hom-Commutative-Ringᵉ Aᵉ Bᵉ
preserves-comp-functor-Large-Precategoryᵉ
  group-of-units-commutative-ring-functor-Large-Precategoryᵉ
  {Xᵉ = Aᵉ}
  {Yᵉ = Bᵉ}
  {Zᵉ = Cᵉ} =
  preserves-comp-hom-group-of-units-hom-Commutative-Ringᵉ Aᵉ Bᵉ Cᵉ
preserves-id-functor-Large-Precategoryᵉ
  group-of-units-commutative-ring-functor-Large-Precategoryᵉ {Xᵉ = Aᵉ} =
  preserves-id-hom-group-of-units-hom-Commutative-Ringᵉ Aᵉ
```