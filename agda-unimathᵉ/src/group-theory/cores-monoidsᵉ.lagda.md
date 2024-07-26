# Cores of monoids

```agda
module group-theory.cores-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.homomorphisms-monoidsᵉ
open import group-theory.invertible-elements-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.precategory-of-groupsᵉ
open import group-theory.precategory-of-monoidsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.submonoidsᵉ
```

</details>

## Idea

Theᵉ **core**ᵉ ofᵉ aᵉ [monoid](group-theory.monoids.mdᵉ) `M`ᵉ isᵉ theᵉ maximalᵉ
[group](group-theory.groups.mdᵉ) containedᵉ in `M`,ᵉ andᵉ consistsᵉ ofᵉ allᵉ theᵉ
elementsᵉ thatᵉ areᵉ [invertible](group-theory.invertible-elements-monoids.md).ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  subtype-core-Monoidᵉ : type-Monoidᵉ Mᵉ → Propᵉ lᵉ
  subtype-core-Monoidᵉ = is-invertible-element-prop-Monoidᵉ Mᵉ

  submonoid-core-Monoidᵉ : Submonoidᵉ lᵉ Mᵉ
  pr1ᵉ submonoid-core-Monoidᵉ = subtype-core-Monoidᵉ
  pr1ᵉ (pr2ᵉ submonoid-core-Monoidᵉ) = is-invertible-element-unit-Monoidᵉ Mᵉ
  pr2ᵉ (pr2ᵉ submonoid-core-Monoidᵉ) = is-invertible-element-mul-Monoidᵉ Mᵉ

  monoid-core-Monoidᵉ : Monoidᵉ lᵉ
  monoid-core-Monoidᵉ = monoid-Submonoidᵉ Mᵉ submonoid-core-Monoidᵉ

  semigroup-core-Monoidᵉ : Semigroupᵉ lᵉ
  semigroup-core-Monoidᵉ = semigroup-Submonoidᵉ Mᵉ submonoid-core-Monoidᵉ

  type-core-Monoidᵉ : UUᵉ lᵉ
  type-core-Monoidᵉ = type-Submonoidᵉ Mᵉ submonoid-core-Monoidᵉ

  mul-core-Monoidᵉ : type-core-Monoidᵉ → type-core-Monoidᵉ → type-core-Monoidᵉ
  mul-core-Monoidᵉ = mul-Semigroupᵉ semigroup-core-Monoidᵉ

  associative-mul-core-Monoidᵉ :
    (xᵉ yᵉ zᵉ : type-core-Monoidᵉ) →
    mul-core-Monoidᵉ (mul-core-Monoidᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-core-Monoidᵉ xᵉ (mul-core-Monoidᵉ yᵉ zᵉ)
  associative-mul-core-Monoidᵉ =
    associative-mul-Semigroupᵉ semigroup-core-Monoidᵉ

  unit-core-Monoidᵉ : type-core-Monoidᵉ
  pr1ᵉ unit-core-Monoidᵉ = unit-Monoidᵉ Mᵉ
  pr2ᵉ unit-core-Monoidᵉ = is-invertible-element-unit-Monoidᵉ Mᵉ

  left-unit-law-mul-core-Monoidᵉ :
    (xᵉ : type-core-Monoidᵉ) →
    mul-core-Monoidᵉ unit-core-Monoidᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-core-Monoidᵉ xᵉ =
    eq-type-subtypeᵉ subtype-core-Monoidᵉ (left-unit-law-mul-Monoidᵉ Mᵉ (pr1ᵉ xᵉ))

  right-unit-law-mul-core-Monoidᵉ :
    (xᵉ : type-core-Monoidᵉ) →
    mul-core-Monoidᵉ xᵉ unit-core-Monoidᵉ ＝ᵉ xᵉ
  right-unit-law-mul-core-Monoidᵉ xᵉ =
    eq-type-subtypeᵉ subtype-core-Monoidᵉ (right-unit-law-mul-Monoidᵉ Mᵉ (pr1ᵉ xᵉ))

  is-unital-core-Monoidᵉ : is-unital-Semigroupᵉ semigroup-core-Monoidᵉ
  pr1ᵉ is-unital-core-Monoidᵉ = unit-core-Monoidᵉ
  pr1ᵉ (pr2ᵉ is-unital-core-Monoidᵉ) = left-unit-law-mul-core-Monoidᵉ
  pr2ᵉ (pr2ᵉ is-unital-core-Monoidᵉ) = right-unit-law-mul-core-Monoidᵉ

  inv-core-Monoidᵉ : type-core-Monoidᵉ → type-core-Monoidᵉ
  pr1ᵉ (inv-core-Monoidᵉ xᵉ) =
    inv-is-invertible-element-Monoidᵉ Mᵉ (pr2ᵉ xᵉ)
  pr2ᵉ (inv-core-Monoidᵉ xᵉ) =
    is-invertible-element-inv-is-invertible-element-Monoidᵉ Mᵉ (pr2ᵉ xᵉ)

  left-inverse-law-mul-core-Monoidᵉ :
    (xᵉ : type-core-Monoidᵉ) →
    mul-core-Monoidᵉ (inv-core-Monoidᵉ xᵉ) xᵉ ＝ᵉ unit-core-Monoidᵉ
  left-inverse-law-mul-core-Monoidᵉ xᵉ =
    eq-type-subtypeᵉ
      ( subtype-core-Monoidᵉ)
      ( is-left-inverse-inv-is-invertible-element-Monoidᵉ Mᵉ (pr2ᵉ xᵉ))

  right-inverse-law-mul-core-Monoidᵉ :
    (xᵉ : type-core-Monoidᵉ) →
    mul-core-Monoidᵉ xᵉ (inv-core-Monoidᵉ xᵉ) ＝ᵉ unit-core-Monoidᵉ
  right-inverse-law-mul-core-Monoidᵉ xᵉ =
    eq-type-subtypeᵉ
      ( subtype-core-Monoidᵉ)
      ( is-right-inverse-inv-is-invertible-element-Monoidᵉ Mᵉ (pr2ᵉ xᵉ))

  is-group-core-Monoid'ᵉ :
    is-group-is-unital-Semigroupᵉ semigroup-core-Monoidᵉ is-unital-core-Monoidᵉ
  pr1ᵉ is-group-core-Monoid'ᵉ = inv-core-Monoidᵉ
  pr1ᵉ (pr2ᵉ is-group-core-Monoid'ᵉ) = left-inverse-law-mul-core-Monoidᵉ
  pr2ᵉ (pr2ᵉ is-group-core-Monoid'ᵉ) = right-inverse-law-mul-core-Monoidᵉ

  is-group-core-Monoidᵉ : is-group-Semigroupᵉ semigroup-core-Monoidᵉ
  pr1ᵉ is-group-core-Monoidᵉ = is-unital-core-Monoidᵉ
  pr2ᵉ is-group-core-Monoidᵉ = is-group-core-Monoid'ᵉ

  core-Monoidᵉ : Groupᵉ lᵉ
  pr1ᵉ core-Monoidᵉ = semigroup-core-Monoidᵉ
  pr2ᵉ core-Monoidᵉ = is-group-core-Monoidᵉ

  inclusion-core-Monoidᵉ :
    type-core-Monoidᵉ → type-Monoidᵉ Mᵉ
  inclusion-core-Monoidᵉ =
    inclusion-Submonoidᵉ Mᵉ submonoid-core-Monoidᵉ

  preserves-mul-inclusion-core-Monoidᵉ :
    {xᵉ yᵉ : type-core-Monoidᵉ} →
    inclusion-core-Monoidᵉ (mul-core-Monoidᵉ xᵉ yᵉ) ＝ᵉ
    mul-Monoidᵉ Mᵉ
      ( inclusion-core-Monoidᵉ xᵉ)
      ( inclusion-core-Monoidᵉ yᵉ)
  preserves-mul-inclusion-core-Monoidᵉ {xᵉ} {yᵉ} =
    preserves-mul-inclusion-Submonoidᵉ Mᵉ submonoid-core-Monoidᵉ {xᵉ} {yᵉ}

  hom-inclusion-core-Monoidᵉ :
    hom-Monoidᵉ monoid-core-Monoidᵉ Mᵉ
  hom-inclusion-core-Monoidᵉ =
    hom-inclusion-Submonoidᵉ Mᵉ submonoid-core-Monoidᵉ
```

## Properties

### The core of a monoid is a functor from monoids to groups

#### The functorial action of `core-Monoid`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ) (fᵉ : hom-Monoidᵉ Mᵉ Nᵉ)
  where

  map-core-hom-Monoidᵉ : type-core-Monoidᵉ Mᵉ → type-core-Monoidᵉ Nᵉ
  pr1ᵉ (map-core-hom-Monoidᵉ xᵉ) = map-hom-Monoidᵉ Mᵉ Nᵉ fᵉ (pr1ᵉ xᵉ)
  pr2ᵉ (map-core-hom-Monoidᵉ xᵉ) =
    preserves-invertible-elements-hom-Monoidᵉ Mᵉ Nᵉ fᵉ (pr2ᵉ xᵉ)

  preserves-mul-hom-core-hom-Monoidᵉ :
    {xᵉ yᵉ : type-core-Monoidᵉ Mᵉ} →
    map-core-hom-Monoidᵉ (mul-core-Monoidᵉ Mᵉ xᵉ yᵉ) ＝ᵉ
    mul-core-Monoidᵉ Nᵉ (map-core-hom-Monoidᵉ xᵉ) (map-core-hom-Monoidᵉ yᵉ)
  preserves-mul-hom-core-hom-Monoidᵉ =
    eq-type-subtypeᵉ
      ( subtype-core-Monoidᵉ Nᵉ)
      ( preserves-mul-hom-Monoidᵉ Mᵉ Nᵉ fᵉ)

  hom-core-hom-Monoidᵉ : hom-Groupᵉ (core-Monoidᵉ Mᵉ) (core-Monoidᵉ Nᵉ)
  pr1ᵉ hom-core-hom-Monoidᵉ = map-core-hom-Monoidᵉ
  pr2ᵉ hom-core-hom-Monoidᵉ = preserves-mul-hom-core-hom-Monoidᵉ

  preserves-unit-hom-core-hom-Monoidᵉ :
    map-core-hom-Monoidᵉ (unit-core-Monoidᵉ Mᵉ) ＝ᵉ unit-core-Monoidᵉ Nᵉ
  preserves-unit-hom-core-hom-Monoidᵉ =
    preserves-unit-hom-Groupᵉ (core-Monoidᵉ Mᵉ) (core-Monoidᵉ Nᵉ) hom-core-hom-Monoidᵉ

  preserves-inv-hom-core-hom-Monoidᵉ :
    {xᵉ : type-core-Monoidᵉ Mᵉ} →
    map-core-hom-Monoidᵉ (inv-core-Monoidᵉ Mᵉ xᵉ) ＝ᵉ
    inv-core-Monoidᵉ Nᵉ (map-core-hom-Monoidᵉ xᵉ)
  preserves-inv-hom-core-hom-Monoidᵉ =
    preserves-inv-hom-Groupᵉ (core-Monoidᵉ Mᵉ) (core-Monoidᵉ Nᵉ) hom-core-hom-Monoidᵉ
```

#### The functorial laws of `core-Monoid`

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  preserves-id-hom-core-hom-Monoidᵉ :
    hom-core-hom-Monoidᵉ Mᵉ Mᵉ (id-hom-Monoidᵉ Mᵉ) ＝ᵉ id-hom-Groupᵉ (core-Monoidᵉ Mᵉ)
  preserves-id-hom-core-hom-Monoidᵉ =
    eq-htpy-hom-Groupᵉ
      ( core-Monoidᵉ Mᵉ)
      ( core-Monoidᵉ Mᵉ)
      ( λ _ → eq-type-subtypeᵉ (subtype-core-Monoidᵉ Mᵉ) reflᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ) (Kᵉ : Monoidᵉ l3ᵉ)
  where

  preserves-comp-hom-core-hom-Monoidᵉ :
    (gᵉ : hom-Monoidᵉ Nᵉ Kᵉ) (fᵉ : hom-Monoidᵉ Mᵉ Nᵉ) →
    hom-core-hom-Monoidᵉ Mᵉ Kᵉ (comp-hom-Monoidᵉ Mᵉ Nᵉ Kᵉ gᵉ fᵉ) ＝ᵉ
    comp-hom-Groupᵉ
      ( core-Monoidᵉ Mᵉ)
      ( core-Monoidᵉ Nᵉ)
      ( core-Monoidᵉ Kᵉ)
      ( hom-core-hom-Monoidᵉ Nᵉ Kᵉ gᵉ)
      ( hom-core-hom-Monoidᵉ Mᵉ Nᵉ fᵉ)
  preserves-comp-hom-core-hom-Monoidᵉ gᵉ fᵉ =
    eq-htpy-hom-Groupᵉ
      ( core-Monoidᵉ Mᵉ)
      ( core-Monoidᵉ Kᵉ)
      ( λ _ → eq-type-subtypeᵉ (subtype-core-Monoidᵉ Kᵉ) reflᵉ)
```

#### The functor `core-Monoid`

```agda
core-monoid-functor-Large-Precategoryᵉ :
  functor-Large-Precategoryᵉ (λ lᵉ → lᵉ)
    Monoid-Large-Precategoryᵉ
    Group-Large-Precategoryᵉ
obj-functor-Large-Precategoryᵉ
  core-monoid-functor-Large-Precategoryᵉ =
  core-Monoidᵉ
hom-functor-Large-Precategoryᵉ
  core-monoid-functor-Large-Precategoryᵉ {Xᵉ = Mᵉ} {Yᵉ = Nᵉ} =
  hom-core-hom-Monoidᵉ Mᵉ Nᵉ
preserves-comp-functor-Large-Precategoryᵉ
  core-monoid-functor-Large-Precategoryᵉ {Xᵉ = Mᵉ} {Yᵉ = Nᵉ} {Zᵉ = Kᵉ} =
  preserves-comp-hom-core-hom-Monoidᵉ Mᵉ Nᵉ Kᵉ
preserves-id-functor-Large-Precategoryᵉ
  core-monoid-functor-Large-Precategoryᵉ {Xᵉ = Mᵉ} =
  preserves-id-hom-core-hom-Monoidᵉ Mᵉ
```

### The core functor is right adjoint to the forgetful functor from groups to monoids

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ Thisᵉ forgetfulᵉ functorᵉ alsoᵉ hasᵉ aᵉ leftᵉ adjoint,ᵉ
correspondingᵉ to _groupificationᵉ_ ofᵉ theᵉ monoid.ᵉ