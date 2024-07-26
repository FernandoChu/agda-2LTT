# Subgroups

```agda
module group-theory.subgroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.binary-relationsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.disjunctionᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.powersetsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.integer-powers-of-elements-groupsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.subsemigroupsᵉ
open import group-theory.subsets-groupsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.large-preordersᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
open import order-theory.similarity-of-elements-large-posetsᵉ
```

</details>

## Definitions

### Subgroups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Pᵉ : subset-Groupᵉ l2ᵉ Gᵉ)
  where

  contains-unit-prop-subset-Groupᵉ : Propᵉ l2ᵉ
  contains-unit-prop-subset-Groupᵉ = Pᵉ (unit-Groupᵉ Gᵉ)

  contains-unit-subset-Groupᵉ : UUᵉ l2ᵉ
  contains-unit-subset-Groupᵉ =
    type-Propᵉ contains-unit-prop-subset-Groupᵉ

  is-prop-contains-unit-subset-Groupᵉ :
    is-propᵉ contains-unit-subset-Groupᵉ
  is-prop-contains-unit-subset-Groupᵉ =
    is-prop-type-Propᵉ contains-unit-prop-subset-Groupᵉ

  is-closed-under-multiplication-prop-subset-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-multiplication-prop-subset-Groupᵉ =
    is-closed-under-multiplication-prop-subset-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( Pᵉ)

  is-closed-under-multiplication-subset-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-multiplication-subset-Groupᵉ =
    type-Propᵉ is-closed-under-multiplication-prop-subset-Groupᵉ

  is-prop-is-closed-under-multiplication-subset-Groupᵉ :
    is-propᵉ is-closed-under-multiplication-subset-Groupᵉ
  is-prop-is-closed-under-multiplication-subset-Groupᵉ =
    is-prop-type-Propᵉ is-closed-under-multiplication-prop-subset-Groupᵉ

  is-closed-under-inverses-prop-subset-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-inverses-prop-subset-Groupᵉ =
    implicit-Π-Propᵉ
      ( type-Groupᵉ Gᵉ)
      ( λ xᵉ → hom-Propᵉ (Pᵉ xᵉ) (Pᵉ (inv-Groupᵉ Gᵉ xᵉ)))

  is-closed-under-inverses-subset-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-inverses-subset-Groupᵉ =
    type-Propᵉ is-closed-under-inverses-prop-subset-Groupᵉ

  is-prop-is-closed-under-inverses-subset-Groupᵉ :
    is-propᵉ is-closed-under-inverses-subset-Groupᵉ
  is-prop-is-closed-under-inverses-subset-Groupᵉ =
    is-prop-type-Propᵉ is-closed-under-inverses-prop-subset-Groupᵉ

  is-subgroup-prop-subset-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-subgroup-prop-subset-Groupᵉ =
    product-Propᵉ
      ( contains-unit-prop-subset-Groupᵉ)
      ( product-Propᵉ
        ( is-closed-under-multiplication-prop-subset-Groupᵉ)
        ( is-closed-under-inverses-prop-subset-Groupᵉ))

  is-subgroup-subset-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-subgroup-subset-Groupᵉ = type-Propᵉ is-subgroup-prop-subset-Groupᵉ

  is-prop-is-subgroup-subset-Groupᵉ : is-propᵉ is-subgroup-subset-Groupᵉ
  is-prop-is-subgroup-subset-Groupᵉ =
    is-prop-type-Propᵉ is-subgroup-prop-subset-Groupᵉ
```

### The type of all subgroups of a group

```agda
Subgroupᵉ : (lᵉ : Level) {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
Subgroupᵉ lᵉ Gᵉ = type-subtypeᵉ (is-subgroup-prop-subset-Groupᵉ {l2ᵉ = lᵉ} Gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  subset-Subgroupᵉ : subset-Groupᵉ l2ᵉ Gᵉ
  subset-Subgroupᵉ =
    inclusion-subtypeᵉ (is-subgroup-prop-subset-Groupᵉ Gᵉ) Hᵉ

  type-Subgroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Subgroupᵉ = type-subtypeᵉ subset-Subgroupᵉ

  inclusion-Subgroupᵉ : type-Subgroupᵉ → type-Groupᵉ Gᵉ
  inclusion-Subgroupᵉ = inclusion-subtypeᵉ subset-Subgroupᵉ

  is-emb-inclusion-Subgroupᵉ : is-embᵉ inclusion-Subgroupᵉ
  is-emb-inclusion-Subgroupᵉ = is-emb-inclusion-subtypeᵉ subset-Subgroupᵉ

  emb-inclusion-Subgroupᵉ : type-Subgroupᵉ ↪ᵉ type-Groupᵉ Gᵉ
  emb-inclusion-Subgroupᵉ = emb-subtypeᵉ subset-Subgroupᵉ

  is-in-Subgroupᵉ : type-Groupᵉ Gᵉ → UUᵉ l2ᵉ
  is-in-Subgroupᵉ = is-in-subtypeᵉ subset-Subgroupᵉ

  is-closed-under-eq-Subgroupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    is-in-Subgroupᵉ xᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-Subgroupᵉ yᵉ
  is-closed-under-eq-Subgroupᵉ =
    is-closed-under-eq-subtypeᵉ subset-Subgroupᵉ

  is-closed-under-eq-Subgroup'ᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    is-in-Subgroupᵉ yᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-Subgroupᵉ xᵉ
  is-closed-under-eq-Subgroup'ᵉ =
    is-closed-under-eq-subtype'ᵉ subset-Subgroupᵉ

  is-in-subgroup-inclusion-Subgroupᵉ :
    (xᵉ : type-Subgroupᵉ) → is-in-Subgroupᵉ (inclusion-Subgroupᵉ xᵉ)
  is-in-subgroup-inclusion-Subgroupᵉ xᵉ = pr2ᵉ xᵉ

  is-prop-is-in-Subgroupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) → is-propᵉ (is-in-Subgroupᵉ xᵉ)
  is-prop-is-in-Subgroupᵉ = is-prop-is-in-subtypeᵉ subset-Subgroupᵉ

  is-subgroup-Subgroupᵉ : is-subgroup-subset-Groupᵉ Gᵉ subset-Subgroupᵉ
  is-subgroup-Subgroupᵉ = pr2ᵉ Hᵉ

  contains-unit-Subgroupᵉ :
    contains-unit-subset-Groupᵉ Gᵉ subset-Subgroupᵉ
  contains-unit-Subgroupᵉ = pr1ᵉ is-subgroup-Subgroupᵉ

  is-closed-under-multiplication-Subgroupᵉ :
    is-closed-under-multiplication-subset-Groupᵉ Gᵉ subset-Subgroupᵉ
  is-closed-under-multiplication-Subgroupᵉ = pr1ᵉ (pr2ᵉ is-subgroup-Subgroupᵉ)

  is-closed-under-inverses-Subgroupᵉ :
    is-closed-under-inverses-subset-Groupᵉ Gᵉ subset-Subgroupᵉ
  is-closed-under-inverses-Subgroupᵉ = pr2ᵉ (pr2ᵉ is-subgroup-Subgroupᵉ)

  is-closed-under-inverses-Subgroup'ᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) →
    is-in-Subgroupᵉ (inv-Groupᵉ Gᵉ xᵉ) → is-in-Subgroupᵉ xᵉ
  is-closed-under-inverses-Subgroup'ᵉ xᵉ pᵉ =
    is-closed-under-eq-Subgroupᵉ
      ( is-closed-under-inverses-Subgroupᵉ pᵉ)
      ( inv-inv-Groupᵉ Gᵉ xᵉ)

  is-in-subgroup-left-factor-Subgroupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    is-in-Subgroupᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) → is-in-Subgroupᵉ yᵉ →
    is-in-Subgroupᵉ xᵉ
  is-in-subgroup-left-factor-Subgroupᵉ xᵉ yᵉ pᵉ qᵉ =
    is-closed-under-eq-Subgroupᵉ
      ( is-closed-under-multiplication-Subgroupᵉ
        ( pᵉ)
        ( is-closed-under-inverses-Subgroupᵉ qᵉ))
      ( is-retraction-right-div-Groupᵉ Gᵉ yᵉ xᵉ)

  is-in-subgroup-right-factor-Subgroupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    is-in-Subgroupᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) → is-in-Subgroupᵉ xᵉ →
    is-in-Subgroupᵉ yᵉ
  is-in-subgroup-right-factor-Subgroupᵉ xᵉ yᵉ pᵉ qᵉ =
    is-closed-under-eq-Subgroupᵉ
      ( is-closed-under-multiplication-Subgroupᵉ
        ( is-closed-under-inverses-Subgroupᵉ qᵉ)
        ( pᵉ))
      ( is-retraction-left-div-Groupᵉ Gᵉ xᵉ yᵉ)

  is-closed-under-powers-int-Subgroupᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Groupᵉ Gᵉ) →
    is-in-Subgroupᵉ xᵉ → is-in-Subgroupᵉ (integer-power-Groupᵉ Gᵉ kᵉ xᵉ)
  is-closed-under-powers-int-Subgroupᵉ (inlᵉ zero-ℕᵉ) xᵉ Hᵉ =
    is-closed-under-eq-Subgroup'ᵉ
      ( is-closed-under-inverses-Subgroupᵉ Hᵉ)
      ( right-unit-law-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ))
  is-closed-under-powers-int-Subgroupᵉ (inlᵉ (succ-ℕᵉ kᵉ)) xᵉ Hᵉ =
    is-closed-under-multiplication-Subgroupᵉ
      ( is-closed-under-inverses-Subgroupᵉ Hᵉ)
      ( is-closed-under-powers-int-Subgroupᵉ (inlᵉ kᵉ) xᵉ Hᵉ)
  is-closed-under-powers-int-Subgroupᵉ (inrᵉ (inlᵉ _)) xᵉ Hᵉ =
    contains-unit-Subgroupᵉ
  is-closed-under-powers-int-Subgroupᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) xᵉ Hᵉ =
    is-closed-under-eq-Subgroup'ᵉ Hᵉ (right-unit-law-mul-Groupᵉ Gᵉ xᵉ)
  is-closed-under-powers-int-Subgroupᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ))) xᵉ Hᵉ =
    is-closed-under-multiplication-Subgroupᵉ
      ( Hᵉ)
      ( is-closed-under-powers-int-Subgroupᵉ (inrᵉ (inrᵉ kᵉ)) xᵉ Hᵉ)

  subsemigroup-Subgroupᵉ : Subsemigroupᵉ l2ᵉ (semigroup-Groupᵉ Gᵉ)
  pr1ᵉ subsemigroup-Subgroupᵉ = subset-Subgroupᵉ
  pr2ᵉ subsemigroup-Subgroupᵉ = is-closed-under-multiplication-Subgroupᵉ

is-emb-subset-Subgroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  is-embᵉ (subset-Subgroupᵉ {l2ᵉ = l2ᵉ} Gᵉ)
is-emb-subset-Subgroupᵉ Gᵉ =
  is-emb-inclusion-subtypeᵉ (is-subgroup-prop-subset-Groupᵉ Gᵉ)
```

### The underlying group of a subgroup

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  type-group-Subgroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-group-Subgroupᵉ = type-subtypeᵉ (subset-Subgroupᵉ Gᵉ Hᵉ)

  map-inclusion-Subgroupᵉ : type-group-Subgroupᵉ → type-Groupᵉ Gᵉ
  map-inclusion-Subgroupᵉ =
    inclusion-subtypeᵉ (subset-Subgroupᵉ Gᵉ Hᵉ)

  eq-subgroup-eq-groupᵉ : is-injectiveᵉ map-inclusion-Subgroupᵉ
  eq-subgroup-eq-groupᵉ {xᵉ} {yᵉ} =
    map-inv-is-equivᵉ (is-emb-inclusion-Subgroupᵉ Gᵉ Hᵉ xᵉ yᵉ)

  set-group-Subgroupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ set-group-Subgroupᵉ = type-group-Subgroupᵉ
  pr2ᵉ set-group-Subgroupᵉ =
    is-set-type-subtypeᵉ (subset-Subgroupᵉ Gᵉ Hᵉ) (is-set-type-Groupᵉ Gᵉ)

  mul-Subgroupᵉ : (xᵉ yᵉ : type-group-Subgroupᵉ) → type-group-Subgroupᵉ
  pr1ᵉ (mul-Subgroupᵉ xᵉ yᵉ) = mul-Groupᵉ Gᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ)
  pr2ᵉ (mul-Subgroupᵉ xᵉ yᵉ) =
    is-closed-under-multiplication-Subgroupᵉ Gᵉ Hᵉ (pr2ᵉ xᵉ) (pr2ᵉ yᵉ)

  associative-mul-Subgroupᵉ :
    (xᵉ yᵉ zᵉ : type-group-Subgroupᵉ) →
    Idᵉ
      ( mul-Subgroupᵉ (mul-Subgroupᵉ xᵉ yᵉ) zᵉ)
      ( mul-Subgroupᵉ xᵉ (mul-Subgroupᵉ yᵉ zᵉ))
  associative-mul-Subgroupᵉ xᵉ yᵉ zᵉ =
    eq-subgroup-eq-groupᵉ
      ( associative-mul-Groupᵉ Gᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ) (pr1ᵉ zᵉ))

  unit-Subgroupᵉ : type-group-Subgroupᵉ
  pr1ᵉ unit-Subgroupᵉ = unit-Groupᵉ Gᵉ
  pr2ᵉ unit-Subgroupᵉ = contains-unit-Subgroupᵉ Gᵉ Hᵉ

  left-unit-law-mul-Subgroupᵉ :
    (xᵉ : type-group-Subgroupᵉ) → Idᵉ (mul-Subgroupᵉ unit-Subgroupᵉ xᵉ) xᵉ
  left-unit-law-mul-Subgroupᵉ xᵉ =
    eq-subgroup-eq-groupᵉ (left-unit-law-mul-Groupᵉ Gᵉ (pr1ᵉ xᵉ))

  right-unit-law-mul-Subgroupᵉ :
    (xᵉ : type-group-Subgroupᵉ) → Idᵉ (mul-Subgroupᵉ xᵉ unit-Subgroupᵉ) xᵉ
  right-unit-law-mul-Subgroupᵉ xᵉ =
    eq-subgroup-eq-groupᵉ (right-unit-law-mul-Groupᵉ Gᵉ (pr1ᵉ xᵉ))

  inv-Subgroupᵉ : type-group-Subgroupᵉ → type-group-Subgroupᵉ
  pr1ᵉ (inv-Subgroupᵉ xᵉ) = inv-Groupᵉ Gᵉ (pr1ᵉ xᵉ)
  pr2ᵉ (inv-Subgroupᵉ xᵉ) =
    is-closed-under-inverses-Subgroupᵉ Gᵉ Hᵉ (pr2ᵉ xᵉ)

  left-inverse-law-mul-Subgroupᵉ :
    ( xᵉ : type-group-Subgroupᵉ) →
    Idᵉ
      ( mul-Subgroupᵉ (inv-Subgroupᵉ xᵉ) xᵉ)
      ( unit-Subgroupᵉ)
  left-inverse-law-mul-Subgroupᵉ xᵉ =
    eq-subgroup-eq-groupᵉ (left-inverse-law-mul-Groupᵉ Gᵉ (pr1ᵉ xᵉ))

  right-inverse-law-mul-Subgroupᵉ :
    (xᵉ : type-group-Subgroupᵉ) →
    Idᵉ
      ( mul-Subgroupᵉ xᵉ (inv-Subgroupᵉ xᵉ))
      ( unit-Subgroupᵉ)
  right-inverse-law-mul-Subgroupᵉ xᵉ =
    eq-subgroup-eq-groupᵉ (right-inverse-law-mul-Groupᵉ Gᵉ (pr1ᵉ xᵉ))

  semigroup-Subgroupᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ semigroup-Subgroupᵉ = set-group-Subgroupᵉ
  pr1ᵉ (pr2ᵉ semigroup-Subgroupᵉ) = mul-Subgroupᵉ
  pr2ᵉ (pr2ᵉ semigroup-Subgroupᵉ) = associative-mul-Subgroupᵉ

  group-Subgroupᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ group-Subgroupᵉ = semigroup-Subgroupᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ group-Subgroupᵉ)) = unit-Subgroupᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ group-Subgroupᵉ))) = left-unit-law-mul-Subgroupᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ group-Subgroupᵉ))) = right-unit-law-mul-Subgroupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ group-Subgroupᵉ)) = inv-Subgroupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ group-Subgroupᵉ))) = left-inverse-law-mul-Subgroupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ group-Subgroupᵉ))) =
    right-inverse-law-mul-Subgroupᵉ
```

### The inclusion of the underlying group of a subgroup into the ambient group

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  preserves-mul-inclusion-Subgroupᵉ :
    preserves-mul-Groupᵉ
      ( group-Subgroupᵉ Gᵉ Hᵉ)
      ( Gᵉ)
      ( map-inclusion-Subgroupᵉ Gᵉ Hᵉ)
  preserves-mul-inclusion-Subgroupᵉ = reflᵉ

  preserves-unit-inclusion-Subgroupᵉ :
    preserves-unit-Groupᵉ
      ( group-Subgroupᵉ Gᵉ Hᵉ)
      ( Gᵉ)
      ( map-inclusion-Subgroupᵉ Gᵉ Hᵉ)
  preserves-unit-inclusion-Subgroupᵉ = reflᵉ

  preserves-inverses-inclusion-Subgroupᵉ :
    preserves-inverses-Groupᵉ
      ( group-Subgroupᵉ Gᵉ Hᵉ)
      ( Gᵉ)
      ( map-inclusion-Subgroupᵉ Gᵉ Hᵉ)
  preserves-inverses-inclusion-Subgroupᵉ = reflᵉ

  hom-inclusion-Subgroupᵉ :
    hom-Groupᵉ (group-Subgroupᵉ Gᵉ Hᵉ) Gᵉ
  pr1ᵉ hom-inclusion-Subgroupᵉ = inclusion-Subgroupᵉ Gᵉ Hᵉ
  pr2ᵉ hom-inclusion-Subgroupᵉ {xᵉ} {yᵉ} = preserves-mul-inclusion-Subgroupᵉ {xᵉ} {yᵉ}
```

## Properties

### Extensionality of the type of all subgroups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  has-same-elements-prop-Subgroupᵉ :
    {l3ᵉ : Level} → Subgroupᵉ l3ᵉ Gᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-prop-Subgroupᵉ Kᵉ =
    has-same-elements-subtype-Propᵉ
      ( subset-Subgroupᵉ Gᵉ Hᵉ)
      ( subset-Subgroupᵉ Gᵉ Kᵉ)

  has-same-elements-Subgroupᵉ :
    {l3ᵉ : Level} → Subgroupᵉ l3ᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-Subgroupᵉ Kᵉ =
    has-same-elements-subtypeᵉ
      ( subset-Subgroupᵉ Gᵉ Hᵉ)
      ( subset-Subgroupᵉ Gᵉ Kᵉ)

  extensionality-Subgroupᵉ :
    (Kᵉ : Subgroupᵉ l2ᵉ Gᵉ) → (Hᵉ ＝ᵉ Kᵉ) ≃ᵉ has-same-elements-Subgroupᵉ Kᵉ
  extensionality-Subgroupᵉ =
    extensionality-type-subtypeᵉ
      ( is-subgroup-prop-subset-Groupᵉ Gᵉ)
      ( is-subgroup-Subgroupᵉ Gᵉ Hᵉ)
      ( λ xᵉ → pairᵉ idᵉ idᵉ)
      ( extensionality-subtypeᵉ (subset-Subgroupᵉ Gᵉ Hᵉ))

  refl-has-same-elements-Subgroupᵉ : has-same-elements-Subgroupᵉ Hᵉ
  refl-has-same-elements-Subgroupᵉ =
    refl-has-same-elements-subtypeᵉ (subset-Subgroupᵉ Gᵉ Hᵉ)

  has-same-elements-eq-Subgroupᵉ :
    (Kᵉ : Subgroupᵉ l2ᵉ Gᵉ) → (Hᵉ ＝ᵉ Kᵉ) → has-same-elements-Subgroupᵉ Kᵉ
  has-same-elements-eq-Subgroupᵉ Kᵉ =
    map-equivᵉ (extensionality-Subgroupᵉ Kᵉ)

  eq-has-same-elements-Subgroupᵉ :
    (Kᵉ : Subgroupᵉ l2ᵉ Gᵉ) → has-same-elements-Subgroupᵉ Kᵉ → (Hᵉ ＝ᵉ Kᵉ)
  eq-has-same-elements-Subgroupᵉ Kᵉ =
    map-inv-equivᵉ (extensionality-Subgroupᵉ Kᵉ)
```

### The containment relation of subgroups

```agda
leq-prop-Subgroupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  Subgroupᵉ l2ᵉ Gᵉ → Subgroupᵉ l3ᵉ Gᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
leq-prop-Subgroupᵉ Gᵉ Hᵉ Kᵉ =
  leq-prop-subtypeᵉ
    ( subset-Subgroupᵉ Gᵉ Hᵉ)
    ( subset-Subgroupᵉ Gᵉ Kᵉ)

leq-Subgroupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  Subgroupᵉ l2ᵉ Gᵉ → Subgroupᵉ l3ᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
leq-Subgroupᵉ Gᵉ Hᵉ Kᵉ = subset-Subgroupᵉ Gᵉ Hᵉ ⊆ᵉ subset-Subgroupᵉ Gᵉ Kᵉ

is-prop-leq-Subgroupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ) (Kᵉ : Subgroupᵉ l3ᵉ Gᵉ) →
  is-propᵉ (leq-Subgroupᵉ Gᵉ Hᵉ Kᵉ)
is-prop-leq-Subgroupᵉ Gᵉ Hᵉ Kᵉ =
  is-prop-leq-subtypeᵉ (subset-Subgroupᵉ Gᵉ Hᵉ) (subset-Subgroupᵉ Gᵉ Kᵉ)

refl-leq-Subgroupᵉ :
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  is-reflexive-Large-Relationᵉ (λ lᵉ → Subgroupᵉ lᵉ Gᵉ) (leq-Subgroupᵉ Gᵉ)
refl-leq-Subgroupᵉ Gᵉ Hᵉ = refl-leq-subtypeᵉ (subset-Subgroupᵉ Gᵉ Hᵉ)

transitive-leq-Subgroupᵉ :
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  is-transitive-Large-Relationᵉ (λ lᵉ → Subgroupᵉ lᵉ Gᵉ) (leq-Subgroupᵉ Gᵉ)
transitive-leq-Subgroupᵉ Gᵉ Hᵉ Kᵉ Lᵉ =
  transitive-leq-subtypeᵉ
    ( subset-Subgroupᵉ Gᵉ Hᵉ)
    ( subset-Subgroupᵉ Gᵉ Kᵉ)
    ( subset-Subgroupᵉ Gᵉ Lᵉ)

antisymmetric-leq-Subgroupᵉ :
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  is-antisymmetric-Large-Relationᵉ (λ lᵉ → Subgroupᵉ lᵉ Gᵉ) (leq-Subgroupᵉ Gᵉ)
antisymmetric-leq-Subgroupᵉ Gᵉ Hᵉ Kᵉ αᵉ βᵉ =
  eq-has-same-elements-Subgroupᵉ Gᵉ Hᵉ Kᵉ (λ xᵉ → (αᵉ xᵉ ,ᵉ βᵉ xᵉ))

Subgroup-Large-Preorderᵉ :
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  Large-Preorderᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
type-Large-Preorderᵉ (Subgroup-Large-Preorderᵉ Gᵉ) l2ᵉ = Subgroupᵉ l2ᵉ Gᵉ
leq-prop-Large-Preorderᵉ (Subgroup-Large-Preorderᵉ Gᵉ) Hᵉ Kᵉ =
  leq-prop-Subgroupᵉ Gᵉ Hᵉ Kᵉ
refl-leq-Large-Preorderᵉ (Subgroup-Large-Preorderᵉ Gᵉ) =
  refl-leq-Subgroupᵉ Gᵉ
transitive-leq-Large-Preorderᵉ (Subgroup-Large-Preorderᵉ Gᵉ) =
  transitive-leq-Subgroupᵉ Gᵉ

Subgroup-Preorderᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Groupᵉ l1ᵉ) →
  Preorderᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
Subgroup-Preorderᵉ l2ᵉ Gᵉ =
  preorder-Large-Preorderᵉ (Subgroup-Large-Preorderᵉ Gᵉ) l2ᵉ

Subgroup-Large-Posetᵉ :
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  Large-Posetᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
large-preorder-Large-Posetᵉ (Subgroup-Large-Posetᵉ Gᵉ) =
  Subgroup-Large-Preorderᵉ Gᵉ
antisymmetric-leq-Large-Posetᵉ (Subgroup-Large-Posetᵉ Gᵉ) =
  antisymmetric-leq-Subgroupᵉ Gᵉ

Subgroup-Posetᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Groupᵉ l1ᵉ) →
  Posetᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
Subgroup-Posetᵉ l2ᵉ Gᵉ = poset-Large-Posetᵉ (Subgroup-Large-Posetᵉ Gᵉ) l2ᵉ

preserves-order-subset-Subgroupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ) (Kᵉ : Subgroupᵉ l3ᵉ Gᵉ) →
  leq-Subgroupᵉ Gᵉ Hᵉ Kᵉ → (subset-Subgroupᵉ Gᵉ Hᵉ ⊆ᵉ subset-Subgroupᵉ Gᵉ Kᵉ)
preserves-order-subset-Subgroupᵉ Gᵉ Hᵉ Kᵉ = idᵉ

subset-subgroup-hom-large-poset-Groupᵉ :
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  hom-Large-Posetᵉ
    ( λ lᵉ → lᵉ)
    ( Subgroup-Large-Posetᵉ Gᵉ)
    ( powerset-Large-Posetᵉ (type-Groupᵉ Gᵉ))
map-hom-Large-Preorderᵉ
  ( subset-subgroup-hom-large-poset-Groupᵉ Gᵉ) =
  subset-Subgroupᵉ Gᵉ
preserves-order-hom-Large-Preorderᵉ
  ( subset-subgroup-hom-large-poset-Groupᵉ Gᵉ) =
  preserves-order-subset-Subgroupᵉ Gᵉ
```

### The type of subgroups of a group is a set

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-set-Subgroupᵉ : {l2ᵉ : Level} → is-setᵉ (Subgroupᵉ l2ᵉ Gᵉ)
  is-set-Subgroupᵉ = is-set-type-Posetᵉ (Subgroup-Posetᵉ _ Gᵉ)
```

### Subgroups have the same elements if and only if they are similar in the poset of subgroups

**Note:**ᵉ Weᵉ don'tᵉ abbreviateᵉ theᵉ wordᵉ `similar`ᵉ in theᵉ nameᵉ ofᵉ theᵉ similarityᵉ
relationᵉ onᵉ subgroups,ᵉ becauseᵉ belowᵉ weᵉ willᵉ defineᵉ forᵉ eachᵉ subgroupᵉ `H`ᵉ ofᵉ `G`ᵉ
twoᵉ equivalenceᵉ relationsᵉ onᵉ `G`,ᵉ whichᵉ weᵉ willᵉ callᵉ `right-sim-Subgroup`ᵉ andᵉ
`left-sim-Subgroup`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ) (Kᵉ : Subgroupᵉ l3ᵉ Gᵉ)
  where

  similar-Subgroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  similar-Subgroupᵉ = sim-Large-Posetᵉ (Subgroup-Large-Posetᵉ Gᵉ) Hᵉ Kᵉ

  has-same-elements-similar-Subgroupᵉ :
    similar-Subgroupᵉ → has-same-elements-Subgroupᵉ Gᵉ Hᵉ Kᵉ
  pr1ᵉ (has-same-elements-similar-Subgroupᵉ (sᵉ ,ᵉ tᵉ) xᵉ) = sᵉ xᵉ
  pr2ᵉ (has-same-elements-similar-Subgroupᵉ (sᵉ ,ᵉ tᵉ) xᵉ) = tᵉ xᵉ

  leq-has-same-elements-Subgroupᵉ :
    has-same-elements-Subgroupᵉ Gᵉ Hᵉ Kᵉ → leq-Subgroupᵉ Gᵉ Hᵉ Kᵉ
  leq-has-same-elements-Subgroupᵉ sᵉ xᵉ = forward-implicationᵉ (sᵉ xᵉ)

  leq-has-same-elements-Subgroup'ᵉ :
    has-same-elements-Subgroupᵉ Gᵉ Hᵉ Kᵉ → leq-Subgroupᵉ Gᵉ Kᵉ Hᵉ
  leq-has-same-elements-Subgroup'ᵉ sᵉ xᵉ = backward-implicationᵉ (sᵉ xᵉ)

  similar-has-same-elements-Subgroupᵉ :
    has-same-elements-Subgroupᵉ Gᵉ Hᵉ Kᵉ → similar-Subgroupᵉ
  pr1ᵉ (similar-has-same-elements-Subgroupᵉ sᵉ) = leq-has-same-elements-Subgroupᵉ sᵉ
  pr2ᵉ (similar-has-same-elements-Subgroupᵉ sᵉ) = leq-has-same-elements-Subgroup'ᵉ sᵉ
```

### Every subgroup induces two equivalence relations

#### The equivalence relation where `x ~ y` if and only if `x⁻¹ y ∈ H`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  right-sim-Subgroupᵉ : (xᵉ yᵉ : type-Groupᵉ Gᵉ) → UUᵉ l2ᵉ
  right-sim-Subgroupᵉ xᵉ yᵉ = is-in-Subgroupᵉ Gᵉ Hᵉ (left-div-Groupᵉ Gᵉ xᵉ yᵉ)

  is-prop-right-sim-Subgroupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → is-propᵉ (right-sim-Subgroupᵉ xᵉ yᵉ)
  is-prop-right-sim-Subgroupᵉ xᵉ yᵉ =
    is-prop-is-in-Subgroupᵉ Gᵉ Hᵉ (left-div-Groupᵉ Gᵉ xᵉ yᵉ)

  prop-right-equivalence-relation-Subgroupᵉ : (xᵉ yᵉ : type-Groupᵉ Gᵉ) → Propᵉ l2ᵉ
  pr1ᵉ (prop-right-equivalence-relation-Subgroupᵉ xᵉ yᵉ) = right-sim-Subgroupᵉ xᵉ yᵉ
  pr2ᵉ (prop-right-equivalence-relation-Subgroupᵉ xᵉ yᵉ) =
    is-prop-right-sim-Subgroupᵉ xᵉ yᵉ

  refl-right-sim-Subgroupᵉ : is-reflexiveᵉ right-sim-Subgroupᵉ
  refl-right-sim-Subgroupᵉ xᵉ =
    trᵉ
      ( is-in-Subgroupᵉ Gᵉ Hᵉ)
      ( invᵉ (left-inverse-law-mul-Groupᵉ Gᵉ xᵉ))
      ( contains-unit-Subgroupᵉ Gᵉ Hᵉ)

  symmetric-right-sim-Subgroupᵉ : is-symmetricᵉ right-sim-Subgroupᵉ
  symmetric-right-sim-Subgroupᵉ xᵉ yᵉ pᵉ =
    trᵉ
      ( is-in-Subgroupᵉ Gᵉ Hᵉ)
      ( inv-left-div-Groupᵉ Gᵉ xᵉ yᵉ)
      ( is-closed-under-inverses-Subgroupᵉ Gᵉ Hᵉ pᵉ)

  transitive-right-sim-Subgroupᵉ : is-transitiveᵉ right-sim-Subgroupᵉ
  transitive-right-sim-Subgroupᵉ xᵉ yᵉ zᵉ pᵉ qᵉ =
    trᵉ
      ( is-in-Subgroupᵉ Gᵉ Hᵉ)
      ( mul-left-div-Groupᵉ Gᵉ xᵉ yᵉ zᵉ)
      ( is-closed-under-multiplication-Subgroupᵉ Gᵉ Hᵉ
        ( qᵉ)
        ( pᵉ))

  right-equivalence-relation-Subgroupᵉ : equivalence-relationᵉ l2ᵉ (type-Groupᵉ Gᵉ)
  pr1ᵉ right-equivalence-relation-Subgroupᵉ =
    prop-right-equivalence-relation-Subgroupᵉ
  pr1ᵉ (pr2ᵉ right-equivalence-relation-Subgroupᵉ) = refl-right-sim-Subgroupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ right-equivalence-relation-Subgroupᵉ)) =
    symmetric-right-sim-Subgroupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ right-equivalence-relation-Subgroupᵉ)) =
    transitive-right-sim-Subgroupᵉ
```

#### The equivalence relation where `x ~ y` if and only if `xy⁻¹ ∈ H`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  left-sim-Subgroupᵉ : (xᵉ yᵉ : type-Groupᵉ Gᵉ) → UUᵉ l2ᵉ
  left-sim-Subgroupᵉ xᵉ yᵉ = is-in-Subgroupᵉ Gᵉ Hᵉ (right-div-Groupᵉ Gᵉ xᵉ yᵉ)

  is-prop-left-sim-Subgroupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → is-propᵉ (left-sim-Subgroupᵉ xᵉ yᵉ)
  is-prop-left-sim-Subgroupᵉ xᵉ yᵉ =
    is-prop-is-in-Subgroupᵉ Gᵉ Hᵉ (right-div-Groupᵉ Gᵉ xᵉ yᵉ)

  prop-left-equivalence-relation-Subgroupᵉ : (xᵉ yᵉ : type-Groupᵉ Gᵉ) → Propᵉ l2ᵉ
  pr1ᵉ (prop-left-equivalence-relation-Subgroupᵉ xᵉ yᵉ) = left-sim-Subgroupᵉ xᵉ yᵉ
  pr2ᵉ (prop-left-equivalence-relation-Subgroupᵉ xᵉ yᵉ) =
    is-prop-left-sim-Subgroupᵉ xᵉ yᵉ

  refl-left-sim-Subgroupᵉ : is-reflexiveᵉ left-sim-Subgroupᵉ
  refl-left-sim-Subgroupᵉ xᵉ =
    trᵉ
      ( is-in-Subgroupᵉ Gᵉ Hᵉ)
      ( invᵉ (right-inverse-law-mul-Groupᵉ Gᵉ xᵉ))
      ( contains-unit-Subgroupᵉ Gᵉ Hᵉ)

  symmetric-left-sim-Subgroupᵉ : is-symmetricᵉ left-sim-Subgroupᵉ
  symmetric-left-sim-Subgroupᵉ xᵉ yᵉ pᵉ =
    trᵉ
      ( is-in-Subgroupᵉ Gᵉ Hᵉ)
      ( inv-right-div-Groupᵉ Gᵉ xᵉ yᵉ)
      ( is-closed-under-inverses-Subgroupᵉ Gᵉ Hᵉ pᵉ)

  transitive-left-sim-Subgroupᵉ : is-transitiveᵉ left-sim-Subgroupᵉ
  transitive-left-sim-Subgroupᵉ xᵉ yᵉ zᵉ pᵉ qᵉ =
    trᵉ
      ( is-in-Subgroupᵉ Gᵉ Hᵉ)
      ( mul-right-div-Groupᵉ Gᵉ xᵉ yᵉ zᵉ)
      ( is-closed-under-multiplication-Subgroupᵉ Gᵉ Hᵉ qᵉ pᵉ)

  left-equivalence-relation-Subgroupᵉ : equivalence-relationᵉ l2ᵉ (type-Groupᵉ Gᵉ)
  pr1ᵉ left-equivalence-relation-Subgroupᵉ =
    prop-left-equivalence-relation-Subgroupᵉ
  pr1ᵉ (pr2ᵉ left-equivalence-relation-Subgroupᵉ) = refl-left-sim-Subgroupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ left-equivalence-relation-Subgroupᵉ)) =
    symmetric-left-sim-Subgroupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ left-equivalence-relation-Subgroupᵉ)) =
    transitive-left-sim-Subgroupᵉ
```

### Any proposition `P` induces a subgroup of any group `G`

Theᵉ subsetᵉ consistingᵉ ofᵉ elementsᵉ `xᵉ : G`ᵉ suchᵉ thatᵉ `(1ᵉ ＝ᵉ xᵉ) ∨ᵉ P`ᵉ holdsᵉ isᵉ
alwaysᵉ aᵉ subgroupᵉ ofᵉ `G`.ᵉ Thisᵉ subgroupᵉ consistsᵉ onlyᵉ ofᵉ theᵉ unitᵉ elementᵉ ifᵉ `P`ᵉ
isᵉ false,ᵉ andᵉ itᵉ isᵉ theᵉ [fullᵉ subgroup](group-theory.full-subgroups.md)`if`P`ᵉ isᵉ
true.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Pᵉ : Propᵉ l2ᵉ)
  where

  subset-subgroup-Propᵉ : subset-Groupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
  subset-subgroup-Propᵉ xᵉ =
    disjunction-Propᵉ (Id-Propᵉ (set-Groupᵉ Gᵉ) (unit-Groupᵉ Gᵉ) xᵉ) Pᵉ

  contains-unit-subgroup-Propᵉ :
    contains-unit-subset-Groupᵉ Gᵉ subset-subgroup-Propᵉ
  contains-unit-subgroup-Propᵉ = inl-disjunctionᵉ reflᵉ

  is-closed-under-multiplication-subgroup-Prop'ᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    ((unit-Groupᵉ Gᵉ ＝ᵉ xᵉ) +ᵉ type-Propᵉ Pᵉ) →
    ((unit-Groupᵉ Gᵉ ＝ᵉ yᵉ) +ᵉ type-Propᵉ Pᵉ) →
    ((unit-Groupᵉ Gᵉ ＝ᵉ mul-Groupᵉ Gᵉ xᵉ yᵉ) +ᵉ type-Propᵉ Pᵉ)
  is-closed-under-multiplication-subgroup-Prop'ᵉ ._ ._ (inlᵉ reflᵉ) (inlᵉ reflᵉ) =
    inlᵉ (invᵉ (left-unit-law-mul-Groupᵉ Gᵉ _))
  is-closed-under-multiplication-subgroup-Prop'ᵉ ._ yᵉ (inlᵉ reflᵉ) (inrᵉ qᵉ) =
    inrᵉ qᵉ
  is-closed-under-multiplication-subgroup-Prop'ᵉ xᵉ yᵉ (inrᵉ pᵉ) (inlᵉ βᵉ) =
    inrᵉ pᵉ
  is-closed-under-multiplication-subgroup-Prop'ᵉ xᵉ yᵉ (inrᵉ pᵉ) (inrᵉ qᵉ) =
    inrᵉ pᵉ

  is-closed-under-multiplication-subgroup-Propᵉ :
    is-closed-under-multiplication-subset-Groupᵉ Gᵉ subset-subgroup-Propᵉ
  is-closed-under-multiplication-subgroup-Propᵉ Hᵉ Kᵉ =
    apply-twice-universal-property-trunc-Propᵉ Hᵉ Kᵉ
      ( disjunction-Propᵉ (Id-Propᵉ (set-Groupᵉ Gᵉ) _ _) Pᵉ)
      ( λ H'ᵉ K'ᵉ →
        unit-trunc-Propᵉ
          ( is-closed-under-multiplication-subgroup-Prop'ᵉ _ _ H'ᵉ K'ᵉ))

  is-closed-under-inverses-subgroup-Prop'ᵉ :
    {xᵉ : type-Groupᵉ Gᵉ} → ((unit-Groupᵉ Gᵉ ＝ᵉ xᵉ) +ᵉ type-Propᵉ Pᵉ) →
    ((unit-Groupᵉ Gᵉ ＝ᵉ inv-Groupᵉ Gᵉ xᵉ) +ᵉ type-Propᵉ Pᵉ)
  is-closed-under-inverses-subgroup-Prop'ᵉ (inlᵉ reflᵉ) =
    inlᵉ (invᵉ (inv-unit-Groupᵉ Gᵉ))
  is-closed-under-inverses-subgroup-Prop'ᵉ (inrᵉ pᵉ) =
    inrᵉ pᵉ

  is-closed-under-inverses-subgroup-Propᵉ :
    is-closed-under-inverses-subset-Groupᵉ Gᵉ subset-subgroup-Propᵉ
  is-closed-under-inverses-subgroup-Propᵉ {xᵉ} Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( disjunction-Propᵉ (Id-Propᵉ (set-Groupᵉ Gᵉ) _ _) Pᵉ)
      ( unit-trunc-Propᵉ ∘ᵉ is-closed-under-inverses-subgroup-Prop'ᵉ)

  subgroup-Propᵉ : Subgroupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
  pr1ᵉ subgroup-Propᵉ = subset-subgroup-Propᵉ
  pr1ᵉ (pr2ᵉ subgroup-Propᵉ) = contains-unit-subgroup-Propᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ subgroup-Propᵉ)) = is-closed-under-multiplication-subgroup-Propᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ subgroup-Propᵉ)) = is-closed-under-inverses-subgroup-Propᵉ

  group-subgroup-Propᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  group-subgroup-Propᵉ = group-Subgroupᵉ Gᵉ subgroup-Propᵉ
```

## See also

-ᵉ [Monomorphismsᵉ in theᵉ categoryᵉ ofᵉ groups](group-theory.monomorphisms-groups.mdᵉ)
-ᵉ [Normalᵉ subgroups](group-theory.normal-subgroups.mdᵉ)
-ᵉ [Submonoids](group-theory.submonoids.mdᵉ)

## External links

-ᵉ [Subgroups](https://1lab.dev/Algebra.Group.Subgroup.htmlᵉ) atᵉ 1labᵉ
-ᵉ [subgroup](https://ncatlab.org/nlab/show/subgroupᵉ) atᵉ $n$Labᵉ
-ᵉ [Subgroup](https://en.wikipedia.org/wiki/Subgroupᵉ) atᵉ Wikipediaᵉ
-ᵉ [Subgroup](https://mathworld.wolfram.com/Subgroup.htmlᵉ) atᵉ Wolframᵉ MathWorldᵉ
-ᵉ [subgroup](https://www.wikidata.org/wiki/Q466109ᵉ) atᵉ Wikidataᵉ