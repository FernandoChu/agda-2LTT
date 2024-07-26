# Quotients of abelian groups

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module group-theory.quotients-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-functoriality-set-quotientsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.effective-maps-equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-set-quotientsᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.set-quotientsᵉ
open import foundation.setsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universal-property-set-quotientsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-abelian-groupsᵉ
open import group-theory.nullifying-group-homomorphismsᵉ
open import group-theory.quotient-groupsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.subgroups-abelian-groupsᵉ
```

</details>

## Idea

Givenᵉ aᵉ subgroupᵉ `B`ᵉ ofᵉ anᵉ abelianᵉ groupᵉ `A`,ᵉ theᵉ quotientᵉ groupᵉ isᵉ anᵉ abelianᵉ
groupᵉ `A/B`ᵉ equippedᵉ with aᵉ groupᵉ homomorphismᵉ `qᵉ : Aᵉ → A/B`ᵉ suchᵉ thatᵉ
`Hᵉ ⊆ᵉ kerᵉ q`,ᵉ andᵉ suchᵉ thatᵉ `q`ᵉ satisfiesᵉ theᵉ universalᵉ abelianᵉ groupᵉ with theᵉ
propertyᵉ thatᵉ anyᵉ groupᵉ homomorphismᵉ `fᵉ : Aᵉ → C`ᵉ suchᵉ thatᵉ `Bᵉ ⊆ᵉ kerᵉ f`ᵉ extendsᵉ
uniquelyᵉ alongᵉ `q`ᵉ to aᵉ groupᵉ homomorphismᵉ `A/Bᵉ → C`.ᵉ

## Definitions

### Group homomorphisms that nullify a subgroup, i.e., that contain a subgroup in their kernel

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  nullifies-subgroup-prop-hom-Abᵉ :
    hom-Abᵉ Aᵉ Bᵉ → Subgroup-Abᵉ l3ᵉ Aᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  nullifies-subgroup-prop-hom-Abᵉ fᵉ Hᵉ =
    nullifies-normal-subgroup-prop-hom-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( group-Abᵉ Bᵉ)
      ( fᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  nullifies-normal-subgroup-hom-Abᵉ :
    hom-Abᵉ Aᵉ Bᵉ → Subgroup-Abᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  nullifies-normal-subgroup-hom-Abᵉ fᵉ Hᵉ =
    nullifies-normal-subgroup-hom-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( group-Abᵉ Bᵉ)
      ( fᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  nullifying-hom-Abᵉ : Subgroup-Abᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  nullifying-hom-Abᵉ Hᵉ =
    nullifying-hom-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( group-Abᵉ Bᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  hom-nullifying-hom-Abᵉ :
    (Hᵉ : Subgroup-Abᵉ l3ᵉ Aᵉ) → nullifying-hom-Abᵉ Hᵉ → hom-Abᵉ Aᵉ Bᵉ
  hom-nullifying-hom-Abᵉ Hᵉ =
    hom-nullifying-hom-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( group-Abᵉ Bᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  nullifies-subgroup-nullifying-hom-Abᵉ :
    (Hᵉ : Subgroup-Abᵉ l3ᵉ Aᵉ) (fᵉ : nullifying-hom-Abᵉ Hᵉ) →
    nullifies-normal-subgroup-hom-Abᵉ
      ( hom-nullifying-hom-Abᵉ Hᵉ fᵉ) Hᵉ
  nullifies-subgroup-nullifying-hom-Abᵉ Hᵉ =
    nullifies-normal-subgroup-nullifying-hom-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( group-Abᵉ Bᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)
```

### The universal property of quotient groups

```agda
precomp-nullifying-hom-Abᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Hᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ)
  (Bᵉ : Abᵉ l3ᵉ) (fᵉ : nullifying-hom-Abᵉ Aᵉ Bᵉ Hᵉ)
  (Cᵉ : Abᵉ l4ᵉ) → hom-Abᵉ Bᵉ Cᵉ → nullifying-hom-Abᵉ Aᵉ Cᵉ Hᵉ
precomp-nullifying-hom-Abᵉ Aᵉ Hᵉ Bᵉ fᵉ Cᵉ =
  precomp-nullifying-hom-Groupᵉ
    ( group-Abᵉ Aᵉ)
    ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)
    ( group-Abᵉ Bᵉ)
    ( fᵉ)
    ( group-Abᵉ Cᵉ)

universal-property-quotient-Abᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (lᵉ : Level) (Aᵉ : Abᵉ l1ᵉ)
  (Hᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ) (Bᵉ : Abᵉ l3ᵉ)
  (qᵉ : nullifying-hom-Abᵉ Aᵉ Bᵉ Hᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ lsuc lᵉ)
universal-property-quotient-Abᵉ lᵉ Aᵉ Hᵉ Bᵉ qᵉ =
  (Cᵉ : Abᵉ lᵉ) → is-equivᵉ (precomp-nullifying-hom-Abᵉ Aᵉ Hᵉ Bᵉ qᵉ Cᵉ)
```

### The quotient group

#### The quotient map and the underlying set of the quotient group

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Hᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ)
  where

  set-quotient-Abᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-quotient-Abᵉ =
    quotient-Setᵉ (equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)

  type-quotient-Abᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-quotient-Abᵉ =
    set-quotientᵉ (equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)

  is-set-type-quotient-Abᵉ : is-setᵉ type-quotient-Abᵉ
  is-set-type-quotient-Abᵉ =
    is-set-set-quotientᵉ (equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)

  map-quotient-hom-Abᵉ : type-Abᵉ Aᵉ → type-quotient-Abᵉ
  map-quotient-hom-Abᵉ =
    quotient-mapᵉ (equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)

  is-surjective-map-quotient-hom-Abᵉ :
    is-surjectiveᵉ map-quotient-hom-Abᵉ
  is-surjective-map-quotient-hom-Abᵉ =
    is-surjective-quotient-mapᵉ (equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)

  is-effective-map-quotient-hom-Abᵉ :
    is-effectiveᵉ
      ( equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)
      ( map-quotient-hom-Abᵉ)
  is-effective-map-quotient-hom-Abᵉ =
    is-effective-quotient-mapᵉ (equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)

  apply-effectiveness-map-quotient-hom-Abᵉ :
    {xᵉ yᵉ : type-Abᵉ Aᵉ} →
    map-quotient-hom-Abᵉ xᵉ ＝ᵉ map-quotient-hom-Abᵉ yᵉ →
    sim-congruence-Subgroup-Abᵉ Aᵉ Hᵉ xᵉ yᵉ
  apply-effectiveness-map-quotient-hom-Abᵉ =
    apply-effectiveness-quotient-mapᵉ
      ( equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)

  apply-effectiveness-map-quotient-hom-Ab'ᵉ :
    {xᵉ yᵉ : type-Abᵉ Aᵉ} →
    sim-congruence-Subgroup-Abᵉ Aᵉ Hᵉ xᵉ yᵉ →
    map-quotient-hom-Abᵉ xᵉ ＝ᵉ map-quotient-hom-Abᵉ yᵉ
  apply-effectiveness-map-quotient-hom-Ab'ᵉ =
    apply-effectiveness-quotient-map'ᵉ
      ( equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)

  reflecting-map-quotient-hom-Abᵉ :
    reflecting-map-equivalence-relationᵉ
      ( equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)
      ( type-quotient-Abᵉ)
  reflecting-map-quotient-hom-Abᵉ =
    reflecting-map-quotient-mapᵉ
      ( equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)

  is-set-quotient-set-quotient-Abᵉ :
    is-set-quotientᵉ
      ( equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)
      ( set-quotient-Abᵉ)
      ( reflecting-map-quotient-hom-Abᵉ)
  is-set-quotient-set-quotient-Abᵉ =
    is-set-quotient-set-quotientᵉ
      ( equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)
```

#### The group structure on the quotient group

```agda
  zero-quotient-Abᵉ : type-quotient-Abᵉ
  zero-quotient-Abᵉ = map-quotient-hom-Abᵉ (zero-Abᵉ Aᵉ)

  binary-hom-add-quotient-Abᵉ :
    binary-hom-equivalence-relationᵉ
      ( equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)
      ( equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)
      ( equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)
  binary-hom-add-quotient-Abᵉ =
    binary-hom-mul-quotient-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  add-quotient-Abᵉ :
    (xᵉ yᵉ : type-quotient-Abᵉ) → type-quotient-Abᵉ
  add-quotient-Abᵉ =
    mul-quotient-Groupᵉ (group-Abᵉ Aᵉ) (normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  add-quotient-Ab'ᵉ :
    (xᵉ yᵉ : type-quotient-Abᵉ) → type-quotient-Abᵉ
  add-quotient-Ab'ᵉ =
    mul-quotient-Group'ᵉ (group-Abᵉ Aᵉ) (normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  compute-add-quotient-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    add-quotient-Abᵉ
      ( map-quotient-hom-Abᵉ xᵉ)
      ( map-quotient-hom-Abᵉ yᵉ) ＝ᵉ
    map-quotient-hom-Abᵉ (add-Abᵉ Aᵉ xᵉ yᵉ)
  compute-add-quotient-Abᵉ =
    compute-mul-quotient-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  hom-neg-quotient-Abᵉ :
    hom-equivalence-relationᵉ
      ( equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)
      ( equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)
  hom-neg-quotient-Abᵉ =
    hom-inv-quotient-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  neg-quotient-Abᵉ : type-quotient-Abᵉ → type-quotient-Abᵉ
  neg-quotient-Abᵉ =
    inv-quotient-Groupᵉ (group-Abᵉ Aᵉ) (normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  compute-neg-quotient-Abᵉ :
    (xᵉ : type-Abᵉ Aᵉ) →
    neg-quotient-Abᵉ (map-quotient-hom-Abᵉ xᵉ) ＝ᵉ
    map-quotient-hom-Abᵉ (neg-Abᵉ Aᵉ xᵉ)
  compute-neg-quotient-Abᵉ =
    compute-inv-quotient-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  left-unit-law-add-quotient-Abᵉ :
    (xᵉ : type-quotient-Abᵉ) → add-quotient-Abᵉ zero-quotient-Abᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-quotient-Abᵉ =
    left-unit-law-mul-quotient-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  right-unit-law-add-quotient-Abᵉ :
    (xᵉ : type-quotient-Abᵉ) → add-quotient-Abᵉ xᵉ zero-quotient-Abᵉ ＝ᵉ xᵉ
  right-unit-law-add-quotient-Abᵉ =
    right-unit-law-mul-quotient-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  associative-add-quotient-Abᵉ :
    (xᵉ yᵉ zᵉ : type-quotient-Abᵉ) →
    ( add-quotient-Abᵉ (add-quotient-Abᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-quotient-Abᵉ xᵉ (add-quotient-Abᵉ yᵉ zᵉ))
  associative-add-quotient-Abᵉ =
    associative-mul-quotient-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  left-inverse-law-add-quotient-Abᵉ :
    (xᵉ : type-quotient-Abᵉ) →
    add-quotient-Abᵉ (neg-quotient-Abᵉ xᵉ) xᵉ ＝ᵉ zero-quotient-Abᵉ
  left-inverse-law-add-quotient-Abᵉ =
    left-inverse-law-mul-quotient-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  right-inverse-law-add-quotient-Abᵉ :
    (xᵉ : type-quotient-Abᵉ) →
    add-quotient-Abᵉ xᵉ (neg-quotient-Abᵉ xᵉ) ＝ᵉ zero-quotient-Abᵉ
  right-inverse-law-add-quotient-Abᵉ =
    right-inverse-law-mul-quotient-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  commutative-add-quotient-Abᵉ :
    (xᵉ yᵉ : type-quotient-Abᵉ) →
    add-quotient-Abᵉ xᵉ yᵉ ＝ᵉ add-quotient-Abᵉ yᵉ xᵉ
  commutative-add-quotient-Abᵉ =
    double-induction-set-quotient'ᵉ
      ( equivalence-relation-congruence-Subgroup-Abᵉ Aᵉ Hᵉ)
      ( λ xᵉ yᵉ →
        Id-Propᵉ
          ( set-quotient-Abᵉ)
          ( add-quotient-Abᵉ xᵉ yᵉ)
          ( add-quotient-Abᵉ yᵉ xᵉ))
      ( λ xᵉ yᵉ →
        ( compute-add-quotient-Abᵉ xᵉ yᵉ) ∙ᵉ
        ( apᵉ map-quotient-hom-Abᵉ (commutative-add-Abᵉ Aᵉ xᵉ yᵉ)) ∙ᵉ
        ( invᵉ (compute-add-quotient-Abᵉ yᵉ xᵉ)))

  semigroup-quotient-Abᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-quotient-Abᵉ =
    semigroup-quotient-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  group-quotient-Abᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  group-quotient-Abᵉ =
    quotient-Groupᵉ (group-Abᵉ Aᵉ) (normal-subgroup-Subgroup-Abᵉ Aᵉ Hᵉ)

  quotient-Abᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ quotient-Abᵉ = group-quotient-Abᵉ
  pr2ᵉ quotient-Abᵉ = commutative-add-quotient-Abᵉ
```