# The full subgroup of a group

```agda
module group-theory.full-subgroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.full-subtypesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.isomorphisms-groupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subsets-groupsᵉ
```

</details>

## Idea

Theᵉ **fullᵉ subgroup**ᵉ ofᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ theᵉ
[subgroup](group-theory.subgroups.mdᵉ) consistingᵉ ofᵉ allᵉ elementsᵉ ofᵉ theᵉ groupᵉ
`G`.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ fullᵉ subgroupᵉ isᵉ theᵉ subgroupᵉ whoseᵉ underlyingᵉ subsetᵉ
isᵉ theᵉ [fullᵉ subset](foundation.full-subtypes.mdᵉ) ofᵉ theᵉ group.ᵉ

## Definition

### Full subgroups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  is-full-prop-Subgroupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-full-prop-Subgroupᵉ = is-full-subtype-Propᵉ (subset-Subgroupᵉ Gᵉ Hᵉ)

  is-full-Subgroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-full-Subgroupᵉ = type-Propᵉ is-full-prop-Subgroupᵉ

  is-prop-is-full-Subgroupᵉ : is-propᵉ is-full-Subgroupᵉ
  is-prop-is-full-Subgroupᵉ = is-prop-type-Propᵉ is-full-prop-Subgroupᵉ
```

### The full subgroup at each universe level

```agda
subset-full-Subgroupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Groupᵉ l1ᵉ) → subset-Groupᵉ l2ᵉ Gᵉ
subset-full-Subgroupᵉ l2ᵉ Gᵉ = full-subtypeᵉ l2ᵉ (type-Groupᵉ Gᵉ)

type-full-Subgroupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Groupᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-full-Subgroupᵉ l2ᵉ Gᵉ = type-full-subtypeᵉ l2ᵉ (type-Groupᵉ Gᵉ)

contains-unit-full-Subgroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  contains-unit-subset-Groupᵉ Gᵉ (subset-full-Subgroupᵉ l2ᵉ Gᵉ)
contains-unit-full-Subgroupᵉ Gᵉ = is-in-full-subtypeᵉ (unit-Groupᵉ Gᵉ)

is-closed-under-multiplication-full-Subgroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  is-closed-under-multiplication-subset-Groupᵉ Gᵉ (subset-full-Subgroupᵉ l2ᵉ Gᵉ)
is-closed-under-multiplication-full-Subgroupᵉ Gᵉ {xᵉ} {yᵉ} _ _ =
  is-in-full-subtypeᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ)

is-closed-under-inverses-full-Subgroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  is-closed-under-inverses-subset-Groupᵉ Gᵉ (subset-full-Subgroupᵉ l2ᵉ Gᵉ)
is-closed-under-inverses-full-Subgroupᵉ Gᵉ {xᵉ} _ =
  is-in-full-subtypeᵉ (inv-Groupᵉ Gᵉ xᵉ)

full-Subgroupᵉ : {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Groupᵉ l1ᵉ) → Subgroupᵉ l2ᵉ Gᵉ
pr1ᵉ (full-Subgroupᵉ l2ᵉ Gᵉ) =
  subset-full-Subgroupᵉ l2ᵉ Gᵉ
pr1ᵉ (pr2ᵉ (full-Subgroupᵉ l2ᵉ Gᵉ)) =
  contains-unit-full-Subgroupᵉ Gᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (full-Subgroupᵉ l2ᵉ Gᵉ))) {xᵉ} {yᵉ} =
  is-closed-under-multiplication-full-Subgroupᵉ Gᵉ {xᵉ} {yᵉ}
pr2ᵉ (pr2ᵉ (pr2ᵉ (full-Subgroupᵉ l2ᵉ Gᵉ))) {xᵉ} =
  is-closed-under-inverses-full-Subgroupᵉ Gᵉ {xᵉ}

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  inclusion-full-Subgroupᵉ : type-full-Subgroupᵉ l2ᵉ Gᵉ → type-Groupᵉ Gᵉ
  inclusion-full-Subgroupᵉ = inclusion-Subgroupᵉ Gᵉ (full-Subgroupᵉ l2ᵉ Gᵉ)

  is-equiv-inclusion-full-Subgroupᵉ : is-equivᵉ inclusion-full-Subgroupᵉ
  is-equiv-inclusion-full-Subgroupᵉ = is-equiv-inclusion-full-subtypeᵉ

  equiv-inclusion-full-Subgroupᵉ : type-full-Subgroupᵉ l2ᵉ Gᵉ ≃ᵉ type-Groupᵉ Gᵉ
  pr1ᵉ equiv-inclusion-full-Subgroupᵉ = inclusion-full-Subgroupᵉ
  pr2ᵉ equiv-inclusion-full-Subgroupᵉ = is-equiv-inclusion-full-Subgroupᵉ

  group-full-Subgroupᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  group-full-Subgroupᵉ = group-Subgroupᵉ Gᵉ (full-Subgroupᵉ l2ᵉ Gᵉ)

  hom-inclusion-full-Subgroupᵉ : hom-Groupᵉ group-full-Subgroupᵉ Gᵉ
  hom-inclusion-full-Subgroupᵉ =
    hom-inclusion-Subgroupᵉ Gᵉ (full-Subgroupᵉ l2ᵉ Gᵉ)

  preserves-mul-inclusion-full-Subgroupᵉ :
    preserves-mul-Groupᵉ group-full-Subgroupᵉ Gᵉ inclusion-full-Subgroupᵉ
  preserves-mul-inclusion-full-Subgroupᵉ {xᵉ} {yᵉ} =
    preserves-mul-inclusion-Subgroupᵉ Gᵉ (full-Subgroupᵉ l2ᵉ Gᵉ) {xᵉ} {yᵉ}

  equiv-group-inclusion-full-Subgroupᵉ : equiv-Groupᵉ group-full-Subgroupᵉ Gᵉ
  pr1ᵉ equiv-group-inclusion-full-Subgroupᵉ =
    equiv-inclusion-full-Subgroupᵉ
  pr2ᵉ equiv-group-inclusion-full-Subgroupᵉ {xᵉ} {yᵉ} =
    preserves-mul-inclusion-full-Subgroupᵉ {xᵉ} {yᵉ}

  iso-full-Subgroupᵉ : iso-Groupᵉ group-full-Subgroupᵉ Gᵉ
  iso-full-Subgroupᵉ =
    iso-equiv-Groupᵉ group-full-Subgroupᵉ Gᵉ equiv-group-inclusion-full-Subgroupᵉ

  inv-iso-full-Subgroupᵉ :
    iso-Groupᵉ Gᵉ group-full-Subgroupᵉ
  inv-iso-full-Subgroupᵉ =
    inv-iso-Groupᵉ group-full-Subgroupᵉ Gᵉ iso-full-Subgroupᵉ
```

## Properties

### A subgroup is full if and only if the inclusion is an isomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  is-iso-inclusion-is-full-Subgroupᵉ :
    is-full-Subgroupᵉ Gᵉ Hᵉ →
    is-iso-Groupᵉ (group-Subgroupᵉ Gᵉ Hᵉ) Gᵉ (hom-inclusion-Subgroupᵉ Gᵉ Hᵉ)
  is-iso-inclusion-is-full-Subgroupᵉ Kᵉ =
    is-iso-is-equiv-hom-Groupᵉ
      ( group-Subgroupᵉ Gᵉ Hᵉ)
      ( Gᵉ)
      ( hom-inclusion-Subgroupᵉ Gᵉ Hᵉ)
      ( is-equiv-inclusion-is-full-subtypeᵉ (subset-Subgroupᵉ Gᵉ Hᵉ) Kᵉ)

  iso-inclusion-is-full-Subgroupᵉ :
    is-full-Subgroupᵉ Gᵉ Hᵉ → iso-Groupᵉ (group-Subgroupᵉ Gᵉ Hᵉ) Gᵉ
  pr1ᵉ (iso-inclusion-is-full-Subgroupᵉ Kᵉ) = hom-inclusion-Subgroupᵉ Gᵉ Hᵉ
  pr2ᵉ (iso-inclusion-is-full-Subgroupᵉ Kᵉ) = is-iso-inclusion-is-full-Subgroupᵉ Kᵉ

  is-full-is-iso-inclusion-Subgroupᵉ :
    is-iso-Groupᵉ (group-Subgroupᵉ Gᵉ Hᵉ) Gᵉ (hom-inclusion-Subgroupᵉ Gᵉ Hᵉ) →
    is-full-Subgroupᵉ Gᵉ Hᵉ
  is-full-is-iso-inclusion-Subgroupᵉ Kᵉ =
    is-full-is-equiv-inclusion-subtypeᵉ
      ( subset-Subgroupᵉ Gᵉ Hᵉ)
      ( is-equiv-is-iso-Groupᵉ
        ( group-Subgroupᵉ Gᵉ Hᵉ)
        ( Gᵉ)
        ( hom-inclusion-Subgroupᵉ Gᵉ Hᵉ)
        ( Kᵉ))
```