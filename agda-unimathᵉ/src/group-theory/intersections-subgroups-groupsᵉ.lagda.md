# Intersections of subgroups of groups

```agda
module group-theory.intersections-subgroups-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.intersections-subtypesᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subsets-groupsᵉ

open import order-theory.greatest-lower-bounds-large-posetsᵉ
```

</details>

## Idea

Theᵉ **intersection**ᵉ ofᵉ twoᵉ subgroupsᵉ `H,ᵉ Kᵉ ≤ᵉ G`ᵉ isᵉ againᵉ closedᵉ underᵉ theᵉ groupᵉ
operations,ᵉ andᵉ isᵉ thereforeᵉ aᵉ subgroupᵉ ofᵉ `G`.ᵉ

## Definitions

### The intersection of two subgroups

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ) (Kᵉ : Subgroupᵉ l3ᵉ Gᵉ)
  where

  subset-intersection-Subgroupᵉ :
    subset-Groupᵉ (l2ᵉ ⊔ l3ᵉ) Gᵉ
  subset-intersection-Subgroupᵉ =
    intersection-subtypeᵉ (subset-Subgroupᵉ Gᵉ Hᵉ) (subset-Subgroupᵉ Gᵉ Kᵉ)

  is-in-intersection-Subgroupᵉ :
    type-Groupᵉ Gᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  is-in-intersection-Subgroupᵉ =
    is-in-subtypeᵉ subset-intersection-Subgroupᵉ

  contains-unit-intersection-Subgroupᵉ :
    is-in-intersection-Subgroupᵉ (unit-Groupᵉ Gᵉ)
  pr1ᵉ contains-unit-intersection-Subgroupᵉ = contains-unit-Subgroupᵉ Gᵉ Hᵉ
  pr2ᵉ contains-unit-intersection-Subgroupᵉ = contains-unit-Subgroupᵉ Gᵉ Kᵉ

  is-closed-under-multiplication-intersection-Subgroupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    is-in-intersection-Subgroupᵉ xᵉ →
    is-in-intersection-Subgroupᵉ yᵉ →
    is-in-intersection-Subgroupᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ)
  pr1ᵉ
    ( is-closed-under-multiplication-intersection-Subgroupᵉ
      ( pHᵉ ,ᵉ pKᵉ)
      ( qHᵉ ,ᵉ qKᵉ)) =
    is-closed-under-multiplication-Subgroupᵉ Gᵉ Hᵉ pHᵉ qHᵉ
  pr2ᵉ
    ( is-closed-under-multiplication-intersection-Subgroupᵉ
      ( pHᵉ ,ᵉ pKᵉ)
      ( qHᵉ ,ᵉ qKᵉ)) =
    is-closed-under-multiplication-Subgroupᵉ Gᵉ Kᵉ pKᵉ qKᵉ

  is-closed-under-inverses-intersection-Subgroupᵉ :
    {xᵉ : type-Groupᵉ Gᵉ} →
    is-in-intersection-Subgroupᵉ xᵉ → is-in-intersection-Subgroupᵉ (inv-Groupᵉ Gᵉ xᵉ)
  pr1ᵉ (is-closed-under-inverses-intersection-Subgroupᵉ (pHᵉ ,ᵉ pKᵉ)) =
    is-closed-under-inverses-Subgroupᵉ Gᵉ Hᵉ pHᵉ
  pr2ᵉ (is-closed-under-inverses-intersection-Subgroupᵉ (pHᵉ ,ᵉ pKᵉ)) =
    is-closed-under-inverses-Subgroupᵉ Gᵉ Kᵉ pKᵉ

  is-subgroup-intersection-Subgroupᵉ :
    is-subgroup-subset-Groupᵉ Gᵉ subset-intersection-Subgroupᵉ
  pr1ᵉ is-subgroup-intersection-Subgroupᵉ =
    contains-unit-intersection-Subgroupᵉ
  pr1ᵉ (pr2ᵉ is-subgroup-intersection-Subgroupᵉ) =
    is-closed-under-multiplication-intersection-Subgroupᵉ
  pr2ᵉ (pr2ᵉ is-subgroup-intersection-Subgroupᵉ) =
    is-closed-under-inverses-intersection-Subgroupᵉ

  intersection-Subgroupᵉ : Subgroupᵉ (l2ᵉ ⊔ l3ᵉ) Gᵉ
  pr1ᵉ intersection-Subgroupᵉ = subset-intersection-Subgroupᵉ
  pr2ᵉ intersection-Subgroupᵉ = is-subgroup-intersection-Subgroupᵉ
```

### The intersection of a family of subgroups

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) {Iᵉ : UUᵉ l2ᵉ} (Hᵉ : Iᵉ → Subgroupᵉ l3ᵉ Gᵉ)
  where

  subset-intersection-family-of-subgroups-Groupᵉ : subset-Groupᵉ (l2ᵉ ⊔ l3ᵉ) Gᵉ
  subset-intersection-family-of-subgroups-Groupᵉ =
    intersection-family-of-subtypesᵉ (λ iᵉ → subset-Subgroupᵉ Gᵉ (Hᵉ iᵉ))

  is-in-intersection-family-of-subgroups-Groupᵉ : type-Groupᵉ Gᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  is-in-intersection-family-of-subgroups-Groupᵉ =
    is-in-subtypeᵉ subset-intersection-family-of-subgroups-Groupᵉ

  contains-unit-intersection-family-of-subgroups-Groupᵉ :
    contains-unit-subset-Groupᵉ Gᵉ subset-intersection-family-of-subgroups-Groupᵉ
  contains-unit-intersection-family-of-subgroups-Groupᵉ iᵉ =
    contains-unit-Subgroupᵉ Gᵉ (Hᵉ iᵉ)

  is-closed-under-multiplication-intersection-family-of-subgroups-Groupᵉ :
    is-closed-under-multiplication-subset-Groupᵉ Gᵉ
      subset-intersection-family-of-subgroups-Groupᵉ
  is-closed-under-multiplication-intersection-family-of-subgroups-Groupᵉ pᵉ qᵉ iᵉ =
    is-closed-under-multiplication-Subgroupᵉ Gᵉ (Hᵉ iᵉ) (pᵉ iᵉ) (qᵉ iᵉ)

  is-closed-under-inverses-intersection-family-of-subgroups-Groupᵉ :
    is-closed-under-inverses-subset-Groupᵉ Gᵉ
      subset-intersection-family-of-subgroups-Groupᵉ
  is-closed-under-inverses-intersection-family-of-subgroups-Groupᵉ pᵉ iᵉ =
    is-closed-under-inverses-Subgroupᵉ Gᵉ (Hᵉ iᵉ) (pᵉ iᵉ)

  is-subgroup-intersection-family-of-subgroups-Groupᵉ :
    is-subgroup-subset-Groupᵉ Gᵉ subset-intersection-family-of-subgroups-Groupᵉ
  pr1ᵉ is-subgroup-intersection-family-of-subgroups-Groupᵉ =
    contains-unit-intersection-family-of-subgroups-Groupᵉ
  pr1ᵉ (pr2ᵉ is-subgroup-intersection-family-of-subgroups-Groupᵉ) =
    is-closed-under-multiplication-intersection-family-of-subgroups-Groupᵉ
  pr2ᵉ (pr2ᵉ is-subgroup-intersection-family-of-subgroups-Groupᵉ) =
    is-closed-under-inverses-intersection-family-of-subgroups-Groupᵉ

  intersection-family-of-subgroups-Groupᵉ : Subgroupᵉ (l2ᵉ ⊔ l3ᵉ) Gᵉ
  pr1ᵉ intersection-family-of-subgroups-Groupᵉ =
    subset-intersection-family-of-subgroups-Groupᵉ
  pr2ᵉ intersection-family-of-subgroups-Groupᵉ =
    is-subgroup-intersection-family-of-subgroups-Groupᵉ
```

## Properties

### The intersection of `H` and `K` is the greatest binary lower bound of `H` and `K` in the poset of subgroups of `G`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ) (Kᵉ : Subgroupᵉ l3ᵉ Gᵉ)
  where

  is-greatest-binary-lower-bound-intersection-Subgroupᵉ :
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( Subgroup-Large-Posetᵉ Gᵉ)
      ( Hᵉ)
      ( Kᵉ)
      ( intersection-Subgroupᵉ Gᵉ Hᵉ Kᵉ)
  is-greatest-binary-lower-bound-intersection-Subgroupᵉ Lᵉ =
    is-greatest-binary-lower-bound-intersection-subtypeᵉ
      ( subset-Subgroupᵉ Gᵉ Hᵉ)
      ( subset-Subgroupᵉ Gᵉ Kᵉ)
      ( subset-Subgroupᵉ Gᵉ Lᵉ)
```