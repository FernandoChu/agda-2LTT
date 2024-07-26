# The center of a group

```agda
module group-theory.centers-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.central-elements-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.normal-subgroupsᵉ
open import group-theory.subgroupsᵉ
```

</details>

## Idea

Theᵉ **center**ᵉ ofᵉ aᵉ groupᵉ consistsᵉ ofᵉ thoseᵉ elementsᵉ thatᵉ areᵉ central.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  subtype-center-Groupᵉ : type-Groupᵉ Gᵉ → Propᵉ lᵉ
  subtype-center-Groupᵉ = is-central-element-prop-Groupᵉ Gᵉ

  subgroup-center-Groupᵉ : Subgroupᵉ lᵉ Gᵉ
  pr1ᵉ subgroup-center-Groupᵉ =
    subtype-center-Groupᵉ
  pr1ᵉ (pr2ᵉ subgroup-center-Groupᵉ) =
    is-central-element-unit-Groupᵉ Gᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ subgroup-center-Groupᵉ)) =
    is-central-element-mul-Groupᵉ Gᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ subgroup-center-Groupᵉ)) =
    is-central-element-inv-Groupᵉ Gᵉ

  group-center-Groupᵉ : Groupᵉ lᵉ
  group-center-Groupᵉ = group-Subgroupᵉ Gᵉ subgroup-center-Groupᵉ

  type-center-Groupᵉ : UUᵉ lᵉ
  type-center-Groupᵉ =
    type-Subgroupᵉ Gᵉ subgroup-center-Groupᵉ

  mul-center-Groupᵉ :
    (xᵉ yᵉ : type-center-Groupᵉ) → type-center-Groupᵉ
  mul-center-Groupᵉ = mul-Subgroupᵉ Gᵉ subgroup-center-Groupᵉ

  associative-mul-center-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-center-Groupᵉ) →
    mul-center-Groupᵉ (mul-center-Groupᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-center-Groupᵉ xᵉ (mul-center-Groupᵉ yᵉ zᵉ)
  associative-mul-center-Groupᵉ =
    associative-mul-Subgroupᵉ Gᵉ subgroup-center-Groupᵉ

  inclusion-center-Groupᵉ :
    type-center-Groupᵉ → type-Groupᵉ Gᵉ
  inclusion-center-Groupᵉ =
    inclusion-Subgroupᵉ Gᵉ subgroup-center-Groupᵉ

  is-central-element-inclusion-center-Groupᵉ :
    (xᵉ : type-center-Groupᵉ) →
    is-central-element-Groupᵉ Gᵉ (inclusion-center-Groupᵉ xᵉ)
  is-central-element-inclusion-center-Groupᵉ xᵉ =
    is-in-subgroup-inclusion-Subgroupᵉ Gᵉ subgroup-center-Groupᵉ xᵉ

  preserves-mul-inclusion-center-Groupᵉ :
    {xᵉ yᵉ : type-center-Groupᵉ} →
    inclusion-center-Groupᵉ (mul-center-Groupᵉ xᵉ yᵉ) ＝ᵉ
    mul-Groupᵉ Gᵉ
      ( inclusion-center-Groupᵉ xᵉ)
      ( inclusion-center-Groupᵉ yᵉ)
  preserves-mul-inclusion-center-Groupᵉ {xᵉ} {yᵉ} =
    preserves-mul-inclusion-Subgroupᵉ Gᵉ subgroup-center-Groupᵉ {xᵉ} {yᵉ}

  hom-inclusion-center-Groupᵉ :
    hom-Groupᵉ group-center-Groupᵉ Gᵉ
  hom-inclusion-center-Groupᵉ =
    hom-inclusion-Subgroupᵉ Gᵉ subgroup-center-Groupᵉ

  is-normal-subgroup-center-Groupᵉ :
    is-normal-Subgroupᵉ Gᵉ subgroup-center-Groupᵉ
  is-normal-subgroup-center-Groupᵉ xᵉ yᵉ =
    is-central-element-conjugation-Groupᵉ Gᵉ
      ( inclusion-center-Groupᵉ yᵉ)
      ( xᵉ)
      ( is-central-element-inclusion-center-Groupᵉ yᵉ)

  center-Groupᵉ : Normal-Subgroupᵉ lᵉ Gᵉ
  pr1ᵉ center-Groupᵉ = subgroup-center-Groupᵉ
  pr2ᵉ center-Groupᵉ = is-normal-subgroup-center-Groupᵉ
```