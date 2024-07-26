# Kernels of homomorphisms of groups

```agda
module group-theory.kernels-homomorphisms-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.embeddings-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.normal-subgroupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subsets-groupsᵉ
```

</details>

## Idea

Theᵉ **kernel**ᵉ ofᵉ aᵉ [groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ)
`fᵉ : Gᵉ → H`ᵉ isᵉ theᵉ [normalᵉ subgroup](group-theory.normal-subgroups.mdᵉ) ofᵉ `G`ᵉ
consistingᵉ ofᵉ thoseᵉ elementsᵉ `xᵉ : G`ᵉ suchᵉ thatᵉ `fᵉ xᵉ ＝ᵉ unit-Groupᵉ H`.ᵉ

## Definition

Weᵉ defineᵉ theᵉ kernelᵉ asᵉ theᵉ subgroupᵉ generatedᵉ byᵉ theᵉ predicateᵉ whichᵉ associatesᵉ
to `x`ᵉ theᵉ propositionᵉ `f(xᵉ) = unit`.ᵉ

```agda
module _
  {lᵉ kᵉ : Level} (Gᵉ : Groupᵉ lᵉ) (Hᵉ : Groupᵉ kᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  subset-kernel-hom-Groupᵉ : subset-Groupᵉ kᵉ Gᵉ
  subset-kernel-hom-Groupᵉ xᵉ =
    is-unit-prop-Group'ᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ)

  is-in-kernel-hom-Groupᵉ : type-Groupᵉ Gᵉ → UUᵉ kᵉ
  is-in-kernel-hom-Groupᵉ xᵉ = type-Propᵉ (subset-kernel-hom-Groupᵉ xᵉ)

  contains-unit-subset-kernel-hom-Groupᵉ :
    is-in-kernel-hom-Groupᵉ (unit-Groupᵉ Gᵉ)
  contains-unit-subset-kernel-hom-Groupᵉ = invᵉ (preserves-unit-hom-Groupᵉ Gᵉ Hᵉ fᵉ)

  is-closed-under-multiplication-subset-kernel-hom-Groupᵉ :
    is-closed-under-multiplication-subset-Groupᵉ Gᵉ subset-kernel-hom-Groupᵉ
  is-closed-under-multiplication-subset-kernel-hom-Groupᵉ pᵉ qᵉ =
    ( invᵉ (left-unit-law-mul-Groupᵉ Hᵉ _)) ∙ᵉ
    ( ap-mul-Groupᵉ Hᵉ pᵉ qᵉ) ∙ᵉ
    ( invᵉ (preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ))

  is-closed-under-inverses-subset-kernel-hom-Groupᵉ :
    is-closed-under-inverses-subset-Groupᵉ Gᵉ subset-kernel-hom-Groupᵉ
  is-closed-under-inverses-subset-kernel-hom-Groupᵉ pᵉ =
    ( invᵉ (inv-unit-Groupᵉ Hᵉ)) ∙ᵉ
    ( apᵉ (inv-Groupᵉ Hᵉ) pᵉ) ∙ᵉ
    ( invᵉ (preserves-inv-hom-Groupᵉ Gᵉ Hᵉ fᵉ))

  subgroup-kernel-hom-Groupᵉ : Subgroupᵉ kᵉ Gᵉ
  pr1ᵉ subgroup-kernel-hom-Groupᵉ = subset-kernel-hom-Groupᵉ
  pr1ᵉ (pr2ᵉ subgroup-kernel-hom-Groupᵉ) = contains-unit-subset-kernel-hom-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ subgroup-kernel-hom-Groupᵉ)) =
    is-closed-under-multiplication-subset-kernel-hom-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ subgroup-kernel-hom-Groupᵉ)) =
    is-closed-under-inverses-subset-kernel-hom-Groupᵉ

  group-kernel-hom-Groupᵉ : Groupᵉ (lᵉ ⊔ kᵉ)
  group-kernel-hom-Groupᵉ = group-Subgroupᵉ Gᵉ subgroup-kernel-hom-Groupᵉ

  inclusion-kernel-hom-Groupᵉ : hom-Groupᵉ group-kernel-hom-Groupᵉ Gᵉ
  inclusion-kernel-hom-Groupᵉ =
    hom-inclusion-Subgroupᵉ Gᵉ subgroup-kernel-hom-Groupᵉ

  type-kernel-hom-Groupᵉ : UUᵉ (lᵉ ⊔ kᵉ)
  type-kernel-hom-Groupᵉ = type-Subgroupᵉ Gᵉ subgroup-kernel-hom-Groupᵉ

  map-inclusion-kernel-hom-Groupᵉ : type-kernel-hom-Groupᵉ → type-Groupᵉ Gᵉ
  map-inclusion-kernel-hom-Groupᵉ =
    map-hom-Groupᵉ group-kernel-hom-Groupᵉ Gᵉ inclusion-kernel-hom-Groupᵉ

  is-in-subgroup-inclusion-kernel-hom-Groupᵉ :
    (xᵉ : type-kernel-hom-Groupᵉ) →
    is-in-kernel-hom-Groupᵉ (map-inclusion-kernel-hom-Groupᵉ xᵉ)
  is-in-subgroup-inclusion-kernel-hom-Groupᵉ =
    is-in-subgroup-inclusion-Subgroupᵉ Gᵉ subgroup-kernel-hom-Groupᵉ

  is-emb-inclusion-kernel-hom-Groupᵉ :
    is-emb-hom-Groupᵉ group-kernel-hom-Groupᵉ Gᵉ inclusion-kernel-hom-Groupᵉ
  is-emb-inclusion-kernel-hom-Groupᵉ =
    is-emb-inclusion-Subgroupᵉ Gᵉ subgroup-kernel-hom-Groupᵉ

  emb-inclusion-kernel-hom-Groupᵉ : emb-Groupᵉ group-kernel-hom-Groupᵉ Gᵉ
  pr1ᵉ emb-inclusion-kernel-hom-Groupᵉ =
    inclusion-kernel-hom-Groupᵉ
  pr2ᵉ emb-inclusion-kernel-hom-Groupᵉ =
    is-emb-inclusion-kernel-hom-Groupᵉ
```

## Properties

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  is-normal-kernel-hom-Groupᵉ :
    is-normal-Subgroupᵉ Gᵉ (subgroup-kernel-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
  is-normal-kernel-hom-Groupᵉ gᵉ hᵉ =
    invᵉ
      ( ( preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ) ∙ᵉ
        ( apᵉ
          ( mul-Group'ᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (inv-Groupᵉ Gᵉ gᵉ)))
          ( ( preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ) ∙ᵉ
            ( invᵉ
              ( apᵉ
                ( mul-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ gᵉ))
                ( is-in-subgroup-inclusion-kernel-hom-Groupᵉ Gᵉ Hᵉ fᵉ hᵉ))) ∙ᵉ
            ( right-unit-law-mul-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ gᵉ)))) ∙ᵉ
        ( apᵉ (mul-Groupᵉ Hᵉ _) (preserves-inv-hom-Groupᵉ Gᵉ Hᵉ fᵉ)) ∙ᵉ
        ( right-inverse-law-mul-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ gᵉ)))

  kernel-hom-Groupᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ
  pr1ᵉ kernel-hom-Groupᵉ = subgroup-kernel-hom-Groupᵉ Gᵉ Hᵉ fᵉ
  pr2ᵉ kernel-hom-Groupᵉ = is-normal-kernel-hom-Groupᵉ
```