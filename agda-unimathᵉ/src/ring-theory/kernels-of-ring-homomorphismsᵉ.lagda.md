# Kernels of ring homomorphisms

```agda
module ring-theory.kernels-of-ring-homomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.kernels-homomorphisms-groupsᵉ
open import group-theory.subgroups-abelian-groupsᵉ

open import ring-theory.homomorphisms-ringsᵉ
open import ring-theory.ideals-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.subsets-ringsᵉ
```

</details>

## Idea

Theᵉ **kernel**ᵉ ofᵉ aᵉ [ringᵉ homomorphism](ring-theory.homomorphisms-rings.mdᵉ)
`fᵉ : Rᵉ → S`ᵉ isᵉ theᵉ [ideal](ring-theory.ideals-rings.mdᵉ) ofᵉ `R`ᵉ consistingᵉ ofᵉ allᵉ
elementsᵉ `xᵉ : R`ᵉ equippedᵉ with anᵉ identificationᵉ `fᵉ xᵉ ＝ᵉ 0`.ᵉ

## Definitions

### The kernel of a ring homomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (fᵉ : hom-Ringᵉ Rᵉ Sᵉ)
  where

  subgroup-kernel-hom-Ringᵉ : Subgroup-Abᵉ l2ᵉ (ab-Ringᵉ Rᵉ)
  subgroup-kernel-hom-Ringᵉ =
    subgroup-kernel-hom-Groupᵉ
      ( group-Ringᵉ Rᵉ)
      ( group-Ringᵉ Sᵉ)
      ( hom-group-hom-Ringᵉ Rᵉ Sᵉ fᵉ)

  subset-kernel-hom-Ringᵉ : subset-Ringᵉ l2ᵉ Rᵉ
  subset-kernel-hom-Ringᵉ =
    subset-Subgroup-Abᵉ (ab-Ringᵉ Rᵉ) subgroup-kernel-hom-Ringᵉ

  contains-zero-kernel-hom-Ringᵉ :
    contains-zero-subset-Ringᵉ Rᵉ subset-kernel-hom-Ringᵉ
  contains-zero-kernel-hom-Ringᵉ =
    contains-zero-Subgroup-Abᵉ (ab-Ringᵉ Rᵉ) subgroup-kernel-hom-Ringᵉ

  is-closed-under-addition-kernel-hom-Ringᵉ :
    is-closed-under-addition-subset-Ringᵉ Rᵉ subset-kernel-hom-Ringᵉ
  is-closed-under-addition-kernel-hom-Ringᵉ =
    is-closed-under-addition-Subgroup-Abᵉ (ab-Ringᵉ Rᵉ) subgroup-kernel-hom-Ringᵉ

  is-closed-under-negatives-kernel-hom-Ringᵉ :
    is-closed-under-negatives-subset-Ringᵉ Rᵉ subset-kernel-hom-Ringᵉ
  is-closed-under-negatives-kernel-hom-Ringᵉ =
    is-closed-under-negatives-Subgroup-Abᵉ (ab-Ringᵉ Rᵉ) subgroup-kernel-hom-Ringᵉ

  is-additive-subgroup-kernel-hom-Ringᵉ :
    is-additive-subgroup-subset-Ringᵉ Rᵉ subset-kernel-hom-Ringᵉ
  pr1ᵉ is-additive-subgroup-kernel-hom-Ringᵉ =
    contains-zero-kernel-hom-Ringᵉ
  pr1ᵉ (pr2ᵉ is-additive-subgroup-kernel-hom-Ringᵉ) =
    is-closed-under-addition-kernel-hom-Ringᵉ
  pr2ᵉ (pr2ᵉ is-additive-subgroup-kernel-hom-Ringᵉ) =
    is-closed-under-negatives-kernel-hom-Ringᵉ

  is-closed-under-left-multiplication-kernel-hom-Ringᵉ :
    is-closed-under-left-multiplication-subset-Ringᵉ Rᵉ subset-kernel-hom-Ringᵉ
  is-closed-under-left-multiplication-kernel-hom-Ringᵉ xᵉ yᵉ Hᵉ =
    ( invᵉ (right-zero-law-mul-Ringᵉ Sᵉ _)) ∙ᵉ
    ( apᵉ (mul-Ringᵉ Sᵉ _) Hᵉ) ∙ᵉ
    ( invᵉ (preserves-mul-hom-Ringᵉ Rᵉ Sᵉ fᵉ))

  is-closed-under-right-multiplication-kernel-hom-Ringᵉ :
    is-closed-under-right-multiplication-subset-Ringᵉ Rᵉ subset-kernel-hom-Ringᵉ
  is-closed-under-right-multiplication-kernel-hom-Ringᵉ xᵉ yᵉ Hᵉ =
    ( invᵉ (left-zero-law-mul-Ringᵉ Sᵉ _)) ∙ᵉ
    ( apᵉ (mul-Ring'ᵉ Sᵉ _) Hᵉ) ∙ᵉ
    ( invᵉ (preserves-mul-hom-Ringᵉ Rᵉ Sᵉ fᵉ))

  kernel-hom-Ringᵉ : ideal-Ringᵉ l2ᵉ Rᵉ
  pr1ᵉ kernel-hom-Ringᵉ =
    subset-kernel-hom-Ringᵉ
  pr1ᵉ (pr2ᵉ kernel-hom-Ringᵉ) =
    is-additive-subgroup-kernel-hom-Ringᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ kernel-hom-Ringᵉ)) =
    is-closed-under-left-multiplication-kernel-hom-Ringᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ kernel-hom-Ringᵉ)) =
    is-closed-under-right-multiplication-kernel-hom-Ringᵉ
```