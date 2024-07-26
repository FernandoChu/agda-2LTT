# Kernels of homomorphisms between abelian groups

```agda
module group-theory.kernels-homomorphisms-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.embeddings-abelian-groupsᵉ
open import group-theory.homomorphisms-abelian-groupsᵉ
open import group-theory.kernels-homomorphisms-groupsᵉ
open import group-theory.subgroups-abelian-groupsᵉ
open import group-theory.subsets-abelian-groupsᵉ
```

</details>

## Idea

Theᵉ **kernel**ᵉ ofᵉ aᵉ
[groupᵉ homomorphism](group-theory.homomorphisms-abelian-groups.mdᵉ) `fᵉ : Aᵉ → B`ᵉ
betweenᵉ [abelianᵉ groups](group-theory.abelian-groups.mdᵉ) `A`ᵉ andᵉ `B`ᵉ isᵉ theᵉ
[subgroup](group-theory.subgroups-abelian-groups.mdᵉ) ofᵉ `A`ᵉ consistingᵉ ofᵉ thoseᵉ
elementsᵉ `xᵉ : A`ᵉ suchᵉ thatᵉ `fᵉ xᵉ ＝ᵉ zero-Abᵉ B`.ᵉ

## Definitions

### Kernels of group homomorphisms between abelian groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ) (fᵉ : hom-Abᵉ Aᵉ Bᵉ)
  where

  subset-kernel-hom-Abᵉ : subset-Abᵉ l2ᵉ Aᵉ
  subset-kernel-hom-Abᵉ =
    subset-kernel-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  is-in-kernel-hom-Abᵉ : type-Abᵉ Aᵉ → UUᵉ l2ᵉ
  is-in-kernel-hom-Abᵉ =
    is-in-kernel-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  contains-zero-subset-kernel-hom-Abᵉ :
    is-in-kernel-hom-Abᵉ (zero-Abᵉ Aᵉ)
  contains-zero-subset-kernel-hom-Abᵉ =
    contains-unit-subset-kernel-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  is-closed-under-addition-subset-kernel-hom-Abᵉ :
    is-closed-under-addition-subset-Abᵉ Aᵉ subset-kernel-hom-Abᵉ
  is-closed-under-addition-subset-kernel-hom-Abᵉ =
    is-closed-under-multiplication-subset-kernel-hom-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( group-Abᵉ Bᵉ)
      ( fᵉ)

  is-closed-under-negatives-subset-kernel-hom-Abᵉ :
    is-closed-under-negatives-subset-Abᵉ Aᵉ subset-kernel-hom-Abᵉ
  is-closed-under-negatives-subset-kernel-hom-Abᵉ =
    is-closed-under-inverses-subset-kernel-hom-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( group-Abᵉ Bᵉ)
      ( fᵉ)

  kernel-hom-Abᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ
  kernel-hom-Abᵉ =
    subgroup-kernel-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  ab-kernel-hom-Abᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  ab-kernel-hom-Abᵉ = ab-Subgroup-Abᵉ Aᵉ kernel-hom-Abᵉ

  inclusion-kernel-hom-Abᵉ : hom-Abᵉ ab-kernel-hom-Abᵉ Aᵉ
  inclusion-kernel-hom-Abᵉ =
    inclusion-kernel-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  is-emb-inclusion-kernel-hom-Abᵉ :
    is-emb-hom-Abᵉ ab-kernel-hom-Abᵉ Aᵉ inclusion-kernel-hom-Abᵉ
  is-emb-inclusion-kernel-hom-Abᵉ =
    is-emb-inclusion-kernel-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  emb-inclusion-kernel-hom-Abᵉ : emb-Abᵉ ab-kernel-hom-Abᵉ Aᵉ
  emb-inclusion-kernel-hom-Abᵉ =
    emb-inclusion-kernel-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ
```