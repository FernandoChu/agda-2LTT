# Centralizer subgroups

```agda
module group-theory.centralizer-subgroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.conjugationᵉ
open import group-theory.groupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subsets-groupsᵉ
```

</details>

## Idea

Considerᵉ aᵉ [subset](group-theory.subsets-groups.mdᵉ) `S`ᵉ ofᵉ aᵉ
[group](group-theory.groups.mdᵉ) `G`.ᵉ Theᵉ **centralizerᵉ subgroup**ᵉ `Cᴳ(S)`ᵉ ofᵉ `S`ᵉ
isᵉ theᵉ subgroupᵉ ofᵉ elementsᵉ `gᵉ : G`ᵉ suchᵉ thatᵉ `gs=sg`ᵉ forᵉ everyᵉ `sᵉ ∈ᵉ S`.ᵉ Inᵉ
otherᵉ words,ᵉ itᵉ consistsᵉ ofᵉ theᵉ elementsᵉ ofᵉ `G`ᵉ thatᵉ commuteᵉ with allᵉ theᵉ
elementsᵉ ofᵉ `S`.ᵉ

Theᵉ definitionᵉ ofᵉ theᵉ centralizerᵉ isᵉ similar,ᵉ butᵉ notᵉ identicalᵉ to theᵉ
definitionᵉ ofᵉ theᵉ [normalizer](group-theory.normalizer-subgroups.md).ᵉ Thereᵉ isᵉ
anᵉ inclusionᵉ ofᵉ theᵉ centralizerᵉ intoᵉ theᵉ normalizer,ᵉ butᵉ notᵉ theᵉ otherᵉ wayᵉ
around.ᵉ Theᵉ centralizerᵉ shouldᵉ alsoᵉ notᵉ beᵉ confusedᵉ with theᵉ
[center](group-theory.centers-groups.mdᵉ) ofᵉ aᵉ group.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Sᵉ : subset-Groupᵉ l2ᵉ Gᵉ)
  where

  subset-centralizer-subset-Groupᵉ : subset-Groupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
  subset-centralizer-subset-Groupᵉ xᵉ =
    Π-Propᵉ
      ( type-Groupᵉ Gᵉ)
      ( λ yᵉ →
        hom-Propᵉ (Sᵉ yᵉ) (Id-Propᵉ (set-Groupᵉ Gᵉ) (conjugation-Groupᵉ Gᵉ xᵉ yᵉ) yᵉ))

  is-in-centralizer-subset-Groupᵉ : type-Groupᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-in-centralizer-subset-Groupᵉ =
    is-in-subtypeᵉ subset-centralizer-subset-Groupᵉ

  contains-unit-centralizer-subset-Groupᵉ :
    contains-unit-subset-Groupᵉ Gᵉ subset-centralizer-subset-Groupᵉ
  contains-unit-centralizer-subset-Groupᵉ yᵉ sᵉ =
    compute-conjugation-unit-Groupᵉ Gᵉ yᵉ

  is-closed-under-multiplication-centralizer-subset-Groupᵉ :
    is-closed-under-multiplication-subset-Groupᵉ Gᵉ
      subset-centralizer-subset-Groupᵉ
  is-closed-under-multiplication-centralizer-subset-Groupᵉ {xᵉ} {yᵉ} uᵉ vᵉ zᵉ sᵉ =
    ( compute-conjugation-mul-Groupᵉ Gᵉ xᵉ yᵉ zᵉ) ∙ᵉ
    ( apᵉ (conjugation-Groupᵉ Gᵉ xᵉ) (vᵉ zᵉ sᵉ)) ∙ᵉ
    ( uᵉ zᵉ sᵉ)

  is-closed-under-inverses-centralizer-subset-Groupᵉ :
    is-closed-under-inverses-subset-Groupᵉ Gᵉ subset-centralizer-subset-Groupᵉ
  is-closed-under-inverses-centralizer-subset-Groupᵉ {xᵉ} uᵉ yᵉ sᵉ =
    transpose-eq-conjugation-inv-Groupᵉ Gᵉ (invᵉ (uᵉ yᵉ sᵉ))

  centralizer-subset-Groupᵉ : Subgroupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
  pr1ᵉ centralizer-subset-Groupᵉ =
    subset-centralizer-subset-Groupᵉ
  pr1ᵉ (pr2ᵉ centralizer-subset-Groupᵉ) =
    contains-unit-centralizer-subset-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ centralizer-subset-Groupᵉ)) =
    is-closed-under-multiplication-centralizer-subset-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ centralizer-subset-Groupᵉ)) =
    is-closed-under-inverses-centralizer-subset-Groupᵉ
```