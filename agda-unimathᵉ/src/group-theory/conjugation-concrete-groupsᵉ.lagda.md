# Conjugation on concrete groups

```agda
module group-theory.conjugation-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.conjugationᵉ
open import group-theory.homomorphisms-concrete-groupsᵉ

open import higher-group-theory.conjugationᵉ
```

</details>

## Idea

Theᵉ **conjugationᵉ operation**ᵉ onᵉ aᵉ
[concreteᵉ group](group-theory.concrete-groups.mdᵉ) `G`ᵉ canᵉ beᵉ seenᵉ asᵉ aᵉ
[homomorphism](group-theory.homomorphisms-concrete-groups.mdᵉ) ofᵉ concreteᵉ groupsᵉ
andᵉ asᵉ aᵉ [concreteᵉ groupᵉ action](group-theory.concrete-group-actions.md).ᵉ

Noteᵉ thatᵉ theᵉ deloopingᵉ ofᵉ theᵉ
[conjugationᵉ homomorphism](structured-types.conjugation-pointed-types.mdᵉ) canᵉ beᵉ
definedᵉ directlyᵉ forᵉ [pointedᵉ types](structured-types.pointed-types.md),ᵉ whichᵉ
appliesᵉ alsoᵉ to theᵉ caseᵉ ofᵉ [∞-groups](higher-group-theory.higher-groups.md).ᵉ

## Definitions

### The conjugation homomorphism on concrete groups

```agda
module _
  {lᵉ : Level} (Gᵉ : Concrete-Groupᵉ lᵉ) (gᵉ : type-Concrete-Groupᵉ Gᵉ)
  where

  conjugation-Concrete-Groupᵉ : hom-Concrete-Groupᵉ Gᵉ Gᵉ
  conjugation-Concrete-Groupᵉ = conjugation-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ) gᵉ

  classifying-map-conjugation-Concrete-Groupᵉ :
    classifying-type-Concrete-Groupᵉ Gᵉ → classifying-type-Concrete-Groupᵉ Gᵉ
  classifying-map-conjugation-Concrete-Groupᵉ =
    classifying-map-hom-Concrete-Groupᵉ Gᵉ Gᵉ conjugation-Concrete-Groupᵉ

  preserves-point-classifying-map-conjugation-Concrete-Groupᵉ :
    classifying-map-conjugation-Concrete-Groupᵉ (shape-Concrete-Groupᵉ Gᵉ) ＝ᵉ
    shape-Concrete-Groupᵉ Gᵉ
  preserves-point-classifying-map-conjugation-Concrete-Groupᵉ =
    preserves-point-classifying-map-hom-Concrete-Groupᵉ Gᵉ Gᵉ
      ( conjugation-Concrete-Groupᵉ)

  map-conjugation-Concrete-Groupᵉ :
    type-Concrete-Groupᵉ Gᵉ → type-Concrete-Groupᵉ Gᵉ
  map-conjugation-Concrete-Groupᵉ =
    map-hom-Concrete-Groupᵉ Gᵉ Gᵉ conjugation-Concrete-Groupᵉ

  compute-map-conjugation-Concrete-Groupᵉ :
    conjugation-Group'ᵉ (group-Concrete-Groupᵉ Gᵉ) gᵉ ~ᵉ
    map-conjugation-Concrete-Groupᵉ
  compute-map-conjugation-Concrete-Groupᵉ xᵉ =
    ( assocᵉ (invᵉ gᵉ) xᵉ gᵉ) ∙ᵉ
    ( compute-map-conjugation-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ) gᵉ xᵉ)
```