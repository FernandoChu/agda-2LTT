# Commutator subgroups

```agda
module group-theory.commutator-subgroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutators-of-elements-groupsᵉ
open import group-theory.conjugationᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.images-of-group-homomorphismsᵉ
open import group-theory.normal-subgroupsᵉ
open import group-theory.pullbacks-subgroupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subgroups-generated-by-families-of-elements-groupsᵉ
open import group-theory.subgroups-generated-by-subsets-groupsᵉ
open import group-theory.subsets-groupsᵉ
```

</details>

## Idea

Considerᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`.ᵉ Theᵉ **commutatorᵉ subgroup**ᵉ
`[G,G]`ᵉ ofᵉ `G`ᵉ isᵉ theᵉ
[subgroupᵉ generatedᵉ by](group-theory.subgroups-generated-by-families-of-elements-groups.mdᵉ)
theᵉ [commutators](group-theory.commutators-of-elements-groups.mdᵉ) ofᵉ `G`.ᵉ

## Definitions

### The commutator subgroup of a group

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  family-of-commutators-Groupᵉ :
    type-Groupᵉ Gᵉ ×ᵉ type-Groupᵉ Gᵉ → type-Groupᵉ Gᵉ
  family-of-commutators-Groupᵉ xᵉ =
    commutator-Groupᵉ Gᵉ (pr1ᵉ xᵉ) (pr2ᵉ xᵉ)

  commutator-subgroup-Groupᵉ : Subgroupᵉ lᵉ Gᵉ
  commutator-subgroup-Groupᵉ =
    subgroup-family-of-elements-Groupᵉ Gᵉ family-of-commutators-Groupᵉ

  generating-subset-commutator-subgroup-Groupᵉ : subset-Groupᵉ lᵉ Gᵉ
  generating-subset-commutator-subgroup-Groupᵉ =
    generating-subset-subgroup-family-of-elements-Groupᵉ Gᵉ
      family-of-commutators-Groupᵉ

  subset-commutator-subgroup-Groupᵉ : subset-Groupᵉ lᵉ Gᵉ
  subset-commutator-subgroup-Groupᵉ =
    subset-subgroup-family-of-elements-Groupᵉ Gᵉ family-of-commutators-Groupᵉ

  is-in-commutator-subgroup-Groupᵉ : type-Groupᵉ Gᵉ → UUᵉ lᵉ
  is-in-commutator-subgroup-Groupᵉ =
    is-in-subgroup-family-of-elements-Groupᵉ Gᵉ family-of-commutators-Groupᵉ

  is-closed-under-eq-commutator-subgroup-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} → is-in-commutator-subgroup-Groupᵉ xᵉ →
    xᵉ ＝ᵉ yᵉ → is-in-commutator-subgroup-Groupᵉ yᵉ
  is-closed-under-eq-commutator-subgroup-Groupᵉ =
    is-closed-under-eq-subgroup-family-of-elements-Groupᵉ Gᵉ
      family-of-commutators-Groupᵉ

  is-closed-under-eq-commutator-subgroup-Group'ᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} → is-in-commutator-subgroup-Groupᵉ yᵉ →
    xᵉ ＝ᵉ yᵉ → is-in-commutator-subgroup-Groupᵉ xᵉ
  is-closed-under-eq-commutator-subgroup-Group'ᵉ =
    is-closed-under-eq-subgroup-family-of-elements-Group'ᵉ Gᵉ
      family-of-commutators-Groupᵉ

  contains-unit-commutator-subgroup-Groupᵉ :
    contains-unit-subset-Groupᵉ Gᵉ subset-commutator-subgroup-Groupᵉ
  contains-unit-commutator-subgroup-Groupᵉ =
    contains-unit-subgroup-family-of-elements-Groupᵉ Gᵉ
      family-of-commutators-Groupᵉ

  is-closed-under-multiplication-commutator-subgroup-Groupᵉ :
    is-closed-under-multiplication-subset-Groupᵉ Gᵉ
      subset-commutator-subgroup-Groupᵉ
  is-closed-under-multiplication-commutator-subgroup-Groupᵉ =
    is-closed-under-multiplication-subgroup-family-of-elements-Groupᵉ Gᵉ
      family-of-commutators-Groupᵉ

  is-closed-under-inverses-commutator-subgroup-Groupᵉ :
    is-closed-under-inverses-subset-Groupᵉ Gᵉ
      subset-commutator-subgroup-Groupᵉ
  is-closed-under-inverses-commutator-subgroup-Groupᵉ =
    is-closed-under-inverses-subgroup-family-of-elements-Groupᵉ Gᵉ
      family-of-commutators-Groupᵉ

  contains-commutator-commutator-subgroup-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    is-in-commutator-subgroup-Groupᵉ (commutator-Groupᵉ Gᵉ xᵉ yᵉ)
  contains-commutator-commutator-subgroup-Groupᵉ xᵉ yᵉ =
    contains-element-subgroup-family-of-elements-Groupᵉ Gᵉ
      ( family-of-commutators-Groupᵉ)
      ( xᵉ ,ᵉ yᵉ)

  is-subgroup-generated-by-family-of-commutators-commutator-subgroup-Groupᵉ :
    is-subgroup-generated-by-family-of-elements-Groupᵉ Gᵉ
      family-of-commutators-Groupᵉ
      commutator-subgroup-Groupᵉ
  is-subgroup-generated-by-family-of-commutators-commutator-subgroup-Groupᵉ =
    is-subgroup-generated-by-family-of-elements-subgroup-family-of-elements-Groupᵉ
      ( Gᵉ)
      ( family-of-commutators-Groupᵉ)

  abstract
    is-closed-under-conjugation-generating-subset-commutator-subgroup-Groupᵉ :
      is-closed-under-conjugation-subset-Groupᵉ Gᵉ
        generating-subset-commutator-subgroup-Groupᵉ
    is-closed-under-conjugation-generating-subset-commutator-subgroup-Groupᵉ
      xᵉ yᵉ Hᵉ =
      apply-universal-property-trunc-Propᵉ Hᵉ
        ( generating-subset-commutator-subgroup-Groupᵉ (conjugation-Groupᵉ Gᵉ xᵉ yᵉ))
        ( λ where
          ( (yᵉ ,ᵉ zᵉ) ,ᵉ reflᵉ) →
            intro-existsᵉ
              ( conjugation-Groupᵉ Gᵉ xᵉ yᵉ ,ᵉ conjugation-Groupᵉ Gᵉ xᵉ zᵉ)
              ( invᵉ (distributive-conjugation-commutator-Groupᵉ Gᵉ xᵉ yᵉ zᵉ)))

  abstract
    is-normal-commutator-subgroup-Groupᵉ :
      is-normal-Subgroupᵉ Gᵉ commutator-subgroup-Groupᵉ
    is-normal-commutator-subgroup-Groupᵉ =
      is-normal-is-closed-under-conjugation-subgroup-subset-Groupᵉ Gᵉ
        generating-subset-commutator-subgroup-Groupᵉ
        is-closed-under-conjugation-generating-subset-commutator-subgroup-Groupᵉ

  commutator-normal-subgroup-Groupᵉ : Normal-Subgroupᵉ lᵉ Gᵉ
  pr1ᵉ commutator-normal-subgroup-Groupᵉ = commutator-subgroup-Groupᵉ
  pr2ᵉ commutator-normal-subgroup-Groupᵉ = is-normal-commutator-subgroup-Groupᵉ
```

## Properties

### Every group homomorphism `f : G → H` maps `[G,G]` to `[H,H]`

Thereᵉ areᵉ twoᵉ equivalentᵉ waysᵉ to expressᵉ thisᵉ factᵉ:

1.ᵉ Theᵉ [image](group-theory.images-of-group-homomorphisms.mdᵉ) `imᵉ fᵉ [G,G]`ᵉ ofᵉ
   theᵉ commutatorᵉ subgroupᵉ ofᵉ `G`ᵉ isᵉ containedᵉ in theᵉ commutatorᵉ subgroupᵉ ofᵉ
   `H`.ᵉ
2.ᵉ Theᵉ commutatorᵉ subgroupᵉ ofᵉ `G`ᵉ isᵉ containedᵉ in theᵉ
   [pullback](group-theory.pullbacks-subgroups.mdᵉ) ofᵉ theᵉ commutatorᵉ subgroupᵉ
   `[H,H]`ᵉ alongᵉ theᵉ [groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ)
   `f`.ᵉ

Indeed,ᵉ byᵉ theᵉ image-pullbackᵉ
[Galoisᵉ connection](order-theory.galois-connections-large-posets.mdᵉ) thereᵉ isᵉ aᵉ
[logicalᵉ equivalence](foundation.logical-equivalences.mdᵉ)

```text
  (imᵉ fᵉ [G,Gᵉ] ⊆ᵉ [H,Hᵉ]) ↔ᵉ ([G,Gᵉ] ⊆ᵉ pullbackᵉ fᵉ [H,H]).ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  contains-image-commutator-subgroup-hom-Groupᵉ :
    leq-Subgroupᵉ Hᵉ
      ( im-hom-Subgroupᵉ Gᵉ Hᵉ fᵉ (commutator-subgroup-Groupᵉ Gᵉ))
      ( commutator-subgroup-Groupᵉ Hᵉ)
  contains-image-commutator-subgroup-hom-Groupᵉ =
    leq-subgroup-is-subgroup-generated-by-family-of-elements-Groupᵉ Hᵉ
      ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ ∘ᵉ family-of-commutators-Groupᵉ Gᵉ)
      ( im-hom-Subgroupᵉ Gᵉ Hᵉ fᵉ (commutator-subgroup-Groupᵉ Gᵉ))
      ( is-subgroup-generated-by-family-of-elements-image-subgroup-family-of-elements-Groupᵉ
        ( Gᵉ)
        ( Hᵉ)
        ( fᵉ)
        ( family-of-commutators-Groupᵉ Gᵉ))
      ( commutator-subgroup-Groupᵉ Hᵉ)
      ( λ xᵉ →
        is-closed-under-eq-commutator-subgroup-Group'ᵉ Hᵉ
          ( contains-commutator-commutator-subgroup-Groupᵉ Hᵉ _ _)
          ( preserves-commutator-hom-Groupᵉ Gᵉ Hᵉ fᵉ))

  preserves-commutator-subgroup-hom-Groupᵉ :
    leq-Subgroupᵉ Gᵉ
      ( commutator-subgroup-Groupᵉ Gᵉ)
      ( pullback-Subgroupᵉ Gᵉ Hᵉ fᵉ (commutator-subgroup-Groupᵉ Hᵉ))
  preserves-commutator-subgroup-hom-Groupᵉ =
    forward-implication-is-image-subgroup-im-hom-Subgroupᵉ Gᵉ Hᵉ fᵉ
      ( commutator-subgroup-Groupᵉ Gᵉ)
      ( commutator-subgroup-Groupᵉ Hᵉ)
      ( contains-image-commutator-subgroup-hom-Groupᵉ)
```

## See also

-ᵉ Theᵉ factᵉ thatᵉ theᵉ commutatorᵉ subgroupᵉ isᵉ
  [trivial](group-theory.trivial-subgroups.mdᵉ) ifᵉ andᵉ onlyᵉ ifᵉ theᵉ ambientᵉ groupᵉ
  isᵉ abelianᵉ isᵉ recordedᵉ in
  [`group-theory.abelian-groups`](group-theory.abelian-groups.md).ᵉ

## External links

-ᵉ [Commutatorᵉ subgroup](https://ncatlab.org/nlab/show/commutator%20subgroupᵉ) atᵉ
  $n$Labᵉ
-ᵉ [Commutatorᵉ subgroup](https://www.wikidata.org/wiki/Q522216ᵉ) atᵉ Wikidataᵉ
-ᵉ [Commutatorᵉ subgroup](https://en.wikipedia.org/wiki/Commutator_subgroupᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [Commutatorᵉ subgroup](https://mathworld.wolfram.com/CommutatorSubgroup.htmlᵉ)
  atᵉ Wolframᵉ Mathworldᵉ