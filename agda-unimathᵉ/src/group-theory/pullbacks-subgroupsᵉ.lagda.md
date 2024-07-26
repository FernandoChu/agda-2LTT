# Pullbacks of subgroups

```agda
module group-theory.pullbacks-subgroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.powersetsᵉ
open import foundation.pullbacks-subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.conjugationᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.normal-subgroupsᵉ
open import group-theory.pullbacks-subsemigroupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subsemigroupsᵉ
open import group-theory.subsets-groupsᵉ

open import order-theory.commuting-squares-of-order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
open import order-theory.similarity-of-order-preserving-maps-large-posetsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ) `fᵉ : Gᵉ → H`ᵉ
intoᵉ aᵉ [group](group-theory.groups.mdᵉ) `H`ᵉ equippedᵉ with aᵉ
[subgroup](group-theory.subgroups.mdᵉ) `Kᵉ ≤ᵉ H`,ᵉ theᵉ **pullback**ᵉ `pullbackᵉ fᵉ K`ᵉ
ofᵉ `K`ᵉ alongᵉ `f`ᵉ isᵉ definedᵉ byᵉ substitutingᵉ `f`ᵉ in `K`.ᵉ Inᵉ otherᵉ words,ᵉ itᵉ isᵉ
theᵉ subgroupᵉ `pullbackᵉ fᵉ K`ᵉ ofᵉ `G`ᵉ consistingᵉ ofᵉ theᵉ elementsᵉ `xᵉ : G`ᵉ suchᵉ thatᵉ
`fᵉ xᵉ ∈ᵉ K`.ᵉ

## Definitions

### Pullbacks of subgroups

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  (Kᵉ : Subgroupᵉ l3ᵉ Hᵉ)
  where

  subsemigroup-pullback-Subgroupᵉ : Subsemigroupᵉ l3ᵉ (semigroup-Groupᵉ Gᵉ)
  subsemigroup-pullback-Subgroupᵉ =
    pullback-Subsemigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( fᵉ)
      ( subsemigroup-Subgroupᵉ Hᵉ Kᵉ)

  subset-pullback-Subgroupᵉ : subset-Groupᵉ l3ᵉ Gᵉ
  subset-pullback-Subgroupᵉ =
    subset-pullback-Subsemigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( fᵉ)
      ( subsemigroup-Subgroupᵉ Hᵉ Kᵉ)

  is-in-pullback-Subgroupᵉ : type-Groupᵉ Gᵉ → UUᵉ l3ᵉ
  is-in-pullback-Subgroupᵉ =
    is-in-pullback-Subsemigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( fᵉ)
      ( subsemigroup-Subgroupᵉ Hᵉ Kᵉ)

  is-closed-under-eq-pullback-Subgroupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    is-in-pullback-Subgroupᵉ xᵉ → xᵉ ＝ᵉ yᵉ → is-in-pullback-Subgroupᵉ yᵉ
  is-closed-under-eq-pullback-Subgroupᵉ =
    is-closed-under-eq-pullback-Subsemigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( fᵉ)
      ( subsemigroup-Subgroupᵉ Hᵉ Kᵉ)

  is-closed-under-eq-pullback-Subgroup'ᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    is-in-pullback-Subgroupᵉ yᵉ → xᵉ ＝ᵉ yᵉ → is-in-pullback-Subgroupᵉ xᵉ
  is-closed-under-eq-pullback-Subgroup'ᵉ =
    is-closed-under-eq-pullback-Subsemigroup'ᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( fᵉ)
      ( subsemigroup-Subgroupᵉ Hᵉ Kᵉ)

  contains-unit-pullback-Subgroupᵉ :
    contains-unit-subset-Groupᵉ Gᵉ subset-pullback-Subgroupᵉ
  contains-unit-pullback-Subgroupᵉ =
    is-closed-under-eq-Subgroup'ᵉ Hᵉ Kᵉ
      ( contains-unit-Subgroupᵉ Hᵉ Kᵉ)
      ( preserves-unit-hom-Groupᵉ Gᵉ Hᵉ fᵉ)

  is-closed-under-multiplication-pullback-Subgroupᵉ :
    is-closed-under-multiplication-subset-Groupᵉ Gᵉ subset-pullback-Subgroupᵉ
  is-closed-under-multiplication-pullback-Subgroupᵉ =
    is-closed-under-multiplication-pullback-Subsemigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( fᵉ)
      ( subsemigroup-Subgroupᵉ Hᵉ Kᵉ)

  is-closed-under-inverses-pullback-Subgroupᵉ :
    is-closed-under-inverses-subset-Groupᵉ Gᵉ subset-pullback-Subgroupᵉ
  is-closed-under-inverses-pullback-Subgroupᵉ pᵉ =
    is-closed-under-eq-Subgroup'ᵉ Hᵉ Kᵉ
      ( is-closed-under-inverses-Subgroupᵉ Hᵉ Kᵉ pᵉ)
      ( preserves-inv-hom-Groupᵉ Gᵉ Hᵉ fᵉ)

  is-subgroup-pullback-Subgroupᵉ :
    is-subgroup-subset-Groupᵉ Gᵉ subset-pullback-Subgroupᵉ
  pr1ᵉ is-subgroup-pullback-Subgroupᵉ =
    contains-unit-pullback-Subgroupᵉ
  pr1ᵉ (pr2ᵉ is-subgroup-pullback-Subgroupᵉ) =
    is-closed-under-multiplication-pullback-Subgroupᵉ
  pr2ᵉ (pr2ᵉ is-subgroup-pullback-Subgroupᵉ) =
    is-closed-under-inverses-pullback-Subgroupᵉ

  pullback-Subgroupᵉ : Subgroupᵉ l3ᵉ Gᵉ
  pr1ᵉ pullback-Subgroupᵉ = subset-pullback-Subgroupᵉ
  pr2ᵉ pullback-Subgroupᵉ = is-subgroup-pullback-Subgroupᵉ
```

### The order preserving map `pullback-Subgroup`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  preserves-order-pullback-Subgroupᵉ :
    {l3ᵉ l4ᵉ : Level} (Sᵉ : Subgroupᵉ l3ᵉ Hᵉ) (Tᵉ : Subgroupᵉ l4ᵉ Hᵉ) →
    leq-Subgroupᵉ Hᵉ Sᵉ Tᵉ →
    leq-Subgroupᵉ Gᵉ (pullback-Subgroupᵉ Gᵉ Hᵉ fᵉ Sᵉ) (pullback-Subgroupᵉ Gᵉ Hᵉ fᵉ Tᵉ)
  preserves-order-pullback-Subgroupᵉ Sᵉ Tᵉ =
    preserves-order-pullback-Subsemigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( fᵉ)
      ( subsemigroup-Subgroupᵉ Hᵉ Sᵉ)
      ( subsemigroup-Subgroupᵉ Hᵉ Tᵉ)

  pullback-subgroup-hom-large-poset-hom-Groupᵉ :
    hom-Large-Posetᵉ (λ lᵉ → lᵉ) (Subgroup-Large-Posetᵉ Hᵉ) (Subgroup-Large-Posetᵉ Gᵉ)
  map-hom-Large-Preorderᵉ pullback-subgroup-hom-large-poset-hom-Groupᵉ =
    pullback-Subgroupᵉ Gᵉ Hᵉ fᵉ
  preserves-order-hom-Large-Preorderᵉ
    pullback-subgroup-hom-large-poset-hom-Groupᵉ =
    preserves-order-pullback-Subgroupᵉ
```

## Properties

### The pullback operation commutes with the underlying subtype operation

Theᵉ squareᵉ

```text
                   pullbackᵉ fᵉ
     Subgroupᵉ Hᵉ ---------------->ᵉ Subgroupᵉ Gᵉ
         |                            |
  Kᵉ ↦ᵉ UKᵉ |                            | Kᵉ ↦ᵉ UKᵉ
         |                            |
         ∨ᵉ                            ∨ᵉ
   subset-Groupᵉ Hᵉ ------------>ᵉ subset-Groupᵉ Gᵉ
                   pullbackᵉ fᵉ
```

ofᵉ [orderᵉ preservingᵉ maps](order-theory.order-preserving-maps-large-posets.mdᵉ)
[commutes](order-theory.commuting-squares-of-order-preserving-maps-large-posets.mdᵉ)
byᵉ reflexivity.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  coherence-square-pullback-subset-Subgroupᵉ :
    coherence-square-hom-Large-Posetᵉ
      ( Subgroup-Large-Posetᵉ Hᵉ)
      ( powerset-Large-Posetᵉ (type-Groupᵉ Hᵉ))
      ( Subgroup-Large-Posetᵉ Gᵉ)
      ( powerset-Large-Posetᵉ (type-Groupᵉ Gᵉ))
      ( pullback-subgroup-hom-large-poset-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
      ( subset-subgroup-hom-large-poset-Groupᵉ Hᵉ)
      ( subset-subgroup-hom-large-poset-Groupᵉ Gᵉ)
      ( pullback-subtype-hom-Large-Posetᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ))
  coherence-square-pullback-subset-Subgroupᵉ =
    refl-sim-hom-Large-Posetᵉ
      ( Subgroup-Large-Posetᵉ Hᵉ)
      ( powerset-Large-Posetᵉ (type-Groupᵉ Gᵉ))
      ( comp-hom-Large-Posetᵉ
        ( Subgroup-Large-Posetᵉ Hᵉ)
        ( Subgroup-Large-Posetᵉ Gᵉ)
        ( powerset-Large-Posetᵉ (type-Groupᵉ Gᵉ))
        ( subset-subgroup-hom-large-poset-Groupᵉ Gᵉ)
        ( pullback-subgroup-hom-large-poset-hom-Groupᵉ Gᵉ Hᵉ fᵉ))
```

### Pullbacks of normal subgroups are normal

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  (Nᵉ : Normal-Subgroupᵉ l3ᵉ Hᵉ)
  where

  subgroup-pullback-Normal-Subgroupᵉ : Subgroupᵉ l3ᵉ Gᵉ
  subgroup-pullback-Normal-Subgroupᵉ =
    pullback-Subgroupᵉ Gᵉ Hᵉ fᵉ (subgroup-Normal-Subgroupᵉ Hᵉ Nᵉ)

  is-normal-pullback-Normal-Subgroupᵉ :
    is-normal-Subgroupᵉ Gᵉ subgroup-pullback-Normal-Subgroupᵉ
  is-normal-pullback-Normal-Subgroupᵉ xᵉ (yᵉ ,ᵉ nᵉ) =
    is-closed-under-eq-Normal-Subgroup'ᵉ Hᵉ Nᵉ
      ( is-normal-Normal-Subgroupᵉ Hᵉ Nᵉ
        ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ)
        ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ yᵉ)
        ( nᵉ))
      ( preserves-conjugation-hom-Groupᵉ Gᵉ Hᵉ fᵉ)

  pullback-Normal-Subgroupᵉ : Normal-Subgroupᵉ l3ᵉ Gᵉ
  pr1ᵉ pullback-Normal-Subgroupᵉ = subgroup-pullback-Normal-Subgroupᵉ
  pr2ᵉ pullback-Normal-Subgroupᵉ = is-normal-pullback-Normal-Subgroupᵉ
```