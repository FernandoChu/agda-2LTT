# Normal closures of subgroups

```agda
module group-theory.normal-closures-subgroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.conjugationᵉ
open import group-theory.groupsᵉ
open import group-theory.normal-subgroupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subgroups-generated-by-subsets-groupsᵉ
open import group-theory.subsets-groupsᵉ

open import order-theory.galois-connections-large-posetsᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
```

</details>

## Idea

Considerᵉ aᵉ [subgroup](group-theory.subgroups.mdᵉ) `H`ᵉ ofᵉ aᵉ
[group](group-theory.groups.mdᵉ) `G`.ᵉ Theᵉ **normalᵉ closure**ᵉ `jH`ᵉ ofᵉ `G`ᵉ isᵉ theᵉ
leastᵉ [normalᵉ subgroup](group-theory.normal-subgroups.mdᵉ) ofᵉ `G`ᵉ thatᵉ containsᵉ
`H`.ᵉ Theᵉ normalᵉ closureᵉ ofᵉ `H`ᵉ isᵉ theᵉ
[subgroupᵉ generatedᵉ by](group-theory.subgroups-generated-by-subsets-groups.mdᵉ)
allᵉ theᵉ [conjugates](group-theory.conjugation.mdᵉ) ofᵉ elementsᵉ ofᵉ `H`.ᵉ

Inᵉ otherᵉ words,ᵉ theᵉ normalᵉ closureᵉ operationᵉ isᵉ theᵉ lowerᵉ adjointᵉ in aᵉ
[Galoisᵉ connection](order-theory.galois-connections-large-posets.mdᵉ) betweenᵉ theᵉ
[largeᵉ poset](order-theory.large-posets.mdᵉ) ofᵉ normalᵉ subgroupsᵉ ofᵉ `G`ᵉ andᵉ
subgroupsᵉ ofᵉ `G`.ᵉ Theᵉ upperᵉ adjointᵉ ofᵉ thisᵉ Galoisᵉ connectionᵉ isᵉ theᵉ inclusionᵉ
functionᵉ fromᵉ normalᵉ subgroupsᵉ to subgroupsᵉ ofᵉ `G`.ᵉ

Noteᵉ: Theᵉ normalᵉ closureᵉ shouldᵉ notᵉ beᵉ confusedᵉ with theᵉ
[normalizer](group-theory.normalizer-subgroups.mdᵉ) ofᵉ aᵉ subgroup,ᵉ orᵉ with theᵉ
[normalᵉ core](group-theory.normal-cores-subgroups.mdᵉ) ofᵉ aᵉ subgroup.ᵉ

## Definitions

### The universal property of the normal closure

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  (Nᵉ : Normal-Subgroupᵉ l3ᵉ Gᵉ)
  where

  is-normal-closure-Subgroupᵉ : UUωᵉ
  is-normal-closure-Subgroupᵉ =
    {lᵉ : Level} (Mᵉ : Normal-Subgroupᵉ lᵉ Gᵉ) →
    leq-Normal-Subgroupᵉ Gᵉ Nᵉ Mᵉ ↔ᵉ leq-Subgroupᵉ Gᵉ Hᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Mᵉ)
```

### The construction of the normal closure

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  generating-subset-normal-closure-Subgroupᵉ : subset-Groupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
  generating-subset-normal-closure-Subgroupᵉ xᵉ =
    exists-structure-Propᵉ
      ( type-Groupᵉ Gᵉ)
      ( λ yᵉ → fiberᵉ (conjugation-Groupᵉ Gᵉ yᵉ ∘ᵉ inclusion-Subgroupᵉ Gᵉ Hᵉ) xᵉ)

  contains-subgroup-generating-subset-normal-closure-Subgroupᵉ :
    subset-Subgroupᵉ Gᵉ Hᵉ ⊆ᵉ generating-subset-normal-closure-Subgroupᵉ
  contains-subgroup-generating-subset-normal-closure-Subgroupᵉ xᵉ hᵉ =
    unit-trunc-Propᵉ
      ( unit-Groupᵉ Gᵉ ,ᵉ (xᵉ ,ᵉ hᵉ) ,ᵉ compute-conjugation-unit-Groupᵉ Gᵉ xᵉ)

  abstract
    is-closed-under-conjugation-generating-subset-normal-closure-Subgroupᵉ :
      is-closed-under-conjugation-subset-Groupᵉ Gᵉ
        generating-subset-normal-closure-Subgroupᵉ
    is-closed-under-conjugation-generating-subset-normal-closure-Subgroupᵉ
      xᵉ yᵉ sᵉ =
      apply-universal-property-trunc-Propᵉ sᵉ
        ( generating-subset-normal-closure-Subgroupᵉ (conjugation-Groupᵉ Gᵉ xᵉ yᵉ))
        ( λ where
          ( zᵉ ,ᵉ hᵉ ,ᵉ reflᵉ) →
            unit-trunc-Propᵉ
              ( mul-Groupᵉ Gᵉ xᵉ zᵉ ,ᵉ
                hᵉ ,ᵉ
                compute-conjugation-mul-Groupᵉ Gᵉ xᵉ zᵉ (pr1ᵉ hᵉ)))

  subgroup-normal-closure-Subgroupᵉ : Subgroupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
  subgroup-normal-closure-Subgroupᵉ =
    subgroup-subset-Groupᵉ Gᵉ generating-subset-normal-closure-Subgroupᵉ

  subset-normal-closure-Subgroupᵉ : subset-Groupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
  subset-normal-closure-Subgroupᵉ =
    subset-Subgroupᵉ Gᵉ subgroup-normal-closure-Subgroupᵉ

  is-in-normal-closure-Subgroupᵉ : type-Groupᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-in-normal-closure-Subgroupᵉ =
    is-in-Subgroupᵉ Gᵉ subgroup-normal-closure-Subgroupᵉ

  is-closed-under-eq-normal-closure-Subgroupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} → is-in-normal-closure-Subgroupᵉ xᵉ → xᵉ ＝ᵉ yᵉ →
    is-in-normal-closure-Subgroupᵉ yᵉ
  is-closed-under-eq-normal-closure-Subgroupᵉ =
    is-closed-under-eq-Subgroupᵉ Gᵉ subgroup-normal-closure-Subgroupᵉ

  is-closed-under-eq-normal-closure-Subgroup'ᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} → is-in-normal-closure-Subgroupᵉ yᵉ → xᵉ ＝ᵉ yᵉ →
    is-in-normal-closure-Subgroupᵉ xᵉ
  is-closed-under-eq-normal-closure-Subgroup'ᵉ =
    is-closed-under-eq-Subgroup'ᵉ Gᵉ subgroup-normal-closure-Subgroupᵉ

  contains-unit-normal-closure-Subgroupᵉ :
    contains-unit-subset-Groupᵉ Gᵉ subset-normal-closure-Subgroupᵉ
  contains-unit-normal-closure-Subgroupᵉ =
    contains-unit-Subgroupᵉ Gᵉ subgroup-normal-closure-Subgroupᵉ

  is-closed-under-multiplication-normal-closure-Subgroupᵉ :
    is-closed-under-multiplication-subset-Groupᵉ Gᵉ subset-normal-closure-Subgroupᵉ
  is-closed-under-multiplication-normal-closure-Subgroupᵉ =
    is-closed-under-multiplication-Subgroupᵉ Gᵉ subgroup-normal-closure-Subgroupᵉ

  is-closed-under-inverses-normal-closure-Subgroupᵉ :
    is-closed-under-inverses-subset-Groupᵉ Gᵉ subset-normal-closure-Subgroupᵉ
  is-closed-under-inverses-normal-closure-Subgroupᵉ =
    is-closed-under-inverses-Subgroupᵉ Gᵉ subgroup-normal-closure-Subgroupᵉ

  contains-generating-subset-normal-closure-Subgroupᵉ :
    generating-subset-normal-closure-Subgroupᵉ ⊆ᵉ subset-normal-closure-Subgroupᵉ
  contains-generating-subset-normal-closure-Subgroupᵉ =
    contains-subset-subgroup-subset-Groupᵉ Gᵉ
      generating-subset-normal-closure-Subgroupᵉ

  is-subgroup-generated-by-generating-subset-normal-closure-Subgroupᵉ :
    is-subgroup-generated-by-subset-Groupᵉ Gᵉ
      generating-subset-normal-closure-Subgroupᵉ
      subgroup-normal-closure-Subgroupᵉ
  is-subgroup-generated-by-generating-subset-normal-closure-Subgroupᵉ =
    is-subgroup-generated-by-subset-subgroup-subset-Groupᵉ Gᵉ
      generating-subset-normal-closure-Subgroupᵉ

  is-normal-subgroup-normal-closure-Subgroupᵉ :
    is-normal-Subgroupᵉ Gᵉ subgroup-normal-closure-Subgroupᵉ
  is-normal-subgroup-normal-closure-Subgroupᵉ =
    is-normal-is-closed-under-conjugation-subgroup-subset-Groupᵉ Gᵉ
      generating-subset-normal-closure-Subgroupᵉ
      is-closed-under-conjugation-generating-subset-normal-closure-Subgroupᵉ

  normal-closure-Subgroupᵉ : Normal-Subgroupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
  pr1ᵉ normal-closure-Subgroupᵉ = subgroup-normal-closure-Subgroupᵉ
  pr2ᵉ normal-closure-Subgroupᵉ = is-normal-subgroup-normal-closure-Subgroupᵉ

  contains-subgroup-normal-closure-Subgroupᵉ :
    leq-Subgroupᵉ Gᵉ Hᵉ subgroup-normal-closure-Subgroupᵉ
  contains-subgroup-normal-closure-Subgroupᵉ =
    transitive-leq-subtypeᵉ
      ( subset-Subgroupᵉ Gᵉ Hᵉ)
      ( generating-subset-normal-closure-Subgroupᵉ)
      ( subset-normal-closure-Subgroupᵉ)
      ( contains-subset-subgroup-subset-Groupᵉ Gᵉ
        generating-subset-normal-closure-Subgroupᵉ)
      ( contains-subgroup-generating-subset-normal-closure-Subgroupᵉ)

  forward-implication-is-normal-closure-normal-closure-Subgroupᵉ :
    {lᵉ : Level} (Nᵉ : Normal-Subgroupᵉ lᵉ Gᵉ) →
    leq-Normal-Subgroupᵉ Gᵉ normal-closure-Subgroupᵉ Nᵉ →
    leq-Subgroupᵉ Gᵉ Hᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ)
  forward-implication-is-normal-closure-normal-closure-Subgroupᵉ Nᵉ uᵉ =
    transitive-leq-subtypeᵉ
      ( subset-Subgroupᵉ Gᵉ Hᵉ)
      ( subset-normal-closure-Subgroupᵉ)
      ( subset-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( uᵉ)
      ( contains-subgroup-normal-closure-Subgroupᵉ)

  abstract
    contains-generating-subset-normal-closure-Normal-Subgroupᵉ :
      {lᵉ : Level} (Nᵉ : Normal-Subgroupᵉ lᵉ Gᵉ) →
      leq-Subgroupᵉ Gᵉ Hᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ) →
      generating-subset-normal-closure-Subgroupᵉ ⊆ᵉ subset-Normal-Subgroupᵉ Gᵉ Nᵉ
    contains-generating-subset-normal-closure-Normal-Subgroupᵉ Nᵉ uᵉ xᵉ gᵉ =
      apply-universal-property-trunc-Propᵉ gᵉ
        ( subset-Normal-Subgroupᵉ Gᵉ Nᵉ xᵉ)
        ( λ where
          ( zᵉ ,ᵉ (yᵉ ,ᵉ hᵉ) ,ᵉ reflᵉ) → is-normal-Normal-Subgroupᵉ Gᵉ Nᵉ zᵉ yᵉ (uᵉ yᵉ hᵉ))

  backward-implication-is-normal-closure-normal-closure-Subgroupᵉ :
    {lᵉ : Level} (Nᵉ : Normal-Subgroupᵉ lᵉ Gᵉ) →
    leq-Subgroupᵉ Gᵉ Hᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ) →
    leq-Normal-Subgroupᵉ Gᵉ normal-closure-Subgroupᵉ Nᵉ
  backward-implication-is-normal-closure-normal-closure-Subgroupᵉ Nᵉ uᵉ =
    backward-implicationᵉ
      ( is-subgroup-generated-by-generating-subset-normal-closure-Subgroupᵉ
        ( subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ))
      ( contains-generating-subset-normal-closure-Normal-Subgroupᵉ Nᵉ uᵉ)

  is-normal-closure-normal-closure-Subgroupᵉ :
    is-normal-closure-Subgroupᵉ Gᵉ Hᵉ normal-closure-Subgroupᵉ
  pr1ᵉ (is-normal-closure-normal-closure-Subgroupᵉ Nᵉ) =
    forward-implication-is-normal-closure-normal-closure-Subgroupᵉ Nᵉ
  pr2ᵉ (is-normal-closure-normal-closure-Subgroupᵉ Nᵉ) =
    backward-implication-is-normal-closure-normal-closure-Subgroupᵉ Nᵉ
```

### The normal closure Galois connection

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  preserves-order-normal-closure-Subgroupᵉ :
    {l2ᵉ l3ᵉ : Level} (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ) (Kᵉ : Subgroupᵉ l3ᵉ Gᵉ) →
    leq-Subgroupᵉ Gᵉ Hᵉ Kᵉ →
    leq-Normal-Subgroupᵉ Gᵉ
      ( normal-closure-Subgroupᵉ Gᵉ Hᵉ)
      ( normal-closure-Subgroupᵉ Gᵉ Kᵉ)
  preserves-order-normal-closure-Subgroupᵉ Hᵉ Kᵉ uᵉ =
    backward-implication-is-normal-closure-normal-closure-Subgroupᵉ Gᵉ Hᵉ
      ( normal-closure-Subgroupᵉ Gᵉ Kᵉ)
      ( transitive-leq-subtypeᵉ
        ( subset-Subgroupᵉ Gᵉ Hᵉ)
        ( subset-Subgroupᵉ Gᵉ Kᵉ)
        ( subset-normal-closure-Subgroupᵉ Gᵉ Kᵉ)
        ( contains-subgroup-normal-closure-Subgroupᵉ Gᵉ Kᵉ)
        ( uᵉ))

  normal-closure-subgroup-hom-Large-Posetᵉ :
    hom-Large-Posetᵉ
      ( λ l2ᵉ → l1ᵉ ⊔ l2ᵉ)
      ( Subgroup-Large-Posetᵉ Gᵉ)
      ( Normal-Subgroup-Large-Posetᵉ Gᵉ)
  normal-closure-subgroup-hom-Large-Posetᵉ =
    make-hom-Large-Preorderᵉ
      ( normal-closure-Subgroupᵉ Gᵉ)
      ( preserves-order-normal-closure-Subgroupᵉ)

  normal-closure-Galois-Connectionᵉ :
    galois-connection-Large-Posetᵉ
      ( λ l2ᵉ → l1ᵉ ⊔ l2ᵉ)
      ( λ lᵉ → lᵉ)
      ( Subgroup-Large-Posetᵉ Gᵉ)
      ( Normal-Subgroup-Large-Posetᵉ Gᵉ)
  normal-closure-Galois-Connectionᵉ =
    make-galois-connection-Large-Posetᵉ
      ( normal-closure-subgroup-hom-Large-Posetᵉ)
      ( subgroup-normal-subgroup-hom-Large-Posetᵉ Gᵉ)
      ( λ Hᵉ Nᵉ → is-normal-closure-normal-closure-Subgroupᵉ Gᵉ Hᵉ Nᵉ)
```

## See also

-ᵉ [Centralizerᵉ subgroups](group-theory.centralizer-subgroups.mdᵉ)
-ᵉ [Normalᵉ coresᵉ ofᵉ subgroups](group-theory.normal-cores-subgroups.mdᵉ)
-ᵉ [Normalizersᵉ ofᵉ subgroups](group-theory.normalizer-subgroups.mdᵉ)