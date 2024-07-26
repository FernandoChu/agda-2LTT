# Normal cores of subgroups

```agda
module group-theory.normal-cores-subgroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.intersections-subtypesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-mapsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.conjugationᵉ
open import group-theory.groupsᵉ
open import group-theory.normal-subgroupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subsets-groupsᵉ

open import order-theory.galois-connections-large-posetsᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
```

</details>

## Idea

Considerᵉ aᵉ [subgroup](group-theory.subgroups.mdᵉ) `H`ᵉ ofᵉ aᵉ
[group](group-theory.groups.mdᵉ) `G`.ᵉ Theᵉ **normalᵉ core**ᵉ ofᵉ `H`ᵉ isᵉ theᵉ largestᵉ
[normalᵉ subgroup](group-theory.normal-subgroups.mdᵉ) ofᵉ `G`ᵉ thatᵉ isᵉ containedᵉ in
`H`.ᵉ Itᵉ isᵉ equivalentlyᵉ describedᵉ asᵉ theᵉ intersectionᵉ ofᵉ allᵉ
[conjugates](group-theory.conjugation.mdᵉ) ofᵉ `H`.ᵉ

Inᵉ otherᵉ words,ᵉ theᵉ normalᵉ coreᵉ operationᵉ isᵉ theᵉ upperᵉ adjointᵉ in aᵉ
[Galoisᵉ connection](order-theory.galois-connections-large-posets.mdᵉ) betweenᵉ theᵉ
[largeᵉ poset](order-theory.large-posets.mdᵉ) ofᵉ subgroupsᵉ ofᵉ `G`ᵉ andᵉ normalᵉ
subgroupsᵉ ofᵉ `G`.ᵉ Theᵉ lowerᵉ adjointᵉ ofᵉ thisᵉ Galoisᵉ connectionᵉ isᵉ theᵉ inclusionᵉ
functionᵉ fromᵉ normalᵉ subgroupsᵉ to subgroupsᵉ ofᵉ `G`.ᵉ

Noteᵉ: Theᵉ normalᵉ coreᵉ shouldᵉ notᵉ beᵉ confusedᵉ with theᵉ
[normalizer](group-theory.normalizer-subgroups.mdᵉ) ofᵉ aᵉ subgroup,ᵉ orᵉ with theᵉ
[normalᵉ closure](group-theory.normal-closures-subgroups.mdᵉ) ofᵉ aᵉ subgroup.ᵉ

## Definitions

### The universal property of the normal core

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  is-normal-core-Subgroupᵉ :
    {l3ᵉ : Level} (Nᵉ : Normal-Subgroupᵉ l3ᵉ Gᵉ) → UUωᵉ
  is-normal-core-Subgroupᵉ Nᵉ =
    {lᵉ : Level} (Mᵉ : Normal-Subgroupᵉ lᵉ Gᵉ) →
    leq-Subgroupᵉ Gᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Mᵉ) Hᵉ ↔ᵉ leq-Normal-Subgroupᵉ Gᵉ Mᵉ Nᵉ
```

### The construction of the normal core

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  subset-normal-core-Subgroupᵉ : subset-Groupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
  subset-normal-core-Subgroupᵉ =
    intersection-family-of-subtypesᵉ
      ( λ (xᵉ : type-Groupᵉ Gᵉ) →
        fiber-emb-Propᵉ
          ( comp-embᵉ
            ( emb-equivᵉ (equiv-conjugation-Groupᵉ Gᵉ xᵉ))
            ( emb-inclusion-Subgroupᵉ Gᵉ Hᵉ)))

  is-in-normal-core-Subgroupᵉ : type-Groupᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-in-normal-core-Subgroupᵉ =
    is-in-subtypeᵉ subset-normal-core-Subgroupᵉ

  is-closed-under-eq-normal-core-Subgroupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} → is-in-normal-core-Subgroupᵉ xᵉ →
    xᵉ ＝ᵉ yᵉ → is-in-normal-core-Subgroupᵉ yᵉ
  is-closed-under-eq-normal-core-Subgroupᵉ =
    is-closed-under-eq-subtypeᵉ subset-normal-core-Subgroupᵉ

  is-closed-under-eq-normal-core-Subgroup'ᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} → is-in-normal-core-Subgroupᵉ yᵉ →
    xᵉ ＝ᵉ yᵉ → is-in-normal-core-Subgroupᵉ xᵉ
  is-closed-under-eq-normal-core-Subgroup'ᵉ =
    is-closed-under-eq-subtype'ᵉ subset-normal-core-Subgroupᵉ

  contains-unit-normal-core-Subgroupᵉ :
    contains-unit-subset-Groupᵉ Gᵉ subset-normal-core-Subgroupᵉ
  pr1ᵉ (contains-unit-normal-core-Subgroupᵉ xᵉ) = unit-Subgroupᵉ Gᵉ Hᵉ
  pr2ᵉ (contains-unit-normal-core-Subgroupᵉ xᵉ) = conjugation-unit-Groupᵉ Gᵉ xᵉ

  is-closed-under-multiplication-normal-core-Subgroupᵉ :
    is-closed-under-multiplication-subset-Groupᵉ Gᵉ subset-normal-core-Subgroupᵉ
  pr1ᵉ (is-closed-under-multiplication-normal-core-Subgroupᵉ uᵉ vᵉ zᵉ) =
    mul-Subgroupᵉ Gᵉ Hᵉ (pr1ᵉ (uᵉ zᵉ)) (pr1ᵉ (vᵉ zᵉ))
  pr2ᵉ (is-closed-under-multiplication-normal-core-Subgroupᵉ uᵉ vᵉ zᵉ) =
    ( distributive-conjugation-mul-Groupᵉ Gᵉ zᵉ
      ( inclusion-Subgroupᵉ Gᵉ Hᵉ (pr1ᵉ (uᵉ zᵉ)))
      ( inclusion-Subgroupᵉ Gᵉ Hᵉ (pr1ᵉ (vᵉ zᵉ)))) ∙ᵉ
    ( ap-mul-Groupᵉ Gᵉ (pr2ᵉ (uᵉ zᵉ)) (pr2ᵉ (vᵉ zᵉ)))

  is-closed-under-inverses-normal-core-Subgroupᵉ :
    is-closed-under-inverses-subset-Groupᵉ Gᵉ subset-normal-core-Subgroupᵉ
  pr1ᵉ (is-closed-under-inverses-normal-core-Subgroupᵉ uᵉ zᵉ) =
    inv-Subgroupᵉ Gᵉ Hᵉ (pr1ᵉ (uᵉ zᵉ))
  pr2ᵉ (is-closed-under-inverses-normal-core-Subgroupᵉ uᵉ zᵉ) =
    ( conjugation-inv-Groupᵉ Gᵉ zᵉ (inclusion-Subgroupᵉ Gᵉ Hᵉ (pr1ᵉ (uᵉ zᵉ)))) ∙ᵉ
    ( apᵉ (inv-Groupᵉ Gᵉ) (pr2ᵉ (uᵉ zᵉ)))

  subgroup-normal-core-Subgroupᵉ : Subgroupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
  pr1ᵉ subgroup-normal-core-Subgroupᵉ =
    subset-normal-core-Subgroupᵉ
  pr1ᵉ (pr2ᵉ subgroup-normal-core-Subgroupᵉ) =
    contains-unit-normal-core-Subgroupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ subgroup-normal-core-Subgroupᵉ)) =
    is-closed-under-multiplication-normal-core-Subgroupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ subgroup-normal-core-Subgroupᵉ)) =
    is-closed-under-inverses-normal-core-Subgroupᵉ

  is-normal-normal-core-Subgroupᵉ :
    is-normal-Subgroupᵉ Gᵉ subgroup-normal-core-Subgroupᵉ
  pr1ᵉ (is-normal-normal-core-Subgroupᵉ xᵉ (yᵉ ,ᵉ uᵉ) zᵉ) =
    pr1ᵉ (uᵉ (left-div-Groupᵉ Gᵉ xᵉ zᵉ))
  pr2ᵉ (is-normal-normal-core-Subgroupᵉ xᵉ (yᵉ ,ᵉ uᵉ) zᵉ) =
    transpose-eq-conjugation-Group'ᵉ Gᵉ
      ( ( invᵉ (compute-conjugation-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) zᵉ _)) ∙ᵉ
        ( pr2ᵉ (uᵉ _)))

  normal-core-Subgroupᵉ : Normal-Subgroupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
  pr1ᵉ normal-core-Subgroupᵉ = subgroup-normal-core-Subgroupᵉ
  pr2ᵉ normal-core-Subgroupᵉ = is-normal-normal-core-Subgroupᵉ

  is-contained-in-subgroup-normal-core-Subgroupᵉ :
    leq-Subgroupᵉ Gᵉ subgroup-normal-core-Subgroupᵉ Hᵉ
  is-contained-in-subgroup-normal-core-Subgroupᵉ xᵉ hᵉ =
    is-closed-under-eq-Subgroupᵉ Gᵉ Hᵉ
      ( is-in-subgroup-inclusion-Subgroupᵉ Gᵉ Hᵉ (pr1ᵉ (hᵉ (unit-Groupᵉ Gᵉ))))
      ( ( invᵉ
          ( compute-conjugation-unit-Groupᵉ Gᵉ
            ( inclusion-Subgroupᵉ Gᵉ Hᵉ (pr1ᵉ (hᵉ (unit-Groupᵉ Gᵉ)))))) ∙ᵉ
        ( pr2ᵉ (hᵉ (unit-Groupᵉ Gᵉ))))

  forward-implication-is-normal-core-normal-core-Subgroupᵉ :
    {lᵉ : Level} (Nᵉ : Normal-Subgroupᵉ lᵉ Gᵉ) →
    leq-Subgroupᵉ Gᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ) Hᵉ →
    leq-Normal-Subgroupᵉ Gᵉ Nᵉ normal-core-Subgroupᵉ
  pr1ᵉ
    ( pr1ᵉ
      ( forward-implication-is-normal-core-normal-core-Subgroupᵉ Nᵉ uᵉ xᵉ nᵉ yᵉ)) =
    conjugation-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ yᵉ) xᵉ
  pr2ᵉ
    ( pr1ᵉ
      ( forward-implication-is-normal-core-normal-core-Subgroupᵉ Nᵉ uᵉ xᵉ nᵉ yᵉ)) =
    uᵉ ( conjugation-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ yᵉ) xᵉ)
      ( (is-normal-Normal-Subgroupᵉ Gᵉ Nᵉ (inv-Groupᵉ Gᵉ yᵉ) xᵉ nᵉ))
  pr2ᵉ (forward-implication-is-normal-core-normal-core-Subgroupᵉ Nᵉ uᵉ xᵉ nᵉ yᵉ) =
    is-section-conjugation-inv-Groupᵉ Gᵉ yᵉ xᵉ

  backward-implication-is-normal-core-normal-core-Subgroupᵉ :
    {lᵉ : Level} (Nᵉ : Normal-Subgroupᵉ lᵉ Gᵉ) →
    leq-Normal-Subgroupᵉ Gᵉ Nᵉ normal-core-Subgroupᵉ →
    leq-Subgroupᵉ Gᵉ (subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ) Hᵉ
  backward-implication-is-normal-core-normal-core-Subgroupᵉ Nᵉ =
    transitive-leq-Subgroupᵉ Gᵉ
      ( subgroup-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( subgroup-normal-core-Subgroupᵉ)
      ( Hᵉ)
      ( is-contained-in-subgroup-normal-core-Subgroupᵉ)

  is-normal-core-normal-core-Subgroupᵉ :
    is-normal-core-Subgroupᵉ Gᵉ Hᵉ normal-core-Subgroupᵉ
  pr1ᵉ (is-normal-core-normal-core-Subgroupᵉ Nᵉ) =
    forward-implication-is-normal-core-normal-core-Subgroupᵉ Nᵉ
  pr2ᵉ (is-normal-core-normal-core-Subgroupᵉ Nᵉ) =
    backward-implication-is-normal-core-normal-core-Subgroupᵉ Nᵉ
```

### The normal core Galois connection

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  preserves-order-normal-core-Subgroupᵉ :
    {l2ᵉ l3ᵉ : Level} (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ) (Kᵉ : Subgroupᵉ l3ᵉ Gᵉ) →
    leq-Subgroupᵉ Gᵉ Hᵉ Kᵉ →
    leq-Normal-Subgroupᵉ Gᵉ
      ( normal-core-Subgroupᵉ Gᵉ Hᵉ)
      ( normal-core-Subgroupᵉ Gᵉ Kᵉ)
  preserves-order-normal-core-Subgroupᵉ Hᵉ Kᵉ uᵉ =
    forward-implication-is-normal-core-normal-core-Subgroupᵉ Gᵉ Kᵉ
      ( normal-core-Subgroupᵉ Gᵉ Hᵉ)
      ( transitive-leq-Subgroupᵉ Gᵉ
        ( subgroup-normal-core-Subgroupᵉ Gᵉ Hᵉ)
        ( Hᵉ)
        ( Kᵉ)
        ( uᵉ)
        ( is-contained-in-subgroup-normal-core-Subgroupᵉ Gᵉ Hᵉ))

  normal-core-subgroup-hom-Large-Posetᵉ :
    hom-Large-Posetᵉ
      ( λ l2ᵉ → l1ᵉ ⊔ l2ᵉ)
      ( Subgroup-Large-Posetᵉ Gᵉ)
      ( Normal-Subgroup-Large-Posetᵉ Gᵉ)
  normal-core-subgroup-hom-Large-Posetᵉ =
    make-hom-Large-Preorderᵉ
      ( normal-core-Subgroupᵉ Gᵉ)
      ( preserves-order-normal-core-Subgroupᵉ)

  normal-core-subgroup-Galois-Connectionᵉ :
    galois-connection-Large-Posetᵉ
      ( λ lᵉ → lᵉ)
      ( λ l2ᵉ → l1ᵉ ⊔ l2ᵉ)
      ( Normal-Subgroup-Large-Posetᵉ Gᵉ)
      ( Subgroup-Large-Posetᵉ Gᵉ)
  lower-adjoint-galois-connection-Large-Posetᵉ
    normal-core-subgroup-Galois-Connectionᵉ =
    subgroup-normal-subgroup-hom-Large-Posetᵉ Gᵉ
  upper-adjoint-galois-connection-Large-Posetᵉ
    normal-core-subgroup-Galois-Connectionᵉ =
    normal-core-subgroup-hom-Large-Posetᵉ
  adjoint-relation-galois-connection-Large-Posetᵉ
    normal-core-subgroup-Galois-Connectionᵉ Nᵉ Hᵉ =
    is-normal-core-normal-core-Subgroupᵉ Gᵉ Hᵉ Nᵉ
```

## See also

-ᵉ [Centralizerᵉ subgroups](group-theory.centralizer-subgroups.mdᵉ)
-ᵉ [Normalᵉ closuresᵉ ofᵉ subgroups](group-theory.normal-closures-subgroups.mdᵉ)
-ᵉ [Normalizersᵉ ofᵉ subgroups](group-theory.normalizer-subgroups.mdᵉ)