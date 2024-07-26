# Abelianization of groups

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module group-theory.abelianization-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.adjunctions-large-categoriesᵉ
open import category-theory.adjunctions-large-precategoriesᵉ
open import category-theory.functors-large-categoriesᵉ
open import category-theory.functors-large-precategoriesᵉ
open import category-theory.natural-transformations-functors-large-categoriesᵉ
open import category-theory.natural-transformations-functors-large-precategoriesᵉ

open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.set-quotientsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.category-of-abelian-groupsᵉ
open import group-theory.category-of-groupsᵉ
open import group-theory.commutator-subgroupsᵉ
open import group-theory.commuting-squares-of-group-homomorphismsᵉ
open import group-theory.functoriality-quotient-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-abelian-groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.normal-subgroupsᵉ
open import group-theory.nullifying-group-homomorphismsᵉ
open import group-theory.quotient-groupsᵉ
```

</details>

## Idea

Considerᵉ aᵉ [groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ)
`fᵉ : Gᵉ → A`ᵉ fromᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ intoᵉ anᵉ
[abelianᵉ group](group-theory.abelian-groups.mdᵉ) `A`.ᵉ Weᵉ sayᵉ thatᵉ `f`ᵉ **isᵉ anᵉ
abelianization**ᵉ ofᵉ `G`ᵉ ifᵉ theᵉ precompositionᵉ functionᵉ

```text
  -ᵉ ∘ᵉ fᵉ : homᵉ Aᵉ Bᵉ → homᵉ Gᵉ Bᵉ
```

isᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) forᵉ anyᵉ abelianᵉ groupᵉ `B`.ᵉ

Theᵉ **abelianization**ᵉ `Gᵃᵇ`ᵉ ofᵉ aᵉ groupᵉ `G`ᵉ alwaysᵉ exists,ᵉ andᵉ canᵉ beᵉ
constructedᵉ asᵉ theᵉ [quotientᵉ group](group-theory.quotient-groups.mdᵉ) `G/[G,G]`ᵉ
ofᵉ `G`ᵉ moduloᵉ itsᵉ [commutatorᵉ subgroup](group-theory.commutator-subgroups.md).ᵉ
Thereforeᵉ weᵉ obtainᵉ anᵉ
[adjunction](category-theory.adjunctions-large-categories.mdᵉ)

```text
  homᵉ Gᵃᵇᵉ Aᵉ ≃ᵉ homᵉ Gᵉ A,ᵉ
```

i.e.,ᵉ theᵉ abelianizationᵉ isᵉ leftᵉ adjointᵉ to theᵉ inclusionᵉ functorᵉ fromᵉ theᵉ
[categoryᵉ ofᵉ abelianᵉ groups](group-theory.category-of-abelian-groups.mdᵉ) intoᵉ
theᵉ [categoryᵉ ofᵉ groups](group-theory.category-of-groups.md).ᵉ

## Definitions

### The predicate of being an abelianization

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Aᵉ : Abᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ (group-Abᵉ Aᵉ))
  where

  is-abelianization-Groupᵉ : UUωᵉ
  is-abelianization-Groupᵉ =
    {lᵉ : Level} (Bᵉ : Abᵉ lᵉ) →
    is-equivᵉ (λ hᵉ → comp-hom-Groupᵉ Gᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) hᵉ fᵉ)
```

### The abelianization of a group

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  group-abelianization-Groupᵉ : Groupᵉ l1ᵉ
  group-abelianization-Groupᵉ =
    quotient-Groupᵉ Gᵉ (commutator-normal-subgroup-Groupᵉ Gᵉ)

  hom-abelianization-Groupᵉ : hom-Groupᵉ Gᵉ group-abelianization-Groupᵉ
  hom-abelianization-Groupᵉ =
    quotient-hom-Groupᵉ Gᵉ (commutator-normal-subgroup-Groupᵉ Gᵉ)

  set-abelianization-Groupᵉ : Setᵉ l1ᵉ
  set-abelianization-Groupᵉ = set-Groupᵉ group-abelianization-Groupᵉ

  type-abelianization-Groupᵉ : UUᵉ l1ᵉ
  type-abelianization-Groupᵉ = type-Groupᵉ group-abelianization-Groupᵉ

  zero-abelianization-Groupᵉ : type-abelianization-Groupᵉ
  zero-abelianization-Groupᵉ = unit-Groupᵉ group-abelianization-Groupᵉ

  add-abelianization-Groupᵉ :
    (xᵉ yᵉ : type-abelianization-Groupᵉ) → type-abelianization-Groupᵉ
  add-abelianization-Groupᵉ = mul-Groupᵉ group-abelianization-Groupᵉ

  neg-abelianization-Groupᵉ :
    type-abelianization-Groupᵉ → type-abelianization-Groupᵉ
  neg-abelianization-Groupᵉ = inv-Groupᵉ group-abelianization-Groupᵉ

  associative-add-abelianization-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-abelianization-Groupᵉ) →
    add-abelianization-Groupᵉ (add-abelianization-Groupᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    add-abelianization-Groupᵉ xᵉ (add-abelianization-Groupᵉ yᵉ zᵉ)
  associative-add-abelianization-Groupᵉ =
    associative-mul-Groupᵉ group-abelianization-Groupᵉ

  left-unit-law-add-abelianization-Groupᵉ :
    (xᵉ : type-abelianization-Groupᵉ) →
    add-abelianization-Groupᵉ zero-abelianization-Groupᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-abelianization-Groupᵉ =
    left-unit-law-mul-Groupᵉ group-abelianization-Groupᵉ

  right-unit-law-add-abelianization-Groupᵉ :
    (xᵉ : type-abelianization-Groupᵉ) →
    add-abelianization-Groupᵉ xᵉ zero-abelianization-Groupᵉ ＝ᵉ xᵉ
  right-unit-law-add-abelianization-Groupᵉ =
    right-unit-law-mul-Groupᵉ group-abelianization-Groupᵉ

  left-inverse-law-add-abelianization-Groupᵉ :
    (xᵉ : type-abelianization-Groupᵉ) →
    add-abelianization-Groupᵉ (neg-abelianization-Groupᵉ xᵉ) xᵉ ＝ᵉ
    zero-abelianization-Groupᵉ
  left-inverse-law-add-abelianization-Groupᵉ =
    left-inverse-law-mul-Groupᵉ group-abelianization-Groupᵉ

  right-inverse-law-add-abelianization-Groupᵉ :
    (xᵉ : type-abelianization-Groupᵉ) →
    add-abelianization-Groupᵉ xᵉ (neg-abelianization-Groupᵉ xᵉ) ＝ᵉ
    zero-abelianization-Groupᵉ
  right-inverse-law-add-abelianization-Groupᵉ =
    right-inverse-law-mul-Groupᵉ group-abelianization-Groupᵉ

  map-abelianization-Groupᵉ :
    type-Groupᵉ Gᵉ → type-abelianization-Groupᵉ
  map-abelianization-Groupᵉ =
    map-hom-Groupᵉ Gᵉ group-abelianization-Groupᵉ hom-abelianization-Groupᵉ

  compute-add-abelianization-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    add-abelianization-Groupᵉ
      ( map-abelianization-Groupᵉ xᵉ)
      ( map-abelianization-Groupᵉ yᵉ) ＝ᵉ
    map-abelianization-Groupᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ)
  compute-add-abelianization-Groupᵉ =
    compute-mul-quotient-Groupᵉ Gᵉ (commutator-normal-subgroup-Groupᵉ Gᵉ)

  abstract
    commutative-add-abelianization-Groupᵉ :
      (xᵉ yᵉ : type-abelianization-Groupᵉ) →
      add-abelianization-Groupᵉ xᵉ yᵉ ＝ᵉ add-abelianization-Groupᵉ yᵉ xᵉ
    commutative-add-abelianization-Groupᵉ =
      double-induction-quotient-Groupᵉ Gᵉ Gᵉ
        ( commutator-normal-subgroup-Groupᵉ Gᵉ)
        ( commutator-normal-subgroup-Groupᵉ Gᵉ)
        ( λ xᵉ yᵉ → Id-Propᵉ set-abelianization-Groupᵉ _ _)
        ( λ xᵉ yᵉ →
          ( compute-add-abelianization-Groupᵉ xᵉ yᵉ) ∙ᵉ
          ( apply-effectiveness-map-quotient-hom-Group'ᵉ Gᵉ
            ( commutator-normal-subgroup-Groupᵉ Gᵉ)
            ( sim-left-sim-congruence-Normal-Subgroupᵉ Gᵉ
              ( commutator-normal-subgroup-Groupᵉ Gᵉ)
              ( mul-Groupᵉ Gᵉ xᵉ yᵉ)
              ( mul-Groupᵉ Gᵉ yᵉ xᵉ)
              ( contains-commutator-commutator-subgroup-Groupᵉ Gᵉ xᵉ yᵉ))) ∙ᵉ
          ( invᵉ (compute-add-abelianization-Groupᵉ yᵉ xᵉ)))

  abelianization-Groupᵉ : Abᵉ l1ᵉ
  pr1ᵉ abelianization-Groupᵉ = group-abelianization-Groupᵉ
  pr2ᵉ abelianization-Groupᵉ = commutative-add-abelianization-Groupᵉ
```

### The abelianization functor

```agda
abelianization-hom-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ) →
  hom-Abᵉ (abelianization-Groupᵉ Gᵉ) (abelianization-Groupᵉ Hᵉ)
abelianization-hom-Groupᵉ Gᵉ Hᵉ fᵉ =
  hom-quotient-Groupᵉ Gᵉ Hᵉ
    ( commutator-normal-subgroup-Groupᵉ Gᵉ)
    ( commutator-normal-subgroup-Groupᵉ Hᵉ)
    ( fᵉ ,ᵉ preserves-commutator-subgroup-hom-Groupᵉ Gᵉ Hᵉ fᵉ)

preserves-id-abelianization-functor-Groupᵉ :
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  abelianization-hom-Groupᵉ Gᵉ Gᵉ (id-hom-Groupᵉ Gᵉ) ＝ᵉ
  id-hom-Abᵉ (abelianization-Groupᵉ Gᵉ)
preserves-id-abelianization-functor-Groupᵉ Gᵉ =
  preserves-id-hom-quotient-Group'ᵉ Gᵉ
    ( commutator-normal-subgroup-Groupᵉ Gᵉ)
    ( preserves-commutator-subgroup-hom-Groupᵉ Gᵉ Gᵉ (id-hom-Groupᵉ Gᵉ))

preserves-comp-abelianization-functor-Groupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (Kᵉ : Groupᵉ l3ᵉ)
  (gᵉ : hom-Groupᵉ Hᵉ Kᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ) →
  abelianization-hom-Groupᵉ Gᵉ Kᵉ (comp-hom-Groupᵉ Gᵉ Hᵉ Kᵉ gᵉ fᵉ) ＝ᵉ
  comp-hom-Abᵉ
    ( abelianization-Groupᵉ Gᵉ)
    ( abelianization-Groupᵉ Hᵉ)
    ( abelianization-Groupᵉ Kᵉ)
    ( abelianization-hom-Groupᵉ Hᵉ Kᵉ gᵉ)
    ( abelianization-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
preserves-comp-abelianization-functor-Groupᵉ Gᵉ Hᵉ Kᵉ gᵉ fᵉ =
  preserves-comp-hom-quotient-Group'ᵉ Gᵉ Hᵉ Kᵉ
    ( commutator-normal-subgroup-Groupᵉ Gᵉ)
    ( commutator-normal-subgroup-Groupᵉ Hᵉ)
    ( commutator-normal-subgroup-Groupᵉ Kᵉ)
    ( gᵉ ,ᵉ preserves-commutator-subgroup-hom-Groupᵉ Hᵉ Kᵉ gᵉ)
    ( fᵉ ,ᵉ preserves-commutator-subgroup-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
    ( preserves-commutator-subgroup-hom-Groupᵉ Gᵉ Kᵉ (comp-hom-Groupᵉ Gᵉ Hᵉ Kᵉ gᵉ fᵉ))

abelianization-functor-Groupᵉ :
  functor-Large-Categoryᵉ idᵉ Group-Large-Categoryᵉ Ab-Large-Categoryᵉ
obj-functor-Large-Precategoryᵉ
  abelianization-functor-Groupᵉ =
  abelianization-Groupᵉ
hom-functor-Large-Precategoryᵉ
  abelianization-functor-Groupᵉ {l1ᵉ} {l2ᵉ} {Gᵉ} {Hᵉ} =
  abelianization-hom-Groupᵉ Gᵉ Hᵉ
preserves-comp-functor-Large-Precategoryᵉ
  abelianization-functor-Groupᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Gᵉ} {Hᵉ} {Kᵉ} =
  preserves-comp-abelianization-functor-Groupᵉ Gᵉ Hᵉ Kᵉ
preserves-id-functor-Large-Precategoryᵉ
  abelianization-functor-Groupᵉ {l1ᵉ} {Gᵉ} =
  preserves-id-abelianization-functor-Groupᵉ Gᵉ
```

### The unit of the abelianization adjunction

```agda
hom-unit-abelianization-Groupᵉ :
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) → hom-Groupᵉ Gᵉ (group-abelianization-Groupᵉ Gᵉ)
hom-unit-abelianization-Groupᵉ Gᵉ =
  quotient-hom-Groupᵉ Gᵉ (commutator-normal-subgroup-Groupᵉ Gᵉ)

naturality-unit-abelianization-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ) →
  coherence-square-hom-Groupᵉ Gᵉ Hᵉ
    ( group-abelianization-Groupᵉ Gᵉ)
    ( group-abelianization-Groupᵉ Hᵉ)
    ( fᵉ)
    ( hom-unit-abelianization-Groupᵉ Gᵉ)
    ( hom-unit-abelianization-Groupᵉ Hᵉ)
    ( abelianization-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
naturality-unit-abelianization-Groupᵉ Gᵉ Hᵉ fᵉ =
  naturality-hom-quotient-Groupᵉ Gᵉ Hᵉ
    ( commutator-normal-subgroup-Groupᵉ Gᵉ)
    ( commutator-normal-subgroup-Groupᵉ Hᵉ)
    ( fᵉ ,ᵉ preserves-commutator-subgroup-hom-Groupᵉ Gᵉ Hᵉ fᵉ)

naturality-unit-abelianization-Group'ᵉ :
  naturality-family-of-morphisms-functor-Large-Categoryᵉ
    ( Group-Large-Categoryᵉ)
    ( Group-Large-Categoryᵉ)
    ( id-functor-Large-Categoryᵉ Group-Large-Categoryᵉ)
    ( comp-functor-Large-Categoryᵉ
      ( Group-Large-Categoryᵉ)
      ( Ab-Large-Categoryᵉ)
      ( Group-Large-Categoryᵉ)
      ( forgetful-functor-Abᵉ)
      ( abelianization-functor-Groupᵉ))
    ( hom-unit-abelianization-Groupᵉ)
naturality-unit-abelianization-Group'ᵉ {Xᵉ = Gᵉ} {Hᵉ} fᵉ =
  eq-htpy-hom-Groupᵉ Gᵉ
    ( group-abelianization-Groupᵉ Hᵉ)
    ( naturality-unit-abelianization-Groupᵉ Gᵉ Hᵉ fᵉ)

unit-abelianization-Groupᵉ :
  natural-transformation-Large-Categoryᵉ
    ( Group-Large-Categoryᵉ)
    ( Group-Large-Categoryᵉ)
    ( id-functor-Large-Categoryᵉ Group-Large-Categoryᵉ)
    ( comp-functor-Large-Categoryᵉ
      ( Group-Large-Categoryᵉ)
      ( Ab-Large-Categoryᵉ)
      ( Group-Large-Categoryᵉ)
      ( forgetful-functor-Abᵉ)
      ( abelianization-functor-Groupᵉ))

hom-natural-transformation-Large-Precategoryᵉ
  unit-abelianization-Groupᵉ =
  hom-unit-abelianization-Groupᵉ
naturality-natural-transformation-Large-Precategoryᵉ
  unit-abelianization-Groupᵉ =
  naturality-unit-abelianization-Group'ᵉ
```

### The universal property of abelianization

**Proof:**ᵉ Sinceᵉ theᵉ abelianizationᵉ ofᵉ `G`ᵉ isᵉ constructedᵉ asᵉ theᵉ quotientᵉ groupᵉ
`G/[G,G]`,ᵉ weᵉ immediatelyᵉ obtainᵉ thatᵉ theᵉ precompositionᵉ functionᵉ

```text
  hom-Groupᵉ Gᵃᵇᵉ Hᵉ → nullifying-hom-Groupᵉ Gᵉ Hᵉ [G,Gᵉ]
```

isᵉ anᵉ equivalenceᵉ forᵉ anyᵉ groupᵉ `H`.ᵉ Thatᵉ is,ᵉ anyᵉ groupᵉ homomorphismᵉ `fᵉ : Gᵉ → H`ᵉ
ofᵉ whichᵉ theᵉ [kernel](group-theory.kernels-homomorphisms-groups.mdᵉ) containsᵉ theᵉ
commutatorᵉ subgroupᵉ `[G,G]`ᵉ extendsᵉ uniquelyᵉ to theᵉ abelianization.ᵉ

Sinceᵉ abelianᵉ groupsᵉ haveᵉ [trivial](group-theory.trivial-subgroups.mdᵉ)
commutatorᵉ subgroupsᵉ andᵉ sinceᵉ theᵉ inclusionᵉ `fᵉ [G,Gᵉ] ⊆ᵉ [H,H]`ᵉ holdsᵉ forᵉ anyᵉ
groupᵉ homomorphism,ᵉ itᵉ followsᵉ thatᵉ anyᵉ groupᵉ homomorphismᵉ `Gᵉ → A`ᵉ intoᵉ anᵉ
abelianᵉ groupᵉ `A`ᵉ extendsᵉ uniquelyᵉ to theᵉ abelianizationᵉ `Gᵃᵇ`.ᵉ Thisᵉ provesᵉ theᵉ
claim.ᵉ

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-quotient-group-abelianization-Groupᵉ :
    universal-property-quotient-Groupᵉ Gᵉ
      ( commutator-normal-subgroup-Groupᵉ Gᵉ)
      ( group-abelianization-Groupᵉ Gᵉ)
      ( nullifying-quotient-hom-Groupᵉ Gᵉ (commutator-normal-subgroup-Groupᵉ Gᵉ))
  is-quotient-group-abelianization-Groupᵉ =
    is-quotient-group-quotient-Groupᵉ Gᵉ (commutator-normal-subgroup-Groupᵉ Gᵉ)

  is-abelianization-abelianization-Groupᵉ :
    is-abelianization-Groupᵉ Gᵉ
      ( abelianization-Groupᵉ Gᵉ)
      ( hom-unit-abelianization-Groupᵉ Gᵉ)
  is-abelianization-abelianization-Groupᵉ Aᵉ =
    is-equiv-compᵉ
      ( hom-nullifying-hom-Groupᵉ Gᵉ
        ( group-Abᵉ Aᵉ)
        ( commutator-normal-subgroup-Groupᵉ Gᵉ))
      ( precomp-nullifying-hom-Groupᵉ Gᵉ
        ( commutator-normal-subgroup-Groupᵉ Gᵉ)
        ( group-abelianization-Groupᵉ Gᵉ)
        ( nullifying-quotient-hom-Groupᵉ Gᵉ
          ( commutator-normal-subgroup-Groupᵉ Gᵉ))
        ( group-Abᵉ Aᵉ))
      ( is-quotient-group-abelianization-Groupᵉ (group-Abᵉ Aᵉ))
      ( is-equiv-hom-nullifying-hom-group-Abᵉ Gᵉ Aᵉ)
```

### The abelianization adjunction

```agda
equiv-is-adjoint-pair-abelianization-forgetful-functor-Abᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Aᵉ : Abᵉ l2ᵉ) →
  hom-Abᵉ (abelianization-Groupᵉ Gᵉ) Aᵉ ≃ᵉ hom-Groupᵉ Gᵉ (group-Abᵉ Aᵉ)
pr1ᵉ (equiv-is-adjoint-pair-abelianization-forgetful-functor-Abᵉ Gᵉ Aᵉ) hᵉ =
  comp-hom-Groupᵉ Gᵉ
    ( group-abelianization-Groupᵉ Gᵉ)
    ( group-Abᵉ Aᵉ)
    ( hᵉ)
    ( hom-unit-abelianization-Groupᵉ Gᵉ)
pr2ᵉ (equiv-is-adjoint-pair-abelianization-forgetful-functor-Abᵉ Gᵉ Aᵉ) =
  is-abelianization-abelianization-Groupᵉ Gᵉ Aᵉ

naturality-equiv-is-adjoint-pair-abelianization-forgetful-functor-Abᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  (Aᵉ : Abᵉ l3ᵉ) (Bᵉ : Abᵉ l4ᵉ) (gᵉ : hom-Abᵉ Aᵉ Bᵉ) →
  coherence-square-mapsᵉ
    ( map-equivᵉ (equiv-is-adjoint-pair-abelianization-forgetful-functor-Abᵉ Hᵉ Aᵉ))
    ( λ hᵉ →
      comp-hom-Abᵉ
        ( abelianization-Groupᵉ Gᵉ)
        ( abelianization-Groupᵉ Hᵉ)
        ( Bᵉ)
        ( comp-hom-Abᵉ (abelianization-Groupᵉ Hᵉ) Aᵉ Bᵉ gᵉ hᵉ)
        ( abelianization-hom-Groupᵉ Gᵉ Hᵉ fᵉ))
    ( λ hᵉ →
      comp-hom-Groupᵉ Gᵉ Hᵉ
        ( group-Abᵉ Bᵉ)
        ( comp-hom-Groupᵉ Hᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) gᵉ hᵉ)
        ( fᵉ))
    ( map-equivᵉ (equiv-is-adjoint-pair-abelianization-forgetful-functor-Abᵉ Gᵉ Bᵉ))
naturality-equiv-is-adjoint-pair-abelianization-forgetful-functor-Abᵉ
  Gᵉ Hᵉ fᵉ Aᵉ Bᵉ gᵉ hᵉ =
  eq-htpy-hom-Groupᵉ Gᵉ
    ( group-Abᵉ Bᵉ)
    ( ( map-hom-Abᵉ Aᵉ Bᵉ gᵉ ∘ᵉ map-hom-Abᵉ (abelianization-Groupᵉ Hᵉ) Aᵉ hᵉ) ·lᵉ
      ( naturality-unit-abelianization-Groupᵉ Gᵉ Hᵉ fᵉ))

is-adjoint-pair-abelianization-forgetful-functor-Abᵉ :
  is-adjoint-pair-Large-Categoryᵉ
    ( Group-Large-Categoryᵉ)
    ( Ab-Large-Categoryᵉ)
    ( abelianization-functor-Groupᵉ)
    ( forgetful-functor-Abᵉ)
equiv-is-adjoint-pair-Large-Precategoryᵉ
  is-adjoint-pair-abelianization-forgetful-functor-Abᵉ Gᵉ Aᵉ =
  equiv-is-adjoint-pair-abelianization-forgetful-functor-Abᵉ Gᵉ Aᵉ
naturality-equiv-is-adjoint-pair-Large-Precategoryᵉ
  is-adjoint-pair-abelianization-forgetful-functor-Abᵉ
  { X1ᵉ = Gᵉ}
  { X2ᵉ = Hᵉ}
  { Y1ᵉ = Aᵉ}
  { Y2ᵉ = Bᵉ}
  ( fᵉ)
  ( gᵉ) =
  naturality-equiv-is-adjoint-pair-abelianization-forgetful-functor-Abᵉ Hᵉ Gᵉ fᵉ
    Aᵉ Bᵉ gᵉ

abelianization-adjunction-Groupᵉ :
  Adjunction-Large-Categoryᵉ
    ( λ lᵉ → lᵉ)
    ( λ lᵉ → lᵉ)
    ( Group-Large-Categoryᵉ)
    ( Ab-Large-Categoryᵉ)
left-adjoint-Adjunction-Large-Precategoryᵉ
  abelianization-adjunction-Groupᵉ =
  abelianization-functor-Groupᵉ
right-adjoint-Adjunction-Large-Precategoryᵉ
  abelianization-adjunction-Groupᵉ =
  forgetful-functor-Abᵉ
is-adjoint-pair-Adjunction-Large-Precategoryᵉ
  abelianization-adjunction-Groupᵉ =
  is-adjoint-pair-abelianization-forgetful-functor-Abᵉ
```

## External links

-ᵉ [Abelianization](https://groupprops.subwiki.org/wiki/Abelianizationᵉ) atᵉ
  Grouppropsᵉ
-ᵉ [Abelianization](https://ncatlab.org/nlab/show/abelianizationᵉ) atᵉ $n$labᵉ
-ᵉ [Abelianization](https://www.wikidata.org/wiki/Q318598ᵉ) atᵉ Wikidataᵉ
-ᵉ [Abelianization](https://en.wikipedia.org/wiki/Commutator_subgroup#Abelianizationᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Abelianization](https://mathworld.wolfram.com/Abelianization.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ