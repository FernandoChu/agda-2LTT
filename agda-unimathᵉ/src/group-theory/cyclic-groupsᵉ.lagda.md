# Cyclic groups

```agda
module group-theory.cyclic-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.identity-typesᵉ
open import foundation.inhabited-subtypesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.generating-elements-groupsᵉ
open import group-theory.groupsᵉ
```

</details>

## Idea

Aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ saidᵉ to beᵉ **cyclic**ᵉ ifᵉ itᵉ isᵉ
[generatedᵉ byᵉ aᵉ singleᵉ element](group-theory.generating-elements-groups.md),ᵉ
i.e.,ᵉ ifᵉ thereᵉ [exists](foundation.existential-quantification.mdᵉ) anᵉ elementᵉ
`gᵉ : G`ᵉ suchᵉ thatᵉ theᵉ [groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ)

```text
  g̃ᵉ : ℤᵉ → Gᵉ
```

equippedᵉ with anᵉ identificationᵉ `g̃(1ᵉ) ＝ᵉ g`ᵉ isᵉ
[surjective](foundation.surjective-maps.mdᵉ)

## Definitions

### Cyclic groups

#### The standard definition of cyclic groups

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-cyclic-prop-Groupᵉ : Propᵉ l1ᵉ
  is-cyclic-prop-Groupᵉ =
    ∃ᵉ (type-Groupᵉ Gᵉ) (is-generating-element-prop-Groupᵉ Gᵉ)

  is-cyclic-Groupᵉ : UUᵉ l1ᵉ
  is-cyclic-Groupᵉ = type-Propᵉ is-cyclic-prop-Groupᵉ

  is-prop-is-cyclic-Groupᵉ : is-propᵉ is-cyclic-Groupᵉ
  is-prop-is-cyclic-Groupᵉ = is-prop-type-Propᵉ is-cyclic-prop-Groupᵉ

Cyclic-Groupᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Cyclic-Groupᵉ lᵉ = type-subtypeᵉ (is-cyclic-prop-Groupᵉ {lᵉ})

module _
  {lᵉ : Level} (Cᵉ : Cyclic-Groupᵉ lᵉ)
  where

  group-Cyclic-Groupᵉ : Groupᵉ lᵉ
  group-Cyclic-Groupᵉ = pr1ᵉ Cᵉ

  is-cyclic-Cyclic-Groupᵉ : is-cyclic-Groupᵉ group-Cyclic-Groupᵉ
  is-cyclic-Cyclic-Groupᵉ = pr2ᵉ Cᵉ

  set-Cyclic-Groupᵉ : Setᵉ lᵉ
  set-Cyclic-Groupᵉ = set-Groupᵉ group-Cyclic-Groupᵉ

  type-Cyclic-Groupᵉ : UUᵉ lᵉ
  type-Cyclic-Groupᵉ = type-Groupᵉ group-Cyclic-Groupᵉ

  zero-Cyclic-Groupᵉ : type-Cyclic-Groupᵉ
  zero-Cyclic-Groupᵉ = unit-Groupᵉ group-Cyclic-Groupᵉ

  add-Cyclic-Groupᵉ : (xᵉ yᵉ : type-Cyclic-Groupᵉ) → type-Cyclic-Groupᵉ
  add-Cyclic-Groupᵉ = mul-Groupᵉ group-Cyclic-Groupᵉ

  neg-Cyclic-Groupᵉ : type-Cyclic-Groupᵉ → type-Cyclic-Groupᵉ
  neg-Cyclic-Groupᵉ = inv-Groupᵉ group-Cyclic-Groupᵉ

  associative-add-Cyclic-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-Cyclic-Groupᵉ) →
    add-Cyclic-Groupᵉ (add-Cyclic-Groupᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    add-Cyclic-Groupᵉ xᵉ (add-Cyclic-Groupᵉ yᵉ zᵉ)
  associative-add-Cyclic-Groupᵉ = associative-mul-Groupᵉ group-Cyclic-Groupᵉ

  commutative-add-Cyclic-Groupᵉ :
    (xᵉ yᵉ : type-Cyclic-Groupᵉ) →
    add-Cyclic-Groupᵉ xᵉ yᵉ ＝ᵉ add-Cyclic-Groupᵉ yᵉ xᵉ
  commutative-add-Cyclic-Groupᵉ xᵉ yᵉ =
    apply-universal-property-trunc-Propᵉ
      ( is-cyclic-Cyclic-Groupᵉ)
      ( Id-Propᵉ set-Cyclic-Groupᵉ (add-Cyclic-Groupᵉ xᵉ yᵉ) (add-Cyclic-Groupᵉ yᵉ xᵉ))
      ( λ (gᵉ ,ᵉ uᵉ) →
        commutative-mul-is-generating-element-Groupᵉ group-Cyclic-Groupᵉ gᵉ uᵉ xᵉ yᵉ)

  ab-Cyclic-Groupᵉ : Abᵉ lᵉ
  pr1ᵉ ab-Cyclic-Groupᵉ = group-Cyclic-Groupᵉ
  pr2ᵉ ab-Cyclic-Groupᵉ = commutative-add-Cyclic-Groupᵉ
```

#### The definition where `G` has a generating element

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  has-generating-element-prop-Groupᵉ : Propᵉ l1ᵉ
  has-generating-element-prop-Groupᵉ =
    is-inhabited-subtype-Propᵉ (generating-element-Groupᵉ Gᵉ)

  has-generating-element-Groupᵉ : UUᵉ l1ᵉ
  has-generating-element-Groupᵉ = type-Propᵉ has-generating-element-prop-Groupᵉ
```

## Properties

### A group is cyclic if and only if it has a generating element

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-cyclic-has-generating-element-Groupᵉ :
    is-cyclic-Groupᵉ Gᵉ →
    {lᵉ : Level} →
    exists-structureᵉ
      ( type-Groupᵉ Gᵉ)
      ( λ gᵉ → is-emb-ev-element-hom-Group'ᵉ Gᵉ gᵉ lᵉ)
  is-cyclic-has-generating-element-Groupᵉ Hᵉ {lᵉ} =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( exists-structure-Propᵉ
        ( type-Groupᵉ Gᵉ)
        ( λ gᵉ → is-emb-ev-element-hom-Group'ᵉ Gᵉ gᵉ lᵉ))
      ( λ (gᵉ ,ᵉ uᵉ) →
        intro-existsᵉ gᵉ (is-emb-ev-element-is-generating-element-Groupᵉ Gᵉ gᵉ uᵉ))
```

## See also

-ᵉ Inᵉ
  [`group-theory.generating-elements-groups`](group-theory.generating-elements-groups.mdᵉ)
  weᵉ showᵉ thatᵉ groupsᵉ equippedᵉ with aᵉ generatingᵉ elementᵉ areᵉ isomorphicᵉ to theirᵉ
  endomorphismᵉ rings.ᵉ Furthermore,ᵉ theᵉ multiplicativeᵉ structureᵉ ofᵉ theseᵉ ringsᵉ
  isᵉ commutative,ᵉ soᵉ thatᵉ groupsᵉ equippedᵉ with aᵉ generatingᵉ elementᵉ areᵉ alsoᵉ
  equippedᵉ with theᵉ structureᵉ ofᵉ aᵉ commutativeᵉ ring.ᵉ

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}