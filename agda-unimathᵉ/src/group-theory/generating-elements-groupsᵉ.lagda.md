# Generating elements of groups

```agda
module group-theory.generating-elements-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import elementary-number-theory.integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.imagesᵉ
open import foundation.injective-mapsᵉ
open import foundation.propositional-mapsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.addition-homomorphisms-abelian-groupsᵉ
open import group-theory.commuting-elements-groupsᵉ
open import group-theory.conjugationᵉ
open import group-theory.endomorphism-rings-abelian-groupsᵉ
open import group-theory.free-groups-with-one-generatorᵉ
open import group-theory.full-subgroupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.integer-multiples-of-elements-abelian-groupsᵉ
open import group-theory.integer-powers-of-elements-groupsᵉ
open import group-theory.isomorphisms-abelian-groupsᵉ
open import group-theory.normal-subgroupsᵉ
open import group-theory.quotient-groupsᵉ
open import group-theory.subgroups-generated-by-elements-groupsᵉ
open import group-theory.subsets-groupsᵉ
open import group-theory.trivial-group-homomorphismsᵉ

open import ring-theory.integer-multiples-of-elements-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.transporting-ring-structure-along-isomorphisms-abelian-groupsᵉ
```

</details>

## Idea

Anᵉ elementᵉ $g$ᵉ ofᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ saidᵉ to beᵉ aᵉ
**generatingᵉ element**ᵉ ifᵉ theᵉ uniqueᵉ morphismᵉ `g̃ᵉ : ℤᵉ → G`ᵉ equippedᵉ with anᵉ
[identification](foundation-core.identity-types.mdᵉ) `g̃(1ᵉ) = g`ᵉ isᵉ
[surjective](foundation.surjective-maps.md).ᵉ
[Equivalently](foundation.logical-equivalences.md),ᵉ `g`ᵉ isᵉ aᵉ generatingᵉ elementᵉ
ifᵉ theᵉ [subgroup](group-theory.subgroups.mdᵉ) `⟨g⟩`ᵉ ofᵉ `G`ᵉ
[generatedᵉ byᵉ theᵉ element](group-theory.subgroups-generated-by-elements-groups.mdᵉ)
`g`ᵉ isᵉ theᵉ [fullᵉ subgroup](group-theory.full-subgroups.mdᵉ) ofᵉ `G`.ᵉ Weᵉ giveᵉ in
totalᵉ fourᵉ differentᵉ characterizationsᵉ ofᵉ theᵉ notionᵉ ofᵉ generatingᵉ elementᵉ:

1.ᵉ Theᵉ subgroupᵉ generatedᵉ byᵉ theᵉ elementᵉ `g`ᵉ isᵉ full.ᵉ
2.ᵉ Theᵉ fullᵉ subgroupᵉ ofᵉ `G`ᵉ isᵉ generatedᵉ byᵉ theᵉ elementᵉ `g`.ᵉ
3.ᵉ Theᵉ groupᵉ homomorphismᵉ `g̃ᵉ : ℤᵉ → G`ᵉ mappingᵉ `1`ᵉ to `g`ᵉ isᵉ surjective.ᵉ
4.ᵉ Theᵉ evaluationᵉ mapᵉ `hom(G,Hᵉ) → H`ᵉ atᵉ `g`ᵉ isᵉ anᵉ embeddingᵉ forᵉ everyᵉ groupᵉ `H`.ᵉ

Ofᵉ theseᵉ fourᵉ equivalentᵉ characterizations,ᵉ weᵉ takeᵉ theᵉ firstᵉ asᵉ ourᵉ standardᵉ
definition.ᵉ

Weᵉ noteᵉ thatᵉ theᵉ conceptᵉ ofᵉ _groupᵉ equippedᵉ with aᵉ generatingᵉ elementᵉ_ isᵉ subtlyᵉ
differentᵉ fromᵉ theᵉ conceptᵉ ofᵉ [cyclicᵉ group](group-theory.cyclic-groups.md).ᵉ
Groupsᵉ equippedᵉ with generatingᵉ elementsᵉ haveᵉ aᵉ specifiedᵉ generatingᵉ elementᵉ asᵉ
partᵉ ofᵉ theirᵉ structure,ᵉ whereasᵉ cyclicᵉ groupsᵉ areᵉ groupsᵉ with theᵉ
[property](foundation-core.propositions.mdᵉ) thatᵉ thereᵉ
[exists](foundation.existential-quantification.mdᵉ) aᵉ generatingᵉ element.ᵉ

Furthermore,ᵉ weᵉ showᵉ thatᵉ forᵉ anyᵉ groupᵉ `G`ᵉ equippedᵉ with aᵉ generatingᵉ element,ᵉ
theᵉ evaluationᵉ mapᵉ `hom(G,Gᵉ) → G`ᵉ isᵉ anᵉ
[equivalence](foundation.equivalences.md).ᵉ Sinceᵉ groupsᵉ equippedᵉ with aᵉ
generatingᵉ elementᵉ areᵉ [abelian](group-theory.abelian-groups.md),ᵉ itᵉ followsᵉ
thatᵉ `hom(G,G)`ᵉ isᵉ theᵉ
[endomorphismᵉ ring](group-theory.endomorphism-rings-abelian-groups.mdᵉ) ofᵉ anᵉ
abelianᵉ group.ᵉ Theᵉ evaluationᵉ mapᵉ onᵉ anᵉ endomorphismᵉ ringᵉ isᵉ alwaysᵉ aᵉ groupᵉ
homomorphism,ᵉ soᵉ itᵉ followsᵉ fromᵉ theᵉ
[isomorphism](group-theory.isomorphisms-groups.mdᵉ)

```text
  hom(G,Gᵉ) ≅ᵉ Gᵉ
```

thatᵉ anyᵉ groupᵉ equippedᵉ with aᵉ generatingᵉ elementᵉ isᵉ in factᵉ aᵉ
[commutativeᵉ ring](commutative-algebra.commutative-rings.md).ᵉ Hereᵉ weᵉ seeᵉ
anotherᵉ differenceᵉ betweenᵉ groupsᵉ equippedᵉ with aᵉ specifiedᵉ generatingᵉ elementᵉ
andᵉ cyclicᵉ groupsᵉ: Equippingᵉ aᵉ cyclicᵉ groupᵉ with theᵉ structureᵉ ofᵉ aᵉ commutativeᵉ
ringᵉ amountsᵉ to equippingᵉ theᵉ cyclicᵉ groupᵉ with aᵉ _specifiedᵉ_ generatingᵉ
element,ᵉ whichᵉ correspondsᵉ to theᵉ unitᵉ elementᵉ ofᵉ theᵉ commutativeᵉ ringᵉ
structure.ᵉ

## Definitions

### Generating elements

Weᵉ stateᵉ theᵉ definitionᵉ ofᵉ generatingᵉ elementsᵉ in fourᵉ equivalentᵉ waysᵉ: Anᵉ
elementᵉ `g`ᵉ generatesᵉ theᵉ groupᵉ `G`ᵉ ifᵉ

1.ᵉ theᵉ subgroupᵉ generatedᵉ byᵉ theᵉ elementᵉ `g`ᵉ isᵉ full,ᵉ orᵉ ifᵉ
2.ᵉ theᵉ fullᵉ subgroupᵉ ofᵉ `G`ᵉ isᵉ generatedᵉ byᵉ theᵉ elementᵉ `g`,ᵉ orᵉ ifᵉ
3.ᵉ theᵉ groupᵉ homomorphismᵉ `g̃ᵉ : ℤᵉ → G`ᵉ mappingᵉ `1`ᵉ to `g`ᵉ isᵉ surjective,ᵉ orᵉ ifᵉ
4.ᵉ theᵉ evaluationᵉ mapᵉ `hom(G,Hᵉ) → H`ᵉ atᵉ `g`ᵉ isᵉ anᵉ embeddingᵉ forᵉ everyᵉ groupᵉ `H`.ᵉ

#### The standard definition

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) (gᵉ : type-Groupᵉ Gᵉ)
  where

  is-generating-element-prop-Groupᵉ : Propᵉ lᵉ
  is-generating-element-prop-Groupᵉ =
    is-full-prop-Subgroupᵉ Gᵉ (subgroup-element-Groupᵉ Gᵉ gᵉ)

  is-generating-element-Groupᵉ : UUᵉ lᵉ
  is-generating-element-Groupᵉ = type-Propᵉ is-generating-element-prop-Groupᵉ

  is-prop-is-generating-element-Groupᵉ : is-propᵉ is-generating-element-Groupᵉ
  is-prop-is-generating-element-Groupᵉ =
    is-prop-type-Propᵉ is-generating-element-prop-Groupᵉ
```

#### The definition where the full subgroup is asserted to be generated by the element

```agda
  is-subgroup-generated-by-element-full-Subgroupᵉ : UUωᵉ
  is-subgroup-generated-by-element-full-Subgroupᵉ =
    is-subgroup-generated-by-element-Groupᵉ Gᵉ gᵉ (full-Subgroupᵉ lzero Gᵉ)
```

#### The definition where the unique morphism `ℤ → G` mapping `1` to `g` is surjective

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  is-surjective-hom-element-Groupᵉ : type-Groupᵉ Gᵉ → UUᵉ lᵉ
  is-surjective-hom-element-Groupᵉ gᵉ =
    is-surjectiveᵉ (map-hom-element-Groupᵉ Gᵉ gᵉ)
```

#### The definition where the evaluation map `hom(G,H) → H` at `g` is an embedding for every `H`

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (gᵉ : type-Groupᵉ Gᵉ)
  where

  is-emb-ev-element-hom-Group'ᵉ : (lᵉ : Level) → UUᵉ (l1ᵉ ⊔ lsuc lᵉ)
  is-emb-ev-element-hom-Group'ᵉ lᵉ =
    (Hᵉ : Groupᵉ lᵉ) → is-embᵉ (ev-element-hom-Groupᵉ Gᵉ Hᵉ gᵉ)

  is-emb-ev-element-hom-Groupᵉ : UUωᵉ
  is-emb-ev-element-hom-Groupᵉ =
    {lᵉ : Level} → is-emb-ev-element-hom-Group'ᵉ lᵉ

  is-prop-map-ev-element-hom-Groupᵉ : UUωᵉ
  is-prop-map-ev-element-hom-Groupᵉ =
    {lᵉ : Level} (Hᵉ : Groupᵉ lᵉ) → is-prop-mapᵉ (ev-element-hom-Groupᵉ Gᵉ Hᵉ gᵉ)
```

### The subset of generating elements of a group

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  generating-element-Groupᵉ : subset-Groupᵉ lᵉ Gᵉ
  generating-element-Groupᵉ xᵉ = is-generating-element-prop-Groupᵉ Gᵉ xᵉ
```

### Groups equipped with a generating element

```agda
Group-With-Generating-Elementᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Group-With-Generating-Elementᵉ lᵉ =
  Σᵉ (Groupᵉ lᵉ) (λ Gᵉ → type-subtypeᵉ (generating-element-Groupᵉ Gᵉ))

module _
  {lᵉ : Level} (Gᵉ : Group-With-Generating-Elementᵉ lᵉ)
  where

  group-Group-With-Generating-Elementᵉ : Groupᵉ lᵉ
  group-Group-With-Generating-Elementᵉ = pr1ᵉ Gᵉ

  set-Group-With-Generating-Elementᵉ : Setᵉ lᵉ
  set-Group-With-Generating-Elementᵉ =
    set-Groupᵉ group-Group-With-Generating-Elementᵉ

  type-Group-With-Generating-Elementᵉ : UUᵉ lᵉ
  type-Group-With-Generating-Elementᵉ =
    type-Groupᵉ group-Group-With-Generating-Elementᵉ

  generating-element-Group-With-Generating-Elementᵉ :
    type-subtypeᵉ (generating-element-Groupᵉ group-Group-With-Generating-Elementᵉ)
  generating-element-Group-With-Generating-Elementᵉ = pr2ᵉ Gᵉ

  element-Group-With-Generating-Elementᵉ : type-Group-With-Generating-Elementᵉ
  element-Group-With-Generating-Elementᵉ =
    pr1ᵉ generating-element-Group-With-Generating-Elementᵉ

  is-generating-element-element-Group-With-Generating-Elementᵉ :
    is-generating-element-Groupᵉ
      group-Group-With-Generating-Elementᵉ
      element-Group-With-Generating-Elementᵉ
  is-generating-element-element-Group-With-Generating-Elementᵉ =
    pr2ᵉ generating-element-Group-With-Generating-Elementᵉ

  ev-element-hom-Group-With-Generating-Elementᵉ :
    (Hᵉ : Groupᵉ lᵉ) →
    hom-Groupᵉ group-Group-With-Generating-Elementᵉ Hᵉ → type-Groupᵉ Hᵉ
  ev-element-hom-Group-With-Generating-Elementᵉ Hᵉ =
    ev-element-hom-Groupᵉ
      ( group-Group-With-Generating-Elementᵉ)
      ( Hᵉ)
      ( element-Group-With-Generating-Elementᵉ)
```

## Properties

### The four definitions of generating elements are equivalent

#### An element is generating if and only if it generates the full subgroup

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) (gᵉ : type-Groupᵉ Gᵉ)
  where

  is-generating-element-is-subgroup-generated-by-element-full-Subgroupᵉ :
    is-subgroup-generated-by-element-full-Subgroupᵉ Gᵉ gᵉ →
    is-generating-element-Groupᵉ Gᵉ gᵉ
  is-generating-element-is-subgroup-generated-by-element-full-Subgroupᵉ Hᵉ xᵉ =
    leq-subgroup-is-subgroup-generated-by-element-Groupᵉ Gᵉ gᵉ
      ( full-Subgroupᵉ lzero Gᵉ)
      ( subgroup-element-Groupᵉ Gᵉ gᵉ)
      ( Hᵉ)
      ( contains-element-subgroup-element-Groupᵉ Gᵉ gᵉ)
      ( xᵉ)
      ( raise-starᵉ)

  is-subgroup-generated-by-element-full-subgroup-is-generating-element-Groupᵉ :
    is-generating-element-Groupᵉ Gᵉ gᵉ →
    is-subgroup-generated-by-element-full-Subgroupᵉ Gᵉ gᵉ
  pr1ᵉ
    ( is-subgroup-generated-by-element-full-subgroup-is-generating-element-Groupᵉ
      Hᵉ Kᵉ)
    ( uᵉ)
    ( xᵉ)
    ( vᵉ) =
    leq-subgroup-element-Groupᵉ Gᵉ gᵉ Kᵉ uᵉ xᵉ (Hᵉ xᵉ)
  pr2ᵉ
    ( is-subgroup-generated-by-element-full-subgroup-is-generating-element-Groupᵉ
      Hᵉ Kᵉ)
    ( uᵉ) =
    uᵉ gᵉ raise-starᵉ

is-subgroup-generated-by-element-full-subgroup-Group-With-Generating-Elementᵉ :
  {lᵉ : Level} (Gᵉ : Group-With-Generating-Elementᵉ lᵉ) →
  is-subgroup-generated-by-element-full-Subgroupᵉ
    ( group-Group-With-Generating-Elementᵉ Gᵉ)
    ( element-Group-With-Generating-Elementᵉ Gᵉ)
is-subgroup-generated-by-element-full-subgroup-Group-With-Generating-Elementᵉ Gᵉ =
  is-subgroup-generated-by-element-full-subgroup-is-generating-element-Groupᵉ
    ( group-Group-With-Generating-Elementᵉ Gᵉ)
    ( element-Group-With-Generating-Elementᵉ Gᵉ)
    ( is-generating-element-element-Group-With-Generating-Elementᵉ Gᵉ)
```

#### An element `g` is generating if and only if the unique map `g̃ : ℤ → G` is surjective

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) (gᵉ : type-Groupᵉ Gᵉ)
  where

  is-generating-element-is-surjective-hom-element-Group'ᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) (kᵉ : ℤᵉ) (pᵉ : map-hom-element-Groupᵉ Gᵉ gᵉ kᵉ ＝ᵉ xᵉ) →
    is-in-subgroup-element-Groupᵉ Gᵉ gᵉ xᵉ
  is-generating-element-is-surjective-hom-element-Group'ᵉ ._ kᵉ reflᵉ =
    contains-powers-subgroup-element-Groupᵉ Gᵉ gᵉ kᵉ

  is-generating-element-is-surjective-hom-element-Groupᵉ :
    is-surjective-hom-element-Groupᵉ Gᵉ gᵉ → is-generating-element-Groupᵉ Gᵉ gᵉ
  is-generating-element-is-surjective-hom-element-Groupᵉ Hᵉ xᵉ =
    apply-universal-property-trunc-Propᵉ
      ( Hᵉ xᵉ)
      ( subset-subgroup-element-Groupᵉ Gᵉ gᵉ xᵉ)
      ( λ (kᵉ ,ᵉ pᵉ) →
        is-generating-element-is-surjective-hom-element-Group'ᵉ xᵉ kᵉ pᵉ)

  is-surjective-hom-element-is-generating-element-Groupᵉ :
    is-generating-element-Groupᵉ Gᵉ gᵉ → is-surjective-hom-element-Groupᵉ Gᵉ gᵉ
  is-surjective-hom-element-is-generating-element-Groupᵉ Hᵉ xᵉ =
    leq-subgroup-is-subgroup-generated-by-element-Groupᵉ Gᵉ gᵉ
      ( full-Subgroupᵉ lzero Gᵉ)
      ( image-hom-element-Groupᵉ Gᵉ gᵉ)
      ( is-subgroup-generated-by-element-full-subgroup-is-generating-element-Groupᵉ
        ( Gᵉ)
        ( gᵉ)
        ( Hᵉ))
      ( contains-element-image-hom-element-Groupᵉ Gᵉ gᵉ)
      ( xᵉ)
      ( raise-starᵉ)

is-surjective-hom-element-Group-With-Generating-Elementᵉ :
  {lᵉ : Level} (Gᵉ : Group-With-Generating-Elementᵉ lᵉ) →
  is-surjective-hom-element-Groupᵉ
    ( group-Group-With-Generating-Elementᵉ Gᵉ)
    ( element-Group-With-Generating-Elementᵉ Gᵉ)
is-surjective-hom-element-Group-With-Generating-Elementᵉ Gᵉ =
  is-surjective-hom-element-is-generating-element-Groupᵉ
    ( group-Group-With-Generating-Elementᵉ Gᵉ)
    ( element-Group-With-Generating-Elementᵉ Gᵉ)
    ( is-generating-element-element-Group-With-Generating-Elementᵉ Gᵉ)
```

#### If the evaluation map `hom(G,H) → H` at `g` is an embedding for every group `H`, then `g̃ : ℤ → G` is surjective

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) (gᵉ : type-Groupᵉ Gᵉ)
  (Uᵉ : is-emb-ev-element-hom-Groupᵉ Gᵉ gᵉ)
  where

  compute-conjugation-is-emb-ev-element-hom-Groupᵉ :
    htpy-hom-Groupᵉ Gᵉ Gᵉ (conjugation-hom-Groupᵉ Gᵉ gᵉ) (id-hom-Groupᵉ Gᵉ)
  compute-conjugation-is-emb-ev-element-hom-Groupᵉ =
    htpy-eq-hom-Groupᵉ Gᵉ Gᵉ
      ( conjugation-hom-Groupᵉ Gᵉ gᵉ)
      ( id-hom-Groupᵉ Gᵉ)
      ( is-injective-is-embᵉ (Uᵉ Gᵉ)
        ( invᵉ (transpose-eq-mul-Groupᵉ Gᵉ reflᵉ)))

  commute-is-emb-ev-element-hom-Groupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) → mul-Groupᵉ Gᵉ gᵉ xᵉ ＝ᵉ mul-Groupᵉ Gᵉ xᵉ gᵉ
  commute-is-emb-ev-element-hom-Groupᵉ xᵉ =
    invᵉ
      ( inv-transpose-eq-mul-Groupᵉ Gᵉ
        ( invᵉ (compute-conjugation-is-emb-ev-element-hom-Groupᵉ xᵉ)))

  compute-conjugation-is-emb-ev-element-hom-Group'ᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) → conjugation-Groupᵉ Gᵉ xᵉ gᵉ ＝ᵉ gᵉ
  compute-conjugation-is-emb-ev-element-hom-Group'ᵉ xᵉ =
    invᵉ (transpose-eq-mul-Groupᵉ Gᵉ (commute-is-emb-ev-element-hom-Groupᵉ xᵉ))

  abstract
    is-normal-image-hom-element-is-emb-ev-element-hom-Groupᵉ :
      is-normal-Subgroupᵉ Gᵉ (image-hom-element-Groupᵉ Gᵉ gᵉ)
    is-normal-image-hom-element-is-emb-ev-element-hom-Groupᵉ xᵉ (yᵉ ,ᵉ pᵉ) =
      apply-universal-property-trunc-Propᵉ pᵉ
        ( subset-image-hom-element-Groupᵉ Gᵉ gᵉ (conjugation-Groupᵉ Gᵉ xᵉ yᵉ))
        ( λ where
          ( kᵉ ,ᵉ reflᵉ) →
            is-closed-under-eq-image-hom-element-Group'ᵉ Gᵉ gᵉ
              ( unit-trunc-Propᵉ (kᵉ ,ᵉ reflᵉ))
              ( ( preserves-integer-powers-conjugation-Groupᵉ Gᵉ kᵉ xᵉ gᵉ) ∙ᵉ
                ( apᵉ
                  ( integer-power-Groupᵉ Gᵉ kᵉ)
                  ( compute-conjugation-is-emb-ev-element-hom-Group'ᵉ xᵉ))))

  private
    Nᵉ : Normal-Subgroupᵉ lᵉ Gᵉ
    pr1ᵉ Nᵉ = image-hom-element-Groupᵉ Gᵉ gᵉ
    pr2ᵉ Nᵉ = is-normal-image-hom-element-is-emb-ev-element-hom-Groupᵉ

    Hᵉ : Groupᵉ lᵉ
    Hᵉ = quotient-Groupᵉ Gᵉ Nᵉ

    qᵉ : hom-Groupᵉ Gᵉ Hᵉ
    qᵉ = quotient-hom-Groupᵉ Gᵉ Nᵉ

  abstract
    is-trivial-quotient-hom-image-hom-element-is-emb-ev-element-hom-Groupᵉ :
      is-trivial-hom-Groupᵉ Gᵉ Hᵉ qᵉ
    is-trivial-quotient-hom-image-hom-element-is-emb-ev-element-hom-Groupᵉ =
      htpy-eq-hom-Groupᵉ Gᵉ Hᵉ qᵉ
        ( trivial-hom-Groupᵉ Gᵉ Hᵉ)
        ( is-injective-is-embᵉ
          ( Uᵉ Hᵉ)
          ( invᵉ
            ( is-in-kernel-quotient-hom-is-in-Normal-Subgroupᵉ Gᵉ Nᵉ
              ( contains-element-image-hom-element-Groupᵉ Gᵉ gᵉ))))

  is-surjective-hom-element-is-emb-ev-element-hom-Groupᵉ :
    is-surjective-hom-element-Groupᵉ Gᵉ gᵉ
  is-surjective-hom-element-is-emb-ev-element-hom-Groupᵉ xᵉ =
    is-in-normal-subgroup-is-in-kernel-quotient-hom-Groupᵉ Gᵉ Nᵉ
      ( invᵉ
        ( is-trivial-quotient-hom-image-hom-element-is-emb-ev-element-hom-Groupᵉ
          xᵉ))
```

#### A group element `g : G` is generating if and only if for every group `H` the evaluation map `hom(G,H) → H` at `g` is an embedding

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) (gᵉ : type-Groupᵉ Gᵉ)
  where

  abstract
    is-prop-map-ev-element-is-generating-element-Groupᵉ :
      is-generating-element-Groupᵉ Gᵉ gᵉ → is-prop-map-ev-element-hom-Groupᵉ Gᵉ gᵉ
    is-prop-map-ev-element-is-generating-element-Groupᵉ Uᵉ Hᵉ yᵉ =
      is-prop-all-elements-equalᵉ
        ( λ (hᵉ ,ᵉ pᵉ) (kᵉ ,ᵉ qᵉ) →
          eq-type-subtypeᵉ
            ( λ uᵉ → Id-Propᵉ (set-Groupᵉ Hᵉ) (ev-element-hom-Groupᵉ Gᵉ Hᵉ gᵉ uᵉ) yᵉ)
            ( eq-htpy-hom-Groupᵉ Gᵉ Hᵉ
              ( λ xᵉ →
                apply-universal-property-trunc-Propᵉ
                  ( is-surjective-hom-element-is-generating-element-Groupᵉ
                    Gᵉ gᵉ Uᵉ xᵉ)
                  ( Id-Propᵉ
                    ( set-Groupᵉ Hᵉ)
                    ( map-hom-Groupᵉ Gᵉ Hᵉ hᵉ xᵉ)
                    ( map-hom-Groupᵉ Gᵉ Hᵉ kᵉ xᵉ))
                  ( λ where
                    ( zᵉ ,ᵉ reflᵉ) →
                        eq-integer-power-hom-Groupᵉ Gᵉ Hᵉ hᵉ kᵉ zᵉ gᵉ (pᵉ ∙ᵉ invᵉ qᵉ)))))

  is-emb-ev-element-is-generating-element-Groupᵉ :
    is-generating-element-Groupᵉ Gᵉ gᵉ → is-emb-ev-element-hom-Groupᵉ Gᵉ gᵉ
  is-emb-ev-element-is-generating-element-Groupᵉ Uᵉ Hᵉ =
    is-emb-is-prop-mapᵉ (is-prop-map-ev-element-is-generating-element-Groupᵉ Uᵉ Hᵉ)

  is-generating-element-is-emb-ev-element-hom-Groupᵉ :
    is-emb-ev-element-hom-Groupᵉ Gᵉ gᵉ → is-generating-element-Groupᵉ Gᵉ gᵉ
  is-generating-element-is-emb-ev-element-hom-Groupᵉ Uᵉ =
    is-generating-element-is-surjective-hom-element-Groupᵉ Gᵉ gᵉ
      ( is-surjective-hom-element-is-emb-ev-element-hom-Groupᵉ Gᵉ gᵉ Uᵉ)

is-emb-ev-element-Group-With-Generating-Elementᵉ :
  {lᵉ : Level} (Gᵉ : Group-With-Generating-Elementᵉ lᵉ) →
  is-emb-ev-element-hom-Groupᵉ
    ( group-Group-With-Generating-Elementᵉ Gᵉ)
    ( element-Group-With-Generating-Elementᵉ Gᵉ)
is-emb-ev-element-Group-With-Generating-Elementᵉ Gᵉ =
  is-emb-ev-element-is-generating-element-Groupᵉ
    ( group-Group-With-Generating-Elementᵉ Gᵉ)
    ( element-Group-With-Generating-Elementᵉ Gᵉ)
    ( is-generating-element-element-Group-With-Generating-Elementᵉ Gᵉ)
```

### If `g` is a generating element of `G`, then `G` is abelian

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) (gᵉ : type-Groupᵉ Gᵉ)
  where

  abstract
    commutative-mul-is-surjective-hom-element-Groupᵉ :
      (Uᵉ : is-surjective-hom-element-Groupᵉ Gᵉ gᵉ) →
      (xᵉ yᵉ : type-Groupᵉ Gᵉ) → commute-Groupᵉ Gᵉ xᵉ yᵉ
    commutative-mul-is-surjective-hom-element-Groupᵉ Uᵉ xᵉ yᵉ =
      apply-twice-universal-property-trunc-Propᵉ
        ( Uᵉ xᵉ)
        ( Uᵉ yᵉ)
        ( Id-Propᵉ (set-Groupᵉ Gᵉ) (mul-Groupᵉ Gᵉ xᵉ yᵉ) (mul-Groupᵉ Gᵉ yᵉ xᵉ))
        ( λ where
          ( kᵉ ,ᵉ reflᵉ) (lᵉ ,ᵉ reflᵉ) →
            commute-integer-powers-Groupᵉ Gᵉ kᵉ lᵉ reflᵉ)

  commutative-mul-is-generating-element-Groupᵉ :
    (Uᵉ : is-generating-element-Groupᵉ Gᵉ gᵉ) →
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → commute-Groupᵉ Gᵉ xᵉ yᵉ
  commutative-mul-is-generating-element-Groupᵉ Uᵉ =
    commutative-mul-is-surjective-hom-element-Groupᵉ
      ( is-surjective-hom-element-is-generating-element-Groupᵉ Gᵉ gᵉ Uᵉ)

module _
  {lᵉ : Level} (Gᵉ : Group-With-Generating-Elementᵉ lᵉ)
  where

  abelian-group-Group-With-Generating-Elementᵉ : Abᵉ lᵉ
  pr1ᵉ abelian-group-Group-With-Generating-Elementᵉ =
    group-Group-With-Generating-Elementᵉ Gᵉ
  pr2ᵉ abelian-group-Group-With-Generating-Elementᵉ =
    commutative-mul-is-generating-element-Groupᵉ
      ( group-Group-With-Generating-Elementᵉ Gᵉ)
      ( element-Group-With-Generating-Elementᵉ Gᵉ)
      ( is-generating-element-element-Group-With-Generating-Elementᵉ Gᵉ)

  zero-Group-With-Generating-Elementᵉ :
    type-Group-With-Generating-Elementᵉ Gᵉ
  zero-Group-With-Generating-Elementᵉ =
    zero-Abᵉ abelian-group-Group-With-Generating-Elementᵉ

  add-Group-With-Generating-Elementᵉ :
    (xᵉ yᵉ : type-Group-With-Generating-Elementᵉ Gᵉ) →
    type-Group-With-Generating-Elementᵉ Gᵉ
  add-Group-With-Generating-Elementᵉ =
    add-Abᵉ abelian-group-Group-With-Generating-Elementᵉ

  neg-Group-With-Generating-Elementᵉ :
    type-Group-With-Generating-Elementᵉ Gᵉ → type-Group-With-Generating-Elementᵉ Gᵉ
  neg-Group-With-Generating-Elementᵉ =
    neg-Abᵉ abelian-group-Group-With-Generating-Elementᵉ

  associative-add-Group-With-Generating-Elementᵉ :
    (xᵉ yᵉ zᵉ : type-Group-With-Generating-Elementᵉ Gᵉ) →
    add-Group-With-Generating-Elementᵉ
      ( add-Group-With-Generating-Elementᵉ xᵉ yᵉ)
      ( zᵉ) ＝ᵉ
    add-Group-With-Generating-Elementᵉ
      ( xᵉ)
      ( add-Group-With-Generating-Elementᵉ yᵉ zᵉ)
  associative-add-Group-With-Generating-Elementᵉ =
    associative-add-Abᵉ abelian-group-Group-With-Generating-Elementᵉ

  left-unit-law-add-Group-With-Generating-Elementᵉ :
    (xᵉ : type-Group-With-Generating-Elementᵉ Gᵉ) →
    add-Group-With-Generating-Elementᵉ zero-Group-With-Generating-Elementᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Group-With-Generating-Elementᵉ =
    left-unit-law-add-Abᵉ abelian-group-Group-With-Generating-Elementᵉ

  right-unit-law-add-Group-With-Generating-Elementᵉ :
    (xᵉ : type-Group-With-Generating-Elementᵉ Gᵉ) →
    add-Group-With-Generating-Elementᵉ xᵉ zero-Group-With-Generating-Elementᵉ ＝ᵉ xᵉ
  right-unit-law-add-Group-With-Generating-Elementᵉ =
    right-unit-law-add-Abᵉ abelian-group-Group-With-Generating-Elementᵉ

  left-inverse-law-add-Group-With-Generating-Elementᵉ :
    (xᵉ : type-Group-With-Generating-Elementᵉ Gᵉ) →
    add-Group-With-Generating-Elementᵉ (neg-Group-With-Generating-Elementᵉ xᵉ) xᵉ ＝ᵉ
    zero-Group-With-Generating-Elementᵉ
  left-inverse-law-add-Group-With-Generating-Elementᵉ =
    left-inverse-law-add-Abᵉ abelian-group-Group-With-Generating-Elementᵉ

  right-inverse-law-add-Group-With-Generating-Elementᵉ :
    (xᵉ : type-Group-With-Generating-Elementᵉ Gᵉ) →
    add-Group-With-Generating-Elementᵉ xᵉ (neg-Group-With-Generating-Elementᵉ xᵉ) ＝ᵉ
    zero-Group-With-Generating-Elementᵉ
  right-inverse-law-add-Group-With-Generating-Elementᵉ =
    right-inverse-law-add-Abᵉ abelian-group-Group-With-Generating-Elementᵉ
```

### If `g` is a generating element of `G`, then the evaluation map `hom(G,G) → G` is an isomorphism of groups

```agda
module _
  {lᵉ : Level} (Gᵉ : Group-With-Generating-Elementᵉ lᵉ)
  where

  abstract
    is-surjective-ev-element-Group-With-Generating-Elementᵉ :
      is-surjectiveᵉ
        ( ev-element-hom-Group-With-Generating-Elementᵉ Gᵉ
          ( group-Group-With-Generating-Elementᵉ Gᵉ))
    is-surjective-ev-element-Group-With-Generating-Elementᵉ xᵉ =
      apply-universal-property-trunc-Propᵉ
        ( is-surjective-hom-element-Group-With-Generating-Elementᵉ Gᵉ xᵉ)
        ( subtype-imᵉ
          ( ev-element-hom-Group-With-Generating-Elementᵉ Gᵉ
            ( group-Group-With-Generating-Elementᵉ Gᵉ))
          ( xᵉ))
        ( λ where
          ( kᵉ ,ᵉ reflᵉ) →
            unit-trunc-Propᵉ
              ( hom-integer-multiple-Abᵉ
                  ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ)
                  ( kᵉ) ,ᵉ
                reflᵉ))

  is-equiv-ev-element-Group-With-Generating-Elementᵉ :
    is-equivᵉ
      ( ev-element-hom-Group-With-Generating-Elementᵉ Gᵉ
        ( group-Group-With-Generating-Elementᵉ Gᵉ))
  is-equiv-ev-element-Group-With-Generating-Elementᵉ =
    is-equiv-is-emb-is-surjectiveᵉ
      ( is-surjective-ev-element-Group-With-Generating-Elementᵉ)
      ( is-emb-ev-element-Group-With-Generating-Elementᵉ Gᵉ
        ( group-Group-With-Generating-Elementᵉ Gᵉ))

  is-iso-ev-element-Group-With-Generating-Elementᵉ :
    is-iso-Abᵉ
      ( ab-hom-Abᵉ
        ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ)
        ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ))
      ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ)
      ( hom-ev-element-hom-Abᵉ
        ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ)
        ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ)
        ( element-Group-With-Generating-Elementᵉ Gᵉ))
  is-iso-ev-element-Group-With-Generating-Elementᵉ =
    is-iso-is-equiv-hom-Abᵉ
      ( ab-hom-Abᵉ
        ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ)
        ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ))
      ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ)
      ( hom-ev-element-hom-Abᵉ
        ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ)
        ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ)
        ( element-Group-With-Generating-Elementᵉ Gᵉ))
      ( is-equiv-ev-element-Group-With-Generating-Elementᵉ)

  iso-ev-element-Group-With-Generating-Elementᵉ :
    iso-Abᵉ
      ( ab-hom-Abᵉ
        ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ)
        ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ))
      ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ)
  pr1ᵉ iso-ev-element-Group-With-Generating-Elementᵉ =
    hom-ev-element-hom-Abᵉ
      ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ)
      ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ)
      ( element-Group-With-Generating-Elementᵉ Gᵉ)
  pr2ᵉ iso-ev-element-Group-With-Generating-Elementᵉ =
    is-iso-ev-element-Group-With-Generating-Elementᵉ
```

### Groups equipped with generating elements are commutative rings

```agda
module _
  {lᵉ : Level} (Gᵉ : Group-With-Generating-Elementᵉ lᵉ)
  where

  ring-Group-With-Generating-Elementᵉ : Ringᵉ lᵉ
  ring-Group-With-Generating-Elementᵉ =
    transport-ring-structure-iso-Abᵉ
      ( endomorphism-ring-Abᵉ (abelian-group-Group-With-Generating-Elementᵉ Gᵉ))
      ( abelian-group-Group-With-Generating-Elementᵉ Gᵉ)
      ( iso-ev-element-Group-With-Generating-Elementᵉ Gᵉ)

  one-Group-With-Generating-Elementᵉ : type-Group-With-Generating-Elementᵉ Gᵉ
  one-Group-With-Generating-Elementᵉ =
    one-Ringᵉ ring-Group-With-Generating-Elementᵉ

  compute-one-Group-With-Generating-Elementᵉ :
    one-Group-With-Generating-Elementᵉ ＝ᵉ
    element-Group-With-Generating-Elementᵉ Gᵉ
  compute-one-Group-With-Generating-Elementᵉ = reflᵉ

  mul-Group-With-Generating-Elementᵉ :
    (xᵉ yᵉ : type-Group-With-Generating-Elementᵉ Gᵉ) →
    type-Group-With-Generating-Elementᵉ Gᵉ
  mul-Group-With-Generating-Elementᵉ =
    mul-Ringᵉ ring-Group-With-Generating-Elementᵉ

  abstract
    commutative-mul-Group-With-Generating-Elementᵉ :
      (xᵉ yᵉ : type-Group-With-Generating-Elementᵉ Gᵉ) →
      mul-Group-With-Generating-Elementᵉ xᵉ yᵉ ＝ᵉ
      mul-Group-With-Generating-Elementᵉ yᵉ xᵉ
    commutative-mul-Group-With-Generating-Elementᵉ xᵉ yᵉ =
      apply-twice-universal-property-trunc-Propᵉ
        ( is-surjective-hom-element-Group-With-Generating-Elementᵉ Gᵉ xᵉ)
        ( is-surjective-hom-element-Group-With-Generating-Elementᵉ Gᵉ yᵉ)
        ( Id-Propᵉ (set-Group-With-Generating-Elementᵉ Gᵉ) _ _)
        ( λ where
          ( kᵉ ,ᵉ reflᵉ) (lᵉ ,ᵉ reflᵉ) →
            commute-integer-multiples-diagonal-Ringᵉ
              ( ring-Group-With-Generating-Elementᵉ)
              ( kᵉ)
              ( lᵉ))

  commutative-ring-Group-With-Generating-Elementᵉ : Commutative-Ringᵉ lᵉ
  pr1ᵉ commutative-ring-Group-With-Generating-Elementᵉ =
    ring-Group-With-Generating-Elementᵉ
  pr2ᵉ commutative-ring-Group-With-Generating-Elementᵉ =
    commutative-mul-Group-With-Generating-Elementᵉ
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}