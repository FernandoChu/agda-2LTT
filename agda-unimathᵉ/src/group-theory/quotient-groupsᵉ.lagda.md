# Quotient groups

```agda
module group-theory.quotient-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-functoriality-set-quotientsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.effective-maps-equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-set-quotientsᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.set-quotientsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universal-property-set-quotientsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.kernels-homomorphisms-groupsᵉ
open import group-theory.normal-subgroupsᵉ
open import group-theory.nullifying-group-homomorphismsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [normalᵉ subgroup](group-theory.normal-subgroups.mdᵉ) `N`ᵉ ofᵉ `G`,ᵉ theᵉ
**quotientᵉ group**ᵉ `G/N`ᵉ isᵉ aᵉ [group](group-theory.groups.mdᵉ) equippedᵉ with aᵉ
[groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ) `qᵉ : Gᵉ → G/N`ᵉ suchᵉ
thatᵉ `Nᵉ ⊆ᵉ kerᵉ q`,ᵉ andᵉ suchᵉ thatᵉ `q`ᵉ satisfiesᵉ theᵉ **universalᵉ propertyᵉ ofᵉ theᵉ
quotientᵉ group**,ᵉ whichᵉ assertsᵉ thatᵉ anyᵉ groupᵉ homomorphismᵉ `fᵉ : Gᵉ → H`ᵉ suchᵉ
thatᵉ `Nᵉ ⊆ᵉ kerᵉ f`ᵉ extendsᵉ uniquelyᵉ alongᵉ `q`ᵉ to aᵉ groupᵉ homomorphismᵉ `G/Nᵉ → H`.ᵉ
Inᵉ otherᵉ words,ᵉ theᵉ universalᵉ propertyᵉ ofᵉ theᵉ quotientᵉ groupᵉ `G/N`ᵉ assertsᵉ thatᵉ
theᵉ mapᵉ

```text
  hom-Groupᵉ G/Nᵉ Hᵉ → nullifying-hom-Groupᵉ Gᵉ Hᵉ Nᵉ
```

fromᵉ groupᵉ homomorphismsᵉ `G/Nᵉ → H`ᵉ to
[`N`-nullifyingᵉ groupᵉ homomorphism](group-theory.nullifying-group-homomorphisms.mdᵉ)
`Gᵉ → H`ᵉ isᵉ anᵉ [equivalence](foundation-core.equivalences.md).ᵉ Recallᵉ thatᵉ aᵉ
groupᵉ homomorphismᵉ isᵉ saidᵉ to beᵉ `N`-nullifyingᵉ ifᵉ `N`ᵉ isᵉ containedᵉ in theᵉ
[kernel](group-theory.kernels-homomorphisms-groups.mdᵉ) ofᵉ `f`.ᵉ

## Definitions

### The universal property of quotient groups

```agda
precomp-nullifying-hom-Groupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ)
  (Hᵉ : Groupᵉ l3ᵉ) (fᵉ : nullifying-hom-Groupᵉ Gᵉ Hᵉ Nᵉ)
  (Kᵉ : Groupᵉ l4ᵉ) → hom-Groupᵉ Hᵉ Kᵉ → nullifying-hom-Groupᵉ Gᵉ Kᵉ Nᵉ
pr1ᵉ (precomp-nullifying-hom-Groupᵉ Gᵉ Nᵉ Hᵉ fᵉ Kᵉ gᵉ) =
  comp-hom-Groupᵉ Gᵉ Hᵉ Kᵉ gᵉ (hom-nullifying-hom-Groupᵉ Gᵉ Hᵉ Nᵉ fᵉ)
pr2ᵉ (precomp-nullifying-hom-Groupᵉ Gᵉ Nᵉ Hᵉ fᵉ Kᵉ gᵉ) hᵉ pᵉ =
  ( invᵉ (preserves-unit-hom-Groupᵉ Hᵉ Kᵉ gᵉ)) ∙ᵉ
  ( apᵉ
    ( map-hom-Groupᵉ Hᵉ Kᵉ gᵉ)
    ( nullifies-normal-subgroup-nullifying-hom-Groupᵉ Gᵉ Hᵉ Nᵉ fᵉ hᵉ pᵉ))

universal-property-quotient-Groupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ) (Qᵉ : Groupᵉ l3ᵉ)
  (qᵉ : nullifying-hom-Groupᵉ Gᵉ Qᵉ Nᵉ) → UUωᵉ
universal-property-quotient-Groupᵉ Gᵉ Nᵉ Qᵉ qᵉ =
  {lᵉ : Level} (Hᵉ : Groupᵉ lᵉ) → is-equivᵉ (precomp-nullifying-hom-Groupᵉ Gᵉ Nᵉ Qᵉ qᵉ Hᵉ)
```

### The quotient group

#### The quotient map and the underlying set of the quotient group

Theᵉ underlyingᵉ [set](foundation-core.sets.mdᵉ) ofᵉ theᵉ quotientᵉ groupᵉ isᵉ definedᵉ
asᵉ theᵉ [setᵉ quotient](foundation.set-quotients.mdᵉ) ofᵉ theᵉ
[equivalenceᵉ relation](foundation.equivalence-relations.mdᵉ) inducedᵉ byᵉ theᵉ
normalᵉ subgroupᵉ `N`ᵉ ofᵉ `G`.ᵉ Byᵉ thisᵉ constructionᵉ weᵉ immediatelyᵉ obtainᵉ theᵉ
quotientᵉ mapᵉ `qᵉ : Gᵉ → G/N`,ᵉ whichᵉ willᵉ beᵉ
[surjective](foundation.surjective-maps.mdᵉ) andᵉ
[effective](foundation.effective-maps-equivalence-relations.md).ᵉ Thisᵉ meansᵉ thatᵉ
theᵉ quotientᵉ groupᵉ satisfiesᵉ theᵉ conditionᵉ

```text
  x⁻¹yᵉ ∈ᵉ Nᵉ ↔ᵉ qᵉ xᵉ ＝ᵉ qᵉ y.ᵉ
```

Weᵉ willᵉ concludeᵉ laterᵉ thatᵉ thisᵉ impliesᵉ thatᵉ theᵉ quotientᵉ mapᵉ nullifiesᵉ theᵉ
normalᵉ subgroupᵉ `N`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ)
  where

  set-quotient-Groupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-quotient-Groupᵉ =
    quotient-Setᵉ (equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)

  type-quotient-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-quotient-Groupᵉ =
    set-quotientᵉ (equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)

  is-set-type-quotient-Groupᵉ : is-setᵉ type-quotient-Groupᵉ
  is-set-type-quotient-Groupᵉ =
    is-set-set-quotientᵉ (equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)

  map-quotient-hom-Groupᵉ : type-Groupᵉ Gᵉ → type-quotient-Groupᵉ
  map-quotient-hom-Groupᵉ =
    quotient-mapᵉ (equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)

  is-surjective-map-quotient-hom-Groupᵉ :
    is-surjectiveᵉ map-quotient-hom-Groupᵉ
  is-surjective-map-quotient-hom-Groupᵉ =
    is-surjective-quotient-mapᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)

  is-effective-map-quotient-hom-Groupᵉ :
    is-effectiveᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( map-quotient-hom-Groupᵉ)
  is-effective-map-quotient-hom-Groupᵉ =
    is-effective-quotient-mapᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)

  abstract
    apply-effectiveness-map-quotient-hom-Groupᵉ :
      {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
      map-quotient-hom-Groupᵉ xᵉ ＝ᵉ map-quotient-hom-Groupᵉ yᵉ →
      sim-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ xᵉ yᵉ
    apply-effectiveness-map-quotient-hom-Groupᵉ =
      apply-effectiveness-quotient-mapᵉ
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)

  abstract
    apply-effectiveness-map-quotient-hom-Group'ᵉ :
      {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
      sim-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ xᵉ yᵉ →
      map-quotient-hom-Groupᵉ xᵉ ＝ᵉ map-quotient-hom-Groupᵉ yᵉ
    apply-effectiveness-map-quotient-hom-Group'ᵉ =
      apply-effectiveness-quotient-map'ᵉ
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)

  reflecting-map-quotient-hom-Groupᵉ :
    reflecting-map-equivalence-relationᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( type-quotient-Groupᵉ)
  reflecting-map-quotient-hom-Groupᵉ =
    reflecting-map-quotient-mapᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)

  is-set-quotient-set-quotient-Groupᵉ :
    is-set-quotientᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( set-quotient-Groupᵉ)
      ( reflecting-map-quotient-hom-Groupᵉ)
  is-set-quotient-set-quotient-Groupᵉ =
    is-set-quotient-set-quotientᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
```

#### The group structure on the quotient group

Weᵉ nowᵉ introduceᵉ theᵉ groupᵉ structureᵉ onᵉ theᵉ underlyingᵉ setᵉ ofᵉ theᵉ quotientᵉ
group.ᵉ Theᵉ multiplication,ᵉ unit,ᵉ andᵉ inversesᵉ areᵉ definedᵉ byᵉ theᵉ universalᵉ
propertyᵉ ofᵉ theᵉ setᵉ quotientᵉ asᵉ theᵉ uniqueᵉ mapsᵉ equippedᵉ with identificationsᵉ

```text
  (qx)(qyᵉ) ＝ᵉ q(xyᵉ)
         1 ＝ᵉ q1ᵉ
    (qx)⁻¹ᵉ ＝ᵉ q(x⁻¹ᵉ)
```

Theᵉ groupᵉ lawsᵉ followᵉ byᵉ theᵉ inductionᵉ principleᵉ forᵉ setᵉ quotients.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ)
  where

  unit-quotient-Groupᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ
  unit-quotient-Groupᵉ = map-quotient-hom-Groupᵉ Gᵉ Nᵉ (unit-Groupᵉ Gᵉ)

  binary-hom-mul-quotient-Groupᵉ :
    binary-hom-equivalence-relationᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
  pr1ᵉ binary-hom-mul-quotient-Groupᵉ = mul-Groupᵉ Gᵉ
  pr2ᵉ binary-hom-mul-quotient-Groupᵉ =
    mul-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ

  mul-quotient-Groupᵉ :
    (xᵉ yᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ) → type-quotient-Groupᵉ Gᵉ Nᵉ
  mul-quotient-Groupᵉ =
    binary-map-set-quotientᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( binary-hom-mul-quotient-Groupᵉ)

  mul-quotient-Group'ᵉ :
    (xᵉ yᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ) → type-quotient-Groupᵉ Gᵉ Nᵉ
  mul-quotient-Group'ᵉ xᵉ yᵉ = mul-quotient-Groupᵉ yᵉ xᵉ

  abstract
    compute-mul-quotient-Groupᵉ :
      (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
      mul-quotient-Groupᵉ
        ( map-quotient-hom-Groupᵉ Gᵉ Nᵉ xᵉ)
        ( map-quotient-hom-Groupᵉ Gᵉ Nᵉ yᵉ) ＝ᵉ
      map-quotient-hom-Groupᵉ Gᵉ Nᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ)
    compute-mul-quotient-Groupᵉ =
      compute-binary-map-set-quotientᵉ
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
        ( binary-hom-mul-quotient-Groupᵉ)

  hom-inv-quotient-Groupᵉ :
    hom-equivalence-relationᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
  pr1ᵉ hom-inv-quotient-Groupᵉ = inv-Groupᵉ Gᵉ
  pr2ᵉ hom-inv-quotient-Groupᵉ = inv-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ

  inv-quotient-Groupᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ → type-quotient-Groupᵉ Gᵉ Nᵉ
  inv-quotient-Groupᵉ =
    map-set-quotientᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( hom-inv-quotient-Groupᵉ)

  abstract
    compute-inv-quotient-Groupᵉ :
      (xᵉ : type-Groupᵉ Gᵉ) →
      inv-quotient-Groupᵉ (map-quotient-hom-Groupᵉ Gᵉ Nᵉ xᵉ) ＝ᵉ
      map-quotient-hom-Groupᵉ Gᵉ Nᵉ (inv-Groupᵉ Gᵉ xᵉ)
    compute-inv-quotient-Groupᵉ =
      coherence-square-map-set-quotientᵉ
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
        ( hom-inv-quotient-Groupᵉ)

  abstract
    left-unit-law-mul-quotient-Groupᵉ :
      (xᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ) →
      mul-quotient-Groupᵉ unit-quotient-Groupᵉ xᵉ ＝ᵉ xᵉ
    left-unit-law-mul-quotient-Groupᵉ =
      induction-set-quotientᵉ
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
        ( λ yᵉ →
          Id-Propᵉ
            ( set-quotient-Groupᵉ Gᵉ Nᵉ)
            ( mul-quotient-Groupᵉ unit-quotient-Groupᵉ yᵉ)
            ( yᵉ))
        ( λ xᵉ →
          ( compute-mul-quotient-Groupᵉ (unit-Groupᵉ Gᵉ) xᵉ) ∙ᵉ
          ( apᵉ (map-quotient-hom-Groupᵉ Gᵉ Nᵉ) (left-unit-law-mul-Groupᵉ Gᵉ xᵉ)))

  abstract
    right-unit-law-mul-quotient-Groupᵉ :
      (xᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ) →
      mul-quotient-Groupᵉ xᵉ unit-quotient-Groupᵉ ＝ᵉ xᵉ
    right-unit-law-mul-quotient-Groupᵉ =
      induction-set-quotientᵉ
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
        ( λ yᵉ →
          Id-Propᵉ
            ( set-quotient-Groupᵉ Gᵉ Nᵉ)
            ( mul-quotient-Groupᵉ yᵉ unit-quotient-Groupᵉ)
            ( yᵉ))
        ( λ xᵉ →
          ( compute-mul-quotient-Groupᵉ xᵉ (unit-Groupᵉ Gᵉ)) ∙ᵉ
          ( apᵉ (map-quotient-hom-Groupᵉ Gᵉ Nᵉ) (right-unit-law-mul-Groupᵉ Gᵉ xᵉ)))

  abstract
    associative-mul-quotient-Groupᵉ :
      (xᵉ yᵉ zᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ) →
      ( mul-quotient-Groupᵉ (mul-quotient-Groupᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
      ( mul-quotient-Groupᵉ xᵉ (mul-quotient-Groupᵉ yᵉ zᵉ))
    associative-mul-quotient-Groupᵉ =
      triple-induction-set-quotient'ᵉ
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
        ( λ xᵉ yᵉ zᵉ →
          Id-Propᵉ
            ( set-quotient-Groupᵉ Gᵉ Nᵉ)
            ( mul-quotient-Groupᵉ (mul-quotient-Groupᵉ xᵉ yᵉ) zᵉ)
            ( mul-quotient-Groupᵉ xᵉ (mul-quotient-Groupᵉ yᵉ zᵉ)))
        ( λ xᵉ yᵉ zᵉ →
          ( apᵉ
            ( mul-quotient-Group'ᵉ (map-quotient-hom-Groupᵉ Gᵉ Nᵉ zᵉ))
            ( compute-mul-quotient-Groupᵉ xᵉ yᵉ)) ∙ᵉ
          ( compute-mul-quotient-Groupᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) zᵉ) ∙ᵉ
          ( apᵉ
            ( map-quotient-hom-Groupᵉ Gᵉ Nᵉ)
            ( associative-mul-Groupᵉ Gᵉ xᵉ yᵉ zᵉ)) ∙ᵉ
          ( invᵉ (compute-mul-quotient-Groupᵉ xᵉ (mul-Groupᵉ Gᵉ yᵉ zᵉ))) ∙ᵉ
          ( apᵉ
            ( mul-quotient-Groupᵉ (map-quotient-hom-Groupᵉ Gᵉ Nᵉ xᵉ))
            ( invᵉ (compute-mul-quotient-Groupᵉ yᵉ zᵉ))))

  abstract
    left-inverse-law-mul-quotient-Groupᵉ :
      (xᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ) →
      ( mul-quotient-Groupᵉ (inv-quotient-Groupᵉ xᵉ) xᵉ) ＝ᵉ
      ( unit-quotient-Groupᵉ)
    left-inverse-law-mul-quotient-Groupᵉ =
      induction-set-quotientᵉ
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
        ( λ yᵉ →
          Id-Propᵉ
            ( set-quotient-Groupᵉ Gᵉ Nᵉ)
            ( mul-quotient-Groupᵉ (inv-quotient-Groupᵉ yᵉ) yᵉ)
            ( unit-quotient-Groupᵉ))
        ( λ xᵉ →
          ( apᵉ
            ( mul-quotient-Group'ᵉ (map-quotient-hom-Groupᵉ Gᵉ Nᵉ xᵉ))
            ( compute-inv-quotient-Groupᵉ xᵉ)) ∙ᵉ
          ( compute-mul-quotient-Groupᵉ (inv-Groupᵉ Gᵉ xᵉ) xᵉ) ∙ᵉ
          ( apᵉ
            ( map-quotient-hom-Groupᵉ Gᵉ Nᵉ)
            ( left-inverse-law-mul-Groupᵉ Gᵉ xᵉ)))

  abstract
    right-inverse-law-mul-quotient-Groupᵉ :
      (xᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ) →
      ( mul-quotient-Groupᵉ xᵉ (inv-quotient-Groupᵉ xᵉ)) ＝ᵉ
      ( unit-quotient-Groupᵉ)
    right-inverse-law-mul-quotient-Groupᵉ =
      induction-set-quotientᵉ
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
        ( λ yᵉ →
          Id-Propᵉ
            ( set-quotient-Groupᵉ Gᵉ Nᵉ)
            ( mul-quotient-Groupᵉ yᵉ (inv-quotient-Groupᵉ yᵉ))
            ( unit-quotient-Groupᵉ))
        ( λ xᵉ →
          ( apᵉ
            ( mul-quotient-Groupᵉ (map-quotient-hom-Groupᵉ Gᵉ Nᵉ xᵉ))
            ( compute-inv-quotient-Groupᵉ xᵉ)) ∙ᵉ
          ( compute-mul-quotient-Groupᵉ xᵉ (inv-Groupᵉ Gᵉ xᵉ)) ∙ᵉ
          ( apᵉ
            ( map-quotient-hom-Groupᵉ Gᵉ Nᵉ)
            ( right-inverse-law-mul-Groupᵉ Gᵉ xᵉ)))

  semigroup-quotient-Groupᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ semigroup-quotient-Groupᵉ = set-quotient-Groupᵉ Gᵉ Nᵉ
  pr1ᵉ (pr2ᵉ semigroup-quotient-Groupᵉ) = mul-quotient-Groupᵉ
  pr2ᵉ (pr2ᵉ semigroup-quotient-Groupᵉ) = associative-mul-quotient-Groupᵉ

  quotient-Groupᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ quotient-Groupᵉ = semigroup-quotient-Groupᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ quotient-Groupᵉ)) = unit-quotient-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ quotient-Groupᵉ))) = left-unit-law-mul-quotient-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ quotient-Groupᵉ))) = right-unit-law-mul-quotient-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ quotient-Groupᵉ)) = inv-quotient-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ quotient-Groupᵉ))) = left-inverse-law-mul-quotient-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ quotient-Groupᵉ))) = right-inverse-law-mul-quotient-Groupᵉ
```

#### The quotient homomorphism into the quotient group

Theᵉ quotientᵉ mapᵉ `qᵉ : Gᵉ → G/N`ᵉ preservesᵉ theᵉ groupᵉ structureᵉ andᵉ nullifiesᵉ theᵉ
normalᵉ subgroupᵉ `N`.ᵉ Bothᵉ theseᵉ claimsᵉ followᵉ fairlyᵉ directlyᵉ fromᵉ theᵉ
definitionsᵉ ofᵉ theᵉ quotientᵉ mapᵉ `q`ᵉ andᵉ theᵉ groupᵉ operationsᵉ onᵉ `G/N`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ)
  where

  abstract
    preserves-mul-quotient-hom-Groupᵉ :
      preserves-mul-Groupᵉ Gᵉ
        ( quotient-Groupᵉ Gᵉ Nᵉ)
        ( map-quotient-hom-Groupᵉ Gᵉ Nᵉ)
    preserves-mul-quotient-hom-Groupᵉ =
      invᵉ (compute-mul-quotient-Groupᵉ Gᵉ Nᵉ _ _)

  preserves-unit-quotient-hom-Groupᵉ :
    map-quotient-hom-Groupᵉ Gᵉ Nᵉ (unit-Groupᵉ Gᵉ) ＝ᵉ unit-quotient-Groupᵉ Gᵉ Nᵉ
  preserves-unit-quotient-hom-Groupᵉ = reflᵉ

  abstract
    preserves-inv-quotient-hom-Groupᵉ :
      (xᵉ : type-Groupᵉ Gᵉ) →
      map-quotient-hom-Groupᵉ Gᵉ Nᵉ (inv-Groupᵉ Gᵉ xᵉ) ＝ᵉ
      inv-quotient-Groupᵉ Gᵉ Nᵉ (map-quotient-hom-Groupᵉ Gᵉ Nᵉ xᵉ)
    preserves-inv-quotient-hom-Groupᵉ xᵉ =
      invᵉ (compute-inv-quotient-Groupᵉ Gᵉ Nᵉ xᵉ)

  quotient-hom-Groupᵉ : hom-Groupᵉ Gᵉ (quotient-Groupᵉ Gᵉ Nᵉ)
  pr1ᵉ quotient-hom-Groupᵉ = map-quotient-hom-Groupᵉ Gᵉ Nᵉ
  pr2ᵉ quotient-hom-Groupᵉ = preserves-mul-quotient-hom-Groupᵉ

  nullifies-normal-subgroup-quotient-hom-Groupᵉ :
    nullifies-normal-subgroup-hom-Groupᵉ Gᵉ
      ( quotient-Groupᵉ Gᵉ Nᵉ)
      ( quotient-hom-Groupᵉ)
      ( Nᵉ)
  nullifies-normal-subgroup-quotient-hom-Groupᵉ xᵉ nᵉ =
    invᵉ
      ( apply-effectiveness-map-quotient-hom-Group'ᵉ Gᵉ Nᵉ
        ( unit-congruence-Normal-Subgroup'ᵉ Gᵉ Nᵉ nᵉ))

  nullifying-quotient-hom-Groupᵉ : nullifying-hom-Groupᵉ Gᵉ (quotient-Groupᵉ Gᵉ Nᵉ) Nᵉ
  pr1ᵉ nullifying-quotient-hom-Groupᵉ = quotient-hom-Groupᵉ
  pr2ᵉ nullifying-quotient-hom-Groupᵉ =
    nullifies-normal-subgroup-quotient-hom-Groupᵉ
```

#### Induction on quotient groups

Theᵉ **inductionᵉ principle**ᵉ ofᵉ quotientᵉ groupsᵉ assertsᵉ thatᵉ forᵉ anyᵉ propertyᵉ `P`ᵉ
ofᵉ elementsᵉ ofᵉ theᵉ quotientᵉ groupᵉ `G/N`,ᵉ in orderᵉ to showᵉ thatᵉ `Pᵉ x`ᵉ holdsᵉ forᵉ
allᵉ `xᵉ : G/N`ᵉ itᵉ sufficesᵉ to showᵉ thatᵉ `Pᵉ qy`ᵉ holdsᵉ forᵉ allᵉ `yᵉ : G`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ)
  (Pᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ → Propᵉ l3ᵉ)
  where

  equiv-induction-quotient-Groupᵉ :
    ((xᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ) → type-Propᵉ (Pᵉ xᵉ)) ≃ᵉ
    ((xᵉ : type-Groupᵉ Gᵉ) → type-Propᵉ (Pᵉ (map-quotient-hom-Groupᵉ Gᵉ Nᵉ xᵉ)))
  equiv-induction-quotient-Groupᵉ =
    equiv-induction-set-quotientᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( Pᵉ)

  abstract
    induction-quotient-Groupᵉ :
      ((xᵉ : type-Groupᵉ Gᵉ) → type-Propᵉ (Pᵉ (map-quotient-hom-Groupᵉ Gᵉ Nᵉ xᵉ))) →
      ((xᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ) → type-Propᵉ (Pᵉ xᵉ))
    induction-quotient-Groupᵉ =
      induction-set-quotientᵉ
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
        ( Pᵉ)
```

#### Double induction on quotient groups

Theᵉ **doubleᵉ inductionᵉ principle**ᵉ ofᵉ quotientᵉ groupsᵉ assertsᵉ thatᵉ forᵉ anyᵉ
propertyᵉ `P`ᵉ ofᵉ pairsᵉ ofᵉ elementsᵉ ofᵉ theᵉ quotientᵉ groupᵉ `G/N`,ᵉ in orderᵉ to showᵉ
thatᵉ `Pᵉ xᵉ y`ᵉ holdsᵉ forᵉ allᵉ `xᵉ yᵉ : G/N`ᵉ itᵉ sufficesᵉ to showᵉ thatᵉ `Pᵉ quᵉ qv`ᵉ holdsᵉ
forᵉ allᵉ `uᵉ vᵉ : G`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  (Nᵉ : Normal-Subgroupᵉ l3ᵉ Gᵉ) (Mᵉ : Normal-Subgroupᵉ l4ᵉ Hᵉ)
  (Pᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ → type-quotient-Groupᵉ Hᵉ Mᵉ → Propᵉ l5ᵉ)
  where

  equiv-double-induction-quotient-Groupᵉ :
    ( (xᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ) (yᵉ : type-quotient-Groupᵉ Hᵉ Mᵉ) →
      type-Propᵉ (Pᵉ xᵉ yᵉ)) ≃ᵉ
    ( (xᵉ : type-Groupᵉ Gᵉ) (yᵉ : type-Groupᵉ Hᵉ) →
      type-Propᵉ
        ( Pᵉ (map-quotient-hom-Groupᵉ Gᵉ Nᵉ xᵉ) (map-quotient-hom-Groupᵉ Hᵉ Mᵉ yᵉ)))
  equiv-double-induction-quotient-Groupᵉ =
    equiv-double-induction-set-quotientᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Hᵉ Mᵉ)
      ( Pᵉ)

  abstract
    double-induction-quotient-Groupᵉ :
      ( (xᵉ : type-Groupᵉ Gᵉ) (yᵉ : type-Groupᵉ Hᵉ) →
        type-Propᵉ
          ( Pᵉ (map-quotient-hom-Groupᵉ Gᵉ Nᵉ xᵉ) (map-quotient-hom-Groupᵉ Hᵉ Mᵉ yᵉ))) →
      ( (xᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ) (yᵉ : type-quotient-Groupᵉ Hᵉ Mᵉ) →
        type-Propᵉ (Pᵉ xᵉ yᵉ))
    double-induction-quotient-Groupᵉ =
      double-induction-set-quotientᵉ
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Hᵉ Mᵉ)
        ( Pᵉ)
```

#### The universal property of the quotient group

Theᵉ universalᵉ propertyᵉ ofᵉ theᵉ quotientᵉ groupᵉ `G/N`ᵉ assertsᵉ thatᵉ forᵉ anyᵉ groupᵉ
`H`ᵉ theᵉ precompositionᵉ functionᵉ

```text
  hom-Groupᵉ G/Nᵉ Hᵉ → nullifying-hom-Groupᵉ Gᵉ Hᵉ Nᵉ
```

isᵉ anᵉ equivalence.ᵉ

**Proof:**ᵉ Letᵉ `G`ᵉ andᵉ `H`ᵉ beᵉ groupsᵉ andᵉ let `N`ᵉ beᵉ aᵉ normalᵉ subgroupᵉ ofᵉ `G`.ᵉ
Ourᵉ goalᵉ isᵉ to showᵉ thatᵉ theᵉ precompositionᵉ functionᵉ

```text
  hom-Groupᵉ G/Nᵉ Hᵉ → nullifying-hom-Groupᵉ Gᵉ Hᵉ Nᵉ
```

isᵉ anᵉ equivalence.ᵉ Toᵉ seeᵉ this,ᵉ noteᵉ thatᵉ theᵉ aboveᵉ mapᵉ isᵉ aᵉ compositeᵉ ofᵉ theᵉ
mapsᵉ

```text
  hom-Groupᵉ G/Nᵉ Hᵉ → Σᵉ (reflecting-mapᵉ Gᵉ Hᵉ) (λ uᵉ → preserves-mulᵉ (pr1ᵉ uᵉ))
                  ≃ᵉ Σᵉ (hom-Groupᵉ Gᵉ Hᵉ) (λ fᵉ → is-nullifyingᵉ fᵉ)
```

Theᵉ secondᵉ mapᵉ isᵉ theᵉ equivalenceᵉ `compute-nullifying-hom-Group`ᵉ constructedᵉ
above.ᵉ Theᵉ firstᵉ mapᵉ isᵉ anᵉ equivalenceᵉ byᵉ theᵉ universalᵉ propertyᵉ ofᵉ setᵉ
quotients,ᵉ byᵉ whichᵉ weᵉ haveᵉ:

```text
  (G/Nᵉ → Hᵉ) ≃ᵉ reflecting-mapᵉ Gᵉ H.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ)
  where

  top-triangle-is-quotient-group-quotient-Groupᵉ :
    {lᵉ : Level} (Hᵉ : Groupᵉ lᵉ) →
    hom-Groupᵉ (quotient-Groupᵉ Gᵉ Nᵉ) Hᵉ →
    Σᵉ ( reflecting-map-equivalence-relationᵉ
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
        ( type-Groupᵉ Hᵉ))
      ( λ fᵉ → preserves-mul-Groupᵉ Gᵉ Hᵉ (pr1ᵉ fᵉ))
  top-triangle-is-quotient-group-quotient-Groupᵉ Hᵉ =
    map-Σᵉ
      ( λ fᵉ → preserves-mul-Groupᵉ Gᵉ Hᵉ (pr1ᵉ fᵉ))
      ( precomp-Set-Quotientᵉ
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
        ( set-quotient-Groupᵉ Gᵉ Nᵉ)
        ( reflecting-map-quotient-mapᵉ
          ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ))
        ( set-Groupᵉ Hᵉ))
      ( λ fᵉ μᵉ →
        preserves-mul-comp-hom-Groupᵉ Gᵉ
          ( quotient-Groupᵉ Gᵉ Nᵉ)
          ( Hᵉ)
          ( fᵉ ,ᵉ μᵉ)
          ( quotient-hom-Groupᵉ Gᵉ Nᵉ))

  triangle-is-quotient-group-quotient-Groupᵉ :
    {lᵉ : Level} (Hᵉ : Groupᵉ lᵉ) →
    coherence-triangle-mapsᵉ
      ( precomp-nullifying-hom-Groupᵉ Gᵉ Nᵉ
        ( quotient-Groupᵉ Gᵉ Nᵉ)
        ( nullifying-quotient-hom-Groupᵉ Gᵉ Nᵉ)
        ( Hᵉ))
      ( map-equivᵉ (compute-nullifying-hom-Groupᵉ Gᵉ Hᵉ Nᵉ))
      ( top-triangle-is-quotient-group-quotient-Groupᵉ Hᵉ)
  triangle-is-quotient-group-quotient-Groupᵉ Hᵉ xᵉ =
    eq-type-subtypeᵉ
      ( λ fᵉ → nullifies-normal-subgroup-prop-hom-Groupᵉ Gᵉ Hᵉ fᵉ Nᵉ)
      ( reflᵉ)

  abstract
    is-equiv-top-triangle-is-quotient-group-quotient-Groupᵉ :
      {lᵉ : Level} (Hᵉ : Groupᵉ lᵉ) →
      is-equivᵉ (top-triangle-is-quotient-group-quotient-Groupᵉ Hᵉ)
    is-equiv-top-triangle-is-quotient-group-quotient-Groupᵉ Hᵉ =
      is-equiv-map-Σᵉ
        ( λ fᵉ → preserves-mul-Groupᵉ Gᵉ Hᵉ (pr1ᵉ fᵉ))
        ( is-set-quotient-set-quotientᵉ
          ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ)
          ( set-Groupᵉ Hᵉ))
        ( λ fᵉ →
          is-equiv-has-converse-is-propᵉ
            ( is-prop-preserves-mul-Groupᵉ (quotient-Groupᵉ Gᵉ Nᵉ) Hᵉ fᵉ)
            ( is-prop-preserves-mul-Groupᵉ Gᵉ Hᵉ
              ( fᵉ ∘ᵉ map-quotient-hom-Groupᵉ Gᵉ Nᵉ))
            ( λ μᵉ {aᵉ} {bᵉ} →
              double-induction-quotient-Groupᵉ Gᵉ Gᵉ Nᵉ Nᵉ
                ( λ xᵉ yᵉ → Id-Propᵉ (set-Groupᵉ Hᵉ) _ _)
                ( λ xᵉ yᵉ → apᵉ fᵉ (compute-mul-quotient-Groupᵉ Gᵉ Nᵉ xᵉ yᵉ) ∙ᵉ μᵉ)
                ( aᵉ)
                ( bᵉ)))

  abstract
    is-quotient-group-quotient-Groupᵉ :
      universal-property-quotient-Groupᵉ Gᵉ Nᵉ
        ( quotient-Groupᵉ Gᵉ Nᵉ)
        ( nullifying-quotient-hom-Groupᵉ Gᵉ Nᵉ)
    is-quotient-group-quotient-Groupᵉ Hᵉ =
      is-equiv-left-map-triangleᵉ
        ( precomp-nullifying-hom-Groupᵉ Gᵉ Nᵉ
          ( quotient-Groupᵉ Gᵉ Nᵉ)
          ( nullifying-quotient-hom-Groupᵉ Gᵉ Nᵉ)
          ( Hᵉ))
        ( map-equivᵉ (compute-nullifying-hom-Groupᵉ Gᵉ Hᵉ Nᵉ))
        ( top-triangle-is-quotient-group-quotient-Groupᵉ Hᵉ)
        ( triangle-is-quotient-group-quotient-Groupᵉ Hᵉ)
        ( is-equiv-top-triangle-is-quotient-group-quotient-Groupᵉ Hᵉ)
        ( is-equiv-map-equivᵉ (compute-nullifying-hom-Groupᵉ Gᵉ Hᵉ Nᵉ))
```

### The unique mapping property of the quotient group

Theᵉ uniqueᵉ mappingᵉ propertyᵉ ofᵉ theᵉ quotientᵉ groupᵉ `G/N`ᵉ assertsᵉ thatᵉ forᵉ anyᵉ
groupᵉ `H`ᵉ andᵉ anyᵉ `N`-nullifyingᵉ groupᵉ homomorphismᵉ `fᵉ : Gᵉ → H`,ᵉ theᵉ typeᵉ ofᵉ
groupᵉ homomorphismsᵉ `gᵉ : G/Nᵉ → H`ᵉ suchᵉ thatᵉ `fᵉ ~ᵉ gᵉ ∘ᵉ q`ᵉ isᵉ
[contractible](foundation-core.contractible-types.md).ᵉ Inᵉ otherᵉ words,ᵉ itᵉ
assertsᵉ thatᵉ anyᵉ nullifyingᵉ groupᵉ homomorphismᵉ `fᵉ : Gᵉ → H`ᵉ extendsᵉ uniquelyᵉ
alongᵉ `q`ᵉ:

```text
     Gᵉ
    | \ᵉ
  qᵉ |  \ᵉ fᵉ
    |   \ᵉ
    ∨ᵉ    ∨ᵉ
   G/Nᵉ ->ᵉ H.ᵉ
       ∃!ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ)
  (Hᵉ : Groupᵉ l3ᵉ)
  where

  abstract
    unique-mapping-property-quotient-Groupᵉ :
      (fᵉ : nullifying-hom-Groupᵉ Gᵉ Hᵉ Nᵉ) →
      is-contrᵉ
        ( Σᵉ ( hom-Groupᵉ (quotient-Groupᵉ Gᵉ Nᵉ) Hᵉ)
            ( λ gᵉ →
              htpy-hom-Groupᵉ Gᵉ Hᵉ
                ( hom-nullifying-hom-Groupᵉ Gᵉ Hᵉ Nᵉ
                  ( precomp-nullifying-hom-Groupᵉ Gᵉ Nᵉ
                    ( quotient-Groupᵉ Gᵉ Nᵉ)
                    ( nullifying-quotient-hom-Groupᵉ Gᵉ Nᵉ)
                    ( Hᵉ)
                    ( gᵉ)))
                ( hom-nullifying-hom-Groupᵉ Gᵉ Hᵉ Nᵉ fᵉ)))
    unique-mapping-property-quotient-Groupᵉ fᵉ =
      is-contr-equiv'ᵉ _
        ( equiv-totᵉ
          ( λ gᵉ →
            ( extensionality-hom-Groupᵉ Gᵉ Hᵉ _ _) ∘eᵉ
            ( extensionality-type-subtype'ᵉ
              ( λ hᵉ → nullifies-normal-subgroup-prop-hom-Groupᵉ Gᵉ Hᵉ hᵉ Nᵉ)
              ( _)
              ( _))))
        ( is-contr-map-is-equivᵉ
          ( is-quotient-group-quotient-Groupᵉ Gᵉ Nᵉ Hᵉ)
          ( fᵉ))

  abstract
    hom-universal-property-quotient-Groupᵉ :
      (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
      (nᵉ : nullifies-normal-subgroup-hom-Groupᵉ Gᵉ Hᵉ fᵉ Nᵉ) →
      hom-Groupᵉ (quotient-Groupᵉ Gᵉ Nᵉ) Hᵉ
    hom-universal-property-quotient-Groupᵉ fᵉ nᵉ =
      pr1ᵉ (centerᵉ (unique-mapping-property-quotient-Groupᵉ (fᵉ ,ᵉ nᵉ)))

    compute-hom-universal-property-quotient-Groupᵉ :
      (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
      (nᵉ : nullifies-normal-subgroup-hom-Groupᵉ Gᵉ Hᵉ fᵉ Nᵉ) →
      htpy-hom-Groupᵉ Gᵉ Hᵉ
        ( hom-nullifying-hom-Groupᵉ Gᵉ Hᵉ Nᵉ
          ( precomp-nullifying-hom-Groupᵉ Gᵉ Nᵉ
            ( quotient-Groupᵉ Gᵉ Nᵉ)
            ( nullifying-quotient-hom-Groupᵉ Gᵉ Nᵉ)
            ( Hᵉ)
            ( hom-universal-property-quotient-Groupᵉ fᵉ nᵉ)))
        ( hom-nullifying-hom-Groupᵉ Gᵉ Hᵉ Nᵉ (fᵉ ,ᵉ nᵉ))
    compute-hom-universal-property-quotient-Groupᵉ fᵉ nᵉ =
      pr2ᵉ (centerᵉ (unique-mapping-property-quotient-Groupᵉ (fᵉ ,ᵉ nᵉ)))
```

## Properties

### An element is in a normal subgroup `N` if and only if it is in the kernel of the quotient group homomorphism `G → G/N`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ)
  where

  abstract
    is-in-kernel-quotient-hom-is-in-Normal-Subgroupᵉ :
      {xᵉ : type-Groupᵉ Gᵉ} → is-in-Normal-Subgroupᵉ Gᵉ Nᵉ xᵉ →
      is-in-kernel-hom-Groupᵉ Gᵉ (quotient-Groupᵉ Gᵉ Nᵉ) (quotient-hom-Groupᵉ Gᵉ Nᵉ) xᵉ
    is-in-kernel-quotient-hom-is-in-Normal-Subgroupᵉ =
      nullifies-normal-subgroup-quotient-hom-Groupᵉ Gᵉ Nᵉ _

  abstract
    is-in-normal-subgroup-is-in-kernel-quotient-hom-Groupᵉ :
      {xᵉ : type-Groupᵉ Gᵉ} →
      is-in-kernel-hom-Groupᵉ Gᵉ (quotient-Groupᵉ Gᵉ Nᵉ) (quotient-hom-Groupᵉ Gᵉ Nᵉ) xᵉ →
      is-in-Normal-Subgroupᵉ Gᵉ Nᵉ xᵉ
    is-in-normal-subgroup-is-in-kernel-quotient-hom-Groupᵉ {xᵉ} Hᵉ =
      unit-congruence-Normal-Subgroupᵉ Gᵉ Nᵉ
        ( apply-effectiveness-map-quotient-hom-Groupᵉ Gᵉ Nᵉ (invᵉ Hᵉ))
```