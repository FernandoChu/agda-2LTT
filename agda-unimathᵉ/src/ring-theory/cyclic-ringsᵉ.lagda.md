# Cyclic rings

```agda
module ring-theory.cyclic-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.ring-of-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.cyclic-groupsᵉ
open import group-theory.free-groups-with-one-generatorᵉ
open import group-theory.generating-elements-groupsᵉ
open import group-theory.groupsᵉ

open import ring-theory.integer-multiples-of-elements-ringsᵉ
open import ring-theory.invertible-elements-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Aᵉ [ring](ring-theory.rings.mdᵉ) isᵉ saidᵉ to beᵉ **cyclic**ᵉ ifᵉ itsᵉ underlyingᵉ
additiveᵉ [group](group-theory.groups.mdᵉ) isᵉ aᵉ
[cyclicᵉ group](group-theory.cyclic-groups.md).ᵉ Weᵉ willᵉ showᵉ thatᵉ theᵉ followingᵉ
threeᵉ claimsᵉ aboutᵉ aᵉ ringᵉ `R`ᵉ areᵉ equivalentᵉ:

1.ᵉ Theᵉ ringᵉ `R`ᵉ isᵉ cyclic.ᵉ
2.ᵉ Theᵉ elementᵉ `1`ᵉ isᵉ aᵉ
   [generatingᵉ element](group-theory.generating-elements-groups.mdᵉ) ofᵉ theᵉ
   [abelianᵉ group](group-theory.abelian-groups.mdᵉ) `(R,0,+,-)`.ᵉ
3.ᵉ Theᵉ [subset](foundation.subtypes.mdᵉ) ofᵉ generatingᵉ elementsᵉ ofᵉ `R`ᵉ isᵉ theᵉ
   subsetᵉ ofᵉ [invertibleᵉ elements](ring-theory.invertible-elements-rings.mdᵉ) ofᵉ
   `R`.ᵉ

Cyclicᵉ ringsᵉ thereforeᵉ haveᵉ aᵉ specifiedᵉ generatingᵉ element,ᵉ i.e.,ᵉ theᵉ elementᵉ
`1`.ᵉ Withᵉ thisᵉ factᵉ in theᵉ pocket,ᵉ itᵉ isᵉ easyᵉ to showᵉ thatᵉ cyclicᵉ ringsᵉ areᵉ
commutativeᵉ rings.ᵉ Furthermore,ᵉ theᵉ multiplicativeᵉ structureᵉ ofᵉ `R`ᵉ coincidesᵉ
with theᵉ multiplicativeᵉ structureᵉ constructedᵉ in
[`group-theory.generating-elements-groups`](group-theory.generating-elements-groups.mdᵉ)
using theᵉ generatingᵉ elementᵉ `1`.ᵉ Inᵉ particular,ᵉ itᵉ followsᵉ thatᵉ forᵉ anyᵉ cyclicᵉ
groupᵉ `G`,ᵉ theᵉ typeᵉ ofᵉ ringᵉ structuresᵉ onᵉ `G`ᵉ isᵉ equivalentᵉ with theᵉ typeᵉ ofᵉ
generatingᵉ elementsᵉ ofᵉ `G`.ᵉ

Noteᵉ thatᵉ theᵉ classificationᵉ ofᵉ cyclicᵉ unitalᵉ ringsᵉ isᵉ somewhatᵉ differentᵉ fromᵉ
theᵉ nonunitalᵉ cyclicᵉ ringsᵉ: Cyclicᵉ unitalᵉ ringsᵉ areᵉ
[quotients](ring-theory.quotient-rings.mdᵉ) ofᵉ theᵉ
[ringᵉ `ℤ`ᵉ ofᵉ integers](elementary-number-theory.ring-of-integers.md),ᵉ whereasᵉ
cyclicᵉ nonunitalᵉ ringsᵉ areᵉ isomorphicᵉ to [ideals](ring-theory.ideals-rings.mdᵉ)
ofᵉ quotientsᵉ ofᵉ theᵉ ringᵉ `ℤ`.ᵉ {{#citeᵉ BSCS05ᵉ}}

Sinceᵉ cyclicᵉ ringsᵉ areᵉ quotientsᵉ ofᵉ `ℤ`,ᵉ itᵉ followsᵉ thatᵉ quotientsᵉ ofᵉ cyclicᵉ
ringsᵉ areᵉ cyclicᵉ rings.ᵉ

## Definitions

### The predicate of being a cyclic ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-cyclic-prop-Ringᵉ : Propᵉ lᵉ
  is-cyclic-prop-Ringᵉ = is-cyclic-prop-Groupᵉ (group-Ringᵉ Rᵉ)

  is-cyclic-Ringᵉ : UUᵉ lᵉ
  is-cyclic-Ringᵉ = is-cyclic-Groupᵉ (group-Ringᵉ Rᵉ)

  is-prop-is-cyclic-Ringᵉ : is-propᵉ is-cyclic-Ringᵉ
  is-prop-is-cyclic-Ringᵉ = is-prop-is-cyclic-Groupᵉ (group-Ringᵉ Rᵉ)
```

### The predicate of the initial morphism being surjective

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-surjective-initial-hom-prop-Ringᵉ : Propᵉ lᵉ
  is-surjective-initial-hom-prop-Ringᵉ =
    is-surjective-Propᵉ (map-initial-hom-Ringᵉ Rᵉ)

  is-surjective-initial-hom-Ringᵉ : UUᵉ lᵉ
  is-surjective-initial-hom-Ringᵉ =
    type-Propᵉ is-surjective-initial-hom-prop-Ringᵉ

  is-prop-is-surjective-initial-hom-Ringᵉ :
    is-propᵉ is-surjective-initial-hom-Ringᵉ
  is-prop-is-surjective-initial-hom-Ringᵉ =
    is-prop-type-Propᵉ is-surjective-initial-hom-prop-Ringᵉ
```

### Cyclic rings

```agda
Cyclic-Ringᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Cyclic-Ringᵉ lᵉ = Σᵉ (Ringᵉ lᵉ) is-cyclic-Ringᵉ

module _
  {lᵉ : Level} (Rᵉ : Cyclic-Ringᵉ lᵉ)
  where

  ring-Cyclic-Ringᵉ : Ringᵉ lᵉ
  ring-Cyclic-Ringᵉ = pr1ᵉ Rᵉ

  ab-Cyclic-Ringᵉ : Abᵉ lᵉ
  ab-Cyclic-Ringᵉ = ab-Ringᵉ ring-Cyclic-Ringᵉ

  group-Cyclic-Ringᵉ : Groupᵉ lᵉ
  group-Cyclic-Ringᵉ = group-Ringᵉ ring-Cyclic-Ringᵉ

  is-cyclic-Cyclic-Ringᵉ : is-cyclic-Ringᵉ ring-Cyclic-Ringᵉ
  is-cyclic-Cyclic-Ringᵉ = pr2ᵉ Rᵉ

  cyclic-group-Cyclic-Ringᵉ : Cyclic-Groupᵉ lᵉ
  pr1ᵉ cyclic-group-Cyclic-Ringᵉ = group-Cyclic-Ringᵉ
  pr2ᵉ cyclic-group-Cyclic-Ringᵉ = is-cyclic-Cyclic-Ringᵉ

  type-Cyclic-Ringᵉ : UUᵉ lᵉ
  type-Cyclic-Ringᵉ = type-Ringᵉ ring-Cyclic-Ringᵉ

  set-Cyclic-Ringᵉ : Setᵉ lᵉ
  set-Cyclic-Ringᵉ = set-Ringᵉ ring-Cyclic-Ringᵉ

  zero-Cyclic-Ringᵉ : type-Cyclic-Ringᵉ
  zero-Cyclic-Ringᵉ = zero-Ringᵉ ring-Cyclic-Ringᵉ

  one-Cyclic-Ringᵉ : type-Cyclic-Ringᵉ
  one-Cyclic-Ringᵉ = one-Ringᵉ ring-Cyclic-Ringᵉ

  add-Cyclic-Ringᵉ : (xᵉ yᵉ : type-Cyclic-Ringᵉ) → type-Cyclic-Ringᵉ
  add-Cyclic-Ringᵉ = add-Ringᵉ ring-Cyclic-Ringᵉ

  neg-Cyclic-Ringᵉ : type-Cyclic-Ringᵉ → type-Cyclic-Ringᵉ
  neg-Cyclic-Ringᵉ = neg-Ringᵉ ring-Cyclic-Ringᵉ

  mul-Cyclic-Ringᵉ : (xᵉ yᵉ : type-Cyclic-Ringᵉ) → type-Cyclic-Ringᵉ
  mul-Cyclic-Ringᵉ = mul-Ringᵉ ring-Cyclic-Ringᵉ

  mul-Cyclic-Ring'ᵉ : (xᵉ yᵉ : type-Cyclic-Ringᵉ) → type-Cyclic-Ringᵉ
  mul-Cyclic-Ring'ᵉ = mul-Ring'ᵉ ring-Cyclic-Ringᵉ

  integer-multiple-Cyclic-Ringᵉ : ℤᵉ → type-Cyclic-Ringᵉ → type-Cyclic-Ringᵉ
  integer-multiple-Cyclic-Ringᵉ = integer-multiple-Ringᵉ ring-Cyclic-Ringᵉ

  left-unit-law-add-Cyclic-Ringᵉ :
    (xᵉ : type-Cyclic-Ringᵉ) →
    add-Cyclic-Ringᵉ zero-Cyclic-Ringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Cyclic-Ringᵉ =
    left-unit-law-add-Ringᵉ ring-Cyclic-Ringᵉ

  right-unit-law-add-Cyclic-Ringᵉ :
    (xᵉ : type-Cyclic-Ringᵉ) →
    add-Cyclic-Ringᵉ xᵉ zero-Cyclic-Ringᵉ ＝ᵉ xᵉ
  right-unit-law-add-Cyclic-Ringᵉ =
    right-unit-law-add-Ringᵉ ring-Cyclic-Ringᵉ

  associative-add-Cyclic-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Cyclic-Ringᵉ) →
    add-Cyclic-Ringᵉ (add-Cyclic-Ringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    add-Cyclic-Ringᵉ xᵉ (add-Cyclic-Ringᵉ yᵉ zᵉ)
  associative-add-Cyclic-Ringᵉ =
    associative-add-Ringᵉ ring-Cyclic-Ringᵉ

  left-inverse-law-add-Cyclic-Ringᵉ :
    (xᵉ : type-Cyclic-Ringᵉ) →
    add-Cyclic-Ringᵉ (neg-Cyclic-Ringᵉ xᵉ) xᵉ ＝ᵉ zero-Cyclic-Ringᵉ
  left-inverse-law-add-Cyclic-Ringᵉ =
    left-inverse-law-add-Ringᵉ ring-Cyclic-Ringᵉ

  right-inverse-law-add-Cyclic-Ringᵉ :
    (xᵉ : type-Cyclic-Ringᵉ) →
    add-Cyclic-Ringᵉ xᵉ (neg-Cyclic-Ringᵉ xᵉ) ＝ᵉ zero-Cyclic-Ringᵉ
  right-inverse-law-add-Cyclic-Ringᵉ =
    right-inverse-law-add-Ringᵉ ring-Cyclic-Ringᵉ

  left-unit-law-mul-Cyclic-Ringᵉ :
    (xᵉ : type-Cyclic-Ringᵉ) →
    mul-Cyclic-Ringᵉ one-Cyclic-Ringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Cyclic-Ringᵉ =
    left-unit-law-mul-Ringᵉ ring-Cyclic-Ringᵉ

  right-unit-law-mul-Cyclic-Ringᵉ :
    (xᵉ : type-Cyclic-Ringᵉ) →
    mul-Cyclic-Ringᵉ xᵉ one-Cyclic-Ringᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Cyclic-Ringᵉ =
    right-unit-law-mul-Ringᵉ ring-Cyclic-Ringᵉ

  associative-mul-Cyclic-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Cyclic-Ringᵉ) →
    mul-Cyclic-Ringᵉ (mul-Cyclic-Ringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Cyclic-Ringᵉ xᵉ (mul-Cyclic-Ringᵉ yᵉ zᵉ)
  associative-mul-Cyclic-Ringᵉ =
    associative-mul-Ringᵉ ring-Cyclic-Ringᵉ

  left-distributive-mul-add-Cyclic-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Cyclic-Ringᵉ) →
    mul-Cyclic-Ringᵉ xᵉ (add-Cyclic-Ringᵉ yᵉ zᵉ) ＝ᵉ
    add-Cyclic-Ringᵉ (mul-Cyclic-Ringᵉ xᵉ yᵉ) (mul-Cyclic-Ringᵉ xᵉ zᵉ)
  left-distributive-mul-add-Cyclic-Ringᵉ =
    left-distributive-mul-add-Ringᵉ ring-Cyclic-Ringᵉ

  right-distributive-mul-add-Cyclic-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Cyclic-Ringᵉ) →
    mul-Cyclic-Ringᵉ (add-Cyclic-Ringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    add-Cyclic-Ringᵉ (mul-Cyclic-Ringᵉ xᵉ zᵉ) (mul-Cyclic-Ringᵉ yᵉ zᵉ)
  right-distributive-mul-add-Cyclic-Ringᵉ =
    right-distributive-mul-add-Ringᵉ ring-Cyclic-Ringᵉ

  swap-integer-multiple-Cyclic-Ringᵉ :
    (kᵉ lᵉ : ℤᵉ) (xᵉ : type-Cyclic-Ringᵉ) →
    integer-multiple-Cyclic-Ringᵉ kᵉ (integer-multiple-Cyclic-Ringᵉ lᵉ xᵉ) ＝ᵉ
    integer-multiple-Cyclic-Ringᵉ lᵉ (integer-multiple-Cyclic-Ringᵉ kᵉ xᵉ)
  swap-integer-multiple-Cyclic-Ringᵉ =
    swap-integer-multiple-Ringᵉ ring-Cyclic-Ringᵉ

  left-integer-multiple-law-mul-Cyclic-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ yᵉ : type-Cyclic-Ringᵉ) →
    mul-Cyclic-Ringᵉ (integer-multiple-Cyclic-Ringᵉ kᵉ xᵉ) yᵉ ＝ᵉ
    integer-multiple-Cyclic-Ringᵉ kᵉ (mul-Cyclic-Ringᵉ xᵉ yᵉ)
  left-integer-multiple-law-mul-Cyclic-Ringᵉ =
    left-integer-multiple-law-mul-Ringᵉ ring-Cyclic-Ringᵉ

  right-integer-multiple-law-mul-Cyclic-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ yᵉ : type-Cyclic-Ringᵉ) →
    mul-Cyclic-Ringᵉ xᵉ (integer-multiple-Cyclic-Ringᵉ kᵉ yᵉ) ＝ᵉ
    integer-multiple-Cyclic-Ringᵉ kᵉ (mul-Cyclic-Ringᵉ xᵉ yᵉ)
  right-integer-multiple-law-mul-Cyclic-Ringᵉ =
    right-integer-multiple-law-mul-Ringᵉ ring-Cyclic-Ringᵉ
```

## Properties

### If `R` is a cyclic ring, then any generator of its additive group is invertible

**Proof:**ᵉ Letᵉ `g`ᵉ beᵉ aᵉ generatorᵉ ofᵉ theᵉ additiveᵉ groupᵉ `(R,0,+,-)`.ᵉ Thenᵉ thereᵉ
isᵉ anᵉ integerᵉ `n`ᵉ suchᵉ thatᵉ `ngᵉ ＝ᵉ 1`.ᵉ Thenᵉ weᵉ obtainᵉ thatᵉ
`(n1)gᵉ ＝ᵉ n(1gᵉ) ＝ᵉ ngᵉ ＝ᵉ 1`ᵉ andᵉ thatᵉ `g(n1ᵉ) ＝ᵉ n(g1ᵉ) ＝ᵉ ngᵉ ＝ᵉ 1`.ᵉ Itᵉ followsᵉ
thatᵉ theᵉ elementᵉ `n1`ᵉ isᵉ theᵉ multiplicativeᵉ inverseᵉ ofᵉ `g`.ᵉ

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (gᵉ : type-Ringᵉ Rᵉ)
  (Hᵉ : is-generating-element-Groupᵉ (group-Ringᵉ Rᵉ) gᵉ)
  where

  abstract
    is-invertible-is-generating-element-group-Ringᵉ :
      is-invertible-element-Ringᵉ Rᵉ gᵉ
    is-invertible-is-generating-element-group-Ringᵉ =
      apply-universal-property-trunc-Propᵉ
        ( is-surjective-hom-element-is-generating-element-Groupᵉ
          ( group-Ringᵉ Rᵉ)
          ( gᵉ)
          ( Hᵉ)
          ( one-Ringᵉ Rᵉ))
        ( is-invertible-element-prop-Ringᵉ Rᵉ gᵉ)
        ( λ (nᵉ ,ᵉ pᵉ) →
          ( integer-multiple-Ringᵉ Rᵉ nᵉ (one-Ringᵉ Rᵉ)) ,ᵉ
          ( ( right-integer-multiple-law-mul-Ringᵉ Rᵉ nᵉ gᵉ
              ( one-Ringᵉ Rᵉ)) ∙ᵉ
            ( apᵉ
              ( integer-multiple-Ringᵉ Rᵉ nᵉ)
              ( right-unit-law-mul-Ringᵉ Rᵉ gᵉ)) ∙ᵉ
            ( pᵉ)) ,ᵉ
          ( ( left-integer-multiple-law-mul-Ringᵉ Rᵉ nᵉ
              ( one-Ringᵉ Rᵉ)
              ( gᵉ)) ∙ᵉ
            ( apᵉ
              ( integer-multiple-Ringᵉ Rᵉ nᵉ)
              ( left-unit-law-mul-Ringᵉ Rᵉ gᵉ)) ∙ᵉ
            ( pᵉ)))
```

### If `R` is a cyclic ring if and only if `1` is a generator of its additive group

Equivalently,ᵉ weᵉ assertᵉ thatᵉ `R`ᵉ isᵉ cyclicᵉ ifᵉ andᵉ onlyᵉ ifᵉ `initial-hom-Ringᵉ R`ᵉ
isᵉ surjective.ᵉ

**Proof:**ᵉ Ofᵉ course,ᵉ ifᵉ `1`ᵉ isᵉ aᵉ generatorᵉ ofᵉ theᵉ additiveᵉ groupᵉ ofᵉ `R`,ᵉ thenᵉ
theᵉ additiveᵉ groupᵉ ofᵉ `R`ᵉ isᵉ cyclic.ᵉ Forᵉ theᵉ converse,ᵉ considerᵉ aᵉ generatingᵉ
elementᵉ `g`ᵉ ofᵉ theᵉ additiveᵉ groupᵉ `(R,0,+,-)`.ᵉ Thenᵉ thereᵉ existsᵉ anᵉ integerᵉ `n`ᵉ
suchᵉ thatᵉ `ngᵉ ＝ᵉ 1`.ᵉ

Letᵉ `x`ᵉ beᵉ anᵉ arbitraryᵉ elementᵉ ofᵉ theᵉ ringᵉ `R`.ᵉ Thenᵉ thereᵉ existsᵉ anᵉ integerᵉ
`k`ᵉ suchᵉ thatᵉ `kgᵉ ＝ᵉ gx`.ᵉ Weᵉ claimᵉ thatᵉ `k1ᵉ ＝ᵉ x`.ᵉ Toᵉ seeᵉ this,ᵉ weᵉ calculateᵉ:

```text
  k1ᵉ ＝ᵉ k(ngᵉ) ＝ᵉ n(kgᵉ) ＝ᵉ n(gxᵉ) ＝ᵉ (ng)xᵉ ＝ᵉ 1xᵉ ＝ᵉ x.ᵉ
```

Thisᵉ provesᵉ thatᵉ everyᵉ elementᵉ isᵉ anᵉ integerᵉ multipleᵉ ofᵉ `1`.ᵉ Weᵉ concludeᵉ thatᵉ
`1`ᵉ generatesᵉ theᵉ additiveᵉ groupᵉ `(R,0,+,-)`.ᵉ

```agda
module _
  {lᵉ : Level} (Rᵉ : Cyclic-Ringᵉ lᵉ)
  where

  abstract
    is-surjective-initial-hom-Cyclic-Ringᵉ :
      is-surjective-initial-hom-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ)
    is-surjective-initial-hom-Cyclic-Ringᵉ xᵉ =
      apply-universal-property-trunc-Propᵉ
        ( is-cyclic-Cyclic-Ringᵉ Rᵉ)
        ( trunc-Propᵉ
          ( fiberᵉ (map-initial-hom-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ)) xᵉ))
        ( λ (gᵉ ,ᵉ uᵉ) →
          apply-twice-universal-property-trunc-Propᵉ
            ( is-surjective-hom-element-is-generating-element-Groupᵉ
              ( group-Cyclic-Ringᵉ Rᵉ)
              ( gᵉ)
              ( uᵉ)
              ( one-Cyclic-Ringᵉ Rᵉ))
            ( is-surjective-hom-element-is-generating-element-Groupᵉ
              ( group-Cyclic-Ringᵉ Rᵉ)
              ( gᵉ)
              ( uᵉ)
              ( mul-Cyclic-Ringᵉ Rᵉ gᵉ xᵉ))
            ( trunc-Propᵉ
              ( fiberᵉ (map-initial-hom-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ)) xᵉ))
            ( λ (nᵉ ,ᵉ pᵉ) (kᵉ ,ᵉ qᵉ) →
              unit-trunc-Propᵉ
                ( ( kᵉ) ,ᵉ
                  ( equational-reasoningᵉ
                    integer-multiple-Cyclic-Ringᵉ Rᵉ kᵉ
                      ( one-Cyclic-Ringᵉ Rᵉ)
                    ＝ᵉ integer-multiple-Cyclic-Ringᵉ Rᵉ kᵉ
                        ( integer-multiple-Cyclic-Ringᵉ Rᵉ nᵉ gᵉ)
                      byᵉ
                      apᵉ
                        ( integer-multiple-Cyclic-Ringᵉ Rᵉ kᵉ)
                        ( invᵉ pᵉ)
                    ＝ᵉ integer-multiple-Cyclic-Ringᵉ Rᵉ nᵉ
                        ( integer-multiple-Cyclic-Ringᵉ Rᵉ kᵉ gᵉ)
                      byᵉ
                      swap-integer-multiple-Cyclic-Ringᵉ Rᵉ kᵉ nᵉ gᵉ
                    ＝ᵉ integer-multiple-Cyclic-Ringᵉ Rᵉ nᵉ
                        ( mul-Cyclic-Ringᵉ Rᵉ gᵉ xᵉ)
                      byᵉ
                      apᵉ (integer-multiple-Cyclic-Ringᵉ Rᵉ nᵉ) qᵉ
                    ＝ᵉ mul-Cyclic-Ringᵉ Rᵉ
                        ( integer-multiple-Cyclic-Ringᵉ Rᵉ nᵉ gᵉ)
                        ( xᵉ)
                      byᵉ
                      invᵉ (left-integer-multiple-law-mul-Cyclic-Ringᵉ Rᵉ nᵉ gᵉ xᵉ)
                    ＝ᵉ mul-Cyclic-Ringᵉ Rᵉ (one-Cyclic-Ringᵉ Rᵉ) xᵉ
                      byᵉ apᵉ (mul-Cyclic-Ring'ᵉ Rᵉ xᵉ) pᵉ
                    ＝ᵉ xᵉ
                      byᵉ left-unit-law-mul-Cyclic-Ringᵉ Rᵉ xᵉ))))

  abstract
    is-generating-element-one-Cyclic-Ringᵉ :
      is-generating-element-Groupᵉ (group-Cyclic-Ringᵉ Rᵉ) (one-Cyclic-Ringᵉ Rᵉ)
    is-generating-element-one-Cyclic-Ringᵉ =
      is-generating-element-is-surjective-hom-element-Groupᵉ
        ( group-Cyclic-Ringᵉ Rᵉ)
        ( one-Cyclic-Ringᵉ Rᵉ)
        ( is-surjective-initial-hom-Cyclic-Ringᵉ)
```

### The classification of cyclic rings

```agda
module _
  {lᵉ : Level}
  where

  is-cyclic-is-surjective-initial-hom-Ringᵉ :
    (Rᵉ : Ringᵉ lᵉ) →
    is-surjective-initial-hom-Ringᵉ Rᵉ → is-cyclic-Ringᵉ Rᵉ
  is-cyclic-is-surjective-initial-hom-Ringᵉ Rᵉ Hᵉ =
    unit-trunc-Propᵉ
      ( one-Ringᵉ Rᵉ ,ᵉ
        is-generating-element-is-surjective-hom-element-Groupᵉ
          ( group-Ringᵉ Rᵉ)
          ( one-Ringᵉ Rᵉ)
          ( Hᵉ))

  classification-Cyclic-Ringᵉ :
    Cyclic-Ringᵉ lᵉ ≃ᵉ Σᵉ (Ringᵉ lᵉ) is-surjective-initial-hom-Ringᵉ
  classification-Cyclic-Ringᵉ =
    equiv-type-subtypeᵉ
      ( is-prop-is-cyclic-Ringᵉ)
      ( is-prop-is-surjective-initial-hom-Ringᵉ)
      ( λ Rᵉ Hᵉ → is-surjective-initial-hom-Cyclic-Ringᵉ (Rᵉ ,ᵉ Hᵉ))
      ( is-cyclic-is-surjective-initial-hom-Ringᵉ)
```

### If `R` is a cyclic ring, then any invertible element is a generator of its additive group

**Proof:**ᵉ Letᵉ `x`ᵉ beᵉ anᵉ invertibleᵉ elementᵉ ofᵉ `R`.ᵉ Toᵉ showᵉ thatᵉ `x`ᵉ generatesᵉ
theᵉ abelianᵉ groupᵉ `(R,0,+,1)`ᵉ weᵉ needᵉ to showᵉ thatᵉ forᵉ anyᵉ elementᵉ `yᵉ : R`ᵉ thereᵉ
existsᵉ anᵉ integerᵉ `k`ᵉ suchᵉ thatᵉ `kxᵉ ＝ᵉ y`.ᵉ Letᵉ `n1ᵉ ＝ᵉ x⁻¹`ᵉ andᵉ let `m1ᵉ ＝ᵉ y`.ᵉ
Thenᵉ weᵉ calculateᵉ

```text
  (mn)xᵉ ＝ᵉ m(nxᵉ) ＝ᵉ m(n(1xᵉ)) ＝ᵉ m((n1)xᵉ) ＝ᵉ m(x⁻¹xᵉ) ＝ᵉ m1ᵉ ＝ᵉ y.ᵉ
```

```agda
module _
  {lᵉ : Level} (Rᵉ : Cyclic-Ringᵉ lᵉ) {xᵉ : type-Cyclic-Ringᵉ Rᵉ}
  (Hᵉ : is-invertible-element-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ) xᵉ)
  where

  abstract
    is-surjective-hom-element-is-invertible-element-Cyclic-Ringᵉ :
      is-surjective-hom-element-Groupᵉ (group-Cyclic-Ringᵉ Rᵉ) xᵉ
    is-surjective-hom-element-is-invertible-element-Cyclic-Ringᵉ yᵉ =
      apply-twice-universal-property-trunc-Propᵉ
        ( is-surjective-initial-hom-Cyclic-Ringᵉ Rᵉ
          ( inv-is-invertible-element-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ) Hᵉ))
        ( is-surjective-initial-hom-Cyclic-Ringᵉ Rᵉ yᵉ)
        ( trunc-Propᵉ (fiberᵉ (map-hom-element-Groupᵉ (group-Cyclic-Ringᵉ Rᵉ) xᵉ) yᵉ))
        ( λ (nᵉ ,ᵉ pᵉ) (mᵉ ,ᵉ qᵉ) →
          unit-trunc-Propᵉ
            ( ( mul-ℤᵉ mᵉ nᵉ) ,ᵉ
              ( ( integer-multiple-mul-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ) mᵉ nᵉ xᵉ) ∙ᵉ
                ( apᵉ
                  ( integer-multiple-Cyclic-Ringᵉ Rᵉ mᵉ)
                  ( ( apᵉ
                      ( integer-multiple-Cyclic-Ringᵉ Rᵉ nᵉ)
                      ( invᵉ (left-unit-law-mul-Cyclic-Ringᵉ Rᵉ xᵉ))) ∙ᵉ
                    ( invᵉ
                      ( left-integer-multiple-law-mul-Ringᵉ
                        ( ring-Cyclic-Ringᵉ Rᵉ)
                        ( nᵉ)
                        ( one-Cyclic-Ringᵉ Rᵉ)
                        ( xᵉ))) ∙ᵉ
                    ( apᵉ (mul-Cyclic-Ring'ᵉ Rᵉ xᵉ) pᵉ) ∙ᵉ
                    ( is-left-inverse-inv-is-invertible-element-Ringᵉ
                      ( ring-Cyclic-Ringᵉ Rᵉ)
                      ( Hᵉ)))) ∙ᵉ
                ( qᵉ))))

  is-generating-element-group-is-invertible-element-Cyclic-Ringᵉ :
    is-generating-element-Groupᵉ (group-Cyclic-Ringᵉ Rᵉ) xᵉ
  is-generating-element-group-is-invertible-element-Cyclic-Ringᵉ =
    is-generating-element-is-surjective-hom-element-Groupᵉ
      ( group-Cyclic-Ringᵉ Rᵉ)
      ( xᵉ)
      ( is-surjective-hom-element-is-invertible-element-Cyclic-Ringᵉ)
```

### Any cyclic ring is commutative

```agda
module _
  {lᵉ : Level} (Rᵉ : Cyclic-Ringᵉ lᵉ)
  where

  abstract
    commutative-mul-Cyclic-Ringᵉ :
      (xᵉ yᵉ : type-Cyclic-Ringᵉ Rᵉ) →
      mul-Cyclic-Ringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Cyclic-Ringᵉ Rᵉ yᵉ xᵉ
    commutative-mul-Cyclic-Ringᵉ xᵉ yᵉ =
      apply-twice-universal-property-trunc-Propᵉ
        ( is-surjective-initial-hom-Cyclic-Ringᵉ Rᵉ xᵉ)
        ( is-surjective-initial-hom-Cyclic-Ringᵉ Rᵉ yᵉ)
        ( Id-Propᵉ (set-Cyclic-Ringᵉ Rᵉ) _ _)
        ( λ where
          ( nᵉ ,ᵉ reflᵉ) (mᵉ ,ᵉ reflᵉ) →
            commute-integer-multiples-diagonal-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ) nᵉ mᵉ)

  commutative-ring-Cyclic-Ringᵉ : Commutative-Ringᵉ lᵉ
  pr1ᵉ commutative-ring-Cyclic-Ringᵉ = ring-Cyclic-Ringᵉ Rᵉ
  pr2ᵉ commutative-ring-Cyclic-Ringᵉ = commutative-mul-Cyclic-Ringᵉ
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}

## References

{{#bibliographyᵉ}}