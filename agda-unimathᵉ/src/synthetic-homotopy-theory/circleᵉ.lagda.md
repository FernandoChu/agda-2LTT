# The circle

```agda
module synthetic-homotopy-theory.circleᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import higher-group-theory.higher-groupsᵉ

open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.dependent-suspension-structuresᵉ
open import synthetic-homotopy-theory.free-loopsᵉ
open import synthetic-homotopy-theory.spheresᵉ
open import synthetic-homotopy-theory.suspension-structuresᵉ
open import synthetic-homotopy-theory.suspensions-of-typesᵉ
open import synthetic-homotopy-theory.universal-cover-circleᵉ
open import synthetic-homotopy-theory.universal-property-circleᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

**Theᵉ circle**ᵉ isᵉ theᵉ initialᵉ typeᵉ equippedᵉ with aᵉ baseᵉ pointᵉ andᵉ aᵉ
[loop](synthetic-homotopy-theory.loop-spaces.md).ᵉ

## Postulates

```agda
postulate
  𝕊¹ᵉ : UUᵉ lzero

postulate
  base-𝕊¹ᵉ : 𝕊¹ᵉ

postulate
  loop-𝕊¹ᵉ : base-𝕊¹ᵉ ＝ᵉ base-𝕊¹ᵉ

free-loop-𝕊¹ᵉ : free-loopᵉ 𝕊¹ᵉ
free-loop-𝕊¹ᵉ = base-𝕊¹ᵉ ,ᵉ loop-𝕊¹ᵉ

𝕊¹-Pointed-Typeᵉ : Pointed-Typeᵉ lzero
𝕊¹-Pointed-Typeᵉ = 𝕊¹ᵉ ,ᵉ base-𝕊¹ᵉ

postulate
  ind-𝕊¹ᵉ : induction-principle-circleᵉ free-loop-𝕊¹ᵉ
```

## Properties

### The dependent universal property of the circle

```agda
dependent-universal-property-𝕊¹ᵉ :
  dependent-universal-property-circleᵉ free-loop-𝕊¹ᵉ
dependent-universal-property-𝕊¹ᵉ =
  dependent-universal-property-induction-principle-circleᵉ free-loop-𝕊¹ᵉ ind-𝕊¹ᵉ

uniqueness-dependent-universal-property-𝕊¹ᵉ :
  {lᵉ : Level} {Pᵉ : 𝕊¹ᵉ → UUᵉ lᵉ} (kᵉ : free-dependent-loopᵉ free-loop-𝕊¹ᵉ Pᵉ) →
  is-contrᵉ
    ( Σᵉ ( (xᵉ : 𝕊¹ᵉ) → Pᵉ xᵉ)
        ( λ hᵉ →
          Eq-free-dependent-loopᵉ free-loop-𝕊¹ᵉ Pᵉ
            ( ev-free-loop-Πᵉ free-loop-𝕊¹ᵉ Pᵉ hᵉ) kᵉ))
uniqueness-dependent-universal-property-𝕊¹ᵉ {lᵉ} {Pᵉ} =
  uniqueness-dependent-universal-property-circleᵉ
    free-loop-𝕊¹ᵉ
    dependent-universal-property-𝕊¹ᵉ

module _
  {lᵉ : Level} (Pᵉ : 𝕊¹ᵉ → UUᵉ lᵉ) (p0ᵉ : Pᵉ base-𝕊¹ᵉ) (αᵉ : trᵉ Pᵉ loop-𝕊¹ᵉ p0ᵉ ＝ᵉ p0ᵉ)
  where

  Π-𝕊¹ᵉ : UUᵉ lᵉ
  Π-𝕊¹ᵉ =
    Σᵉ ( (xᵉ : 𝕊¹ᵉ) → Pᵉ xᵉ)
      ( λ hᵉ →
        Eq-free-dependent-loopᵉ free-loop-𝕊¹ᵉ Pᵉ
          ( ev-free-loop-Πᵉ free-loop-𝕊¹ᵉ Pᵉ hᵉ) (p0ᵉ ,ᵉ αᵉ))

  apply-dependent-universal-property-𝕊¹ᵉ : Π-𝕊¹ᵉ
  apply-dependent-universal-property-𝕊¹ᵉ =
    centerᵉ (uniqueness-dependent-universal-property-𝕊¹ᵉ (p0ᵉ ,ᵉ αᵉ))

  function-apply-dependent-universal-property-𝕊¹ᵉ : (xᵉ : 𝕊¹ᵉ) → Pᵉ xᵉ
  function-apply-dependent-universal-property-𝕊¹ᵉ =
    pr1ᵉ apply-dependent-universal-property-𝕊¹ᵉ

  base-dependent-universal-property-𝕊¹ᵉ :
    function-apply-dependent-universal-property-𝕊¹ᵉ base-𝕊¹ᵉ ＝ᵉ p0ᵉ
  base-dependent-universal-property-𝕊¹ᵉ =
    pr1ᵉ (pr2ᵉ apply-dependent-universal-property-𝕊¹ᵉ)

  loop-dependent-universal-property-𝕊¹ᵉ :
    ( apdᵉ function-apply-dependent-universal-property-𝕊¹ᵉ loop-𝕊¹ᵉ ∙ᵉ
      base-dependent-universal-property-𝕊¹ᵉ) ＝ᵉ
    ( apᵉ (trᵉ Pᵉ loop-𝕊¹ᵉ) base-dependent-universal-property-𝕊¹ᵉ ∙ᵉ αᵉ)
  loop-dependent-universal-property-𝕊¹ᵉ =
    pr2ᵉ (pr2ᵉ apply-dependent-universal-property-𝕊¹ᵉ)
```

### The universal property of the circle

```agda
universal-property-𝕊¹ᵉ : universal-property-circleᵉ free-loop-𝕊¹ᵉ
universal-property-𝕊¹ᵉ =
  universal-property-dependent-universal-property-circleᵉ
    ( free-loop-𝕊¹ᵉ)
    ( dependent-universal-property-𝕊¹ᵉ)

uniqueness-universal-property-𝕊¹ᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (αᵉ : free-loopᵉ Xᵉ) →
  is-contrᵉ
    ( Σᵉ ( 𝕊¹ᵉ → Xᵉ)
        ( λ hᵉ → Eq-free-loopᵉ (ev-free-loopᵉ free-loop-𝕊¹ᵉ Xᵉ hᵉ) αᵉ))
uniqueness-universal-property-𝕊¹ᵉ {lᵉ} {Xᵉ} =
  uniqueness-universal-property-circleᵉ free-loop-𝕊¹ᵉ universal-property-𝕊¹ᵉ Xᵉ

module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (xᵉ : Xᵉ) (αᵉ : xᵉ ＝ᵉ xᵉ)
  where

  Map-𝕊¹ᵉ : UUᵉ lᵉ
  Map-𝕊¹ᵉ =
    Σᵉ ( 𝕊¹ᵉ → Xᵉ)
      ( λ hᵉ → Eq-free-loopᵉ (ev-free-loopᵉ free-loop-𝕊¹ᵉ Xᵉ hᵉ) (xᵉ ,ᵉ αᵉ))

  apply-universal-property-𝕊¹ᵉ : Map-𝕊¹ᵉ
  apply-universal-property-𝕊¹ᵉ =
    centerᵉ (uniqueness-universal-property-𝕊¹ᵉ (xᵉ ,ᵉ αᵉ))

  map-apply-universal-property-𝕊¹ᵉ : 𝕊¹ᵉ → Xᵉ
  map-apply-universal-property-𝕊¹ᵉ =
    pr1ᵉ apply-universal-property-𝕊¹ᵉ

  base-universal-property-𝕊¹ᵉ :
    map-apply-universal-property-𝕊¹ᵉ base-𝕊¹ᵉ ＝ᵉ xᵉ
  base-universal-property-𝕊¹ᵉ =
    pr1ᵉ (pr2ᵉ apply-universal-property-𝕊¹ᵉ)

  loop-universal-property-𝕊¹ᵉ :
    apᵉ map-apply-universal-property-𝕊¹ᵉ loop-𝕊¹ᵉ ∙ᵉ base-universal-property-𝕊¹ᵉ ＝ᵉ
    base-universal-property-𝕊¹ᵉ ∙ᵉ αᵉ
  loop-universal-property-𝕊¹ᵉ =
    pr2ᵉ (pr2ᵉ apply-universal-property-𝕊¹ᵉ)
```

### The loop of the circle is nontrivial

```agda
is-nontrivial-loop-𝕊¹ᵉ : loop-𝕊¹ᵉ ≠ᵉ reflᵉ
is-nontrivial-loop-𝕊¹ᵉ =
  is-nontrivial-loop-dependent-universal-property-circleᵉ
    ( free-loop-𝕊¹ᵉ)
    ( dependent-universal-property-𝕊¹ᵉ)
```

### The circle is 0-connected

```agda
mere-eq-𝕊¹ᵉ : (xᵉ yᵉ : 𝕊¹ᵉ) → mere-eqᵉ xᵉ yᵉ
mere-eq-𝕊¹ᵉ =
  function-apply-dependent-universal-property-𝕊¹ᵉ
    ( λ xᵉ → (yᵉ : 𝕊¹ᵉ) → mere-eqᵉ xᵉ yᵉ)
    ( function-apply-dependent-universal-property-𝕊¹ᵉ
      ( mere-eqᵉ base-𝕊¹ᵉ)
      ( refl-mere-eqᵉ base-𝕊¹ᵉ)
      ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))
    ( eq-is-propᵉ (is-prop-Πᵉ (λ yᵉ → is-prop-type-trunc-Propᵉ)))

is-0-connected-𝕊¹ᵉ : is-0-connectedᵉ 𝕊¹ᵉ
is-0-connected-𝕊¹ᵉ = is-0-connected-mere-eqᵉ base-𝕊¹ᵉ (mere-eq-𝕊¹ᵉ base-𝕊¹ᵉ)
```

### The circle as a higher group

```agda
𝕊¹-∞-Groupᵉ : ∞-Groupᵉ lzero
pr1ᵉ 𝕊¹-∞-Groupᵉ = 𝕊¹-Pointed-Typeᵉ
pr2ᵉ 𝕊¹-∞-Groupᵉ = is-0-connected-𝕊¹ᵉ
```

### The circle is equivalent to the 1-sphere

Theᵉ [1-sphere](synthetic-homotopy-theory.spheres.mdᵉ) isᵉ definedᵉ asᵉ theᵉ
[suspension](synthetic-homotopy-theory.suspensions-of-types.mdᵉ) ofᵉ theᵉ
[0-sphere](synthetic-homotopy-theory.spheres.md).ᵉ Weᵉ mayᵉ understandᵉ thisᵉ asᵉ theᵉ
1-sphereᵉ havingᵉ twoᵉ pointsᵉ `N`ᵉ andᵉ `S`ᵉ andᵉ twoᵉ
[identifications](foundation-core.identity-types.mdᵉ) (meridiansᵉ) `e,ᵉ wᵉ : Nᵉ = S`ᵉ
betweenᵉ them.ᵉ Theᵉ followingᵉ showsᵉ thatᵉ theᵉ 1-sphereᵉ andᵉ theᵉ circleᵉ areᵉ
[equivalent](foundation-core.equivalences.md).ᵉ

#### The map from the circle to the 1-sphere

Theᵉ mapᵉ fromᵉ theᵉ circleᵉ to theᵉ 1-sphereᵉ isᵉ definedᵉ byᵉ mappingᵉ theᵉ basepointᵉ to
`N`ᵉ andᵉ theᵉ loopᵉ to theᵉ compositeᵉ ofᵉ `e`ᵉ andᵉ theᵉ inverseᵉ ofᵉ `w`,ᵉ whichᵉ formsᵉ aᵉ
loopᵉ atᵉ `N`.ᵉ Theᵉ choiceᵉ ofᵉ whichᵉ meridianᵉ to startᵉ with isᵉ arbitrary,ᵉ butᵉ
informsᵉ theᵉ restᵉ ofᵉ theᵉ constructionᵉ hereafter.ᵉ

```agda
north-sphere-1-loopᵉ : north-sphereᵉ 1 ＝ᵉ north-sphereᵉ 1
north-sphere-1-loopᵉ =
  ( meridian-sphereᵉ 0 (zero-Finᵉ 1ᵉ)) ∙ᵉ
  ( invᵉ (meridian-sphereᵉ 0 (one-Finᵉ 1ᵉ)))

sphere-1-circleᵉ : 𝕊¹ᵉ → sphereᵉ 1
sphere-1-circleᵉ =
  map-apply-universal-property-𝕊¹ᵉ (north-sphereᵉ 1ᵉ) north-sphere-1-loopᵉ

sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ :
  sphere-1-circleᵉ base-𝕊¹ᵉ ＝ᵉ north-sphereᵉ 1
sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ =
  base-universal-property-𝕊¹ᵉ (north-sphereᵉ 1ᵉ) north-sphere-1-loopᵉ

sphere-1-circle-base-𝕊¹-eq-south-sphere-1ᵉ :
  sphere-1-circleᵉ base-𝕊¹ᵉ ＝ᵉ south-sphereᵉ 1
sphere-1-circle-base-𝕊¹-eq-south-sphere-1ᵉ =
  ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ) ∙ᵉ
  ( meridian-sphereᵉ 0 (one-Finᵉ 1ᵉ))
```

#### The map from the 1-sphere to the circle

Theᵉ mapᵉ fromᵉ theᵉ 1-sphereᵉ to theᵉ circleᵉ isᵉ definedᵉ byᵉ mappingᵉ bothᵉ `N`ᵉ andᵉ `S`ᵉ
to theᵉ basepoint,ᵉ `e`ᵉ to theᵉ loopᵉ andᵉ `w`ᵉ to `refl`ᵉ atᵉ theᵉ basepoint.ᵉ Wereᵉ weᵉ to
mapᵉ bothᵉ meridiansᵉ to theᵉ loop,ᵉ weᵉ wouldᵉ wrapᵉ theᵉ 1-sphereᵉ twiceᵉ aroundᵉ theᵉ
circle,ᵉ whichᵉ wouldᵉ notᵉ formᵉ anᵉ equivalence.ᵉ

```agda
map-sphere-0-eq-base-𝕊¹ᵉ : (sphereᵉ 0ᵉ) → base-𝕊¹ᵉ ＝ᵉ base-𝕊¹ᵉ
map-sphere-0-eq-base-𝕊¹ᵉ (inlᵉ nᵉ) = loop-𝕊¹ᵉ
map-sphere-0-eq-base-𝕊¹ᵉ (inrᵉ nᵉ) = reflᵉ

suspension-structure-sphere-0-𝕊¹ᵉ :
  suspension-structureᵉ (sphereᵉ 0ᵉ) 𝕊¹ᵉ
pr1ᵉ suspension-structure-sphere-0-𝕊¹ᵉ = base-𝕊¹ᵉ
pr1ᵉ (pr2ᵉ suspension-structure-sphere-0-𝕊¹ᵉ) = base-𝕊¹ᵉ
pr2ᵉ (pr2ᵉ suspension-structure-sphere-0-𝕊¹ᵉ) = map-sphere-0-eq-base-𝕊¹ᵉ

circle-sphere-1ᵉ : sphereᵉ 1 → 𝕊¹ᵉ
circle-sphere-1ᵉ =
  cogap-suspensionᵉ
    ( suspension-structure-sphere-0-𝕊¹ᵉ)

circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ :
  circle-sphere-1ᵉ (north-sphereᵉ 1ᵉ) ＝ᵉ base-𝕊¹ᵉ
circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ =
  compute-north-cogap-suspensionᵉ
    ( suspension-structure-sphere-0-𝕊¹ᵉ)

circle-sphere-1-south-sphere-1-eq-base-𝕊¹ᵉ :
  circle-sphere-1ᵉ (south-sphereᵉ 1ᵉ) ＝ᵉ base-𝕊¹ᵉ
circle-sphere-1-south-sphere-1-eq-base-𝕊¹ᵉ =
  compute-south-cogap-suspensionᵉ
    ( suspension-structure-sphere-0-𝕊¹ᵉ)
```

#### The map from the circle to the 1-sphere has a section

Someᵉ careᵉ needsᵉ to beᵉ takenᵉ whenᵉ provingᵉ thisᵉ partᵉ ofᵉ theᵉ equivalence.ᵉ Theᵉ pointᵉ
`N`ᵉ isᵉ mappedᵉ to theᵉ basepointᵉ andᵉ thenᵉ backᵉ to `N`,ᵉ butᵉ soᵉ isᵉ theᵉ pointᵉ `S`.ᵉ Itᵉ
needsᵉ to beᵉ furtherᵉ identifiedᵉ backᵉ with `S`ᵉ using theᵉ meridianᵉ `w`.ᵉ Theᵉ
meridianᵉ `w`ᵉ isᵉ thusᵉ mappedᵉ to `refl`ᵉ andᵉ thenᵉ backᵉ to `wᵉ ∙ᵉ reflᵉ = w`,ᵉ whileᵉ theᵉ
meridianᵉ `e`ᵉ isᵉ mappedᵉ to theᵉ loopᵉ andᵉ thenᵉ backᵉ to `wᵉ ∙ᵉ w⁻¹∙ᵉ eᵉ = e`.ᵉ

```agda
sphere-1-circle-sphere-1-north-sphere-1ᵉ :
    ( sphere-1-circleᵉ (circle-sphere-1ᵉ (north-sphereᵉ 1ᵉ))) ＝ᵉ ( north-sphereᵉ 1ᵉ)
sphere-1-circle-sphere-1-north-sphere-1ᵉ =
  ( apᵉ sphere-1-circleᵉ circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ) ∙ᵉ
  ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ)

sphere-1-circle-sphere-1-south-sphere-1ᵉ :
    ( sphere-1-circleᵉ (circle-sphere-1ᵉ (south-sphereᵉ 1ᵉ))) ＝ᵉ ( south-sphereᵉ 1ᵉ)
sphere-1-circle-sphere-1-south-sphere-1ᵉ =
  ( apᵉ sphere-1-circleᵉ circle-sphere-1-south-sphere-1-eq-base-𝕊¹ᵉ) ∙ᵉ
  ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1ᵉ)

apply-up-suspension-meridian-suspension-sphere-1-circle-sphere-1ᵉ :
  ( nᵉ : Finᵉ 2ᵉ) →
  coherence-square-identificationsᵉ
    ( apᵉ
      ( sphere-1-circleᵉ)
      ( ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ) ∙ᵉ
        ( map-sphere-0-eq-base-𝕊¹ᵉ nᵉ)))
    ( apᵉ sphere-1-circleᵉ (apᵉ circle-sphere-1ᵉ (meridian-suspensionᵉ nᵉ)))
    ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1ᵉ)
    ( sphere-1-circle-sphere-1-south-sphere-1ᵉ)
apply-up-suspension-meridian-suspension-sphere-1-circle-sphere-1ᵉ
  nᵉ =
  ( invᵉ
    ( assocᵉ
      ( apᵉ sphere-1-circleᵉ (apᵉ circle-sphere-1ᵉ (meridian-suspensionᵉ nᵉ)))
      ( apᵉ sphere-1-circleᵉ circle-sphere-1-south-sphere-1-eq-base-𝕊¹ᵉ)
      ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1ᵉ))) ∙ᵉ
  ( right-whisker-concatᵉ
    ( invᵉ
      ( ap-concatᵉ
        ( sphere-1-circleᵉ)
        ( apᵉ circle-sphere-1ᵉ (meridian-sphereᵉ 0 nᵉ))
        ( circle-sphere-1-south-sphere-1-eq-base-𝕊¹ᵉ)))
    ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1ᵉ)) ∙ᵉ
  ( apᵉ
    ( λ xᵉ →
      ( apᵉ sphere-1-circleᵉ xᵉ) ∙ᵉ
      ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1ᵉ))
    ( compute-meridian-cogap-suspensionᵉ
      ( suspension-structure-sphere-0-𝕊¹ᵉ)
      ( nᵉ)))

apply-loop-universal-property-𝕊¹-sphere-1-circle-sphere-1ᵉ :
  coherence-square-identificationsᵉ
    ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ)
    ( apᵉ sphere-1-circleᵉ loop-𝕊¹ᵉ)
    ( meridian-sphereᵉ 0 (zero-Finᵉ 1ᵉ))
    ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1ᵉ)
apply-loop-universal-property-𝕊¹-sphere-1-circle-sphere-1ᵉ =
  ( invᵉ
    ( assocᵉ
      ( apᵉ sphere-1-circleᵉ loop-𝕊¹ᵉ)
      ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ)
      ( meridian-sphereᵉ 0 (one-Finᵉ 1ᵉ)))) ∙ᵉ
  ( right-whisker-concatᵉ
    ( loop-universal-property-𝕊¹ᵉ
      ( north-sphereᵉ 1ᵉ)
      ( north-sphere-1-loopᵉ))
    ( meridian-sphereᵉ 0 (one-Finᵉ 1ᵉ))) ∙ᵉ
  ( assocᵉ
    ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ)
    ( north-sphere-1-loopᵉ)
    ( meridian-sphereᵉ 0 (one-Finᵉ 1ᵉ))) ∙ᵉ
  ( left-whisker-concatᵉ
    ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ)
    ( is-section-inv-concat'ᵉ
      ( meridian-sphereᵉ 0 (one-Finᵉ 1ᵉ))
      ( meridian-sphereᵉ 0 (zero-Finᵉ 1ᵉ))))

map-sphere-1-circle-sphere-1-meridianᵉ :
  ( nᵉ : Finᵉ 2ᵉ) →
  ( dependent-identificationᵉ
    ( λ xᵉ → (sphere-1-circleᵉ (circle-sphere-1ᵉ xᵉ)) ＝ᵉ xᵉ)
    ( meridian-suspension-structureᵉ
      ( suspension-structure-suspensionᵉ (Finᵉ 2ᵉ))
      ( nᵉ))
    ( sphere-1-circle-sphere-1-north-sphere-1ᵉ)
    ( sphere-1-circle-sphere-1-south-sphere-1ᵉ))
map-sphere-1-circle-sphere-1-meridianᵉ (inlᵉ (inrᵉ nᵉ)) =
  map-compute-dependent-identification-eq-value-comp-idᵉ
    ( sphere-1-circleᵉ)
    ( circle-sphere-1ᵉ)
    ( meridian-sphereᵉ 0 (inlᵉ (inrᵉ nᵉ)))
    ( sphere-1-circle-sphere-1-north-sphere-1ᵉ)
    ( sphere-1-circle-sphere-1-south-sphere-1ᵉ)
    ( ( apply-up-suspension-meridian-suspension-sphere-1-circle-sphere-1ᵉ
        ( inlᵉ (inrᵉ nᵉ))) ∙ᵉ
      ( right-whisker-concatᵉ
        ( ap-concatᵉ
          ( sphere-1-circleᵉ)
          ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)
          ( loop-𝕊¹ᵉ))
        ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1ᵉ)) ∙ᵉ
      ( assocᵉ
        ( apᵉ sphere-1-circleᵉ (circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ))
        ( apᵉ sphere-1-circleᵉ loop-𝕊¹ᵉ)
        ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1ᵉ)) ∙ᵉ
      ( left-whisker-concatᵉ
        ( apᵉ sphere-1-circleᵉ (circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ))
        ( apply-loop-universal-property-𝕊¹-sphere-1-circle-sphere-1ᵉ)) ∙ᵉ
      ( invᵉ
        ( assocᵉ
          ( apᵉ sphere-1-circleᵉ (circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ))
          ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ)
          ( meridian-sphereᵉ 0 (zero-Finᵉ 1ᵉ)))))
map-sphere-1-circle-sphere-1-meridianᵉ (inrᵉ nᵉ) =
  map-compute-dependent-identification-eq-value-comp-idᵉ
    ( sphere-1-circleᵉ)
    ( circle-sphere-1ᵉ)
    ( meridian-sphereᵉ 0 (inrᵉ nᵉ))
    ( sphere-1-circle-sphere-1-north-sphere-1ᵉ)
    ( sphere-1-circle-sphere-1-south-sphere-1ᵉ)
    ( ( apply-up-suspension-meridian-suspension-sphere-1-circle-sphere-1ᵉ
        ( inrᵉ nᵉ)) ∙ᵉ
      ( apᵉ
        ( λ xᵉ →
          ( apᵉ sphere-1-circleᵉ xᵉ) ∙ᵉ
          ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1ᵉ))
        ( right-unitᵉ {pᵉ = circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ})) ∙ᵉ
      ( invᵉ
        ( assocᵉ
          ( apᵉ sphere-1-circleᵉ circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)
          ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ)
          ( meridian-sphereᵉ 0 (one-Finᵉ 1ᵉ)))))

dependent-suspension-structure-sphere-1-circle-sphere-1ᵉ :
  dependent-suspension-structureᵉ
    ( λ xᵉ → (sphere-1-circleᵉ (circle-sphere-1ᵉ xᵉ)) ＝ᵉ xᵉ)
    ( suspension-structure-suspensionᵉ (Finᵉ 2ᵉ))
pr1ᵉ dependent-suspension-structure-sphere-1-circle-sphere-1ᵉ =
  sphere-1-circle-sphere-1-north-sphere-1ᵉ
pr1ᵉ (pr2ᵉ dependent-suspension-structure-sphere-1-circle-sphere-1ᵉ) =
  sphere-1-circle-sphere-1-south-sphere-1ᵉ
pr2ᵉ (pr2ᵉ dependent-suspension-structure-sphere-1-circle-sphere-1ᵉ) =
  map-sphere-1-circle-sphere-1-meridianᵉ

sphere-1-circle-sphere-1ᵉ : sectionᵉ sphere-1-circleᵉ
pr1ᵉ sphere-1-circle-sphere-1ᵉ = circle-sphere-1ᵉ
pr2ᵉ sphere-1-circle-sphere-1ᵉ =
  dependent-cogap-suspensionᵉ
    ( λ xᵉ → (sphere-1-circleᵉ (circle-sphere-1ᵉ xᵉ)) ＝ᵉ xᵉ)
    ( dependent-suspension-structure-sphere-1-circle-sphere-1ᵉ)
```

#### The map from the circle to the 1-sphere has a retraction

Theᵉ basepointᵉ isᵉ mappedᵉ to `N`ᵉ andᵉ thenᵉ backᵉ to theᵉ basepoint,ᵉ whileᵉ theᵉ loopᵉ isᵉ
mappedᵉ to `w⁻¹∙ᵉ e`ᵉ andᵉ thenᵉ backᵉ to `refl⁻¹ᵉ ∙ᵉ loopᵉ = loop`.ᵉ

```agda
circle-sphere-1-circle-base-𝕊¹ᵉ :
  circle-sphere-1ᵉ (sphere-1-circleᵉ base-𝕊¹ᵉ) ＝ᵉ base-𝕊¹ᵉ
circle-sphere-1-circle-base-𝕊¹ᵉ =
  ( apᵉ circle-sphere-1ᵉ sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ) ∙ᵉ
  ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)

apply-up-suspension-meridian-one-suspension-circle-sphere-1-circleᵉ :
  coherence-square-identificationsᵉ
    ( reflᵉ)
    ( apᵉ circle-sphere-1ᵉ (invᵉ (meridian-sphereᵉ 0 (one-Finᵉ 1ᵉ))))
    ( circle-sphere-1-south-sphere-1-eq-base-𝕊¹ᵉ)
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)
apply-up-suspension-meridian-one-suspension-circle-sphere-1-circleᵉ =
  ( right-whisker-concatᵉ
    ( ap-invᵉ
      ( circle-sphere-1ᵉ)
      ( meridian-suspensionᵉ (one-Finᵉ 1ᵉ)))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)) ∙ᵉ
  ( invᵉ right-unitᵉ) ∙ᵉ
  ( assocᵉ
    ( invᵉ (apᵉ circle-sphere-1ᵉ (meridian-suspensionᵉ (one-Finᵉ 1ᵉ))))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)
    ( reflᵉ)) ∙ᵉ
  ( left-whisker-concatᵉ
    ( invᵉ (apᵉ circle-sphere-1ᵉ (meridian-suspensionᵉ (one-Finᵉ 1ᵉ))))
    ( invᵉ
      ( compute-meridian-cogap-suspensionᵉ
          ( suspension-structure-sphere-0-𝕊¹ᵉ)
          ( one-Finᵉ 1ᵉ)))) ∙ᵉ
  ( invᵉ
    ( assocᵉ
      ( invᵉ (apᵉ circle-sphere-1ᵉ (meridian-suspensionᵉ (one-Finᵉ 1ᵉ))))
      ( apᵉ circle-sphere-1ᵉ (meridian-suspensionᵉ (one-Finᵉ 1ᵉ)))
      ( circle-sphere-1-south-sphere-1-eq-base-𝕊¹ᵉ))) ∙ᵉ
  ( right-whisker-concatᵉ
    ( left-invᵉ (apᵉ circle-sphere-1ᵉ (meridian-suspensionᵉ (one-Finᵉ 1ᵉ))))
    ( circle-sphere-1-south-sphere-1-eq-base-𝕊¹ᵉ))

apply-up-suspension-meridian-zero-suspension-circle-sphere-1-circleᵉ :
  coherence-square-identificationsᵉ
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)
    ( apᵉ (circle-sphere-1ᵉ) (north-sphere-1-loopᵉ))
    ( loop-𝕊¹ᵉ)
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)
apply-up-suspension-meridian-zero-suspension-circle-sphere-1-circleᵉ =
  ( right-whisker-concatᵉ
    ( ap-concatᵉ
      ( circle-sphere-1ᵉ)
      ( meridian-sphereᵉ 0 (zero-Finᵉ 1ᵉ))
      ( invᵉ (meridian-suspensionᵉ (one-Finᵉ 1ᵉ))))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)) ∙ᵉ
  ( assocᵉ
    ( apᵉ circle-sphere-1ᵉ (meridian-suspensionᵉ (zero-Finᵉ 1ᵉ)))
    ( apᵉ circle-sphere-1ᵉ (invᵉ ( meridian-sphereᵉ 0 (one-Finᵉ 1ᵉ))))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)) ∙ᵉ
  ( left-whisker-concatᵉ
    ( apᵉ circle-sphere-1ᵉ (meridian-suspensionᵉ (zero-Finᵉ 1ᵉ)))
    ( apply-up-suspension-meridian-one-suspension-circle-sphere-1-circleᵉ)) ∙ᵉ
  ( compute-meridian-cogap-suspensionᵉ
    ( suspension-structure-sphere-0-𝕊¹ᵉ)
    ( zero-Finᵉ 1ᵉ))

circle-sphere-1-circle-loop-𝕊¹ᵉ :
  coherence-square-identificationsᵉ
    ( circle-sphere-1-circle-base-𝕊¹ᵉ)
    ( apᵉ circle-sphere-1ᵉ (apᵉ sphere-1-circleᵉ loop-𝕊¹ᵉ))
    ( loop-𝕊¹ᵉ)
    ( circle-sphere-1-circle-base-𝕊¹ᵉ)
circle-sphere-1-circle-loop-𝕊¹ᵉ =
  ( invᵉ
    ( assocᵉ
      ( apᵉ circle-sphere-1ᵉ (apᵉ sphere-1-circleᵉ loop-𝕊¹ᵉ))
      ( apᵉ
        ( circle-sphere-1ᵉ)
        ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ))
      ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)) ∙ᵉ
    ( right-whisker-concatᵉ
      ( invᵉ
        ( ap-concatᵉ
          ( circle-sphere-1ᵉ)
          ( apᵉ sphere-1-circleᵉ loop-𝕊¹ᵉ)
          ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ)))
      ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)) ∙ᵉ
    ( right-whisker-concatᵉ
      ( apᵉ
        ( apᵉ circle-sphere-1ᵉ)
        ( loop-universal-property-𝕊¹ᵉ
          ( north-sphereᵉ 1ᵉ)
          ( north-sphere-1-loopᵉ)))
      ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)) ∙ᵉ
    ( right-whisker-concatᵉ
      ( ap-concatᵉ
        ( circle-sphere-1ᵉ)
        ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ)
        ( north-sphere-1-loopᵉ))
      ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)) ∙ᵉ
    ( assocᵉ
      ( apᵉ circle-sphere-1ᵉ sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ)
      ( apᵉ circle-sphere-1ᵉ north-sphere-1-loopᵉ)
      ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)) ∙ᵉ
    ( left-whisker-concatᵉ
      ( apᵉ circle-sphere-1ᵉ sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ)
      ( apply-up-suspension-meridian-zero-suspension-circle-sphere-1-circleᵉ)) ∙ᵉ
    ( invᵉ
      ( assocᵉ
        ( apᵉ circle-sphere-1ᵉ sphere-1-circle-base-𝕊¹-eq-north-sphere-1ᵉ)
        ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ᵉ)
        ( loop-𝕊¹ᵉ))))

circle-sphere-1-circleᵉ : retractionᵉ sphere-1-circleᵉ
pr1ᵉ circle-sphere-1-circleᵉ = circle-sphere-1ᵉ
pr2ᵉ circle-sphere-1-circleᵉ =
  function-apply-dependent-universal-property-𝕊¹ᵉ
    ( λ xᵉ → (circle-sphere-1ᵉ (sphere-1-circleᵉ xᵉ)) ＝ᵉ xᵉ)
    ( circle-sphere-1-circle-base-𝕊¹ᵉ)
    ( map-compute-dependent-identification-eq-value-comp-idᵉ
      ( circle-sphere-1ᵉ)
      ( sphere-1-circleᵉ)
      ( loop-𝕊¹ᵉ)
      ( circle-sphere-1-circle-base-𝕊¹ᵉ)
      ( circle-sphere-1-circle-base-𝕊¹ᵉ)
      ( circle-sphere-1-circle-loop-𝕊¹ᵉ))
```

#### The equivalence between the circle and the 1-sphere

```agda
is-equiv-sphere-1-circleᵉ : is-equivᵉ sphere-1-circleᵉ
pr1ᵉ is-equiv-sphere-1-circleᵉ =
  sphere-1-circle-sphere-1ᵉ
pr2ᵉ is-equiv-sphere-1-circleᵉ =
  circle-sphere-1-circleᵉ

equiv-sphere-1-circleᵉ : 𝕊¹ᵉ ≃ᵉ sphereᵉ 1
pr1ᵉ equiv-sphere-1-circleᵉ = sphere-1-circleᵉ
pr2ᵉ equiv-sphere-1-circleᵉ = is-equiv-sphere-1-circleᵉ
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}