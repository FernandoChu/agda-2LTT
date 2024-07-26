# Yoneda identity types

```agda
module foundation.yoneda-identity-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.multivariable-homotopiesᵉ
open import foundation.strictly-right-unital-concatenation-identificationsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-identity-systemsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Theᵉ standardᵉ definitionᵉ ofᵉ [identityᵉ types](foundation-core.identity-types.mdᵉ)
hasᵉ theᵉ limitationᵉ thatᵉ manyᵉ ofᵉ theᵉ basicᵉ operationsᵉ onlyᵉ satisfyᵉ algebraicᵉ lawsᵉ
_weakly_.ᵉ Onᵉ thisᵉ page,ᵉ weᵉ considerᵉ theᵉ
{{#conceptᵉ "Yonedaᵉ identityᵉ types"ᵉ Agda=yoneda-Idᵉ}}

```text
  (xᵉ ＝ʸᵉ yᵉ) :=ᵉ (zᵉ : Aᵉ) → (zᵉ ＝ᵉ xᵉ) → (zᵉ ＝ᵉ yᵉ)
```

Throughᵉ theᵉ interpretationᵉ ofᵉ typesᵉ asᵉ ∞-categories,ᵉ where theᵉ hom-spaceᵉ
`hom(xᵉ ,ᵉ y)`ᵉ isᵉ definedᵉ to beᵉ theᵉ identityᵉ typeᵉ `xᵉ ＝ᵉ y`,ᵉ weᵉ mayᵉ observeᵉ thatᵉ
thisᵉ isᵉ anᵉ instance ofᵉ theᵉ Yonedaᵉ embedding.ᵉ Weᵉ useᵉ aᵉ superscriptᵉ `y`ᵉ in theᵉ
notationᵉ ofᵉ theᵉ Yonedaᵉ identityᵉ types,ᵉ andᵉ similarlyᵉ weᵉ callᵉ elementsᵉ ofᵉ theᵉ
Yonedaᵉ identityᵉ typesᵉ forᵉ {{#conceptᵉ "Yonedaᵉ identifications"ᵉ Agda=yoneda-Id}}.ᵉ

Theᵉ Yonedaᵉ identityᵉ typesᵉ areᵉ [equivalent](foundation-core.equivalences.mdᵉ) to
theᵉ standardᵉ identityᵉ types,ᵉ butᵉ satisfyᵉ strictᵉ lawsᵉ

-ᵉ `(pᵉ ∙ʸᵉ qᵉ) ∙ʸᵉ rᵉ ≐ᵉ pᵉ ∙ʸᵉ (qᵉ ∙ʸᵉ r)`,ᵉ
-ᵉ `reflʸᵉ ∙ʸᵉ pᵉ ≐ᵉ p`,ᵉ andᵉ
-ᵉ `pᵉ ∙ʸᵉ reflʸᵉ ≐ᵉ p`.ᵉ

Thisᵉ isᵉ achievedᵉ byᵉ proxyingᵉ to functionᵉ compositionᵉ andᵉ utilizingᵉ itsᵉ
computationalᵉ properties,ᵉ andᵉ reliesᵉ heavilyᵉ onᵉ theᵉ
[functionᵉ extensionalityᵉ axiom](foundation.function-extensionality.md).ᵉ Moreᵉ
concretely,ᵉ theᵉ reflexivityᵉ isᵉ givenᵉ byᵉ theᵉ identityᵉ function,ᵉ andᵉ pathᵉ
concatenationᵉ isᵉ givenᵉ byᵉ functionᵉ composition.ᵉ

Inᵉ additionᵉ to theseᵉ strictnessᵉ laws,ᵉ weᵉ canᵉ makeᵉ theᵉ typeᵉ satisfyᵉ theᵉ strictᵉ
lawᵉ `invʸᵉ reflʸᵉ ≐ᵉ reflʸ`.ᵉ Moreover,ᵉ whileᵉ theᵉ inductionᵉ principleᵉ ofᵉ theᵉ Yonedaᵉ
identityᵉ typesᵉ doesᵉ notᵉ in generalᵉ satisfyᵉ theᵉ computationᵉ ruleᵉ strictly,ᵉ weᵉ canᵉ
defineᵉ itsᵉ recursionᵉ principleᵉ suchᵉ thatᵉ does.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  yoneda-Idᵉ : (xᵉ yᵉ : Aᵉ) → UUᵉ lᵉ
  yoneda-Idᵉ xᵉ yᵉ = (zᵉ : Aᵉ) → zᵉ ＝ᵉ xᵉ → zᵉ ＝ᵉ yᵉ

  infix 6 _＝ʸᵉ_
  _＝ʸᵉ_ : Aᵉ → Aᵉ → UUᵉ lᵉ
  (aᵉ ＝ʸᵉ bᵉ) = yoneda-Idᵉ aᵉ bᵉ
```

Weᵉ defineᵉ theᵉ reflexivityᵉ byᵉ theᵉ identityᵉ functionᵉ:

```agda
  reflʸᵉ : {xᵉ : Aᵉ} → xᵉ ＝ʸᵉ xᵉ
  reflʸᵉ zᵉ = idᵉ
```

## Properties

### Elements of the Yoneda identity type act like postconcatenation operations

Theᵉ followingᵉ isᵉ aᵉ collectionᵉ ofᵉ propertiesᵉ ofᵉ Yonedaᵉ identificationsᵉ similarᵉ to
propertiesᵉ ofᵉ theᵉ postconcatenationᵉ operationᵉ ofᵉ identifications.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  commutative-preconcat-Id-yoneda-Idᵉ :
    {xᵉ yᵉ zᵉ wᵉ : Aᵉ} (fᵉ : xᵉ ＝ʸᵉ yᵉ) (pᵉ : wᵉ ＝ᵉ zᵉ) (qᵉ : zᵉ ＝ᵉ xᵉ) →
    fᵉ wᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ pᵉ ∙ᵉ fᵉ zᵉ qᵉ
  commutative-preconcat-Id-yoneda-Idᵉ fᵉ reflᵉ qᵉ = reflᵉ

  commutative-preconcat-refl-Id-yoneda-Idᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (fᵉ : xᵉ ＝ʸᵉ yᵉ) (qᵉ : zᵉ ＝ᵉ xᵉ) → fᵉ zᵉ qᵉ ＝ᵉ qᵉ ∙ᵉ fᵉ xᵉ reflᵉ
  commutative-preconcat-refl-Id-yoneda-Idᵉ {zᵉ = zᵉ} fᵉ qᵉ =
    apᵉ (fᵉ zᵉ) (invᵉ right-unitᵉ) ∙ᵉ commutative-preconcat-Id-yoneda-Idᵉ fᵉ qᵉ reflᵉ

  commutative-preconcatr-Id-yoneda-Idᵉ :
    {xᵉ yᵉ zᵉ wᵉ : Aᵉ} (fᵉ : xᵉ ＝ʸᵉ yᵉ) (pᵉ : wᵉ ＝ᵉ zᵉ) (qᵉ : zᵉ ＝ᵉ xᵉ) →
    fᵉ wᵉ (pᵉ ∙ᵣᵉ qᵉ) ＝ᵉ pᵉ ∙ᵣᵉ fᵉ zᵉ qᵉ
  commutative-preconcatr-Id-yoneda-Idᵉ {xᵉ} {yᵉ} {zᵉ} {wᵉ} fᵉ pᵉ qᵉ =
    ( apᵉ (fᵉ wᵉ) (eq-concat-right-strict-concatᵉ pᵉ qᵉ)) ∙ᵉ
    ( commutative-preconcat-Id-yoneda-Idᵉ fᵉ pᵉ qᵉ) ∙ᵉ
    ( eq-right-strict-concat-concatᵉ pᵉ (fᵉ zᵉ qᵉ))

  commutative-preconcatr-refl-Id-yoneda-Idᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (fᵉ : xᵉ ＝ʸᵉ yᵉ) (qᵉ : zᵉ ＝ᵉ xᵉ) → fᵉ zᵉ qᵉ ＝ᵉ qᵉ ∙ᵣᵉ fᵉ xᵉ reflᵉ
  commutative-preconcatr-refl-Id-yoneda-Idᵉ fᵉ qᵉ =
    commutative-preconcatr-Id-yoneda-Idᵉ fᵉ qᵉ reflᵉ

  compute-inv-Id-yoneda-Idᵉ :
    {xᵉ yᵉ : Aᵉ} (fᵉ : xᵉ ＝ʸᵉ yᵉ) → fᵉ yᵉ (invᵉ (fᵉ xᵉ reflᵉ)) ＝ᵉ reflᵉ
  compute-inv-Id-yoneda-Idᵉ {xᵉ} fᵉ =
    ( commutative-preconcat-refl-Id-yoneda-Idᵉ fᵉ (invᵉ (fᵉ xᵉ reflᵉ))) ∙ᵉ
    ( left-invᵉ (fᵉ xᵉ reflᵉ))

  inv-distributive-inv-Id-yoneda-Idᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (fᵉ : xᵉ ＝ʸᵉ yᵉ) (gᵉ : xᵉ ＝ʸᵉ zᵉ) →
    invᵉ (gᵉ yᵉ (invᵉ (fᵉ xᵉ reflᵉ))) ＝ᵉ fᵉ zᵉ (invᵉ (gᵉ xᵉ reflᵉ))
  inv-distributive-inv-Id-yoneda-Idᵉ {xᵉ} fᵉ gᵉ =
    ( apᵉ invᵉ (commutative-preconcat-refl-Id-yoneda-Idᵉ gᵉ (invᵉ (fᵉ xᵉ reflᵉ)))) ∙ᵉ
    ( distributive-inv-concatᵉ (invᵉ (fᵉ xᵉ reflᵉ)) (gᵉ xᵉ reflᵉ)) ∙ᵉ
    ( apᵉ (invᵉ (gᵉ xᵉ reflᵉ) ∙ᵉ_) (inv-invᵉ (fᵉ xᵉ reflᵉ))) ∙ᵉ
    ( invᵉ (commutative-preconcat-refl-Id-yoneda-Idᵉ fᵉ (invᵉ (gᵉ xᵉ reflᵉ))))

  distributive-inv-Id-yoneda-Idᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (fᵉ : xᵉ ＝ʸᵉ yᵉ) (gᵉ : xᵉ ＝ʸᵉ zᵉ) →
    fᵉ zᵉ (invᵉ (gᵉ xᵉ reflᵉ)) ＝ᵉ invᵉ (gᵉ yᵉ (invᵉ (fᵉ xᵉ reflᵉ)))
  distributive-inv-Id-yoneda-Idᵉ fᵉ gᵉ =
    invᵉ (inv-distributive-inv-Id-yoneda-Idᵉ fᵉ gᵉ)
```

### The Yoneda identity types are equivalent to the standard identity types

Theᵉ equivalenceᵉ `(xᵉ ＝ᵉ yᵉ) ≃ᵉ (xᵉ ＝ʸᵉ y)`ᵉ isᵉ definedᵉ fromᵉ leftᵉ to rightᵉ byᵉ theᵉ
postconcatenationᵉ operationᵉ

```text
  yoneda-eq-eqᵉ :=ᵉ pᵉ ↦ᵉ (qᵉ ↦ᵉ qᵉ ∙ᵉ pᵉ)   : xᵉ ＝ᵉ yᵉ → xᵉ ＝ʸᵉ y,ᵉ
```

andᵉ fromᵉ rightᵉ to leftᵉ byᵉ evaluationᵉ atᵉ theᵉ reflexivityᵉ

```text
  eq-yoneda-eqᵉ :=ᵉ fᵉ ↦ᵉ fᵉ reflᵉ   : xᵉ ＝ʸᵉ yᵉ → xᵉ ＝ᵉ y.ᵉ
```

Itᵉ shouldᵉ beᵉ notedᵉ thatᵉ weᵉ defineᵉ theᵉ mapᵉ `xᵉ ＝ᵉ yᵉ → xᵉ ＝ʸᵉ y`ᵉ using theᵉ
[strictlyᵉ rightᵉ unitalᵉ concatenationᵉ operation](foundation.strictly-right-unital-concatenation-identifications.md).ᵉ
Whileᵉ thisᵉ obstructsᵉ usᵉ fromᵉ showingᵉ thatᵉ theᵉ
[homotopy](foundation-core.homotopies.mdᵉ) `eq-yoneda-eqᵉ ∘ᵉ yoneda-eq-eqᵉ ~ᵉ id`ᵉ
holdsᵉ byᵉ reflexivityᵉ asᵉ demonstratedᵉ byᵉ theᵉ computationᵉ

```text
  eq-yoneda-eqᵉ ∘ᵉ yoneda-eq-eqᵉ
  ≐ᵉ pᵉ ↦ᵉ (fᵉ ↦ᵉ fᵉ reflᵉ) (qᵉ ↦ᵉ qᵉ ∙ᵉ pᵉ)
  ≐ᵉ pᵉ ↦ᵉ ((qᵉ ↦ᵉ qᵉ ∙ᵉ pᵉ) reflᵉ)
  ≐ᵉ pᵉ ↦ᵉ reflᵉ ∙ᵉ p,ᵉ
```

itᵉ allowsᵉ usᵉ to showᵉ thatᵉ reflexivitiesᵉ areᵉ preservedᵉ strictlyᵉ in bothᵉ
directions,ᵉ andᵉ notᵉ justᵉ fromᵉ `xᵉ ＝ʸᵉ y`ᵉ to `xᵉ ＝ᵉ y`.ᵉ

Fromᵉ leftᵉ to rightᵉ:

```text
  yoneda-eq-eqᵉ reflᵉ ≐ᵉ (pᵉ ↦ᵉ (qᵉ ↦ᵉ qᵉ ∙ᵉ pᵉ)) reflᵉ ≐ᵉ (qᵉ ↦ᵉ qᵉ ∙ᵉ reflᵉ) ≐ᵉ (qᵉ ↦ᵉ qᵉ) ≐ᵉ reflʸᵉ
```

andᵉ fromᵉ rightᵉ to leftᵉ:

```text
  eq-yoneda-eqᵉ reflʸᵉ ≐ᵉ (fᵉ ↦ᵉ fᵉ reflᵉ) reflʸᵉ ≐ᵉ (qᵉ ↦ᵉ qᵉ) reflᵉ ≐ᵉ refl.ᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ}
  where

  yoneda-eq-eqᵉ : xᵉ ＝ᵉ yᵉ → xᵉ ＝ʸᵉ yᵉ
  yoneda-eq-eqᵉ pᵉ zᵉ qᵉ = qᵉ ∙ᵣᵉ pᵉ

  eq-yoneda-eqᵉ : xᵉ ＝ʸᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-yoneda-eqᵉ fᵉ = fᵉ xᵉ reflᵉ
```

Theᵉ constructionᵉ ofᵉ theᵉ homotopyᵉ `yoneda-eq-eqᵉ ∘ᵉ eq-yoneda-eqᵉ ~ᵉ id`ᵉ requiresᵉ theᵉ
[functionᵉ extensionalityᵉ axiom](foundation.function-extensionality.md).ᵉ Andᵉ
whileᵉ weᵉ couldᵉ showᵉ anᵉ analogousᵉ inductionᵉ principleᵉ ofᵉ theᵉ Yonedaᵉ identityᵉ
typesᵉ withoutᵉ theᵉ useᵉ ofᵉ thisᵉ axiom,ᵉ functionᵉ extensionalityᵉ willᵉ becomeᵉ
indispensableᵉ regardlessᵉ whenᵉ weᵉ proceedᵉ to provingᵉ miscellaneousᵉ algebraicᵉ lawsᵉ
ofᵉ theᵉ Yonedaᵉ identityᵉ type.ᵉ

```agda
  is-section-eq-yoneda-eqᵉ :
    is-sectionᵉ yoneda-eq-eqᵉ eq-yoneda-eqᵉ
  is-section-eq-yoneda-eqᵉ fᵉ =
    eq-multivariable-htpyᵉ 2
      ( λ _ pᵉ → invᵉ (commutative-preconcatr-refl-Id-yoneda-Idᵉ fᵉ pᵉ))

  is-retraction-eq-yoneda-eqᵉ :
    is-retractionᵉ yoneda-eq-eqᵉ eq-yoneda-eqᵉ
  is-retraction-eq-yoneda-eqᵉ pᵉ = left-unit-right-strict-concatᵉ

  is-equiv-yoneda-eq-eqᵉ : is-equivᵉ yoneda-eq-eqᵉ
  pr1ᵉ (pr1ᵉ is-equiv-yoneda-eq-eqᵉ) = eq-yoneda-eqᵉ
  pr2ᵉ (pr1ᵉ is-equiv-yoneda-eq-eqᵉ) = is-section-eq-yoneda-eqᵉ
  pr1ᵉ (pr2ᵉ is-equiv-yoneda-eq-eqᵉ) = eq-yoneda-eqᵉ
  pr2ᵉ (pr2ᵉ is-equiv-yoneda-eq-eqᵉ) = is-retraction-eq-yoneda-eqᵉ

  is-equiv-eq-yoneda-eqᵉ : is-equivᵉ eq-yoneda-eqᵉ
  pr1ᵉ (pr1ᵉ is-equiv-eq-yoneda-eqᵉ) = yoneda-eq-eqᵉ
  pr2ᵉ (pr1ᵉ is-equiv-eq-yoneda-eqᵉ) = is-retraction-eq-yoneda-eqᵉ
  pr1ᵉ (pr2ᵉ is-equiv-eq-yoneda-eqᵉ) = yoneda-eq-eqᵉ
  pr2ᵉ (pr2ᵉ is-equiv-eq-yoneda-eqᵉ) = is-section-eq-yoneda-eqᵉ

  equiv-yoneda-eq-eqᵉ : (xᵉ ＝ᵉ yᵉ) ≃ᵉ (xᵉ ＝ʸᵉ yᵉ)
  pr1ᵉ equiv-yoneda-eq-eqᵉ = yoneda-eq-eqᵉ
  pr2ᵉ equiv-yoneda-eq-eqᵉ = is-equiv-yoneda-eq-eqᵉ

  equiv-eq-yoneda-eqᵉ : (xᵉ ＝ʸᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ yᵉ)
  pr1ᵉ equiv-eq-yoneda-eqᵉ = eq-yoneda-eqᵉ
  pr2ᵉ equiv-eq-yoneda-eqᵉ = is-equiv-eq-yoneda-eqᵉ
```

Thisᵉ equvialenceᵉ preservesᵉ theᵉ reflexivityᵉ elementsᵉ strictlyᵉ in bothᵉ directions.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ : Aᵉ}
  where

  is-section-eq-yoneda-eq-reflᵉ :
    yoneda-eq-eqᵉ (eq-yoneda-eqᵉ (reflʸᵉ {xᵉ = xᵉ})) ＝ᵉ reflʸᵉ
  is-section-eq-yoneda-eq-reflᵉ = reflᵉ

  preserves-refl-yoneda-eq-eqᵉ :
    yoneda-eq-eqᵉ (reflᵉ {xᵉ = xᵉ}) ＝ᵉ reflʸᵉ
  preserves-refl-yoneda-eq-eqᵉ = reflᵉ

  preserves-refl-eq-yoneda-eqᵉ :
    eq-yoneda-eqᵉ (reflʸᵉ {xᵉ = xᵉ}) ＝ᵉ reflᵉ
  preserves-refl-eq-yoneda-eqᵉ = reflᵉ
```

Below,ᵉ weᵉ considerᵉ theᵉ alternativeᵉ definitionᵉ ofᵉ `yoneda-eq-eq`ᵉ using theᵉ
strictlyᵉ leftᵉ unitalᵉ concatenationᵉ operationᵉ onᵉ standardᵉ identityᵉ types.ᵉ Asᵉ weᵉ
canᵉ see,ᵉ theᵉ retractingᵉ homotopyᵉ holdsᵉ strictly,ᵉ butᵉ nowᵉ `yoneda-eq-eqᵉ refl`ᵉ
doesᵉ notᵉ computeᵉ strictlyᵉ to `reflʸ`.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ}
  where

  yoneda-eq-eq'ᵉ : xᵉ ＝ᵉ yᵉ → xᵉ ＝ʸᵉ yᵉ
  yoneda-eq-eq'ᵉ pᵉ zᵉ qᵉ = qᵉ ∙ᵉ pᵉ

  is-section-eq-yoneda-eq'ᵉ :
    is-sectionᵉ yoneda-eq-eq'ᵉ eq-yoneda-eqᵉ
  is-section-eq-yoneda-eq'ᵉ fᵉ =
    eq-multivariable-htpyᵉ 2
      ( λ _ pᵉ → invᵉ (commutative-preconcat-refl-Id-yoneda-Idᵉ fᵉ pᵉ))

  is-retraction-eq-yoneda-eq'ᵉ :
    is-retractionᵉ yoneda-eq-eq'ᵉ eq-yoneda-eqᵉ
  is-retraction-eq-yoneda-eq'ᵉ pᵉ = reflᵉ

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  preserves-refl-yoneda-eq-eq'ᵉ :
    {xᵉ : Aᵉ} → yoneda-eq-eq'ᵉ (reflᵉ {xᵉ = xᵉ}) ＝ᵉ reflʸᵉ
  preserves-refl-yoneda-eq-eq'ᵉ =
    eq-multivariable-htpyᵉ 2 (λ _ pᵉ → right-unitᵉ)
```

### Torsoriality of the Yoneda identity types

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ : Aᵉ}
  where

  is-torsorial-yoneda-Idᵉ : is-torsorialᵉ (yoneda-Idᵉ xᵉ)
  is-torsorial-yoneda-Idᵉ =
    is-contr-equivᵉ
      ( Σᵉ Aᵉ (xᵉ ＝ᵉ_))
      ( equiv-totᵉ (λ yᵉ → equiv-eq-yoneda-eqᵉ {xᵉ = xᵉ} {yᵉ}))
      ( is-torsorial-Idᵉ xᵉ)
```

### The dependent universal property of the Yoneda identity types

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ : Aᵉ}
  where

  dependent-universal-property-identity-system-yoneda-Idᵉ :
    dependent-universal-property-identity-systemᵉ
      ( yoneda-Idᵉ xᵉ)
      ( reflʸᵉ)
  dependent-universal-property-identity-system-yoneda-Idᵉ =
    dependent-universal-property-identity-system-is-torsorialᵉ
      ( reflʸᵉ)
      ( is-torsorial-yoneda-Idᵉ)
```

### The induction principle for the Yoneda identity types

Theᵉ Yonedaᵉ identityᵉ typesᵉ satisfyᵉ theᵉ inductionᵉ principleᵉ ofᵉ theᵉ identityᵉ types.ᵉ
Thisᵉ statesᵉ thatᵉ givenᵉ aᵉ baseᵉ pointᵉ `xᵉ : A`ᵉ andᵉ aᵉ familyᵉ ofᵉ typesᵉ overᵉ theᵉ
identityᵉ typesᵉ basedᵉ atᵉ `x`,ᵉ `Bᵉ : (yᵉ : Aᵉ) (fᵉ : xᵉ ＝ʸᵉ yᵉ) → UUᵉ l2`,ᵉ thenᵉ to
constructᵉ aᵉ dependentᵉ functionᵉ `gᵉ : (yᵉ : Aᵉ) (fᵉ : xᵉ ＝ʸᵉ yᵉ) → Bᵉ yᵉ p`ᵉ itᵉ sufficesᵉ
to defineᵉ itᵉ atᵉ `gᵉ xᵉ reflʸ`.ᵉ

**Note.**ᵉ Asᵉ statedᵉ before,ᵉ aᵉ drawbackᵉ ofᵉ theᵉ Yonedaᵉ identityᵉ typesᵉ isᵉ thatᵉ theyᵉ
do notᵉ satisfyᵉ aᵉ strictᵉ computationᵉ ruleᵉ forᵉ thisᵉ inductionᵉ principle.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ : Aᵉ}
  (Bᵉ : (yᵉ : Aᵉ) (fᵉ : xᵉ ＝ʸᵉ yᵉ) → UUᵉ l2ᵉ)
  where

  ind-yoneda-Id'ᵉ :
    (bᵉ : Bᵉ xᵉ reflʸᵉ) {yᵉ : Aᵉ} (fᵉ : xᵉ ＝ʸᵉ yᵉ) → Bᵉ yᵉ fᵉ
  ind-yoneda-Id'ᵉ bᵉ {yᵉ} =
    map-inv-is-equivᵉ
      ( dependent-universal-property-identity-system-yoneda-Idᵉ Bᵉ)
      ( bᵉ)
      ( yᵉ)

  compute-ind-yoneda-Id'ᵉ :
    (bᵉ : Bᵉ xᵉ reflʸᵉ) →
    ind-yoneda-Id'ᵉ bᵉ reflʸᵉ ＝ᵉ bᵉ
  compute-ind-yoneda-Id'ᵉ =
    is-section-map-inv-is-equivᵉ
      ( dependent-universal-property-identity-system-yoneda-Idᵉ Bᵉ)

  uniqueness-ind-yoneda-Id'ᵉ :
    (bᵉ : (yᵉ : Aᵉ) (fᵉ : xᵉ ＝ʸᵉ yᵉ) → Bᵉ yᵉ fᵉ) →
    (λ yᵉ → ind-yoneda-Id'ᵉ (bᵉ xᵉ reflʸᵉ) {yᵉ}) ＝ᵉ bᵉ
  uniqueness-ind-yoneda-Id'ᵉ =
    is-retraction-map-inv-is-equivᵉ
      ( dependent-universal-property-identity-system-yoneda-Idᵉ Bᵉ)
```

Theᵉ followingᵉ isᵉ aᵉ moreᵉ concreteᵉ constructionᵉ ofᵉ theᵉ inductionᵉ principle.ᵉ Weᵉ
observeᵉ thatᵉ whileᵉ `eq-yoneda-eq`ᵉ andᵉ `yoneda-eq-eq`ᵉ preserveᵉ reflexivitiesᵉ
strictlyᵉ asᵉ required,ᵉ theᵉ reductionᵉ isᵉ obstructedᵉ becauseᵉ theᵉ proofᵉ ofᵉ
`is-section-eq-yoneda-eq`ᵉ doesᵉ notᵉ reduceᵉ to `refl`ᵉ whenᵉ `fᵉ ≐ᵉ reflʸ`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ : Aᵉ}
  (Bᵉ : (yᵉ : Aᵉ) (fᵉ : xᵉ ＝ʸᵉ yᵉ) → UUᵉ l2ᵉ)
  where

  ind-yoneda-Idᵉ :
    (bᵉ : Bᵉ xᵉ reflʸᵉ) {yᵉ : Aᵉ} (fᵉ : xᵉ ＝ʸᵉ yᵉ) → Bᵉ yᵉ fᵉ
  ind-yoneda-Idᵉ bᵉ {yᵉ} fᵉ =
    trᵉ
      ( Bᵉ yᵉ)
      ( is-section-eq-yoneda-eqᵉ fᵉ)
      ( ind-Idᵉ xᵉ (λ yᵉ pᵉ → Bᵉ yᵉ (yoneda-eq-eqᵉ pᵉ)) bᵉ yᵉ (eq-yoneda-eqᵉ fᵉ))
```

Whileᵉ theᵉ inductionᵉ principleᵉ doesᵉ notᵉ haveᵉ theᵉ desiredᵉ reductionᵉ behaviour,ᵉ theᵉ
nondependentᵉ eliminatorᵉ does.ᵉ Thisᵉ isᵉ simplyᵉ becauseᵉ weᵉ noᵉ longerᵉ needᵉ to
[transport](foundation-core.transport-along-identifications.mdᵉ) alongᵉ
`is-section-eq-yoneda-eq`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  rec-yoneda-Idᵉ :
    (bᵉ : Bᵉ xᵉ) {yᵉ : Aᵉ} → xᵉ ＝ʸᵉ yᵉ → Bᵉ yᵉ
  rec-yoneda-Idᵉ bᵉ fᵉ = trᵉ Bᵉ (eq-yoneda-eqᵉ fᵉ) bᵉ

  compute-rec-yoneda-Idᵉ :
    (bᵉ : Bᵉ xᵉ) → rec-yoneda-Idᵉ bᵉ reflʸᵉ ＝ᵉ bᵉ
  compute-rec-yoneda-Idᵉ bᵉ = reflᵉ

  uniqueness-rec-yoneda-Idᵉ :
    (bᵉ : (yᵉ : Aᵉ) → xᵉ ＝ʸᵉ yᵉ → Bᵉ yᵉ) →
    (λ yᵉ → rec-yoneda-Idᵉ (bᵉ xᵉ reflʸᵉ) {yᵉ}) ＝ᵉ bᵉ
  uniqueness-rec-yoneda-Idᵉ bᵉ =
    ( invᵉ
      ( uniqueness-ind-yoneda-Id'ᵉ
        ( λ yᵉ _ → Bᵉ yᵉ)
        ( λ yᵉ → rec-yoneda-Idᵉ (bᵉ xᵉ reflʸᵉ)))) ∙ᵉ
    ( uniqueness-ind-yoneda-Id'ᵉ (λ yᵉ _ → Bᵉ yᵉ) bᵉ)
```

## Structure

Theᵉ Yonedaᵉ identityᵉ typesᵉ formᵉ aᵉ strictlyᵉ compositionalᵉ weakᵉ groupoidalᵉ
structureᵉ onᵉ types.ᵉ

### Inverting Yoneda identifications

Weᵉ considerᵉ twoᵉ waysᵉ ofᵉ definingᵉ theᵉ inversionᵉ operationᵉ onᵉ Yonedaᵉ
identificationsᵉ: byᵉ theᵉ strictlyᵉ rightᵉ unital,ᵉ andᵉ strictlyᵉ leftᵉ unitalᵉ
concatenationᵉ operationᵉ onᵉ theᵉ underlyingᵉ identityᵉ typeᵉ respectively.ᵉ Inᵉ
contrastᵉ to theᵉ latter,ᵉ theᵉ formerᵉ enjoysᵉ theᵉ computationalᵉ propertyᵉ

```text
  invʸᵉ reflʸᵉ ≐ᵉ reflʸ,ᵉ
```

henceᵉ itᵉ willᵉ beᵉ preferredᵉ goingᵉ forward.ᵉ

#### The inversion operation defined by the strictly right unital concatenation operation on identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  invʸᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ʸᵉ yᵉ → yᵉ ＝ʸᵉ xᵉ
  invʸᵉ {xᵉ} fᵉ zᵉ pᵉ = pᵉ ∙ᵣᵉ invᵉ (fᵉ xᵉ reflᵉ)

  compute-inv-refl-yoneda-Idᵉ :
    {xᵉ : Aᵉ} → invʸᵉ (reflʸᵉ {xᵉ = xᵉ}) ＝ᵉ reflʸᵉ
  compute-inv-refl-yoneda-Idᵉ = reflᵉ

  inv-inv-yoneda-Idᵉ :
    {xᵉ yᵉ : Aᵉ} (fᵉ : xᵉ ＝ʸᵉ yᵉ) → invʸᵉ (invʸᵉ fᵉ) ＝ᵉ fᵉ
  inv-inv-yoneda-Idᵉ {xᵉ} fᵉ =
    eq-multivariable-htpyᵉ 2
      ( λ _ pᵉ →
        ( apᵉ
          ( pᵉ ∙ᵣᵉ_)
          ( apᵉ invᵉ left-unit-right-strict-concatᵉ ∙ᵉ inv-invᵉ (fᵉ xᵉ reflᵉ))) ∙ᵉ
        ( invᵉ (commutative-preconcatr-refl-Id-yoneda-Idᵉ fᵉ pᵉ)))
```

Theᵉ inversionᵉ operationᵉ correspondsᵉ to theᵉ standardᵉ inversionᵉ operationᵉ onᵉ
identificationsᵉ:

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  preserves-inv-yoneda-eq-eq'ᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → yoneda-eq-eqᵉ (invᵉ pᵉ) ＝ᵉ invʸᵉ (yoneda-eq-eq'ᵉ pᵉ)
  preserves-inv-yoneda-eq-eq'ᵉ pᵉ = reflᵉ

  preserves-inv-yoneda-eq-eqᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → yoneda-eq-eqᵉ (invᵉ pᵉ) ＝ᵉ invʸᵉ (yoneda-eq-eqᵉ pᵉ)
  preserves-inv-yoneda-eq-eqᵉ pᵉ =
    eq-multivariable-htpyᵉ 2
      ( λ _ qᵉ → apᵉ (λ rᵉ → qᵉ ∙ᵣᵉ invᵉ rᵉ) (invᵉ left-unit-right-strict-concatᵉ))

  preserves-inv-eq-yoneda-eqᵉ :
    {xᵉ yᵉ : Aᵉ} (fᵉ : xᵉ ＝ʸᵉ yᵉ) → eq-yoneda-eqᵉ (invʸᵉ fᵉ) ＝ᵉ invᵉ (eq-yoneda-eqᵉ fᵉ)
  preserves-inv-eq-yoneda-eqᵉ fᵉ = left-unit-right-strict-concatᵉ
```

#### The inversion operation defined by the strictly left unital concatenation operation on identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  left-strict-inv-yoneda-Idᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ʸᵉ yᵉ → yᵉ ＝ʸᵉ xᵉ
  left-strict-inv-yoneda-Idᵉ {xᵉ} fᵉ zᵉ pᵉ = pᵉ ∙ᵉ invᵉ (fᵉ xᵉ reflᵉ)

  compute-left-strict-inv-yoneda-Id-reflᵉ :
    {xᵉ : Aᵉ} → left-strict-inv-yoneda-Idᵉ (reflʸᵉ {xᵉ = xᵉ}) ＝ᵉ reflʸᵉ
  compute-left-strict-inv-yoneda-Id-reflᵉ =
    eq-multivariable-htpyᵉ 2 (λ _ pᵉ → right-unitᵉ)

  left-strict-inv-left-strict-inv-yoneda-Idᵉ :
    {xᵉ yᵉ : Aᵉ} (fᵉ : xᵉ ＝ʸᵉ yᵉ) →
    left-strict-inv-yoneda-Idᵉ (left-strict-inv-yoneda-Idᵉ fᵉ) ＝ᵉ fᵉ
  left-strict-inv-left-strict-inv-yoneda-Idᵉ {xᵉ} fᵉ =
    eq-multivariable-htpyᵉ 2
      ( λ _ pᵉ →
        ( apᵉ (pᵉ ∙ᵉ_) (inv-invᵉ (fᵉ xᵉ reflᵉ))) ∙ᵉ
        ( invᵉ (commutative-preconcat-refl-Id-yoneda-Idᵉ fᵉ pᵉ)))
```

Thisᵉ inversionᵉ operationᵉ alsoᵉ correspondsᵉ to theᵉ standardᵉ inversionᵉ operationᵉ onᵉ
identificationsᵉ:

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  preserves-left-strict-inv-yoneda-eq-eqᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
    yoneda-eq-eqᵉ (invᵉ pᵉ) ＝ᵉ left-strict-inv-yoneda-Idᵉ (yoneda-eq-eqᵉ pᵉ)
  preserves-left-strict-inv-yoneda-eq-eqᵉ pᵉ =
    eq-multivariable-htpyᵉ 2
      ( λ _ qᵉ →
        ( eq-concat-right-strict-concatᵉ qᵉ (invᵉ pᵉ)) ∙ᵉ
        ( apᵉ (λ rᵉ → qᵉ ∙ᵉ invᵉ rᵉ) (invᵉ left-unit-right-strict-concatᵉ)))

  preserves-left-strict-inv-eq-yoneda-eqᵉ :
    {xᵉ yᵉ : Aᵉ} (fᵉ : xᵉ ＝ʸᵉ yᵉ) →
    eq-yoneda-eqᵉ (left-strict-inv-yoneda-Idᵉ fᵉ) ＝ᵉ invᵉ (eq-yoneda-eqᵉ fᵉ)
  preserves-left-strict-inv-eq-yoneda-eqᵉ fᵉ = reflᵉ
```

### Concatenation of Yoneda identifications

Theᵉ concatenationᵉ operationᵉ onᵉ Yonedaᵉ identificationsᵉ isᵉ definedᵉ byᵉ functionᵉ
compositionᵉ

```text
  fᵉ ∙ʸᵉ gᵉ :=ᵉ zᵉ pᵉ ↦ᵉ gᵉ zᵉ (fᵉ zᵉ pᵉ)
```

andᵉ isᵉ thusᵉ strictlyᵉ associativeᵉ andᵉ two-sidedᵉ unitalᵉ (sinceᵉ theᵉ reflexivitiesᵉ
areᵉ givenᵉ byᵉ theᵉ identityᵉ functions).ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  infixl 15 _∙ʸᵉ_
  _∙ʸᵉ_ : {xᵉ yᵉ zᵉ : Aᵉ} → xᵉ ＝ʸᵉ yᵉ → yᵉ ＝ʸᵉ zᵉ → xᵉ ＝ʸᵉ zᵉ
  (fᵉ ∙ʸᵉ gᵉ) zᵉ pᵉ = gᵉ zᵉ (fᵉ zᵉ pᵉ)

  concat-yoneda-Idᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ʸᵉ yᵉ → (zᵉ : Aᵉ) → yᵉ ＝ʸᵉ zᵉ → xᵉ ＝ʸᵉ zᵉ
  concat-yoneda-Idᵉ fᵉ zᵉ gᵉ = fᵉ ∙ʸᵉ gᵉ

  concat-yoneda-Id'ᵉ : (xᵉ : Aᵉ) {yᵉ zᵉ : Aᵉ} → yᵉ ＝ʸᵉ zᵉ → xᵉ ＝ʸᵉ yᵉ → xᵉ ＝ʸᵉ zᵉ
  concat-yoneda-Id'ᵉ xᵉ gᵉ fᵉ = fᵉ ∙ʸᵉ gᵉ
```

Theᵉ concatenationᵉ operationᵉ correspondsᵉ to theᵉ standardᵉ concatenationᵉ operationᵉ
onᵉ identificationsᵉ:

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  preserves-concat-yoneda-eq-eqᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    yoneda-eq-eqᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ yoneda-eq-eqᵉ pᵉ ∙ʸᵉ yoneda-eq-eqᵉ qᵉ
  preserves-concat-yoneda-eq-eqᵉ reflᵉ reflᵉ = reflᵉ

  preserves-concat-eq-yoneda-eqᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (fᵉ : xᵉ ＝ʸᵉ yᵉ) (gᵉ : yᵉ ＝ʸᵉ zᵉ) →
    eq-yoneda-eqᵉ (fᵉ ∙ʸᵉ gᵉ) ＝ᵉ eq-yoneda-eqᵉ fᵉ ∙ᵉ eq-yoneda-eqᵉ gᵉ
  preserves-concat-eq-yoneda-eqᵉ {xᵉ} fᵉ gᵉ =
    commutative-preconcat-refl-Id-yoneda-Idᵉ gᵉ (fᵉ xᵉ reflᵉ)
```

### The groupoidal laws for the Yoneda identity types

Asᵉ weᵉ mayᵉ nowᵉ observe,ᵉ associativityᵉ andᵉ theᵉ unitᵉ lawsᵉ holdᵉ byᵉ `refl`.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ}
  where

  assoc-yoneda-Idᵉ :
    (fᵉ : xᵉ ＝ʸᵉ yᵉ) {zᵉ wᵉ : Aᵉ} (gᵉ : yᵉ ＝ʸᵉ zᵉ) (hᵉ : zᵉ ＝ʸᵉ wᵉ) →
    (fᵉ ∙ʸᵉ gᵉ) ∙ʸᵉ hᵉ ＝ᵉ fᵉ ∙ʸᵉ (gᵉ ∙ʸᵉ hᵉ)
  assoc-yoneda-Idᵉ fᵉ gᵉ hᵉ = reflᵉ

  left-unit-yoneda-Idᵉ :
    {fᵉ : xᵉ ＝ʸᵉ yᵉ} → reflʸᵉ ∙ʸᵉ fᵉ ＝ᵉ fᵉ
  left-unit-yoneda-Idᵉ = reflᵉ

  right-unit-yoneda-Idᵉ :
    {fᵉ : xᵉ ＝ʸᵉ yᵉ} → fᵉ ∙ʸᵉ reflʸᵉ ＝ᵉ fᵉ
  right-unit-yoneda-Idᵉ = reflᵉ
```

Inᵉ addition,ᵉ weᵉ showᵉ aᵉ rangeᵉ ofᵉ basicᵉ algebraicᵉ lawsᵉ forᵉ theᵉ Yonedaᵉ identityᵉ
types.ᵉ

```agda
  left-inv-yoneda-Idᵉ :
    (fᵉ : xᵉ ＝ʸᵉ yᵉ) → invʸᵉ fᵉ ∙ʸᵉ fᵉ ＝ᵉ reflʸᵉ
  left-inv-yoneda-Idᵉ fᵉ =
    eq-multivariable-htpyᵉ 2
      ( λ _ pᵉ →
        ( commutative-preconcatr-Id-yoneda-Idᵉ fᵉ pᵉ (invᵉ (fᵉ xᵉ reflᵉ))) ∙ᵉ
        ( apᵉ (pᵉ ∙ᵣᵉ_) (compute-inv-Id-yoneda-Idᵉ fᵉ)))

  left-left-strict-inv-yoneda-Idᵉ :
    (fᵉ : xᵉ ＝ʸᵉ yᵉ) → left-strict-inv-yoneda-Idᵉ fᵉ ∙ʸᵉ fᵉ ＝ᵉ reflʸᵉ
  left-left-strict-inv-yoneda-Idᵉ fᵉ =
    eq-multivariable-htpyᵉ 2
      ( λ _ pᵉ →
        ( commutative-preconcat-Id-yoneda-Idᵉ fᵉ pᵉ (invᵉ (fᵉ xᵉ reflᵉ))) ∙ᵉ
        ( apᵉ (pᵉ ∙ᵉ_) (compute-inv-Id-yoneda-Idᵉ fᵉ) ∙ᵉ right-unitᵉ))

  right-inv-yoneda-Idᵉ :
    (fᵉ : xᵉ ＝ʸᵉ yᵉ) → fᵉ ∙ʸᵉ invʸᵉ fᵉ ＝ᵉ reflʸᵉ
  right-inv-yoneda-Idᵉ fᵉ =
    eq-multivariable-htpyᵉ 2
      ( λ _ pᵉ →
        ( apᵉ
          ( _∙ᵣᵉ invᵉ (fᵉ xᵉ reflᵉ))
          ( commutative-preconcatr-refl-Id-yoneda-Idᵉ fᵉ pᵉ)) ∙ᵉ
        ( assoc-right-strict-concatᵉ pᵉ (fᵉ xᵉ reflᵉ) (invᵉ (fᵉ xᵉ reflᵉ))) ∙ᵉ
        ( apᵉ (pᵉ ∙ᵣᵉ_) (right-inv-right-strict-concatᵉ (fᵉ xᵉ reflᵉ))))

  right-left-strict-inv-yoneda-Idᵉ :
    (fᵉ : xᵉ ＝ʸᵉ yᵉ) → fᵉ ∙ʸᵉ left-strict-inv-yoneda-Idᵉ fᵉ ＝ᵉ reflʸᵉ
  right-left-strict-inv-yoneda-Idᵉ fᵉ =
    eq-multivariable-htpyᵉ 2
      ( λ _ pᵉ →
        ( apᵉ
          ( _∙ᵉ invᵉ (fᵉ xᵉ reflᵉ))
          ( commutative-preconcat-refl-Id-yoneda-Idᵉ fᵉ pᵉ)) ∙ᵉ
        ( assocᵉ pᵉ (fᵉ xᵉ reflᵉ) (invᵉ (fᵉ xᵉ reflᵉ))) ∙ᵉ
        ( apᵉ (pᵉ ∙ᵉ_) (right-invᵉ (fᵉ xᵉ reflᵉ))) ∙ᵉ
        ( right-unitᵉ))

  distributive-inv-concat-yoneda-Idᵉ :
    (fᵉ : xᵉ ＝ʸᵉ yᵉ) {zᵉ : Aᵉ} (gᵉ : yᵉ ＝ʸᵉ zᵉ) →
    invʸᵉ (fᵉ ∙ʸᵉ gᵉ) ＝ᵉ invʸᵉ gᵉ ∙ʸᵉ invʸᵉ fᵉ
  distributive-inv-concat-yoneda-Idᵉ fᵉ gᵉ =
    eq-multivariable-htpyᵉ 2
      ( λ _ pᵉ →
        ( apᵉ
          ( pᵉ ∙ᵣᵉ_)
          ( ( apᵉ
              ( invᵉ)
              ( commutative-preconcatr-refl-Id-yoneda-Idᵉ gᵉ (fᵉ xᵉ reflᵉ))) ∙ᵉ
            ( distributive-inv-right-strict-concatᵉ (fᵉ xᵉ reflᵉ) (gᵉ yᵉ reflᵉ)))) ∙ᵉ
          ( invᵉ
            ( assoc-right-strict-concatᵉ pᵉ (invᵉ (gᵉ yᵉ reflᵉ)) (invᵉ (fᵉ xᵉ reflᵉ)))))

  distributive-left-strict-inv-concat-yoneda-Idᵉ :
    (fᵉ : xᵉ ＝ʸᵉ yᵉ) {zᵉ : Aᵉ} (gᵉ : yᵉ ＝ʸᵉ zᵉ) →
    left-strict-inv-yoneda-Idᵉ (fᵉ ∙ʸᵉ gᵉ) ＝ᵉ
    left-strict-inv-yoneda-Idᵉ gᵉ ∙ʸᵉ left-strict-inv-yoneda-Idᵉ fᵉ
  distributive-left-strict-inv-concat-yoneda-Idᵉ fᵉ gᵉ =
    eq-multivariable-htpyᵉ 2
      ( λ _ pᵉ →
        ( apᵉ
          ( pᵉ ∙ᵉ_)
          ( ( apᵉ
              ( invᵉ)
              ( commutative-preconcat-refl-Id-yoneda-Idᵉ gᵉ (fᵉ xᵉ reflᵉ))) ∙ᵉ
            ( distributive-inv-concatᵉ (fᵉ xᵉ reflᵉ) (gᵉ yᵉ reflᵉ)))) ∙ᵉ
        ( invᵉ (assocᵉ pᵉ (invᵉ (gᵉ yᵉ reflᵉ)) (invᵉ (fᵉ xᵉ reflᵉ)))))
```

## Operations

Weᵉ canᵉ defineᵉ aᵉ rangeᵉ basicᵉ operationsᵉ onᵉ theᵉ Yonedaᵉ identificationsᵉ thatᵉ allᵉ
enjoyᵉ strictᵉ computationalᵉ properties.ᵉ

### Action of functions on Yoneda identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  eq-ap-yoneda-Idᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ʸᵉ yᵉ → fᵉ xᵉ ＝ᵉ fᵉ yᵉ
  eq-ap-yoneda-Idᵉ = apᵉ fᵉ ∘ᵉ eq-yoneda-eqᵉ

  ap-yoneda-Idᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ʸᵉ yᵉ → fᵉ xᵉ ＝ʸᵉ fᵉ yᵉ
  ap-yoneda-Idᵉ = yoneda-eq-eqᵉ ∘ᵉ eq-ap-yoneda-Idᵉ

  compute-ap-refl-yoneda-Idᵉ : {xᵉ : Aᵉ} → ap-yoneda-Idᵉ (reflʸᵉ {xᵉ = xᵉ}) ＝ᵉ reflʸᵉ
  compute-ap-refl-yoneda-Idᵉ = reflᵉ

module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  compute-ap-id-yoneda-Idᵉ : {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ʸᵉ yᵉ) → ap-yoneda-Idᵉ idᵉ pᵉ ＝ᵉ pᵉ
  compute-ap-id-yoneda-Idᵉ {xᵉ} pᵉ =
    eq-multivariable-htpyᵉ 2
      ( λ _ qᵉ →
        ( apᵉ (qᵉ ∙ᵣᵉ_) (ap-idᵉ (pᵉ xᵉ reflᵉ))) ∙ᵉ
        ( invᵉ (commutative-preconcatr-refl-Id-yoneda-Idᵉ pᵉ qᵉ)))
```

### Action of binary functions on Yoneda identifications

Weᵉ obtainᵉ anᵉ actionᵉ ofᵉ binaryᵉ functionsᵉ onᵉ Yonedaᵉ identificationsᵉ thatᵉ computesᵉ
onᵉ bothᵉ argumentsᵉ using oneᵉ ofᵉ theᵉ twoᵉ sidesᵉ in theᵉ Grayᵉ interchangerᵉ diagramᵉ

```text
                      apᵉ (rᵉ ↦ᵉ fᵉ xᵉ rᵉ) qᵉ
                 fᵉ xᵉ yᵉ ------------->ᵉ fᵉ xᵉ y'ᵉ
                   |                    |
                   |                    |
  apᵉ (rᵉ ↦ᵉ fᵉ rᵉ yᵉ) pᵉ |                    | apᵉ (rᵉ ↦ᵉ fᵉ rᵉ y'ᵉ) pᵉ
                   |                    |
                   ∨ᵉ                    ∨ᵉ
                 fᵉ x'ᵉ yᵉ ------------>ᵉ fᵉ x'ᵉ y'ᵉ
                      apᵉ (rᵉ ↦ᵉ fᵉ x'ᵉ rᵉ) qᵉ
```

andᵉ theᵉ factᵉ thatᵉ theᵉ concatenationᵉ operationᵉ onᵉ Yonedaᵉ identificationsᵉ isᵉ
two-sidedᵉ strictlyᵉ unital.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ → Cᵉ)
  where

  ap-binary-yoneda-Idᵉ :
    {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ʸᵉ x'ᵉ) {yᵉ y'ᵉ : Bᵉ} (qᵉ : yᵉ ＝ʸᵉ y'ᵉ) → fᵉ xᵉ yᵉ ＝ʸᵉ fᵉ x'ᵉ y'ᵉ
  ap-binary-yoneda-Idᵉ {xᵉ} {x'ᵉ} pᵉ {yᵉ} {y'ᵉ} qᵉ =
    ap-yoneda-Idᵉ (λ zᵉ → fᵉ zᵉ yᵉ) pᵉ ∙ʸᵉ ap-yoneda-Idᵉ (fᵉ x'ᵉ) qᵉ

  left-unit-ap-binary-yoneda-Idᵉ :
    {xᵉ : Aᵉ} {yᵉ y'ᵉ : Bᵉ} (qᵉ : yᵉ ＝ʸᵉ y'ᵉ) →
    ap-binary-yoneda-Idᵉ reflʸᵉ qᵉ ＝ᵉ ap-yoneda-Idᵉ (fᵉ xᵉ) qᵉ
  left-unit-ap-binary-yoneda-Idᵉ qᵉ = reflᵉ

  right-unit-ap-binary-yoneda-Idᵉ :
    {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ʸᵉ x'ᵉ) {yᵉ : Bᵉ} →
    ap-binary-yoneda-Idᵉ pᵉ reflʸᵉ ＝ᵉ ap-yoneda-Idᵉ (λ zᵉ → fᵉ zᵉ yᵉ) pᵉ
  right-unit-ap-binary-yoneda-Idᵉ pᵉ = reflᵉ
```

### Transport along Yoneda identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  tr-yoneda-Idᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ʸᵉ yᵉ → Bᵉ xᵉ → Bᵉ yᵉ
  tr-yoneda-Idᵉ = trᵉ Bᵉ ∘ᵉ eq-yoneda-eqᵉ

  compute-tr-refl-yoneda-Idᵉ : {xᵉ : Aᵉ} → tr-yoneda-Idᵉ (reflʸᵉ {xᵉ = xᵉ}) ＝ᵉ idᵉ
  compute-tr-refl-yoneda-Idᵉ = reflᵉ
```

### Standard function extensionality with respect to Yoneda identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  htpy-yoneda-eqᵉ : fᵉ ＝ʸᵉ gᵉ → fᵉ ~ᵉ gᵉ
  htpy-yoneda-eqᵉ = htpy-eqᵉ ∘ᵉ eq-yoneda-eqᵉ

  yoneda-eq-htpyᵉ : fᵉ ~ᵉ gᵉ → fᵉ ＝ʸᵉ gᵉ
  yoneda-eq-htpyᵉ = yoneda-eq-eqᵉ ∘ᵉ eq-htpyᵉ

  equiv-htpy-yoneda-eqᵉ : (fᵉ ＝ʸᵉ gᵉ) ≃ᵉ (fᵉ ~ᵉ gᵉ)
  equiv-htpy-yoneda-eqᵉ = equiv-funextᵉ ∘eᵉ equiv-eq-yoneda-eqᵉ

  equiv-yoneda-eq-htpyᵉ : (fᵉ ~ᵉ gᵉ) ≃ᵉ (fᵉ ＝ʸᵉ gᵉ)
  equiv-yoneda-eq-htpyᵉ = equiv-yoneda-eq-eqᵉ ∘eᵉ equiv-eq-htpyᵉ

  funext-yoneda-Idᵉ : is-equivᵉ htpy-yoneda-eqᵉ
  funext-yoneda-Idᵉ = is-equiv-map-equivᵉ equiv-htpy-yoneda-eqᵉ
```

### Standard univalence with respect to Yoneda identifications

```agda
module _
  {l1ᵉ : Level} {Aᵉ Bᵉ : UUᵉ l1ᵉ}
  where

  map-yoneda-eqᵉ : Aᵉ ＝ʸᵉ Bᵉ → Aᵉ → Bᵉ
  map-yoneda-eqᵉ = map-eqᵉ ∘ᵉ eq-yoneda-eqᵉ

  equiv-yoneda-eqᵉ : Aᵉ ＝ʸᵉ Bᵉ → Aᵉ ≃ᵉ Bᵉ
  equiv-yoneda-eqᵉ = equiv-eqᵉ ∘ᵉ eq-yoneda-eqᵉ

  yoneda-eq-equivᵉ : Aᵉ ≃ᵉ Bᵉ → Aᵉ ＝ʸᵉ Bᵉ
  yoneda-eq-equivᵉ = yoneda-eq-eqᵉ ∘ᵉ eq-equivᵉ

  equiv-equiv-yoneda-eqᵉ : (Aᵉ ＝ʸᵉ Bᵉ) ≃ᵉ (Aᵉ ≃ᵉ Bᵉ)
  equiv-equiv-yoneda-eqᵉ = equiv-univalenceᵉ ∘eᵉ equiv-eq-yoneda-eqᵉ

  is-equiv-equiv-yoneda-eqᵉ : is-equivᵉ equiv-yoneda-eqᵉ
  is-equiv-equiv-yoneda-eqᵉ = is-equiv-map-equivᵉ equiv-equiv-yoneda-eqᵉ

  equiv-yoneda-eq-equivᵉ : (Aᵉ ≃ᵉ Bᵉ) ≃ᵉ (Aᵉ ＝ʸᵉ Bᵉ)
  equiv-yoneda-eq-equivᵉ = equiv-yoneda-eq-eqᵉ ∘eᵉ equiv-eq-equivᵉ Aᵉ Bᵉ

  is-equiv-yoneda-eq-equivᵉ : is-equivᵉ yoneda-eq-equivᵉ
  is-equiv-yoneda-eq-equivᵉ = is-equiv-map-equivᵉ equiv-yoneda-eq-equivᵉ
```

### Whiskering of Yoneda identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ}
  where

  left-whisker-concat-yoneda-Idᵉ :
    (pᵉ : xᵉ ＝ʸᵉ yᵉ) {qᵉ rᵉ : yᵉ ＝ʸᵉ zᵉ} → qᵉ ＝ʸᵉ rᵉ → pᵉ ∙ʸᵉ qᵉ ＝ʸᵉ pᵉ ∙ʸᵉ rᵉ
  left-whisker-concat-yoneda-Idᵉ pᵉ βᵉ = ap-yoneda-Idᵉ (pᵉ ∙ʸᵉ_) βᵉ

  right-whisker-concat-yoneda-Idᵉ :
    {pᵉ qᵉ : xᵉ ＝ʸᵉ yᵉ} → pᵉ ＝ʸᵉ qᵉ → (rᵉ : yᵉ ＝ʸᵉ zᵉ) → pᵉ ∙ʸᵉ rᵉ ＝ʸᵉ qᵉ ∙ʸᵉ rᵉ
  right-whisker-concat-yoneda-Idᵉ αᵉ rᵉ = ap-yoneda-Idᵉ (_∙ʸᵉ rᵉ) αᵉ
```

### Horizontal concatenation of Yoneda identifications

Weᵉ defineᵉ horizontalᵉ concatenationᵉ in suchᵉ aᵉ wayᵉ thatᵉ itᵉ computesᵉ asᵉ leftᵉ
whiskeringᵉ whenᵉ theᵉ left-handᵉ argumentᵉ isᵉ `refl`,ᵉ andᵉ computesᵉ asᵉ rightᵉ
whiskeringᵉ whenᵉ theᵉ right-handᵉ argumentᵉ isᵉ `refl`.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ}
  where

  horizontal-concat-yoneda-Id²ᵉ :
    {pᵉ qᵉ : xᵉ ＝ʸᵉ yᵉ} → pᵉ ＝ʸᵉ qᵉ → {uᵉ vᵉ : yᵉ ＝ʸᵉ zᵉ} → uᵉ ＝ʸᵉ vᵉ → pᵉ ∙ʸᵉ uᵉ ＝ʸᵉ qᵉ ∙ʸᵉ vᵉ
  horizontal-concat-yoneda-Id²ᵉ = ap-binary-yoneda-Idᵉ (_∙ʸᵉ_)

  compute-left-horizontal-concat-yoneda-Id²ᵉ :
    {pᵉ : xᵉ ＝ʸᵉ yᵉ} {uᵉ vᵉ : yᵉ ＝ʸᵉ zᵉ} (βᵉ : uᵉ ＝ʸᵉ vᵉ) →
    horizontal-concat-yoneda-Id²ᵉ reflʸᵉ βᵉ ＝ᵉ
    left-whisker-concat-yoneda-Idᵉ pᵉ βᵉ
  compute-left-horizontal-concat-yoneda-Id²ᵉ βᵉ = reflᵉ

  compute-right-horizontal-concat-yoneda-Id²ᵉ :
    {pᵉ qᵉ : xᵉ ＝ʸᵉ yᵉ} (αᵉ : pᵉ ＝ʸᵉ qᵉ) {uᵉ : yᵉ ＝ʸᵉ zᵉ} →
    horizontal-concat-yoneda-Id²ᵉ αᵉ (reflʸᵉ {xᵉ = uᵉ}) ＝ᵉ
    right-whisker-concat-yoneda-Idᵉ αᵉ uᵉ
  compute-right-horizontal-concat-yoneda-Id²ᵉ αᵉ = reflᵉ

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ}
  where

  left-unit-horizontal-concat-yoneda-Id²ᵉ :
    {pᵉ qᵉ : xᵉ ＝ʸᵉ yᵉ} (αᵉ : pᵉ ＝ʸᵉ qᵉ) →
    horizontal-concat-yoneda-Id²ᵉ reflʸᵉ αᵉ ＝ᵉ αᵉ
  left-unit-horizontal-concat-yoneda-Id²ᵉ = compute-ap-id-yoneda-Idᵉ

  right-unit-horizontal-concat-yoneda-Id²ᵉ :
    {pᵉ qᵉ : xᵉ ＝ʸᵉ yᵉ} (αᵉ : pᵉ ＝ʸᵉ qᵉ) →
    horizontal-concat-yoneda-Id²ᵉ αᵉ (reflʸᵉ {xᵉ = reflʸᵉ}) ＝ᵉ αᵉ
  right-unit-horizontal-concat-yoneda-Id²ᵉ = compute-ap-id-yoneda-Idᵉ
```

Sinceᵉ concatenationᵉ onᵉ Yonedaᵉ identificationsᵉ isᵉ strictlyᵉ associative,ᵉ theᵉ
compositesᵉ

```text
  horizontal-concat-yoneda-Id²ᵉ (horizontal-concat-yoneda-Id²ᵉ αᵉ βᵉ) γᵉ
```

andᵉ

```text
  horizontal-concat-yoneda-Id²ᵉ αᵉ (horizontal-concat-yoneda-Id²ᵉ βᵉ γᵉ)
```

inhabitᵉ theᵉ sameᵉ type.ᵉ Therefore,ᵉ weᵉ canᵉ poseᵉ theᵉ questionᵉ ofᵉ whetherᵉ theᵉ
horizontalᵉ concatenationᵉ operationᵉ isᵉ associative,ᵉ whichᵉ itᵉ is,ᵉ albeitᵉ weaklyᵉ:

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
  where

  assoc-horizontal-concat-yoneda-Id²ᵉ :
    {pᵉ p'ᵉ : xᵉ ＝ʸᵉ yᵉ} (αᵉ : pᵉ ＝ʸᵉ p'ᵉ)
    {qᵉ q'ᵉ : yᵉ ＝ʸᵉ zᵉ} (βᵉ : qᵉ ＝ʸᵉ q'ᵉ)
    {rᵉ r'ᵉ : zᵉ ＝ʸᵉ wᵉ} (γᵉ : rᵉ ＝ʸᵉ r'ᵉ) →
    horizontal-concat-yoneda-Id²ᵉ (horizontal-concat-yoneda-Id²ᵉ αᵉ βᵉ) γᵉ ＝ᵉ
    horizontal-concat-yoneda-Id²ᵉ αᵉ (horizontal-concat-yoneda-Id²ᵉ βᵉ γᵉ)
  assoc-horizontal-concat-yoneda-Id²ᵉ αᵉ {qᵉ} βᵉ {rᵉ} =
    ind-yoneda-Idᵉ
      ( λ _ γᵉ →
        ( horizontal-concat-yoneda-Id²ᵉ (horizontal-concat-yoneda-Id²ᵉ αᵉ βᵉ) γᵉ) ＝ᵉ
        ( horizontal-concat-yoneda-Id²ᵉ αᵉ (horizontal-concat-yoneda-Id²ᵉ βᵉ γᵉ)))
      ( ind-yoneda-Idᵉ
        ( λ _ βᵉ →
          ( horizontal-concat-yoneda-Id²ᵉ
            ( horizontal-concat-yoneda-Id²ᵉ αᵉ βᵉ)
            ( reflʸᵉ {xᵉ = rᵉ})) ＝ᵉ
          ( horizontal-concat-yoneda-Id²ᵉ
            ( αᵉ)
            ( horizontal-concat-yoneda-Id²ᵉ βᵉ (reflʸᵉ {xᵉ = rᵉ}))))
        ( ind-yoneda-Idᵉ
          ( λ _ αᵉ →
            ( horizontal-concat-yoneda-Id²ᵉ
              ( horizontal-concat-yoneda-Id²ᵉ αᵉ (reflʸᵉ {xᵉ = qᵉ}))
              ( reflʸᵉ {xᵉ = rᵉ})) ＝ᵉ
            ( horizontal-concat-yoneda-Id²ᵉ
              ( αᵉ)
              ( horizontal-concat-yoneda-Id²ᵉ (reflʸᵉ {xᵉ = qᵉ}) (reflʸᵉ {xᵉ = rᵉ}))))
          ( reflᵉ)
          ( αᵉ))
        ( βᵉ))
```

### Vertical concatenation of Yoneda identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ}
  where

  vertical-concat-yoneda-Id²ᵉ :
    {pᵉ qᵉ rᵉ : xᵉ ＝ʸᵉ yᵉ} → pᵉ ＝ʸᵉ qᵉ → qᵉ ＝ʸᵉ rᵉ → pᵉ ＝ʸᵉ rᵉ
  vertical-concat-yoneda-Id²ᵉ αᵉ βᵉ = αᵉ ∙ʸᵉ βᵉ
```

## See also

-ᵉ [Theᵉ strictlyᵉ involutiveᵉ identityᵉ types](foundation.strictly-involutive-identity-types.mdᵉ)
  forᵉ anᵉ identityᵉ relationᵉ thatᵉ isᵉ strictlyᵉ involutive,ᵉ andᵉ one-sidedᵉ unital.ᵉ
-ᵉ [Theᵉ computationalᵉ identityᵉ types](foundation.computational-identity-types.mdᵉ)
  forᵉ anᵉ identityᵉ relationᵉ thatᵉ isᵉ strictlyᵉ involutive,ᵉ associative,ᵉ andᵉ
  one-sidedᵉ unital.ᵉ

## References

{{#bibliographyᵉ}} {{#referenceᵉ Esc19DefinitionsEquivalenceᵉ}}