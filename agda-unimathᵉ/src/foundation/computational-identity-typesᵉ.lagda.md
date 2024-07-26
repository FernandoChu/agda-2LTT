# Computational identity types

```agda
module foundation.computational-identity-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.strictly-right-unital-concatenation-identificationsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-identity-systemsᵉ
open import foundation.universe-levelsᵉ
open import foundation.yoneda-identity-typesᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
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
{{#conceptᵉ "computationalᵉ identityᵉ types"ᵉ Agda=computational-Idᵉ}} `xᵉ ＝ʲᵉ y`,ᵉ
whoseᵉ elementsᵉ weᵉ callᵉ
{{#conceptᵉ "computationalᵉ identifications"ᵉ Agda=computational-Id}}.ᵉ Theseᵉ areᵉ
definedᵉ using theᵉ constructionᵉ ofᵉ theᵉ
[strictlyᵉ involutiveᵉ identityᵉ types](foundation.strictly-involutive-identity-types.mdᵉ):

```text
  (xᵉ ＝ⁱᵉ yᵉ) :=ᵉ Σᵉ (zᵉ : Aᵉ) ((zᵉ ＝ᵉ yᵉ) ×ᵉ (zᵉ ＝ᵉ xᵉ))
```

butᵉ using theᵉ [Yonedaᵉ identityᵉ types](foundation.yoneda-identity-types.mdᵉ)
(`_＝ʸ_`ᵉ) asᵉ theᵉ underlyingᵉ identityᵉ typesᵉ:

```text
  (xᵉ ＝ʸᵉ yᵉ) :=ᵉ (zᵉ : Aᵉ) → (zᵉ ＝ᵉ xᵉ) → (zᵉ ＝ᵉ y),ᵉ
```

hence,ᵉ theirᵉ definitionᵉ isᵉ

```text
  (xᵉ ＝ʲᵉ yᵉ) :=ᵉ Σᵉ (zᵉ : Aᵉ) ((zᵉ ＝ʸᵉ yᵉ) ×ᵉ (zᵉ ＝ʸᵉ x)).ᵉ
```

Theᵉ Yonedaᵉ identityᵉ typesᵉ areᵉ [equivalent](foundation-core.equivalences.mdᵉ) to
theᵉ standardᵉ identityᵉ types,ᵉ butᵉ haveᵉ aᵉ strictlyᵉ associativeᵉ andᵉ unitalᵉ
concatenationᵉ operation.ᵉ Weᵉ canᵉ leverageᵉ thisᵉ andᵉ theᵉ strictnessᵉ propertiesᵉ ofᵉ
theᵉ constructionᵉ ofᵉ theᵉ strictlyᵉ involutiveᵉ identityᵉ typesᵉ to constructᵉ
operationsᵉ onᵉ theᵉ computationalᵉ identityᵉ typesᵉ thatᵉ satisfyᵉ theᵉ strictᵉ algebraicᵉ
lawsᵉ

-ᵉ `(pᵉ ∙ʲᵉ qᵉ) ∙ʲᵉ rᵉ ≐ᵉ pᵉ ∙ʲᵉ (qᵉ ∙ʲᵉ r)`ᵉ
-ᵉ `reflʲᵉ ∙ʲᵉ pᵉ ≐ᵉ p`ᵉ orᵉ `pᵉ ∙ʲᵉ reflʲᵉ ≐ᵉ p`ᵉ
-ᵉ `invʲᵉ (invʲᵉ pᵉ) ≐ᵉ p`ᵉ
-ᵉ `invʲᵉ reflʲᵉ ≐ᵉ reflʲ`.ᵉ

Whileᵉ theᵉ lastᵉ threeᵉ equalitiesᵉ holdᵉ byᵉ theᵉ sameᵉ computationsᵉ asᵉ forᵉ theᵉ
strictlyᵉ involutiveᵉ identityᵉ typesᵉ using theᵉ factᵉ thatᵉ `invʸᵉ reflʸᵉ ≐ᵉ reflʸ`,ᵉ
strictᵉ associativityᵉ reliesᵉ onᵉ theᵉ strictᵉ associativityᵉ ofᵉ theᵉ underlyingᵉ Yonedaᵉ
identityᵉ types.ᵉ Seeᵉ theᵉ fileᵉ aboutᵉ strictlyᵉ involutiveᵉ identityᵉ typesᵉ forᵉ
furtherᵉ detailsᵉ onᵉ computationsᵉ relatedᵉ to theᵉ lastᵉ threeᵉ equalities.ᵉ Inᵉ
additionᵉ to theseᵉ strictᵉ algebraicᵉ laws,ᵉ weᵉ alsoᵉ defineᵉ aᵉ recursionᵉ principleᵉ
forᵉ theᵉ computationalᵉ identityᵉ typesᵉ thatᵉ computesᵉ strictly.ᵉ

**Note.**ᵉ Theᵉ computationalᵉ identityᵉ typesᵉ do _notᵉ_ satisfyᵉ theᵉ strictᵉ lawsᵉ

-ᵉ `reflʲᵉ ∙ʲᵉ pᵉ ≐ᵉ p`ᵉ andᵉ `pᵉ ∙ʲᵉ reflʲᵉ ≐ᵉ p`ᵉ simultaneously,ᵉ
-ᵉ `invʲᵉ pᵉ ∙ʲᵉ pᵉ ≐ᵉ reflʲ`,ᵉ orᵉ
-ᵉ `pᵉ ∙ʲᵉ invʲᵉ pᵉ ≐ᵉ reflʲ`,ᵉ

andᵉ theyᵉ do notᵉ haveᵉ aᵉ strictᵉ computationᵉ propertyᵉ forᵉ theirᵉ inductionᵉ
principle.ᵉ Thisᵉ boilsᵉ downᵉ to theᵉ factᵉ thatᵉ theᵉ Yonedaᵉ identityᵉ typesᵉ do notᵉ
haveᵉ aᵉ strictᵉ computationᵉ propertyᵉ forᵉ theirᵉ inductionᵉ principle,ᵉ whichᵉ isᵉ
explainedᵉ furtherᵉ there.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  computational-Idᵉ : (xᵉ yᵉ : Aᵉ) → UUᵉ lᵉ
  computational-Idᵉ xᵉ yᵉ = Σᵉ Aᵉ (λ zᵉ → (zᵉ ＝ʸᵉ yᵉ) ×ᵉ (zᵉ ＝ʸᵉ xᵉ))

  infix 6 _＝ʲᵉ_
  _＝ʲᵉ_ : Aᵉ → Aᵉ → UUᵉ lᵉ
  (aᵉ ＝ʲᵉ bᵉ) = computational-Idᵉ aᵉ bᵉ

  reflʲᵉ : {xᵉ : Aᵉ} → xᵉ ＝ʲᵉ xᵉ
  reflʲᵉ {xᵉ} = (xᵉ ,ᵉ reflʸᵉ ,ᵉ reflʸᵉ)
```

## Properties

### The computational identity types are equivalent to the Yoneda identity types

Theᵉ computationalᵉ identityᵉ typesᵉ areᵉ equivalentᵉ to theᵉ Yonedaᵉ identityᵉ types,ᵉ
andᵉ similarlyᵉ to theᵉ strictlyᵉ involutiveᵉ identityᵉ types,ᵉ thisᵉ equivalenceᵉ isᵉ aᵉ
strictᵉ [retraction](foundation-core.retractions.mdᵉ) andᵉ preservesᵉ theᵉ
reflexivitiesᵉ strictly.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  computational-eq-yoneda-eqᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ʸᵉ yᵉ → xᵉ ＝ʲᵉ yᵉ
  computational-eq-yoneda-eqᵉ {xᵉ} fᵉ = (xᵉ ,ᵉ fᵉ ,ᵉ reflʸᵉ)

  yoneda-eq-computational-eqᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ʲᵉ yᵉ → xᵉ ＝ʸᵉ yᵉ
  yoneda-eq-computational-eqᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) = invʸᵉ qᵉ ∙ʸᵉ pᵉ

  is-retraction-yoneda-eq-computational-eqᵉ :
    {xᵉ yᵉ : Aᵉ} →
    is-retractionᵉ
      ( computational-eq-yoneda-eqᵉ)
      ( yoneda-eq-computational-eqᵉ {xᵉ} {yᵉ})
  is-retraction-yoneda-eq-computational-eqᵉ fᵉ = reflᵉ

  is-section-yoneda-eq-computational-eqᵉ :
    {xᵉ yᵉ : Aᵉ} →
    is-sectionᵉ
      ( computational-eq-yoneda-eqᵉ)
      ( yoneda-eq-computational-eqᵉ {xᵉ} {yᵉ})
  is-section-yoneda-eq-computational-eqᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) =
    ind-yoneda-Idᵉ
      ( λ _ qᵉ →
        computational-eq-yoneda-eqᵉ (yoneda-eq-computational-eqᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ)) ＝ᵉ
        (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ))
      ( reflᵉ)
      ( qᵉ)

  is-equiv-computational-eq-yoneda-eqᵉ :
    {xᵉ yᵉ : Aᵉ} → is-equivᵉ (computational-eq-yoneda-eqᵉ {xᵉ} {yᵉ})
  is-equiv-computational-eq-yoneda-eqᵉ =
    is-equiv-is-invertibleᵉ
      ( yoneda-eq-computational-eqᵉ)
      ( is-section-yoneda-eq-computational-eqᵉ)
      ( is-retraction-yoneda-eq-computational-eqᵉ)

  is-equiv-yoneda-eq-computational-eqᵉ :
    {xᵉ yᵉ : Aᵉ} → is-equivᵉ (yoneda-eq-computational-eqᵉ {xᵉ} {yᵉ})
  is-equiv-yoneda-eq-computational-eqᵉ =
    is-equiv-is-invertibleᵉ
      ( computational-eq-yoneda-eqᵉ)
      ( is-retraction-yoneda-eq-computational-eqᵉ)
      ( is-section-yoneda-eq-computational-eqᵉ)

  equiv-computational-eq-yoneda-eqᵉ : {xᵉ yᵉ : Aᵉ} → (xᵉ ＝ʸᵉ yᵉ) ≃ᵉ (xᵉ ＝ʲᵉ yᵉ)
  pr1ᵉ equiv-computational-eq-yoneda-eqᵉ = computational-eq-yoneda-eqᵉ
  pr2ᵉ equiv-computational-eq-yoneda-eqᵉ = is-equiv-computational-eq-yoneda-eqᵉ

  equiv-yoneda-eq-computational-eqᵉ : {xᵉ yᵉ : Aᵉ} → (xᵉ ＝ʲᵉ yᵉ) ≃ᵉ (xᵉ ＝ʸᵉ yᵉ)
  pr1ᵉ equiv-yoneda-eq-computational-eqᵉ = yoneda-eq-computational-eqᵉ
  pr2ᵉ equiv-yoneda-eq-computational-eqᵉ = is-equiv-yoneda-eq-computational-eqᵉ
```

Thisᵉ equivalenceᵉ preservesᵉ theᵉ reflexivityᵉ elementsᵉ strictlyᵉ in bothᵉ directions.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  preserves-refl-yoneda-eq-computational-eqᵉ :
    {xᵉ : Aᵉ} →
    yoneda-eq-computational-eqᵉ (reflʲᵉ {xᵉ = xᵉ}) ＝ᵉ reflʸᵉ
  preserves-refl-yoneda-eq-computational-eqᵉ = reflᵉ

  preserves-refl-computational-eq-yoneda-eqᵉ :
    {xᵉ : Aᵉ} →
    computational-eq-yoneda-eqᵉ (reflʸᵉ {xᵉ = xᵉ}) ＝ᵉ reflʲᵉ
  preserves-refl-computational-eq-yoneda-eqᵉ = reflᵉ
```

### The computational identity types are equivalent to the standard identity types

Byᵉ theᵉ compositeᵉ equivalenceᵉ `(xᵉ ＝ᵉ yᵉ) ≃ᵉ (xᵉ ＝ʸᵉ yᵉ) ≃ᵉ (xᵉ ＝ʲᵉ y)`,ᵉ theᵉ
computationalᵉ identityᵉ typesᵉ areᵉ equivalentᵉ to theᵉ standardᵉ identityᵉ types.ᵉ
Sinceᵉ eachᵉ ofᵉ theseᵉ equivalencesᵉ preserveᵉ theᵉ groupoidᵉ structureᵉ weakly,ᵉ soᵉ doesᵉ
theᵉ composite.ᵉ Forᵉ theᵉ sameᵉ reason,ᵉ itᵉ preservesᵉ theᵉ reflexivitiesᵉ strictly.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  computational-eq-eqᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ᵉ yᵉ → xᵉ ＝ʲᵉ yᵉ
  computational-eq-eqᵉ = computational-eq-yoneda-eqᵉ ∘ᵉ yoneda-eq-eqᵉ

  eq-computational-eqᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ʲᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-computational-eqᵉ = eq-yoneda-eqᵉ ∘ᵉ yoneda-eq-computational-eqᵉ

  equiv-computational-eq-eqᵉ : {xᵉ yᵉ : Aᵉ} → (xᵉ ＝ᵉ yᵉ) ≃ᵉ (xᵉ ＝ʲᵉ yᵉ)
  equiv-computational-eq-eqᵉ =
    equiv-computational-eq-yoneda-eqᵉ ∘eᵉ equiv-yoneda-eq-eqᵉ

  equiv-eq-computational-eqᵉ : {xᵉ yᵉ : Aᵉ} → (xᵉ ＝ʲᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ yᵉ)
  equiv-eq-computational-eqᵉ =
    equiv-eq-yoneda-eqᵉ ∘eᵉ equiv-yoneda-eq-computational-eqᵉ

  is-retraction-eq-computational-eqᵉ :
    {xᵉ yᵉ : Aᵉ} → is-retractionᵉ computational-eq-eqᵉ (eq-computational-eqᵉ {xᵉ} {yᵉ})
  is-retraction-eq-computational-eqᵉ pᵉ = left-unit-right-strict-concatᵉ

  is-section-eq-computational-eqᵉ :
    {xᵉ yᵉ : Aᵉ} →
    is-sectionᵉ computational-eq-eqᵉ (eq-computational-eqᵉ {xᵉ} {yᵉ})
  is-section-eq-computational-eqᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) =
    ind-yoneda-Idᵉ
      ( λ _ qᵉ →
        computational-eq-eqᵉ (eq-computational-eqᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ)) ＝ᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ))
      ( eq-pair-eq-fiberᵉ (eq-pairᵉ (is-section-eq-yoneda-eqᵉ pᵉ) reflᵉ))
      ( qᵉ)

  is-equiv-computational-eq-eqᵉ :
    {xᵉ yᵉ : Aᵉ} → is-equivᵉ (computational-eq-eqᵉ {xᵉ} {yᵉ})
  is-equiv-computational-eq-eqᵉ = is-equiv-map-equivᵉ equiv-computational-eq-eqᵉ

  is-equiv-eq-computational-eqᵉ :
    {xᵉ yᵉ : Aᵉ} → is-equivᵉ (eq-computational-eqᵉ {xᵉ} {yᵉ})
  is-equiv-eq-computational-eqᵉ = is-equiv-map-equivᵉ equiv-eq-computational-eqᵉ
```

Thisᵉ equivalenceᵉ preservesᵉ theᵉ reflexivityᵉ elementsᵉ strictlyᵉ in bothᵉ directions.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  preserves-refl-computational-eq-eqᵉ :
    {xᵉ : Aᵉ} → computational-eq-eqᵉ (reflᵉ {xᵉ = xᵉ}) ＝ᵉ reflʲᵉ
  preserves-refl-computational-eq-eqᵉ = reflᵉ

  preserves-refl-eq-computational-eqᵉ :
    {xᵉ : Aᵉ} → eq-computational-eqᵉ (reflʲᵉ {xᵉ = xᵉ}) ＝ᵉ reflᵉ
  preserves-refl-eq-computational-eqᵉ = reflᵉ
```

### Torsoriality of the computational identity types

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ : Aᵉ}
  where

  is-torsorial-computational-Idᵉ : is-torsorialᵉ (computational-Idᵉ xᵉ)
  is-torsorial-computational-Idᵉ =
    is-contr-equivᵉ
      ( Σᵉ Aᵉ (xᵉ ＝ᵉ_))
      ( equiv-totᵉ (λ yᵉ → equiv-eq-computational-eqᵉ {xᵉ = xᵉ} {yᵉ}))
      ( is-torsorial-Idᵉ xᵉ)
```

### The dependent universal property of the computational identity types

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ : Aᵉ}
  where

  dependent-universal-property-identity-system-computational-Idᵉ :
    dependent-universal-property-identity-systemᵉ
      ( computational-Idᵉ xᵉ)
      ( reflʲᵉ)
  dependent-universal-property-identity-system-computational-Idᵉ =
    dependent-universal-property-identity-system-is-torsorialᵉ
      ( reflʲᵉ)
      ( is-torsorial-computational-Idᵉ)
```

### The induction principle for the computational identity types

Theᵉ computationalᵉ identityᵉ typesᵉ satisfyᵉ theᵉ inductionᵉ principleᵉ ofᵉ theᵉ identityᵉ
types.ᵉ Thisᵉ statesᵉ thatᵉ givenᵉ aᵉ baseᵉ pointᵉ `xᵉ : A`ᵉ andᵉ aᵉ familyᵉ ofᵉ typesᵉ overᵉ
theᵉ identityᵉ typesᵉ basedᵉ atᵉ `x`,ᵉ `Bᵉ : (yᵉ : Aᵉ) (pᵉ : xᵉ ＝ʲᵉ yᵉ) → UUᵉ l2`,ᵉ thenᵉ to
constructᵉ aᵉ dependentᵉ functionᵉ `fᵉ : (yᵉ : Aᵉ) (pᵉ : xᵉ ＝ʲᵉ yᵉ) → Bᵉ yᵉ p`ᵉ itᵉ sufficesᵉ
to defineᵉ itᵉ atᵉ `fᵉ xᵉ reflʲ`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ : Aᵉ}
  (Bᵉ : (yᵉ : Aᵉ) (pᵉ : xᵉ ＝ʲᵉ yᵉ) → UUᵉ l2ᵉ)
  where

  ind-computational-Idᵉ :
    (bᵉ : Bᵉ xᵉ reflʲᵉ) {yᵉ : Aᵉ} (pᵉ : xᵉ ＝ʲᵉ yᵉ) → Bᵉ yᵉ pᵉ
  ind-computational-Idᵉ bᵉ {yᵉ} =
    map-inv-is-equivᵉ
      ( dependent-universal-property-identity-system-computational-Idᵉ Bᵉ)
      ( bᵉ)
      ( yᵉ)

  compute-ind-computational-Idᵉ :
    (bᵉ : Bᵉ xᵉ reflʲᵉ) → ind-computational-Idᵉ bᵉ reflʲᵉ ＝ᵉ bᵉ
  compute-ind-computational-Idᵉ =
    is-section-map-inv-is-equivᵉ
      ( dependent-universal-property-identity-system-computational-Idᵉ Bᵉ)

  uniqueness-ind-computational-Idᵉ :
    (bᵉ : (yᵉ : Aᵉ) (pᵉ : xᵉ ＝ʲᵉ yᵉ) → Bᵉ yᵉ pᵉ) →
    (λ yᵉ → ind-computational-Idᵉ (bᵉ xᵉ reflʲᵉ) {yᵉ}) ＝ᵉ bᵉ
  uniqueness-ind-computational-Idᵉ =
    is-retraction-map-inv-is-equivᵉ
      ( dependent-universal-property-identity-system-computational-Idᵉ Bᵉ)
```

### The strict recursion principle for the computational identity types

Usingᵉ theᵉ factᵉ thatᵉ theᵉ recusionᵉ principlesᵉ ofᵉ bothᵉ theᵉ Yonedaᵉ identityᵉ typesᵉ
andᵉ theᵉ strictlyᵉ involutiveᵉ identityᵉ typesᵉ canᵉ beᵉ definedᵉ to computeᵉ strictly,ᵉ
weᵉ obtainᵉ aᵉ strictlyᵉ computingᵉ recursionᵉ principleᵉ forᵉ theᵉ computationalᵉ
identityᵉ typesᵉ asᵉ well.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  rec-computational-Idᵉ :
    (bᵉ : Bᵉ xᵉ) {yᵉ : Aᵉ} → xᵉ ＝ʲᵉ yᵉ → Bᵉ yᵉ
  rec-computational-Idᵉ bᵉ pᵉ = rec-yoneda-Idᵉ bᵉ (yoneda-eq-computational-eqᵉ pᵉ)

  compute-rec-computational-Idᵉ :
    (bᵉ : Bᵉ xᵉ) → rec-computational-Idᵉ bᵉ reflʲᵉ ＝ᵉ bᵉ
  compute-rec-computational-Idᵉ bᵉ = reflᵉ

  uniqueness-rec-computational-Idᵉ :
    (bᵉ : (yᵉ : Aᵉ) → xᵉ ＝ʲᵉ yᵉ → Bᵉ yᵉ) →
    (λ yᵉ → rec-computational-Idᵉ (bᵉ xᵉ reflʲᵉ) {yᵉ}) ＝ᵉ bᵉ
  uniqueness-rec-computational-Idᵉ bᵉ =
    ( invᵉ
      ( uniqueness-ind-computational-Idᵉ
        ( λ yᵉ _ → Bᵉ yᵉ)
        ( λ yᵉ → rec-computational-Idᵉ (bᵉ xᵉ reflʲᵉ)))) ∙ᵉ
    ( uniqueness-ind-computational-Idᵉ (λ yᵉ _ → Bᵉ yᵉ) bᵉ)
```

## Structure

Theᵉ computationalᵉ identityᵉ typesᵉ formᵉ aᵉ groupoidalᵉ structureᵉ onᵉ types.ᵉ Thisᵉ
structureᵉ satisfiesᵉ theᵉ followingᵉ algebraicᵉ lawsᵉ strictlyᵉ

-ᵉ `(pᵉ ∙ʲᵉ qᵉ) ∙ʲᵉ rᵉ ≐ᵉ pᵉ ∙ʲᵉ (qᵉ ∙ʲᵉ r)`ᵉ
-ᵉ `reflʲᵉ ∙ʲᵉ pᵉ ≐ᵉ p`ᵉ orᵉ `pᵉ ∙ʲᵉ reflʲᵉ ≐ᵉ p`ᵉ
-ᵉ `invʲᵉ (invʲᵉ pᵉ) ≐ᵉ p`ᵉ
-ᵉ `invʲᵉ reflʲᵉ ≐ᵉ reflʲ`.ᵉ

### Inverting computational identifications

Theᵉ constructionᵉ andᵉ computationsᵉ areᵉ theᵉ sameᵉ asᵉ forᵉ theᵉ strictlyᵉ involutiveᵉ
identityᵉ types.ᵉ Thus,ᵉ theᵉ inversionᵉ operationᵉ isᵉ definedᵉ byᵉ swappingᵉ theᵉ
positionsᵉ ofᵉ theᵉ twoᵉ Yonedaᵉ identificationsᵉ

```text
  invʲᵉ :=ᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ↦ᵉ (zᵉ ,ᵉ qᵉ ,ᵉ p).ᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  invʲᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ʲᵉ yᵉ → yᵉ ＝ʲᵉ xᵉ
  invʲᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) = (zᵉ ,ᵉ qᵉ ,ᵉ pᵉ)

  compute-inv-refl-computational-Idᵉ :
    {xᵉ : Aᵉ} → invʲᵉ (reflʲᵉ {xᵉ = xᵉ}) ＝ᵉ reflʲᵉ
  compute-inv-refl-computational-Idᵉ = reflᵉ

  inv-inv-computational-Idᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ʲᵉ yᵉ) →
    invʲᵉ (invʲᵉ pᵉ) ＝ᵉ pᵉ
  inv-inv-computational-Idᵉ pᵉ = reflᵉ
```

Theᵉ inversionᵉ operationᵉ onᵉ computationalᵉ identificationsᵉ correspondsᵉ to theᵉ
standardᵉ inversionᵉ operationᵉ onᵉ identificationsᵉ:

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ}
  where

  preserves-inv-computational-eq-eqᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) →
    computational-eq-eqᵉ (invᵉ pᵉ) ＝ᵉ invʲᵉ (computational-eq-eqᵉ pᵉ)
  preserves-inv-computational-eq-eqᵉ reflᵉ = reflᵉ

  preserves-inv-eq-computational-eqᵉ :
    (pᵉ : xᵉ ＝ʲᵉ yᵉ) →
    eq-computational-eqᵉ (invʲᵉ pᵉ) ＝ᵉ invᵉ (eq-computational-eqᵉ pᵉ)
  preserves-inv-eq-computational-eqᵉ (zᵉ ,ᵉ fᵉ ,ᵉ gᵉ) =
    ( apᵉ (gᵉ yᵉ) (left-unit-right-strict-concatᵉ)) ∙ᵉ
    ( distributive-inv-Id-yoneda-Idᵉ gᵉ fᵉ) ∙ᵉ
    ( apᵉ (λ rᵉ → invᵉ (fᵉ xᵉ rᵉ)) (invᵉ left-unit-right-strict-concatᵉ))
```

### The concatenation operations on computational identifications

Thereᵉ isᵉ bothᵉ aᵉ strictlyᵉ leftᵉ unitalᵉ andᵉ aᵉ strictlyᵉ rightᵉ unitalᵉ concatenationᵉ
operation,ᵉ whileᵉ bothᵉ areᵉ strictlyᵉ associative.ᵉ Theᵉ strictᵉ one-sidedᵉ unitalityᵉ
followsᵉ in bothᵉ casesᵉ fromᵉ theᵉ strictᵉ rightᵉ unitalityᵉ ofᵉ theᵉ concatenationᵉ
operationᵉ onᵉ theᵉ Yonedaᵉ identifications,ᵉ followingᵉ theᵉ sameᵉ computationᵉ asᵉ forᵉ
theᵉ strictlyᵉ involutiveᵉ identityᵉ types.ᵉ Forᵉ associativityᵉ onᵉ theᵉ otherᵉ hand,ᵉ weᵉ
mustᵉ useᵉ theᵉ strictᵉ associativityᵉ ofᵉ theᵉ Yonedaᵉ identityᵉ types.ᵉ Weᵉ willᵉ writeᵉ
outᵉ theᵉ explicitᵉ computationᵉ later.ᵉ

**Observation.**ᵉ Sinceᵉ theᵉ concatenationᵉ operationsᵉ areᵉ strictlyᵉ associative,ᵉ
everyᵉ stringᵉ ofᵉ concatenationsᵉ containingᵉ reflexivitiesᵉ willᵉ reduceᵉ asideᵉ fromᵉ
possiblyᵉ whenᵉ theᵉ reflexivityᵉ appearsᵉ allᵉ theᵉ wayᵉ to theᵉ rightᵉ orᵉ leftᵉ in theᵉ
string.ᵉ

#### The strictly left unital concatenation operation

Theᵉ strictlyᵉ leftᵉ unitalᵉ concatenationᵉ operationᵉ isᵉ constructedᵉ theᵉ sameᵉ wayᵉ asᵉ
theᵉ strictlyᵉ leftᵉ unitalᵉ concatenationᵉ operationᵉ forᵉ theᵉ strictlyᵉ involutiveᵉ
identityᵉ typesᵉ

```text
  (wᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ∙ʲᵉ (w'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) :=ᵉ (w'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ ∙ʸᵉ invʸᵉ pᵉ ∙ʸᵉ qᵉ)
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  infixl 15 _∙ʲᵉ_
  _∙ʲᵉ_ : {xᵉ yᵉ zᵉ : Aᵉ} → xᵉ ＝ʲᵉ yᵉ → yᵉ ＝ʲᵉ zᵉ → xᵉ ＝ʲᵉ zᵉ
  (wᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ∙ʲᵉ (w'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) = (w'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ ∙ʸᵉ invʸᵉ pᵉ ∙ʸᵉ qᵉ)

  concat-computational-Idᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ʲᵉ yᵉ → (zᵉ : Aᵉ) → yᵉ ＝ʲᵉ zᵉ → xᵉ ＝ʲᵉ zᵉ
  concat-computational-Idᵉ pᵉ zᵉ qᵉ = pᵉ ∙ʲᵉ qᵉ

  concat-computational-Id'ᵉ : (xᵉ : Aᵉ) {yᵉ zᵉ : Aᵉ} → yᵉ ＝ʲᵉ zᵉ → xᵉ ＝ʲᵉ yᵉ → xᵉ ＝ʲᵉ zᵉ
  concat-computational-Id'ᵉ xᵉ qᵉ pᵉ = pᵉ ∙ʲᵉ qᵉ
```

Theᵉ strictlyᵉ leftᵉ unitalᵉ concatenationᵉ operationᵉ onᵉ computationalᵉ
identificationsᵉ correspondsᵉ to theᵉ strictlyᵉ leftᵉ unitalᵉ concatenationᵉ operationᵉ
onᵉ standardᵉ identifications.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ}
  where

  preserves-concat-computational-eq-eqᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    computational-eq-eqᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ
    computational-eq-eqᵉ pᵉ ∙ʲᵉ computational-eq-eqᵉ qᵉ
  preserves-concat-computational-eq-eqᵉ reflᵉ qᵉ = reflᵉ

  preserves-concat-eq-computational-eqᵉ :
    (pᵉ : xᵉ ＝ʲᵉ yᵉ) (qᵉ : yᵉ ＝ʲᵉ zᵉ) →
    eq-computational-eqᵉ (pᵉ ∙ʲᵉ qᵉ) ＝ᵉ
    eq-computational-eqᵉ pᵉ ∙ᵉ eq-computational-eqᵉ qᵉ
  preserves-concat-eq-computational-eqᵉ (wᵉ ,ᵉ fᵉ ,ᵉ gᵉ) (w'ᵉ ,ᵉ f'ᵉ ,ᵉ g'ᵉ) =
    ( apᵉ (f'ᵉ xᵉ) left-unit-right-strict-concatᵉ) ∙ᵉ
    ( apᵉ
      ( f'ᵉ xᵉ)
      ( ( apᵉ
          ( invᵉ)
          ( commutative-preconcatr-Id-yoneda-Idᵉ
            ( gᵉ)
            ( g'ᵉ w'ᵉ reflᵉ)
            ( invᵉ (fᵉ wᵉ reflᵉ)))) ∙ᵉ
        ( ( distributive-inv-right-strict-concatᵉ
            ( g'ᵉ w'ᵉ reflᵉ)
            ( gᵉ yᵉ (invᵉ (fᵉ wᵉ reflᵉ)))) ∙ᵉ
          ( ( apᵉ
              ( _∙ᵣᵉ invᵉ (g'ᵉ w'ᵉ reflᵉ))
              ( inv-distributive-inv-Id-yoneda-Idᵉ fᵉ gᵉ)) ∙ᵉ
            ( eq-concat-right-strict-concatᵉ
              ( fᵉ xᵉ (invᵉ (gᵉ wᵉ reflᵉ)))
              ( invᵉ (g'ᵉ w'ᵉ reflᵉ)))))) ∙ᵉ
    ( commutative-preconcat-Id-yoneda-Idᵉ f'ᵉ
      ( fᵉ xᵉ (invᵉ (gᵉ wᵉ reflᵉ)))
      ( invᵉ (g'ᵉ w'ᵉ reflᵉ)))) ∙ᵉ
    ( ap-binaryᵉ
      ( _∙ᵉ_)
      ( apᵉ (fᵉ xᵉ) (invᵉ left-unit-right-strict-concatᵉ))
      ( apᵉ (f'ᵉ yᵉ) (invᵉ left-unit-right-strict-concatᵉ)))
```

#### The strictly right unital concatenation operation

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  infixl 15 _∙ᵣʲᵉ_
  _∙ᵣʲᵉ_ : {xᵉ yᵉ zᵉ : Aᵉ} → xᵉ ＝ʲᵉ yᵉ → yᵉ ＝ʲᵉ zᵉ → xᵉ ＝ʲᵉ zᵉ
  (wᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ∙ᵣʲᵉ (w'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) = (wᵉ ,ᵉ pᵉ ∙ʸᵉ invʸᵉ q'ᵉ ∙ʸᵉ p'ᵉ ,ᵉ qᵉ)

  right-strict-concat-computational-Idᵉ :
    {xᵉ yᵉ : Aᵉ} → xᵉ ＝ʲᵉ yᵉ → (zᵉ : Aᵉ) → yᵉ ＝ʲᵉ zᵉ → xᵉ ＝ʲᵉ zᵉ
  right-strict-concat-computational-Idᵉ pᵉ zᵉ qᵉ = pᵉ ∙ᵣʲᵉ qᵉ

  right-strict-concat-computational-Id'ᵉ :
    (xᵉ : Aᵉ) {yᵉ zᵉ : Aᵉ} → yᵉ ＝ʲᵉ zᵉ → xᵉ ＝ʲᵉ yᵉ → xᵉ ＝ʲᵉ zᵉ
  right-strict-concat-computational-Id'ᵉ xᵉ qᵉ pᵉ = pᵉ ∙ᵣʲᵉ qᵉ
```

Theᵉ strictlyᵉ rightᵉ unitalᵉ concatenationᵉ operationᵉ onᵉ computationalᵉ
identificationsᵉ correspondsᵉ to theᵉ strictlyᵉ rightᵉ unitalᵉ concatenationᵉ operationᵉ
onᵉ standardᵉ identifications.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ}
  where

  preserves-right-strict-concat-computational-eq-eqᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    computational-eq-eqᵉ (pᵉ ∙ᵣᵉ qᵉ) ＝ᵉ
    computational-eq-eqᵉ pᵉ ∙ᵣʲᵉ computational-eq-eqᵉ qᵉ
  preserves-right-strict-concat-computational-eq-eqᵉ pᵉ reflᵉ = reflᵉ

  preserves-right-strict-concat-eq-computational-eqᵉ :
    (pᵉ : xᵉ ＝ʲᵉ yᵉ) (qᵉ : yᵉ ＝ʲᵉ zᵉ) →
    eq-computational-eqᵉ (pᵉ ∙ᵣʲᵉ qᵉ) ＝ᵉ
    eq-computational-eqᵉ pᵉ ∙ᵣᵉ eq-computational-eqᵉ qᵉ
  preserves-right-strict-concat-eq-computational-eqᵉ (wᵉ ,ᵉ fᵉ ,ᵉ gᵉ) (w'ᵉ ,ᵉ f'ᵉ ,ᵉ g'ᵉ) =
    ( apᵉ
      ( λ rᵉ → f'ᵉ xᵉ (fᵉ xᵉ rᵉ ∙ᵣᵉ invᵉ (g'ᵉ w'ᵉ reflᵉ)))
      ( left-unit-right-strict-concatᵉ)) ∙ᵉ
    ( commutative-preconcatr-Id-yoneda-Idᵉ
      ( f'ᵉ)
      ( fᵉ xᵉ (invᵉ (gᵉ wᵉ reflᵉ)))
      ( invᵉ (g'ᵉ w'ᵉ reflᵉ))) ∙ᵉ
    ( ap-binaryᵉ
      ( _∙ᵣᵉ_)
      ( apᵉ (fᵉ xᵉ) (invᵉ left-unit-right-strict-concatᵉ))
      ( apᵉ (f'ᵉ yᵉ) (invᵉ left-unit-right-strict-concatᵉ)))
```

### The groupoidal laws for the computational identity types

#### The groupoidal laws for the strictly left unital concatenation operation

Toᵉ seeᵉ thatᵉ `_∙ʲ_`ᵉ isᵉ strictlyᵉ associative,ᵉ weᵉ unfoldᵉ bothᵉ `(Pᵉ ∙ʲᵉ Qᵉ) ∙ʲᵉ R`ᵉ andᵉ
`Pᵉ ∙ʲᵉ (Qᵉ ∙ʲᵉ R)`ᵉ andᵉ observeᵉ thatᵉ itᵉ followsᵉ fromᵉ theᵉ strictᵉ associativityᵉ ofᵉ
`_∙ʸ_`ᵉ:

```text
  (Pᵉ ∙ʲᵉ Qᵉ) ∙ʲᵉ Rᵉ
  ≐ᵉ ((uᵉ ,ᵉ pᵉ ,ᵉ p'ᵉ) ∙ʲᵉ (vᵉ ,ᵉ qᵉ ,ᵉ q'ᵉ)) ∙ʲᵉ (wᵉ ,ᵉ rᵉ ,ᵉ r'ᵉ)
  ≐ᵉ ((vᵉ ,ᵉ qᵉ ,ᵉ (q'ᵉ ∙ʸᵉ invʸᵉ pᵉ) ∙ʸᵉ p'ᵉ)) ∙ʲᵉ (wᵉ ,ᵉ rᵉ ,ᵉ r'ᵉ)
  ≐ᵉ (wᵉ ,ᵉ rᵉ ,ᵉ (r'ᵉ ∙ʸᵉ invʸᵉ qᵉ) ∙ʸᵉ ((q'ᵉ ∙ʸᵉ invʸᵉ pᵉ) ∙ʸᵉ p'ᵉ))

  ≐ᵉ (wᵉ ,ᵉ rᵉ ,ᵉ (((r'ᵉ ∙ʸᵉ invʸᵉ qᵉ) ∙ʸᵉ q'ᵉ) ∙ʸᵉ invʸᵉ pᵉ) ∙ʸᵉ p'ᵉ)
  ≐ᵉ (uᵉ ,ᵉ pᵉ ,ᵉ p'ᵉ) ∙ʲᵉ ((wᵉ ,ᵉ rᵉ ,ᵉ (r'ᵉ ∙ʸᵉ invʸᵉ qᵉ) ∙ʸᵉ q'ᵉ))
  ≐ᵉ (uᵉ ,ᵉ pᵉ ,ᵉ p'ᵉ) ∙ʲᵉ ((vᵉ ,ᵉ qᵉ ,ᵉ q'ᵉ) ∙ʲᵉ (wᵉ ,ᵉ rᵉ ,ᵉ r'ᵉ))
  ≐ᵉ Pᵉ ∙ʲᵉ (Qᵉ ∙ʲᵉ R).ᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
  where

  assoc-concat-computational-Idᵉ :
    (pᵉ : xᵉ ＝ʲᵉ yᵉ) (qᵉ : yᵉ ＝ʲᵉ zᵉ) (rᵉ : zᵉ ＝ʲᵉ wᵉ) →
    (pᵉ ∙ʲᵉ qᵉ) ∙ʲᵉ rᵉ ＝ᵉ pᵉ ∙ʲᵉ (qᵉ ∙ʲᵉ rᵉ)
  assoc-concat-computational-Idᵉ pᵉ qᵉ rᵉ = reflᵉ

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ}
  where

  left-unit-concat-computational-Idᵉ :
    {pᵉ : xᵉ ＝ʲᵉ yᵉ} → reflʲᵉ ∙ʲᵉ pᵉ ＝ᵉ pᵉ
  left-unit-concat-computational-Idᵉ = reflᵉ

  right-unit-concat-computational-Idᵉ :
    {pᵉ : xᵉ ＝ʲᵉ yᵉ} → pᵉ ∙ʲᵉ reflʲᵉ ＝ᵉ pᵉ
  right-unit-concat-computational-Idᵉ {zᵉ ,ᵉ pᵉ ,ᵉ qᵉ} =
    ind-yoneda-Idᵉ
      ( λ _ pᵉ → (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ∙ʲᵉ reflʲᵉ ＝ᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ))
      ( reflᵉ)
      ( pᵉ)

  left-inv-concat-computational-Idᵉ :
    (pᵉ : xᵉ ＝ʲᵉ yᵉ) → invʲᵉ pᵉ ∙ʲᵉ pᵉ ＝ᵉ reflʲᵉ
  left-inv-concat-computational-Idᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) =
    ind-yoneda-Idᵉ
      ( λ _ pᵉ →
        ( invʲᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ∙ʲᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ)) ＝ᵉ
        ( reflʲᵉ))
      ( eq-pair-eq-fiberᵉ (eq-pair-eq-fiberᵉ (right-inv-yoneda-Idᵉ qᵉ)))
      ( pᵉ)

  right-inv-concat-computational-Idᵉ :
    (pᵉ : xᵉ ＝ʲᵉ yᵉ) → pᵉ ∙ʲᵉ invʲᵉ pᵉ ＝ᵉ reflʲᵉ
  right-inv-concat-computational-Idᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) =
    ind-yoneda-Idᵉ
      ( λ _ qᵉ →
        ( (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ∙ʲᵉ invʲᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ)) ＝ᵉ
        ( reflʲᵉ))
      ( eq-pair-eq-fiberᵉ (eq-pair-eq-fiberᵉ (right-inv-yoneda-Idᵉ pᵉ)))
      ( qᵉ)

  distributive-inv-concat-computational-Idᵉ :
    (pᵉ : xᵉ ＝ʲᵉ yᵉ) {zᵉ : Aᵉ} (qᵉ : yᵉ ＝ʲᵉ zᵉ) →
    invʲᵉ (pᵉ ∙ʲᵉ qᵉ) ＝ᵉ
    invʲᵉ qᵉ ∙ʲᵉ invʲᵉ pᵉ
  distributive-inv-concat-computational-Idᵉ pᵉ =
    ind-computational-Idᵉ
      ( λ _ qᵉ →
        invʲᵉ (pᵉ ∙ʲᵉ qᵉ) ＝ᵉ
        invʲᵉ qᵉ ∙ʲᵉ invʲᵉ pᵉ)
      ( apᵉ invʲᵉ (right-unit-concat-computational-Idᵉ))
```

#### The groupoidal laws for the strictly right unital concatenation operation

Associativityᵉ forᵉ theᵉ strictlyᵉ rightᵉ unitalᵉ concatenationᵉ operationᵉ followsᵉ fromᵉ
aᵉ similarᵉ computationᵉ to theᵉ oneᵉ forᵉ theᵉ strictlyᵉ leftᵉ unitalᵉ concatenationᵉ
operation.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  assoc-right-strict-concat-computational-Idᵉ :
    {xᵉ yᵉ zᵉ wᵉ : Aᵉ} (pᵉ : xᵉ ＝ʲᵉ yᵉ) (qᵉ : yᵉ ＝ʲᵉ zᵉ) (rᵉ : zᵉ ＝ʲᵉ wᵉ) →
    (pᵉ ∙ᵣʲᵉ qᵉ) ∙ᵣʲᵉ rᵉ ＝ᵉ pᵉ ∙ᵣʲᵉ (qᵉ ∙ᵣʲᵉ rᵉ)
  assoc-right-strict-concat-computational-Idᵉ pᵉ qᵉ rᵉ = reflᵉ

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ}
  where

  right-unit-right-strict-concat-computational-Idᵉ :
    {pᵉ : xᵉ ＝ʲᵉ yᵉ} → pᵉ ∙ᵣʲᵉ reflʲᵉ ＝ᵉ pᵉ
  right-unit-right-strict-concat-computational-Idᵉ = reflᵉ

  left-unit-right-strict-concat-computational-Idᵉ :
    {pᵉ : xᵉ ＝ʲᵉ yᵉ} → reflʲᵉ ∙ᵣʲᵉ pᵉ ＝ᵉ pᵉ
  left-unit-right-strict-concat-computational-Idᵉ {zᵉ ,ᵉ pᵉ ,ᵉ qᵉ} =
    ind-yoneda-Idᵉ (λ _ qᵉ → reflʲᵉ ∙ᵣʲᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ＝ᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ)) reflᵉ qᵉ

  left-inv-right-strict-concat-computational-Idᵉ :
    (pᵉ : xᵉ ＝ʲᵉ yᵉ) → invʲᵉ pᵉ ∙ᵣʲᵉ pᵉ ＝ᵉ reflʲᵉ
  left-inv-right-strict-concat-computational-Idᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) =
    ind-yoneda-Idᵉ
      ( λ _ pᵉ → invʲᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ∙ᵣʲᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ＝ᵉ reflʲᵉ)
      ( eq-pair-eq-fiberᵉ (eq-pairᵉ (right-inv-yoneda-Idᵉ qᵉ) reflᵉ))
      ( pᵉ)

  right-inv-right-strict-concat-computational-Idᵉ :
    (pᵉ : xᵉ ＝ʲᵉ yᵉ) → pᵉ ∙ᵣʲᵉ invʲᵉ pᵉ ＝ᵉ reflʲᵉ
  right-inv-right-strict-concat-computational-Idᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) =
    ind-yoneda-Idᵉ
      ( λ _ qᵉ → (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ∙ᵣʲᵉ invʲᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ＝ᵉ reflʲᵉ)
      ( eq-pair-eq-fiberᵉ (eq-pairᵉ (right-inv-yoneda-Idᵉ pᵉ) reflᵉ))
      ( qᵉ)

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ}
  where

  distributive-inv-right-strict-concat-computational-Idᵉ :
    (pᵉ : xᵉ ＝ʲᵉ yᵉ) {zᵉ : Aᵉ} (qᵉ : yᵉ ＝ʲᵉ zᵉ) → invʲᵉ (pᵉ ∙ᵣʲᵉ qᵉ) ＝ᵉ invʲᵉ qᵉ ∙ᵣʲᵉ invʲᵉ pᵉ
  distributive-inv-right-strict-concat-computational-Idᵉ pᵉ =
    ind-computational-Idᵉ
      ( λ _ qᵉ → invʲᵉ (pᵉ ∙ᵣʲᵉ qᵉ) ＝ᵉ invʲᵉ qᵉ ∙ᵣʲᵉ invʲᵉ pᵉ)
      ( invᵉ left-unit-right-strict-concat-computational-Idᵉ)
```

## Operations

Weᵉ canᵉ defineᵉ aᵉ rangeᵉ ofᵉ basicᵉ operationsᵉ onᵉ computationalᵉ identificationsᵉ thatᵉ
allᵉ enjoyᵉ strictᵉ computationalᵉ properties.ᵉ

### Action of functions on computational identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  eq-ap-computational-Idᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ʲᵉ yᵉ → fᵉ xᵉ ＝ᵉ fᵉ yᵉ
  eq-ap-computational-Idᵉ = apᵉ fᵉ ∘ᵉ eq-computational-eqᵉ

  ap-computational-Idᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ʲᵉ yᵉ → fᵉ xᵉ ＝ʲᵉ fᵉ yᵉ
  ap-computational-Idᵉ =
    computational-eq-yoneda-eqᵉ ∘ᵉ ap-yoneda-Idᵉ fᵉ ∘ᵉ yoneda-eq-computational-eqᵉ

  compute-ap-refl-computational-Idᵉ :
    {xᵉ : Aᵉ} →
    ap-computational-Idᵉ (reflʲᵉ {xᵉ = xᵉ}) ＝ᵉ reflʲᵉ
  compute-ap-refl-computational-Idᵉ = reflᵉ

module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  compute-ap-id-computational-Idᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ʲᵉ yᵉ) → ap-computational-Idᵉ idᵉ pᵉ ＝ᵉ pᵉ
  compute-ap-id-computational-Idᵉ pᵉ =
    ( apᵉ
      ( computational-eq-yoneda-eqᵉ)
      ( compute-ap-id-yoneda-Idᵉ (yoneda-eq-computational-eqᵉ pᵉ))) ∙ᵉ
    ( is-section-yoneda-eq-computational-eqᵉ pᵉ)
```

### Transport along computational identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  tr-computational-Idᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ʲᵉ yᵉ → Bᵉ xᵉ → Bᵉ yᵉ
  tr-computational-Idᵉ = trᵉ Bᵉ ∘ᵉ eq-computational-eqᵉ

  compute-tr-refl-computational-Idᵉ :
    {xᵉ : Aᵉ} → tr-computational-Idᵉ (reflʲᵉ {xᵉ = xᵉ}) ＝ᵉ idᵉ
  compute-tr-refl-computational-Idᵉ = reflᵉ
```

### Function extensionality with respect to computational identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  htpy-computational-eqᵉ : fᵉ ＝ʲᵉ gᵉ → fᵉ ~ᵉ gᵉ
  htpy-computational-eqᵉ = htpy-eqᵉ ∘ᵉ eq-computational-eqᵉ

  computational-eq-htpyᵉ : fᵉ ~ᵉ gᵉ → fᵉ ＝ʲᵉ gᵉ
  computational-eq-htpyᵉ = computational-eq-eqᵉ ∘ᵉ eq-htpyᵉ

  equiv-htpy-computational-eqᵉ : (fᵉ ＝ʲᵉ gᵉ) ≃ᵉ (fᵉ ~ᵉ gᵉ)
  equiv-htpy-computational-eqᵉ = equiv-funextᵉ ∘eᵉ equiv-eq-computational-eqᵉ

  equiv-computational-eq-htpyᵉ : (fᵉ ~ᵉ gᵉ) ≃ᵉ (fᵉ ＝ʲᵉ gᵉ)
  equiv-computational-eq-htpyᵉ = equiv-computational-eq-eqᵉ ∘eᵉ equiv-eq-htpyᵉ

  funext-computational-Idᵉ : is-equivᵉ htpy-computational-eqᵉ
  funext-computational-Idᵉ = is-equiv-map-equivᵉ equiv-htpy-computational-eqᵉ
```

### Univalence with respect to computational identifications

```agda
module _
  {l1ᵉ : Level} {Aᵉ Bᵉ : UUᵉ l1ᵉ}
  where

  map-computational-eqᵉ : Aᵉ ＝ʲᵉ Bᵉ → Aᵉ → Bᵉ
  map-computational-eqᵉ = map-eqᵉ ∘ᵉ eq-computational-eqᵉ

  equiv-computational-eqᵉ : Aᵉ ＝ʲᵉ Bᵉ → Aᵉ ≃ᵉ Bᵉ
  equiv-computational-eqᵉ = equiv-eqᵉ ∘ᵉ eq-computational-eqᵉ

  computational-eq-equivᵉ : Aᵉ ≃ᵉ Bᵉ → Aᵉ ＝ʲᵉ Bᵉ
  computational-eq-equivᵉ = computational-eq-eqᵉ ∘ᵉ eq-equivᵉ

  equiv-equiv-computational-eqᵉ : (Aᵉ ＝ʲᵉ Bᵉ) ≃ᵉ (Aᵉ ≃ᵉ Bᵉ)
  equiv-equiv-computational-eqᵉ = equiv-univalenceᵉ ∘eᵉ equiv-eq-computational-eqᵉ

  is-equiv-equiv-computational-eqᵉ : is-equivᵉ equiv-computational-eqᵉ
  is-equiv-equiv-computational-eqᵉ =
    is-equiv-map-equivᵉ equiv-equiv-computational-eqᵉ

  equiv-computational-eq-equivᵉ : (Aᵉ ≃ᵉ Bᵉ) ≃ᵉ (Aᵉ ＝ʲᵉ Bᵉ)
  equiv-computational-eq-equivᵉ = equiv-computational-eq-eqᵉ ∘eᵉ equiv-eq-equivᵉ Aᵉ Bᵉ

  is-equiv-computational-eq-equivᵉ : is-equivᵉ computational-eq-equivᵉ
  is-equiv-computational-eq-equivᵉ =
    is-equiv-map-equivᵉ equiv-computational-eq-equivᵉ
```

## See also

-ᵉ [Theᵉ strictlyᵉ involutiveᵉ identityᵉ types](foundation.strictly-involutive-identity-types.mdᵉ)
-ᵉ [Theᵉ Yonedaᵉ identityᵉ types](foundation.yoneda-identity-types.mdᵉ)