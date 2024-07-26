# Pushouts

```agda
module synthetic-homotopy-theory.pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.constant-type-familiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.transport-along-homotopiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import reflection.erasing-equalityᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-universal-property-pushoutsᵉ
open import synthetic-homotopy-theory.flattening-lemma-pushoutsᵉ
open import synthetic-homotopy-theory.induction-principle-pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Considerᵉ aᵉ spanᵉ `𝒮`ᵉ ofᵉ typesᵉ

```text
      fᵉ     gᵉ
  Aᵉ <---ᵉ Sᵉ --->ᵉ B.ᵉ
```

Aᵉ **pushout**ᵉ ofᵉ `𝒮`ᵉ isᵉ anᵉ initialᵉ typeᵉ `X`ᵉ equippedᵉ with aᵉ
[coconeᵉ structure](synthetic-homotopy-theory.cocones-under-spans.mdᵉ) ofᵉ `𝒮`ᵉ in
`X`.ᵉ Inᵉ otherᵉ words,ᵉ aᵉ pushoutᵉ `X`ᵉ ofᵉ `𝒮`ᵉ comesᵉ equippedᵉ with aᵉ coconeᵉ structureᵉ
`(iᵉ ,ᵉ jᵉ ,ᵉ H)`ᵉ where

```text
        gᵉ
    Sᵉ ----->ᵉ Bᵉ
    |        |
  fᵉ |   Hᵉ    | jᵉ
    ∨ᵉ        ∨ᵉ
    Aᵉ ----->ᵉ X,ᵉ
        iᵉ
```

suchᵉ thatᵉ forᵉ anyᵉ typeᵉ `Y`,ᵉ theᵉ followingᵉ evaluationᵉ mapᵉ isᵉ anᵉ equivalenceᵉ

```text
  (Xᵉ → Yᵉ) → coconeᵉ 𝒮ᵉ Y.ᵉ
```

Thisᵉ conditionᵉ isᵉ theᵉ
[universalᵉ propertyᵉ ofᵉ theᵉ pushout](synthetic-homotopy-theory.universal-property-pushouts.mdᵉ)
ofᵉ `𝒮`.ᵉ

Theᵉ ideaᵉ isᵉ thatᵉ theᵉ pushoutᵉ ofᵉ `𝒮`ᵉ isᵉ theᵉ universalᵉ typeᵉ thatᵉ containsᵉ theᵉ
elementsᵉ ofᵉ theᵉ typesᵉ `A`ᵉ andᵉ `B`ᵉ viaᵉ theᵉ 'inclusions'ᵉ `iᵉ : Aᵉ → X`ᵉ andᵉ
`jᵉ : Bᵉ → X`,ᵉ andᵉ furthermoreᵉ anᵉ identificationᵉ `iᵉ aᵉ ＝ᵉ jᵉ b`ᵉ forᵉ everyᵉ `sᵉ : S`ᵉ
suchᵉ thatᵉ `fᵉ sᵉ ＝ᵉ a`ᵉ andᵉ `gᵉ sᵉ ＝ᵉ b`.ᵉ

Examplesᵉ ofᵉ pushoutsᵉ includeᵉ
[suspensions](synthetic-homotopy-theory.suspensions-of-types.md),ᵉ
[spheres](synthetic-homotopy-theory.spheres.md),ᵉ
[joins](synthetic-homotopy-theory.joins-of-types.md),ᵉ andᵉ theᵉ
[smashᵉ product](synthetic-homotopy-theory.smash-products-of-pointed-types.md).ᵉ

## Postulates

### The standard pushout type

Weᵉ willᵉ assumeᵉ thatᵉ forᵉ anyᵉ spanᵉ

```text
      fᵉ     gᵉ
  Aᵉ <---ᵉ Sᵉ --->ᵉ B,ᵉ
```

where `Sᵉ : UUᵉ l1`,ᵉ `Aᵉ : UUᵉ l2`,ᵉ andᵉ `Bᵉ : UUᵉ l3`ᵉ thereᵉ isᵉ aᵉ pushoutᵉ in
`UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3)`.ᵉ

```agda
postulate
  pushoutᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
    (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)

postulate
  inl-pushoutᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
    (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) → Aᵉ → pushoutᵉ fᵉ gᵉ

postulate
  inr-pushoutᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
    (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) → Bᵉ → pushoutᵉ fᵉ gᵉ

postulate
  glue-pushoutᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
    (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) → inl-pushoutᵉ fᵉ gᵉ ∘ᵉ fᵉ ~ᵉ inr-pushoutᵉ fᵉ gᵉ ∘ᵉ gᵉ

cocone-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) → coconeᵉ fᵉ gᵉ (pushoutᵉ fᵉ gᵉ)
pr1ᵉ (cocone-pushoutᵉ fᵉ gᵉ) = inl-pushoutᵉ fᵉ gᵉ
pr1ᵉ (pr2ᵉ (cocone-pushoutᵉ fᵉ gᵉ)) = inr-pushoutᵉ fᵉ gᵉ
pr2ᵉ (pr2ᵉ (cocone-pushoutᵉ fᵉ gᵉ)) = glue-pushoutᵉ fᵉ gᵉ
```

### The dependent cogap map

Weᵉ postulate theᵉ constituentsᵉ ofᵉ aᵉ sectionᵉ ofᵉ
`dependent-cocone-mapᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ g)`ᵉ upᵉ to homotopyᵉ ofᵉ dependentᵉ
cocones.ᵉ Thisᵉ is,ᵉ assumingᵉ
[functionᵉ extensionality](foundation.function-extensionality.md),ᵉ preciselyᵉ theᵉ
data ofᵉ theᵉ inductionᵉ principleᵉ ofᵉ pushouts.ᵉ Weᵉ writeᵉ outᵉ eachᵉ componentᵉ
separatelyᵉ to accomodateᵉ
[optionalᵉ rewriteᵉ rulesᵉ forᵉ theᵉ standardᵉ pushouts](synthetic-homotopy-theory.rewriting-pushouts.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Pᵉ : pushoutᵉ fᵉ gᵉ → UUᵉ l4ᵉ}
  (cᵉ : dependent-coconeᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) Pᵉ)
  where

  postulate
    dependent-cogapᵉ : (xᵉ : pushoutᵉ fᵉ gᵉ) → Pᵉ xᵉ

  compute-inl-dependent-cogapᵉ :
    (aᵉ : Aᵉ) →
    dependent-cogapᵉ (inl-pushoutᵉ fᵉ gᵉ aᵉ) ＝ᵉ
    horizontal-map-dependent-coconeᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) Pᵉ cᵉ aᵉ
  compute-inl-dependent-cogapᵉ aᵉ = primEraseEqualityᵉ compute-inl-dependent-cogap'ᵉ
    where postulate
      compute-inl-dependent-cogap'ᵉ :
        dependent-cogapᵉ (inl-pushoutᵉ fᵉ gᵉ aᵉ) ＝ᵉ
        horizontal-map-dependent-coconeᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) Pᵉ cᵉ aᵉ

  compute-inr-dependent-cogapᵉ :
    (bᵉ : Bᵉ) →
    dependent-cogapᵉ (inr-pushoutᵉ fᵉ gᵉ bᵉ) ＝ᵉ
    vertical-map-dependent-coconeᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) Pᵉ cᵉ bᵉ
  compute-inr-dependent-cogapᵉ bᵉ = primEraseEqualityᵉ compute-inr-dependent-cogap'ᵉ
    where postulate
      compute-inr-dependent-cogap'ᵉ :
        dependent-cogapᵉ (inr-pushoutᵉ fᵉ gᵉ bᵉ) ＝ᵉ
        vertical-map-dependent-coconeᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) Pᵉ cᵉ bᵉ

  postulate
    compute-glue-dependent-cogapᵉ :
      coherence-htpy-dependent-coconeᵉ fᵉ gᵉ
        ( cocone-pushoutᵉ fᵉ gᵉ)
        ( Pᵉ)
        ( dependent-cocone-mapᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) Pᵉ dependent-cogapᵉ)
        ( cᵉ)
        ( compute-inl-dependent-cogapᵉ)
        ( compute-inr-dependent-cogapᵉ)

  htpy-compute-dependent-cogapᵉ :
    htpy-dependent-coconeᵉ fᵉ gᵉ
      ( cocone-pushoutᵉ fᵉ gᵉ)
      ( Pᵉ)
      ( dependent-cocone-mapᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) Pᵉ dependent-cogapᵉ)
      ( cᵉ)
  htpy-compute-dependent-cogapᵉ =
    ( compute-inl-dependent-cogapᵉ ,ᵉ
      compute-inr-dependent-cogapᵉ ,ᵉ
      compute-glue-dependent-cogapᵉ)
```

## Definitions

### The induction principle of standard pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ)
  where

  is-section-dependent-cogapᵉ :
    {lᵉ : Level} {Pᵉ : pushoutᵉ fᵉ gᵉ → UUᵉ lᵉ} →
    is-sectionᵉ
      ( dependent-cocone-mapᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) Pᵉ)
      ( dependent-cogapᵉ fᵉ gᵉ)
  is-section-dependent-cogapᵉ {Pᵉ = Pᵉ} cᵉ =
    eq-htpy-dependent-coconeᵉ fᵉ gᵉ
      ( cocone-pushoutᵉ fᵉ gᵉ)
      ( Pᵉ)
      ( dependent-cocone-mapᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) Pᵉ (dependent-cogapᵉ fᵉ gᵉ cᵉ))
      ( cᵉ)
      ( htpy-compute-dependent-cogapᵉ fᵉ gᵉ cᵉ)

  induction-principle-pushout'ᵉ :
    induction-principle-pushoutᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ)
  induction-principle-pushout'ᵉ Pᵉ =
    ( dependent-cogapᵉ fᵉ gᵉ ,ᵉ is-section-dependent-cogapᵉ)

  is-retraction-dependent-cogapᵉ :
    {lᵉ : Level} {Pᵉ : pushoutᵉ fᵉ gᵉ → UUᵉ lᵉ} →
    is-retractionᵉ
      ( dependent-cocone-mapᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) Pᵉ)
      ( dependent-cogapᵉ fᵉ gᵉ)
  is-retraction-dependent-cogapᵉ {Pᵉ = Pᵉ} =
    is-retraction-ind-induction-principle-pushoutᵉ fᵉ gᵉ
      ( cocone-pushoutᵉ fᵉ gᵉ)
      ( induction-principle-pushout'ᵉ)
      ( Pᵉ)
```

### The dependent universal property of standard pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ)
  where

  dup-pushoutᵉ :
    dependent-universal-property-pushoutᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ)
  dup-pushoutᵉ =
    dependent-universal-property-pushout-induction-principle-pushoutᵉ fᵉ gᵉ
      ( cocone-pushoutᵉ fᵉ gᵉ)
      ( induction-principle-pushout'ᵉ fᵉ gᵉ)

  equiv-dup-pushoutᵉ :
    {lᵉ : Level} (Pᵉ : pushoutᵉ fᵉ gᵉ → UUᵉ lᵉ) →
    ((xᵉ : pushoutᵉ fᵉ gᵉ) → Pᵉ xᵉ) ≃ᵉ dependent-coconeᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) Pᵉ
  pr1ᵉ (equiv-dup-pushoutᵉ Pᵉ) = dependent-cocone-mapᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) Pᵉ
  pr2ᵉ (equiv-dup-pushoutᵉ Pᵉ) = dup-pushoutᵉ Pᵉ
```

### The cogap map

Weᵉ defineᵉ `cogap`ᵉ andᵉ itsᵉ computationᵉ rulesᵉ in termsᵉ ofᵉ `dependent-cogap`ᵉ to
ensureᵉ theᵉ properᵉ computationalᵉ behaviourᵉ whenᵉ in theᵉ presenceᵉ ofᵉ strictᵉ
computationᵉ lawsᵉ onᵉ theᵉ pointᵉ constructorsᵉ ofᵉ theᵉ standardᵉ pushouts.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ}
  where

  cogapᵉ : coconeᵉ fᵉ gᵉ Xᵉ → pushoutᵉ fᵉ gᵉ → Xᵉ
  cogapᵉ =
    dependent-cogapᵉ fᵉ gᵉ ∘ᵉ
    dependent-cocone-constant-type-family-coconeᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ)

  is-section-cogapᵉ : is-sectionᵉ (cocone-mapᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ)) cogapᵉ
  is-section-cogapᵉ =
    ( ( triangle-dependent-cocone-map-constant-type-family'ᵉ fᵉ gᵉ
        ( cocone-pushoutᵉ fᵉ gᵉ)) ·rᵉ
      ( cogapᵉ)) ∙hᵉ
    ( ( cocone-dependent-cocone-constant-type-familyᵉ fᵉ gᵉ
        ( cocone-pushoutᵉ fᵉ gᵉ)) ·lᵉ
      ( is-section-dependent-cogapᵉ fᵉ gᵉ) ·rᵉ
      ( dependent-cocone-constant-type-family-coconeᵉ fᵉ gᵉ
        ( cocone-pushoutᵉ fᵉ gᵉ))) ∙hᵉ
    ( is-retraction-cocone-dependent-cocone-constant-type-familyᵉ fᵉ gᵉ
      ( cocone-pushoutᵉ fᵉ gᵉ))

  is-retraction-cogapᵉ :
    is-retractionᵉ (cocone-mapᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ)) cogapᵉ
  is-retraction-cogapᵉ =
    ( ( cogapᵉ) ·lᵉ
      ( triangle-dependent-cocone-map-constant-type-family'ᵉ fᵉ gᵉ
        ( cocone-pushoutᵉ fᵉ gᵉ))) ∙hᵉ
    ( ( dependent-cogapᵉ fᵉ gᵉ) ·lᵉ
      ( is-section-cocone-dependent-cocone-constant-type-familyᵉ fᵉ gᵉ
        ( cocone-pushoutᵉ fᵉ gᵉ)) ·rᵉ
      ( dependent-cocone-mapᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) (λ _ → Xᵉ))) ∙hᵉ
    ( is-retraction-dependent-cogapᵉ fᵉ gᵉ)
```

### The universal property of standard pushouts

```agda
up-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) →
  universal-property-pushoutᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ)
up-pushoutᵉ fᵉ gᵉ Pᵉ =
  is-equiv-is-invertibleᵉ
    ( cogapᵉ fᵉ gᵉ)
    ( is-section-cogapᵉ fᵉ gᵉ)
    ( is-retraction-cogapᵉ fᵉ gᵉ)

equiv-up-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (Xᵉ : UUᵉ l4ᵉ) → (pushoutᵉ fᵉ gᵉ → Xᵉ) ≃ᵉ (coconeᵉ fᵉ gᵉ Xᵉ)
pr1ᵉ (equiv-up-pushoutᵉ fᵉ gᵉ Xᵉ) = cocone-mapᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ)
pr2ᵉ (equiv-up-pushoutᵉ fᵉ gᵉ Xᵉ) = up-pushoutᵉ fᵉ gᵉ Xᵉ
```

### Computation with the cogap map

Weᵉ defineᵉ theᵉ computationᵉ witnessesᵉ forᵉ theᵉ cogapᵉ mapᵉ in termsᵉ ofᵉ theᵉ
computationᵉ witnessesᵉ forᵉ theᵉ dependentᵉ cogapᵉ mapᵉ soᵉ thatᵉ whenᵉ
[rewritingᵉ isᵉ enabledᵉ forᵉ pushouts](synthetic-homotopy-theory.rewriting-pushouts.md),ᵉ
theseᵉ witnessesᵉ reduceᵉ to reflexivities.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ)
  { Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  where

  compute-inl-cogapᵉ :
    cogapᵉ fᵉ gᵉ cᵉ ∘ᵉ inl-pushoutᵉ fᵉ gᵉ ~ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ
  compute-inl-cogapᵉ =
    compute-inl-dependent-cogapᵉ fᵉ gᵉ
      ( dependent-cocone-constant-type-family-coconeᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) cᵉ)

  compute-inr-cogapᵉ :
    cogapᵉ fᵉ gᵉ cᵉ ∘ᵉ inr-pushoutᵉ fᵉ gᵉ ~ᵉ vertical-map-coconeᵉ fᵉ gᵉ cᵉ
  compute-inr-cogapᵉ =
    compute-inr-dependent-cogapᵉ fᵉ gᵉ
      ( dependent-cocone-constant-type-family-coconeᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) cᵉ)
```

<!-- TODO: find the right infrastructure to make the proof below just an application of a more general construction. Note that this is very almost `coherence-htpy-cocone-coherence-htpy-dependent-cocone-constant-type-family`, but an `apd-constant-type-family` has snuck its way into the proof Issue#1120 -->

```agda
  abstract
    compute-glue-cogapᵉ :
      statement-coherence-htpy-coconeᵉ fᵉ gᵉ
        ( cocone-mapᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) (cogapᵉ fᵉ gᵉ cᵉ))
        ( cᵉ)
        ( compute-inl-cogapᵉ)
        ( compute-inr-cogapᵉ)
    compute-glue-cogapᵉ xᵉ =
      is-injective-concatᵉ
        ( tr-constant-type-familyᵉ
          ( glue-pushoutᵉ fᵉ gᵉ xᵉ)
          ( cogapᵉ fᵉ gᵉ cᵉ ((inl-pushoutᵉ fᵉ gᵉ ∘ᵉ fᵉ) xᵉ)))
        ( ( invᵉ
            ( assocᵉ
              ( tr-constant-type-familyᵉ
                ( glue-pushoutᵉ fᵉ gᵉ xᵉ)
                ( cogapᵉ fᵉ gᵉ cᵉ
                  ( horizontal-map-coconeᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) (fᵉ xᵉ))))
              ( apᵉ (cogapᵉ fᵉ gᵉ cᵉ) (glue-pushoutᵉ fᵉ gᵉ xᵉ))
              ( compute-inr-cogapᵉ (gᵉ xᵉ)))) ∙ᵉ
          ( apᵉ
            ( _∙ᵉ compute-inr-cogapᵉ (gᵉ xᵉ))
            ( invᵉ
              ( apd-constant-type-familyᵉ (cogapᵉ fᵉ gᵉ cᵉ) (glue-pushoutᵉ fᵉ gᵉ xᵉ)))) ∙ᵉ
          ( compute-glue-dependent-cogapᵉ fᵉ gᵉ
            ( dependent-cocone-constant-type-family-coconeᵉ fᵉ gᵉ
              ( cocone-pushoutᵉ fᵉ gᵉ)
              ( cᵉ))
            ( xᵉ)) ∙ᵉ
          ( invᵉ
            ( assocᵉ
              ( apᵉ
                ( trᵉ (λ _ → Xᵉ) (glue-pushoutᵉ fᵉ gᵉ xᵉ))
                ( compute-inl-cogapᵉ (fᵉ xᵉ)))
              ( tr-constant-type-familyᵉ
                ( glue-pushoutᵉ fᵉ gᵉ xᵉ)
                ( pr1ᵉ cᵉ (fᵉ xᵉ)))
              ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ xᵉ))) ∙ᵉ
          ( apᵉ
            ( _∙ᵉ coherence-square-coconeᵉ fᵉ gᵉ cᵉ xᵉ)
            ( invᵉ
              ( naturality-tr-constant-type-familyᵉ
                ( glue-pushoutᵉ fᵉ gᵉ xᵉ)
                ( compute-inl-cogapᵉ (fᵉ xᵉ))))) ∙ᵉ
            ( assocᵉ
              ( tr-constant-type-familyᵉ
                ( glue-pushoutᵉ fᵉ gᵉ xᵉ)
                ( cogapᵉ fᵉ gᵉ cᵉ (inl-pushoutᵉ fᵉ gᵉ (fᵉ xᵉ))))
              ( compute-inl-cogapᵉ (fᵉ xᵉ))
              ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ xᵉ)))

  htpy-compute-cogapᵉ :
    htpy-coconeᵉ fᵉ gᵉ
      ( cocone-mapᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) (cogapᵉ fᵉ gᵉ cᵉ))
      ( cᵉ)
  htpy-compute-cogapᵉ =
    ( compute-inl-cogapᵉ ,ᵉ compute-inr-cogapᵉ ,ᵉ compute-glue-cogapᵉ)
```

### The small predicate of being a pushout cocone

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  where

  is-pushoutᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-pushoutᵉ = is-equivᵉ (cogapᵉ fᵉ gᵉ cᵉ)

  is-prop-is-pushoutᵉ : is-propᵉ is-pushoutᵉ
  is-prop-is-pushoutᵉ = is-property-is-equivᵉ (cogapᵉ fᵉ gᵉ cᵉ)

  is-pushout-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-pushout-Propᵉ = is-pushoutᵉ
  pr2ᵉ is-pushout-Propᵉ = is-prop-is-pushoutᵉ
```

## Properties

### Pushout cocones satisfy the universal property of the pushout

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  where

  universal-property-pushout-is-pushoutᵉ :
    is-pushoutᵉ fᵉ gᵉ cᵉ → universal-property-pushoutᵉ fᵉ gᵉ cᵉ
  universal-property-pushout-is-pushoutᵉ poᵉ =
    up-pushout-up-pushout-is-equivᵉ fᵉ gᵉ
      ( cocone-pushoutᵉ fᵉ gᵉ)
      ( cᵉ)
      ( cogapᵉ fᵉ gᵉ cᵉ)
      ( htpy-cocone-map-universal-property-pushoutᵉ fᵉ gᵉ
        ( cocone-pushoutᵉ fᵉ gᵉ)
        ( up-pushoutᵉ fᵉ gᵉ)
        ( cᵉ))
      ( poᵉ)
      ( up-pushoutᵉ fᵉ gᵉ)

  is-pushout-universal-property-pushoutᵉ :
    universal-property-pushoutᵉ fᵉ gᵉ cᵉ → is-pushoutᵉ fᵉ gᵉ cᵉ
  is-pushout-universal-property-pushoutᵉ =
    is-equiv-up-pushout-up-pushoutᵉ fᵉ gᵉ
      ( cocone-pushoutᵉ fᵉ gᵉ)
      ( cᵉ)
      ( cogapᵉ fᵉ gᵉ cᵉ)
      ( htpy-cocone-map-universal-property-pushoutᵉ fᵉ gᵉ
        ( cocone-pushoutᵉ fᵉ gᵉ)
        ( up-pushoutᵉ fᵉ gᵉ)
        ( cᵉ))
      ( up-pushoutᵉ fᵉ gᵉ)
```

### Fibers of the cogap map

Weᵉ characterizeᵉ theᵉ [fibers](foundation-core.fibers-of-maps.mdᵉ) ofᵉ theᵉ cogapᵉ mapᵉ
asᵉ aᵉ pushoutᵉ ofᵉ fibers.ᵉ Thisᵉ isᵉ anᵉ applicationᵉ ofᵉ theᵉ
[flatteningᵉ lemmaᵉ forᵉ pushouts](synthetic-homotopy-theory.flattening-lemma-pushouts.md).ᵉ

Givenᵉ aᵉ pushoutᵉ squareᵉ with aᵉ
[cocone](synthetic-homotopy-theory.cocones-under-spans.mdᵉ)

```text
       gᵉ
   Sᵉ ---->ᵉ Bᵉ
   |       | \ᵉ
 fᵉ |    inr|ᵉ  \ᵉ  nᵉ
   ∨ᵉ     ⌜ᵉ ∨ᵉ   \ᵉ
   Aᵉ ---->ᵉ ∙ᵉ    \ᵉ
    \ᵉ inlᵉ   \ᵉ   |
  mᵉ  \ᵉ  cogap\ᵉ  |
      \ᵉ       ∨ᵉ ∨ᵉ
       \----->ᵉ Xᵉ
```

weᵉ have,ᵉ forᵉ everyᵉ `xᵉ : X`,ᵉ aᵉ pushoutᵉ squareᵉ ofᵉ fibersᵉ:

```text
    fiberᵉ (mᵉ ∘ᵉ fᵉ) xᵉ --->ᵉ fiberᵉ (cogapᵉ ∘ᵉ inrᵉ) xᵉ
           |                       |
           |                       |
           ∨ᵉ                     ⌜ᵉ ∨ᵉ
 fiberᵉ (cogapᵉ ∘ᵉ inlᵉ) xᵉ ---->ᵉ fiberᵉ cogapᵉ xᵉ
```

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ)
  { Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) (xᵉ : Xᵉ)
  where

  equiv-fiber-horizontal-map-cocone-cogap-inl-horizontal-spanᵉ :
    fiberᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ fᵉ) xᵉ ≃ᵉ
    fiberᵉ (cogapᵉ fᵉ gᵉ cᵉ ∘ᵉ inl-pushoutᵉ fᵉ gᵉ ∘ᵉ fᵉ) xᵉ
  equiv-fiber-horizontal-map-cocone-cogap-inl-horizontal-spanᵉ =
    equiv-totᵉ (λ sᵉ → equiv-concatᵉ (compute-inl-cogapᵉ fᵉ gᵉ cᵉ (fᵉ sᵉ)) xᵉ)

  equiv-fiber-horizontal-map-cocone-cogap-inlᵉ :
    fiberᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ) xᵉ ≃ᵉ
    fiberᵉ (cogapᵉ fᵉ gᵉ cᵉ ∘ᵉ inl-pushoutᵉ fᵉ gᵉ) xᵉ
  equiv-fiber-horizontal-map-cocone-cogap-inlᵉ =
    equiv-totᵉ (λ aᵉ → equiv-concatᵉ (compute-inl-cogapᵉ fᵉ gᵉ cᵉ aᵉ) xᵉ)

  equiv-fiber-vertical-map-cocone-cogap-inrᵉ :
    fiberᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) xᵉ ≃ᵉ
    fiberᵉ (cogapᵉ fᵉ gᵉ cᵉ ∘ᵉ inr-pushoutᵉ fᵉ gᵉ) xᵉ
  equiv-fiber-vertical-map-cocone-cogap-inrᵉ =
    equiv-totᵉ (λ bᵉ → equiv-concatᵉ (compute-inr-cogapᵉ fᵉ gᵉ cᵉ bᵉ) xᵉ)

  horizontal-map-span-cogap-fiberᵉ :
    fiberᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ fᵉ) xᵉ →
    fiberᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ) xᵉ
  horizontal-map-span-cogap-fiberᵉ =
    map-Σ-map-baseᵉ fᵉ (λ aᵉ → horizontal-map-coconeᵉ fᵉ gᵉ cᵉ aᵉ ＝ᵉ xᵉ)
```

Sinceᵉ ourᵉ pushoutᵉ squareᵉ ofᵉ fibersᵉ hasᵉ `fiberᵉ (mᵉ ∘ᵉ fᵉ) x`ᵉ asᵉ itsᵉ top-leftᵉ cornerᵉ
andᵉ notᵉ `fiberᵉ (nᵉ ∘ᵉ gᵉ) x`,ᵉ thingsᵉ areᵉ "left-biased".ᵉ Forᵉ thisᵉ reason,ᵉ theᵉ
followingᵉ mapᵉ isᵉ constructedᵉ asᵉ aᵉ compositionᵉ whichᵉ makesᵉ aᵉ laterᵉ coherenceᵉ
squareᵉ commuteᵉ (almostᵉ) trivially.ᵉ

```agda
  vertical-map-span-cogap-fiberᵉ :
    fiberᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ fᵉ) xᵉ →
    fiberᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) xᵉ
  vertical-map-span-cogap-fiberᵉ =
    ( map-inv-equivᵉ equiv-fiber-vertical-map-cocone-cogap-inrᵉ) ∘ᵉ
    ( horizontal-map-span-flattening-pushoutᵉ
      ( λ yᵉ → (cogapᵉ fᵉ gᵉ cᵉ yᵉ) ＝ᵉ xᵉ) fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ)) ∘ᵉ
    ( map-equivᵉ equiv-fiber-horizontal-map-cocone-cogap-inl-horizontal-spanᵉ)

  statement-universal-property-pushout-cogap-fiberᵉ : UUωᵉ
  statement-universal-property-pushout-cogap-fiberᵉ =
    { lᵉ : Level} →
    Σᵉ ( coconeᵉ
        ( horizontal-map-span-cogap-fiberᵉ)
        ( vertical-map-span-cogap-fiberᵉ)
        ( fiberᵉ (cogapᵉ fᵉ gᵉ cᵉ) xᵉ))
      ( universal-property-pushout-Levelᵉ lᵉ
        ( horizontal-map-span-cogap-fiberᵉ)
        ( vertical-map-span-cogap-fiberᵉ))

  universal-property-pushout-cogap-fiberᵉ :
    statement-universal-property-pushout-cogap-fiberᵉ
  universal-property-pushout-cogap-fiberᵉ =
    universal-property-pushout-extension-by-equivalencesᵉ
      ( vertical-map-span-flattening-pushoutᵉ
        ( λ yᵉ → cogapᵉ fᵉ gᵉ cᵉ yᵉ ＝ᵉ xᵉ)
        ( fᵉ)
        ( gᵉ)
        ( cocone-pushoutᵉ fᵉ gᵉ))
      ( horizontal-map-span-flattening-pushoutᵉ
        ( λ yᵉ → cogapᵉ fᵉ gᵉ cᵉ yᵉ ＝ᵉ xᵉ)
        ( fᵉ)
        ( gᵉ)
        ( cocone-pushoutᵉ fᵉ gᵉ))
      ( horizontal-map-span-cogap-fiberᵉ)
      ( vertical-map-span-cogap-fiberᵉ)
      ( map-equivᵉ equiv-fiber-horizontal-map-cocone-cogap-inlᵉ)
      ( map-equivᵉ equiv-fiber-vertical-map-cocone-cogap-inrᵉ)
      ( map-equivᵉ equiv-fiber-horizontal-map-cocone-cogap-inl-horizontal-spanᵉ)
      ( cocone-flattening-pushoutᵉ
        ( λ yᵉ → cogapᵉ fᵉ gᵉ cᵉ yᵉ ＝ᵉ xᵉ)
        ( fᵉ)
        ( gᵉ)
        ( cocone-pushoutᵉ fᵉ gᵉ))
      ( flattening-lemma-pushoutᵉ
        ( λ yᵉ → cogapᵉ fᵉ gᵉ cᵉ yᵉ ＝ᵉ xᵉ)
        ( fᵉ)
        ( gᵉ)
        ( cocone-pushoutᵉ fᵉ gᵉ)
        ( up-pushoutᵉ fᵉ gᵉ))
      ( refl-htpyᵉ)
      ( λ _ →
        invᵉ
          ( is-section-map-inv-equivᵉ
            ( equiv-fiber-vertical-map-cocone-cogap-inrᵉ)
            ( _)))
      ( is-equiv-map-equivᵉ equiv-fiber-horizontal-map-cocone-cogap-inlᵉ)
      ( is-equiv-map-equivᵉ equiv-fiber-vertical-map-cocone-cogap-inrᵉ)
      ( is-equiv-map-equivᵉ
        ( equiv-fiber-horizontal-map-cocone-cogap-inl-horizontal-spanᵉ))
```

Weᵉ record theᵉ followingᵉ auxiliaryᵉ lemmaᵉ whichᵉ saysᵉ thatᵉ ifᵉ weᵉ haveᵉ typesᵉ `T`,ᵉ
`F`ᵉ andᵉ `G`ᵉ suchᵉ thatᵉ `Tᵉ ≃ᵉ fiberᵉ (mᵉ ∘ᵉ fᵉ) x`,ᵉ `Fᵉ ≃ᵉ fiberᵉ (cogapᵉ ∘ᵉ inlᵉ) x`ᵉ andᵉ
`Gᵉ ≃ᵉ fiberᵉ (cogapᵉ ∘ᵉ inrᵉ) x`,ᵉ togetherᵉ with suitableᵉ mapsᵉ `uᵉ : Tᵉ → F`ᵉ andᵉ
`vᵉ : Tᵉ → G`,ᵉ thenᵉ weᵉ getᵉ aᵉ pushoutᵉ squareᵉ:

```text
          vᵉ
   Tᵉ ---------->ᵉ Gᵉ
   |             |
 uᵉ |             |
   ∨ᵉ           ⌜ᵉ ∨ᵉ
   Fᵉ ---->ᵉ fiberᵉ cogapᵉ xᵉ
```

Thus,ᵉ thisᵉ lemmaᵉ isᵉ usefulᵉ in caseᵉ weᵉ haveᵉ convenientᵉ descriptionsᵉ ofᵉ theᵉ
fibers.ᵉ

```agda
  module _
    { l5ᵉ l6ᵉ l7ᵉ : Level} (Tᵉ : UUᵉ l5ᵉ) (Fᵉ : UUᵉ l6ᵉ) (Gᵉ : UUᵉ l7ᵉ)
    ( iᵉ : Fᵉ ≃ᵉ fiberᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ) xᵉ)
    ( jᵉ : Gᵉ ≃ᵉ fiberᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) xᵉ)
    ( kᵉ : Tᵉ ≃ᵉ fiberᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ fᵉ) xᵉ)
    ( uᵉ : Tᵉ → Fᵉ)
    ( vᵉ : Tᵉ → Gᵉ)
    ( coh-lᵉ :
      coherence-square-mapsᵉ
        ( map-equivᵉ kᵉ)
        ( uᵉ)
        ( horizontal-map-span-cogap-fiberᵉ)
        ( map-equivᵉ iᵉ))
    ( coh-rᵉ :
      coherence-square-mapsᵉ
        ( vᵉ)
        ( map-equivᵉ kᵉ)
        ( map-equivᵉ jᵉ)
        ( vertical-map-span-cogap-fiberᵉ))
    where

    universal-property-pushout-cogap-fiber-up-to-equivᵉ :
      { lᵉ : Level} →
      ( Σᵉ ( coconeᵉ uᵉ vᵉ (fiberᵉ (cogapᵉ fᵉ gᵉ cᵉ) xᵉ))
          ( λ cᵉ → universal-property-pushout-Levelᵉ lᵉ uᵉ vᵉ cᵉ))
    universal-property-pushout-cogap-fiber-up-to-equivᵉ {lᵉ} =
      universal-property-pushout-extension-by-equivalencesᵉ
        ( horizontal-map-span-cogap-fiberᵉ)
        ( vertical-map-span-cogap-fiberᵉ)
        ( uᵉ)
        ( vᵉ)
        ( map-equivᵉ iᵉ)
        ( map-equivᵉ jᵉ)
        ( map-equivᵉ kᵉ)
        ( pr1ᵉ ( universal-property-pushout-cogap-fiberᵉ {lᵉ}))
        ( pr2ᵉ universal-property-pushout-cogap-fiberᵉ)
        ( coh-lᵉ)
        ( coh-rᵉ)
        ( is-equiv-map-equivᵉ iᵉ)
        ( is-equiv-map-equivᵉ jᵉ)
        ( is-equiv-map-equivᵉ kᵉ)
```

### Swapping a pushout cocone yields another pushout cocone

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (Xᵉ : UUᵉ l4ᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  where

  universal-property-pushout-swap-cocone-universal-property-pushoutᵉ :
    universal-property-pushoutᵉ fᵉ gᵉ cᵉ →
    universal-property-pushoutᵉ gᵉ fᵉ (swap-coconeᵉ fᵉ gᵉ Xᵉ cᵉ)
  universal-property-pushout-swap-cocone-universal-property-pushoutᵉ upᵉ Yᵉ =
    is-equiv-equiv'ᵉ
      ( id-equivᵉ)
      ( equiv-swap-coconeᵉ fᵉ gᵉ Yᵉ)
      ( λ hᵉ →
        eq-htpy-coconeᵉ gᵉ fᵉ
          ( swap-coconeᵉ fᵉ gᵉ Yᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ hᵉ))
          ( cocone-mapᵉ gᵉ fᵉ (swap-coconeᵉ fᵉ gᵉ Xᵉ cᵉ) hᵉ)
          ( ( refl-htpyᵉ) ,ᵉ
            ( refl-htpyᵉ) ,ᵉ
            ( λ sᵉ →
              right-unitᵉ ∙ᵉ invᵉ (ap-invᵉ hᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)))))
      ( upᵉ Yᵉ)

  is-pushout-swap-cocone-is-pushoutᵉ :
    is-pushoutᵉ fᵉ gᵉ cᵉ → is-pushoutᵉ gᵉ fᵉ (swap-coconeᵉ fᵉ gᵉ Xᵉ cᵉ)
  is-pushout-swap-cocone-is-pushoutᵉ poᵉ =
    is-pushout-universal-property-pushoutᵉ gᵉ fᵉ
      ( swap-coconeᵉ fᵉ gᵉ Xᵉ cᵉ)
      ( universal-property-pushout-swap-cocone-universal-property-pushoutᵉ
        ( universal-property-pushout-is-pushoutᵉ fᵉ gᵉ cᵉ poᵉ))
```