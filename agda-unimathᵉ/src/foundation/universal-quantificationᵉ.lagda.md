# Universal quantification

```agda
module foundation.universal-quantificationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.evaluation-functionsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Givenᵉ aᵉ typeᵉ `A`ᵉ andᵉ aᵉ [subtype](foundation-core.subtypes.mdᵉ) `Pᵉ : Aᵉ → Prop`,ᵉ
theᵉ
{{#conceptᵉ "universalᵉ quantification"ᵉ Disambiguation="onᵉ aᵉ subtype"ᵉ WDID=Q126695ᵉ WD="universalᵉ quantification"ᵉ}}

```text
  ∀ᵉ (xᵉ : A),ᵉ (Pᵉ xᵉ)
```

isᵉ theᵉ [proposition](foundation-core.propositions.mdᵉ) thatᵉ thereᵉ existsᵉ aᵉ proofᵉ
ofᵉ `Pᵉ x`ᵉ forᵉ everyᵉ `x`ᵉ in `A`.ᵉ

Theᵉ
{{#conceptᵉ "universalᵉ property"ᵉ Disambiguation="ofᵉ universalᵉ quantification"ᵉ Agda=universal-property-for-allᵉ}}
ofᵉ universalᵉ quantificationᵉ statesᵉ thatᵉ itᵉ isᵉ theᵉ
[greatestᵉ lowerᵉ bound](order-theory.greatest-lower-bounds-large-posets.mdᵉ) onᵉ
theᵉ familyᵉ ofᵉ propositionsᵉ `P`ᵉ in theᵉ
[localeᵉ ofᵉ propositions](foundation.large-locale-of-propositions.md),ᵉ byᵉ whichᵉ
weᵉ meanᵉ thatᵉ forᵉ everyᵉ propositionᵉ `Q`ᵉ weᵉ haveᵉ theᵉ
[logicalᵉ equivalence](foundation.logical-equivalences.mdᵉ)

```text
  (∀ᵉ (aᵉ : A),ᵉ (Rᵉ → Pᵉ aᵉ)) ↔ᵉ (Rᵉ → ∀ᵉ (aᵉ : A),ᵉ (Pᵉ aᵉ))
```

**Notation.**ᵉ Becauseᵉ ofᵉ syntacticᵉ limitationsᵉ ofᵉ theᵉ Agdaᵉ language,ᵉ weᵉ cannotᵉ
useᵉ `∀`ᵉ forᵉ theᵉ universalᵉ quantificationᵉ in formalizations,ᵉ andᵉ insteadᵉ useᵉ
`∀'`.ᵉ

## Definitions

### Universal quantification

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Pᵉ : Aᵉ → Propᵉ l2ᵉ)
  where

  for-all-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  for-all-Propᵉ = Π-Propᵉ Aᵉ Pᵉ

  type-for-all-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-for-all-Propᵉ = type-Propᵉ for-all-Propᵉ

  is-prop-for-all-Propᵉ : is-propᵉ type-for-all-Propᵉ
  is-prop-for-all-Propᵉ = is-prop-type-Propᵉ for-all-Propᵉ

  for-allᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  for-allᵉ = type-for-all-Propᵉ

  ∀'ᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  ∀'ᵉ = for-all-Propᵉ
```

### The universal property of universal quantification

Theᵉ
{{#conceptᵉ "universalᵉ property"ᵉ Disambiguation="ofᵉ universalᵉ quantification"ᵉ Agda=universal-property-for-allᵉ}}
ofᵉ theᵉ universalᵉ quantificationᵉ `∀ᵉ (aᵉ : A),ᵉ (Pᵉ a)`ᵉ statesᵉ thatᵉ forᵉ everyᵉ
propositionᵉ `R`,ᵉ theᵉ canonicalᵉ mapᵉ

```text
  (∀ᵉ (aᵉ : A),ᵉ (Rᵉ → Pᵉ aᵉ)) → (Rᵉ → ∀ᵉ (aᵉ : A),ᵉ (Pᵉ aᵉ))
```

isᵉ aᵉ [logicalᵉ equivalence](foundation.logical-equivalences.md).ᵉ Indeed,ᵉ thisᵉ
holdsᵉ forᵉ anyᵉ typeᵉ `R`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Pᵉ : Aᵉ → Propᵉ l2ᵉ)
  where

  universal-property-for-allᵉ : {l3ᵉ : Level} (Sᵉ : Propᵉ l3ᵉ) → UUωᵉ
  universal-property-for-allᵉ Sᵉ =
    {lᵉ : Level} (Rᵉ : Propᵉ lᵉ) →
    type-Propᵉ ((∀'ᵉ Aᵉ (λ aᵉ → Rᵉ ⇒ᵉ Pᵉ aᵉ)) ⇔ᵉ (Rᵉ ⇒ᵉ Sᵉ))

  ev-for-allᵉ :
    {lᵉ : Level} {Bᵉ : UUᵉ lᵉ} →
    for-allᵉ Aᵉ (λ aᵉ → function-Propᵉ Bᵉ (Pᵉ aᵉ)) → Bᵉ → for-allᵉ Aᵉ Pᵉ
  ev-for-allᵉ fᵉ rᵉ aᵉ = fᵉ aᵉ rᵉ
```

## Properties

### Universal quantification satisfies its universal property

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Pᵉ : Aᵉ → Propᵉ l2ᵉ)
  where

  map-up-for-allᵉ :
    {lᵉ : Level} {Bᵉ : UUᵉ lᵉ} →
    (Bᵉ → for-allᵉ Aᵉ Pᵉ) → for-allᵉ Aᵉ (λ aᵉ → function-Propᵉ Bᵉ (Pᵉ aᵉ))
  map-up-for-allᵉ fᵉ aᵉ rᵉ = fᵉ rᵉ aᵉ

  is-equiv-ev-for-allᵉ :
    {lᵉ : Level} {Bᵉ : UUᵉ lᵉ} → is-equivᵉ (ev-for-allᵉ Aᵉ Pᵉ {Bᵉ = Bᵉ})
  is-equiv-ev-for-allᵉ {Bᵉ = Bᵉ} =
    is-equiv-has-converseᵉ
      ( ∀'ᵉ Aᵉ (λ aᵉ → function-Propᵉ Bᵉ (Pᵉ aᵉ)))
      ( function-Propᵉ Bᵉ (∀'ᵉ Aᵉ Pᵉ))
      ( map-up-for-allᵉ)

  up-for-allᵉ : universal-property-for-allᵉ Aᵉ Pᵉ (∀'ᵉ Aᵉ Pᵉ)
  up-for-allᵉ Rᵉ = (ev-for-allᵉ Aᵉ Pᵉ ,ᵉ map-up-for-allᵉ)
```

## See also

-ᵉ Universalᵉ quantificationᵉ isᵉ theᵉ indexedᵉ counterpartᵉ to
  [conjunction](foundation.conjunction.md).ᵉ

## Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}

## External links

-ᵉ [universalᵉ quantifier](https://ncatlab.org/nlab/show/universal+quantifierᵉ) atᵉ
  $n$Labᵉ
-ᵉ [Universalᵉ quantification](https://en.wikipedia.org/wiki/Universal_quantificationᵉ)
  atᵉ Wikipediaᵉ