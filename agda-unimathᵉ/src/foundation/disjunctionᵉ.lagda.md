# Disjunction

```agda
module foundation.disjunctionᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.decidable-propositionsᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "disjunction"ᵉ Disambiguation="ofᵉ propositions"ᵉ WDID=Q1651704ᵉ WD="logicalᵉ disjunction"ᵉ Agda=disjunction-Propᵉ}}
ofᵉ twoᵉ [propositions](foundation-core.propositions.mdᵉ) `P`ᵉ andᵉ `Q`ᵉ isᵉ theᵉ
propositionᵉ thatᵉ `P`ᵉ holdsᵉ orᵉ `Q`ᵉ holds,ᵉ andᵉ isᵉ definedᵉ asᵉ
[propositionalᵉ truncation](foundation.propositional-truncations.mdᵉ) ofᵉ theᵉ
[coproduct](foundation-core.coproduct-types.mdᵉ) ofᵉ theirᵉ underlyingᵉ typesᵉ

```text
  Pᵉ ∨ᵉ Qᵉ :=ᵉ ║ᵉ Pᵉ +ᵉ Qᵉ ║₋₁ᵉ
```

Theᵉ
{{#conceptᵉ "universalᵉ property"ᵉ Disambiguation="ofᵉ theᵉ disjunction"ᵉ Agda=universal-property-disjunction-Propᵉ}}
ofᵉ theᵉ disjunctionᵉ statesᵉ that,ᵉ forᵉ everyᵉ propositionᵉ `R`,ᵉ theᵉ evaluationᵉ mapᵉ

```text
  evᵉ : ((Pᵉ ∨ᵉ Qᵉ) → Rᵉ) → ((Pᵉ → Rᵉ) ∧ᵉ (Qᵉ → Rᵉ))
```

isᵉ aᵉ [logicalᵉ equivalence](foundation.logical-equivalences.md),ᵉ andᵉ thusᵉ theᵉ
disjunctionᵉ isᵉ theᵉ leastᵉ upperᵉ boundᵉ ofᵉ `P`ᵉ andᵉ `Q`ᵉ in theᵉ
[localeᵉ ofᵉ propositions](foundation.large-locale-of-propositions.mdᵉ): thereᵉ isᵉ aᵉ
pairᵉ ofᵉ logicalᵉ implicationsᵉ `Pᵉ → R`ᵉ andᵉ `Qᵉ → R`,ᵉ ifᵉ andᵉ onlyᵉ ifᵉ `Pᵉ ∨ᵉ Q`ᵉ impliesᵉ
`R`ᵉ

```text
Pᵉ --->ᵉ Pᵉ ∨ᵉ Qᵉ <---ᵉ Qᵉ
  \ᵉ      ∶ᵉ      /ᵉ
    \ᵉ    ∶ᵉ    /ᵉ
      ∨ᵉ  ∨ᵉ  ∨ᵉ
         R.ᵉ
```

## Definitions

### The disjunction of arbitrary types

Givenᵉ arbitraryᵉ typesᵉ `A`ᵉ andᵉ `B`,ᵉ theᵉ truncationᵉ

```text
  ║ᵉ Aᵉ +ᵉ Bᵉ ║₋₁ᵉ
```

satisfiesᵉ theᵉ universalᵉ propertyᵉ ofᵉ

```text
  ║ᵉ Aᵉ ║₋₁ᵉ ∨ᵉ ║ᵉ Bᵉ ║₋₁ᵉ
```

andᵉ isᵉ thusᵉ equivalentᵉ to it.ᵉ Therefore,ᵉ weᵉ mayᵉ reasonablyᵉ callᵉ thisᵉ
constructionᵉ theᵉ
{{#conceptᵉ "disjunction"ᵉ Disambiguation="ofᵉ types"ᵉ Agda=disjunction-type-Propᵉ}}
ofᵉ types.ᵉ Itᵉ isᵉ importantᵉ to keepᵉ in mindᵉ thatᵉ thisᵉ isᵉ notᵉ aᵉ generalizationᵉ ofᵉ
theᵉ conceptᵉ butᵉ ratherᵉ aᵉ conflation,ᵉ andᵉ shouldᵉ beᵉ readᵉ asᵉ theᵉ statementᵉ _`A`ᵉ orᵉ
`B`ᵉ isᵉ (merelyᵉ) [inhabited](foundation.inhabited-types.md)_.ᵉ

Becauseᵉ propositionsᵉ areᵉ aᵉ specialᵉ caseᵉ ofᵉ types,ᵉ andᵉ Agdaᵉ canᵉ generallyᵉ inferᵉ
typesᵉ forᵉ us,ᵉ weᵉ willᵉ continueᵉ to conflateᵉ theᵉ twoᵉ in ourᵉ formalizationsᵉ forᵉ theᵉ
benefitᵉ thatᵉ weᵉ haveᵉ to specifyᵉ theᵉ propositionsᵉ in ourᵉ codeᵉ lessᵉ often.ᵉ Forᵉ
instance,ᵉ evenᵉ thoughᵉ theᵉ introductionᵉ rulesᵉ forᵉ disjunctionᵉ areᵉ phrasedᵉ in
termsᵉ ofᵉ disjunctionᵉ ofᵉ types,ᵉ theyᵉ equallyᵉ applyᵉ to disjunctionᵉ ofᵉ
propositions.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  disjunction-type-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  disjunction-type-Propᵉ = trunc-Propᵉ (Aᵉ +ᵉ Bᵉ)

  disjunction-typeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  disjunction-typeᵉ = type-Propᵉ disjunction-type-Propᵉ

  is-prop-disjunction-typeᵉ : is-propᵉ disjunction-typeᵉ
  is-prop-disjunction-typeᵉ = is-prop-type-Propᵉ disjunction-type-Propᵉ
```

### The disjunction

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ)
  where

  disjunction-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  disjunction-Propᵉ = disjunction-type-Propᵉ (type-Propᵉ Pᵉ) (type-Propᵉ Qᵉ)

  type-disjunction-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-disjunction-Propᵉ = type-Propᵉ disjunction-Propᵉ

  abstract
    is-prop-disjunction-Propᵉ : is-propᵉ type-disjunction-Propᵉ
    is-prop-disjunction-Propᵉ = is-prop-type-Propᵉ disjunction-Propᵉ

  infixr 10 _∨ᵉ_
  _∨ᵉ_ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  _∨ᵉ_ = disjunction-Propᵉ
```

**Notation.**ᵉ Theᵉ symbolᵉ usedᵉ forᵉ theᵉ disjunctionᵉ `_∨_`ᵉ isᵉ theᵉ
[logicalᵉ or](https://codepoints.net/U+2228ᵉ) `∨`ᵉ (agda-inputᵉ: `\vee`ᵉ `\or`),ᵉ andᵉ
notᵉ theᵉ [latinᵉ smallᵉ letterᵉ v](https://codepoints.net/U+0076ᵉ) `v`.ᵉ

### The introduction rules for the disjunction

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  inl-disjunctionᵉ : Aᵉ → disjunction-typeᵉ Aᵉ Bᵉ
  inl-disjunctionᵉ = unit-trunc-Propᵉ ∘ᵉ inlᵉ

  inr-disjunctionᵉ : Bᵉ → disjunction-typeᵉ Aᵉ Bᵉ
  inr-disjunctionᵉ = unit-trunc-Propᵉ ∘ᵉ inrᵉ
```

**Note.**ᵉ Evenᵉ thoughᵉ theᵉ introductionᵉ rulesᵉ areᵉ formalizedᵉ in termsᵉ ofᵉ
disjunctionᵉ ofᵉ types,ᵉ itᵉ equallyᵉ appliesᵉ to disjunctionᵉ ofᵉ propositions.ᵉ Thisᵉ isᵉ
becauseᵉ propositionsᵉ areᵉ aᵉ specialᵉ caseᵉ ofᵉ types.ᵉ Theᵉ benefitᵉ ofᵉ thisᵉ approachᵉ
isᵉ thatᵉ Agdaᵉ canᵉ inferᵉ typesᵉ forᵉ us,ᵉ butᵉ notᵉ generallyᵉ propositions.ᵉ

### The universal property of disjunctions

```agda
ev-disjunctionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} →
  (disjunction-typeᵉ Aᵉ Bᵉ → Cᵉ) → (Aᵉ → Cᵉ) ×ᵉ (Bᵉ → Cᵉ)
pr1ᵉ (ev-disjunctionᵉ hᵉ) = hᵉ ∘ᵉ inl-disjunctionᵉ
pr2ᵉ (ev-disjunctionᵉ hᵉ) = hᵉ ∘ᵉ inr-disjunctionᵉ

universal-property-disjunction-typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → Propᵉ l3ᵉ → UUωᵉ
universal-property-disjunction-typeᵉ Aᵉ Bᵉ Sᵉ =
  {lᵉ : Level} (Rᵉ : Propᵉ lᵉ) →
  (type-Propᵉ Sᵉ → type-Propᵉ Rᵉ) ↔ᵉ ((Aᵉ → type-Propᵉ Rᵉ) ×ᵉ (Bᵉ → type-Propᵉ Rᵉ))

universal-property-disjunction-Propᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} → Propᵉ l1ᵉ → Propᵉ l2ᵉ → Propᵉ l3ᵉ → UUωᵉ
universal-property-disjunction-Propᵉ Pᵉ Qᵉ =
  universal-property-disjunction-typeᵉ (type-Propᵉ Pᵉ) (type-Propᵉ Qᵉ)
```

## Properties

### The disjunction satisfies the universal property of disjunctions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  elim-disjunction'ᵉ :
    {lᵉ : Level} (Rᵉ : Propᵉ lᵉ) →
    (Aᵉ → type-Propᵉ Rᵉ) ×ᵉ (Bᵉ → type-Propᵉ Rᵉ) →
    disjunction-typeᵉ Aᵉ Bᵉ → type-Propᵉ Rᵉ
  elim-disjunction'ᵉ Rᵉ (fᵉ ,ᵉ gᵉ) =
    map-universal-property-trunc-Propᵉ Rᵉ (rec-coproductᵉ fᵉ gᵉ)

  up-disjunctionᵉ :
    universal-property-disjunction-typeᵉ Aᵉ Bᵉ (disjunction-type-Propᵉ Aᵉ Bᵉ)
  up-disjunctionᵉ Rᵉ = ev-disjunctionᵉ ,ᵉ elim-disjunction'ᵉ Rᵉ
```

### The elimination principle of disjunctions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Rᵉ : Propᵉ l3ᵉ)
  where

  elim-disjunctionᵉ :
    (Aᵉ → type-Propᵉ Rᵉ) → (Bᵉ → type-Propᵉ Rᵉ) →
    disjunction-typeᵉ Aᵉ Bᵉ → type-Propᵉ Rᵉ
  elim-disjunctionᵉ fᵉ gᵉ = elim-disjunction'ᵉ Rᵉ (fᵉ ,ᵉ gᵉ)
```

### Propositions that satisfy the universal property of a disjunction are equivalent to the disjunction

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Qᵉ : Propᵉ l3ᵉ)
  (up-Qᵉ : universal-property-disjunction-typeᵉ Aᵉ Bᵉ Qᵉ)
  where

  forward-implication-iff-universal-property-disjunctionᵉ :
    disjunction-typeᵉ Aᵉ Bᵉ → type-Propᵉ Qᵉ
  forward-implication-iff-universal-property-disjunctionᵉ =
    elim-disjunctionᵉ Qᵉ
      ( pr1ᵉ (forward-implicationᵉ (up-Qᵉ Qᵉ) idᵉ))
      ( pr2ᵉ (forward-implicationᵉ (up-Qᵉ Qᵉ) idᵉ))

  backward-implication-iff-universal-property-disjunctionᵉ :
    type-Propᵉ Qᵉ → disjunction-typeᵉ Aᵉ Bᵉ
  backward-implication-iff-universal-property-disjunctionᵉ =
    backward-implicationᵉ
      ( up-Qᵉ (disjunction-type-Propᵉ Aᵉ Bᵉ))
      ( inl-disjunctionᵉ ,ᵉ inr-disjunctionᵉ)

  iff-universal-property-disjunctionᵉ :
    disjunction-typeᵉ Aᵉ Bᵉ ↔ᵉ type-Propᵉ Qᵉ
  iff-universal-property-disjunctionᵉ =
    ( forward-implication-iff-universal-property-disjunctionᵉ ,ᵉ
      backward-implication-iff-universal-property-disjunctionᵉ)
```

### The unit laws for the disjunction

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ)
  where

  map-left-unit-law-disjunction-is-empty-Propᵉ :
    is-emptyᵉ (type-Propᵉ Pᵉ) → type-disjunction-Propᵉ Pᵉ Qᵉ → type-Propᵉ Qᵉ
  map-left-unit-law-disjunction-is-empty-Propᵉ fᵉ =
    elim-disjunctionᵉ Qᵉ (ex-falsoᵉ ∘ᵉ fᵉ) idᵉ

  map-right-unit-law-disjunction-is-empty-Propᵉ :
    is-emptyᵉ (type-Propᵉ Qᵉ) → type-disjunction-Propᵉ Pᵉ Qᵉ → type-Propᵉ Pᵉ
  map-right-unit-law-disjunction-is-empty-Propᵉ fᵉ =
    elim-disjunctionᵉ Pᵉ idᵉ (ex-falsoᵉ ∘ᵉ fᵉ)
```

### The unit laws for the disjunction of types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  map-left-unit-law-disjunction-is-empty-typeᵉ :
    is-emptyᵉ Aᵉ → disjunction-typeᵉ Aᵉ Bᵉ → is-inhabitedᵉ Bᵉ
  map-left-unit-law-disjunction-is-empty-typeᵉ fᵉ =
    elim-disjunctionᵉ (is-inhabited-Propᵉ Bᵉ) (ex-falsoᵉ ∘ᵉ fᵉ) unit-trunc-Propᵉ

  map-right-unit-law-disjunction-is-empty-typeᵉ :
    is-emptyᵉ Bᵉ → disjunction-typeᵉ Aᵉ Bᵉ → is-inhabitedᵉ Aᵉ
  map-right-unit-law-disjunction-is-empty-typeᵉ fᵉ =
    elim-disjunctionᵉ (is-inhabited-Propᵉ Aᵉ) unit-trunc-Propᵉ (ex-falsoᵉ ∘ᵉ fᵉ)
```

### The disjunction of arbitrary types is the disjunction of inhabitedness propositions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  universal-property-disjunction-truncᵉ :
    universal-property-disjunction-typeᵉ Aᵉ Bᵉ
      ( disjunction-Propᵉ (trunc-Propᵉ Aᵉ) (trunc-Propᵉ Bᵉ))
  universal-property-disjunction-truncᵉ Rᵉ =
    ( λ fᵉ →
      ( fᵉ ∘ᵉ inl-disjunctionᵉ ∘ᵉ unit-trunc-Propᵉ ,ᵉ
        fᵉ ∘ᵉ inr-disjunctionᵉ ∘ᵉ unit-trunc-Propᵉ)) ,ᵉ
    ( λ (fᵉ ,ᵉ gᵉ) →
      rec-trunc-Propᵉ Rᵉ
        ( rec-coproductᵉ (rec-trunc-Propᵉ Rᵉ fᵉ) (rec-trunc-Propᵉ Rᵉ gᵉ)))

  iff-compute-disjunction-truncᵉ :
    disjunction-typeᵉ Aᵉ Bᵉ ↔ᵉ type-disjunction-Propᵉ (trunc-Propᵉ Aᵉ) (trunc-Propᵉ Bᵉ)
  iff-compute-disjunction-truncᵉ =
    iff-universal-property-disjunctionᵉ
      ( disjunction-Propᵉ (trunc-Propᵉ Aᵉ) (trunc-Propᵉ Bᵉ))
      ( universal-property-disjunction-truncᵉ)
```

### The disjunction preserves decidability

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-decidable-disjunctionᵉ :
    is-decidableᵉ Aᵉ → is-decidableᵉ Bᵉ → is-decidableᵉ (disjunction-typeᵉ Aᵉ Bᵉ)
  is-decidable-disjunctionᵉ is-decidable-Aᵉ is-decidable-Bᵉ =
    is-decidable-trunc-Prop-is-merely-decidableᵉ
      ( Aᵉ +ᵉ Bᵉ)
      ( unit-trunc-Propᵉ (is-decidable-coproductᵉ is-decidable-Aᵉ is-decidable-Bᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Decidable-Propᵉ l1ᵉ) (Qᵉ : Decidable-Propᵉ l2ᵉ)
  where

  type-disjunction-Decidable-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-disjunction-Decidable-Propᵉ =
    type-disjunction-Propᵉ (prop-Decidable-Propᵉ Pᵉ) (prop-Decidable-Propᵉ Qᵉ)

  is-prop-disjunction-Decidable-Propᵉ :
    is-propᵉ type-disjunction-Decidable-Propᵉ
  is-prop-disjunction-Decidable-Propᵉ =
    is-prop-disjunction-Propᵉ
      ( prop-Decidable-Propᵉ Pᵉ)
      ( prop-Decidable-Propᵉ Qᵉ)

  disjunction-Decidable-Propᵉ : Decidable-Propᵉ (l1ᵉ ⊔ l2ᵉ)
  disjunction-Decidable-Propᵉ =
    ( type-disjunction-Decidable-Propᵉ ,ᵉ
      is-prop-disjunction-Decidable-Propᵉ ,ᵉ
      is-decidable-disjunctionᵉ
        ( is-decidable-Decidable-Propᵉ Pᵉ)
        ( is-decidable-Decidable-Propᵉ Qᵉ))
```

## See also

-ᵉ Theᵉ indexedᵉ counterpartᵉ to disjunctionᵉ isᵉ
  [existentialᵉ quantification](foundation.existential-quantification.md).ᵉ

## Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}

## External links

-ᵉ [disjunction](https://ncatlab.org/nlab/show/disjunctionᵉ) atᵉ $n$Labᵉ
-ᵉ [Logicalᵉ disjunction](https://en.wikipedia.org/wiki/Logical_disjunctionᵉ) atᵉ
  Wikipediaᵉ