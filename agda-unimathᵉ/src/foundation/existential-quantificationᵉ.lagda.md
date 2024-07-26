# Existential quantification

```agda
module foundation.existential-quantificationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunctionᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ [propositions](foundation-core.propositions.mdᵉ) `P`ᵉ overᵉ `A`,ᵉ
theᵉ
{{#conceptᵉ "existentialᵉ quantification"ᵉ Disambiguation="onᵉ aᵉ subtype"ᵉ WDID=Q773483ᵉ WD="existentialᵉ quantification"ᵉ Agda=existsᵉ}}
ofᵉ `P`ᵉ overᵉ `A`ᵉ isᵉ theᵉ propositionᵉ `∃ᵉ Aᵉ P`ᵉ assertingᵉ thatᵉ thereᵉ isᵉ anᵉ elementᵉ
`aᵉ : A`ᵉ suchᵉ thatᵉ `Pᵉ a`ᵉ holds.ᵉ Weᵉ useᵉ theᵉ
[propositionalᵉ truncation](foundation.propositional-truncations.mdᵉ) to defineᵉ
theᵉ existentialᵉ quantification,ᵉ

```text
  ∃ᵉ (xᵉ : A),ᵉ (Pᵉ xᵉ) :=ᵉ ║ᵉ Σᵉ (xᵉ : A),ᵉ (Pᵉ xᵉ) ║₋₁ᵉ
```

becauseᵉ theᵉ Curry-Howardᵉ interpretationᵉ ofᵉ theᵉ existentialᵉ quantificationᵉ asᵉ
`Σᵉ Aᵉ P`ᵉ doesᵉ notᵉ guaranteeᵉ thatᵉ existentialᵉ quantificationsᵉ areᵉ interpretedᵉ asᵉ
propositions.ᵉ

Theᵉ
{{#conceptᵉ "universalᵉ property"ᵉ Disambiguation="ofᵉ existentialᵉ quantification"ᵉ Agda=universal-property-existsᵉ}}
ofᵉ existentialᵉ quantificationᵉ statesᵉ thatᵉ itᵉ isᵉ theᵉ
[leastᵉ upperᵉ bound](order-theory.least-upper-bounds-large-posets.mdᵉ) onᵉ theᵉ
familyᵉ ofᵉ propositionsᵉ `P`ᵉ in theᵉ
[localeᵉ ofᵉ propositions](foundation.large-locale-of-propositions.md),ᵉ byᵉ whichᵉ
weᵉ meanᵉ thatᵉ forᵉ everyᵉ propositionᵉ `Q`ᵉ weᵉ haveᵉ theᵉ
[logicalᵉ equivalence](foundation.logical-equivalences.mdᵉ)

```text
  (∀ᵉ (xᵉ : A),ᵉ (Pᵉ xᵉ ⇒ᵉ Qᵉ)) ⇔ᵉ ((∃ᵉ (xᵉ : A),ᵉ (Pᵉ xᵉ)) ⇒ᵉ Q).ᵉ
```

## Definitions

### Existence of structure

Givenᵉ aᵉ [structure](foundation.structure.mdᵉ) `Bᵉ : Aᵉ → 𝒰`ᵉ onᵉ aᵉ typeᵉ `A`,ᵉ theᵉ
propositionalᵉ truncationᵉ

```text
  ║ᵉ Σᵉ (xᵉ : A),ᵉ (Bᵉ xᵉ) ║₋₁ᵉ
```

satisfiesᵉ theᵉ universalᵉ propertyᵉ ofᵉ theᵉ existentialᵉ quantificationᵉ

```text
  ∃ᵉ (xᵉ : A),ᵉ ║ᵉ Bᵉ xᵉ ║₋₁ᵉ
```

andᵉ isᵉ thusᵉ equivalentᵉ to it.ᵉ Therefore,ᵉ weᵉ mayᵉ reasonablyᵉ callᵉ thisᵉ
constructionᵉ theᵉ
{{#conceptᵉ "existentialᵉ quantification"ᵉ Disambiguation="structure"ᵉ Agda=exists-structure-Propᵉ}}
ofᵉ structure.ᵉ Itᵉ isᵉ importantᵉ to keepᵉ in mindᵉ thatᵉ thisᵉ isᵉ notᵉ aᵉ generalizationᵉ
ofᵉ theᵉ conceptᵉ butᵉ ratherᵉ aᵉ conflation,ᵉ andᵉ shouldᵉ beᵉ readᵉ asᵉ theᵉ statementᵉ _theᵉ
typeᵉ ofᵉ elementsᵉ `xᵉ : A`ᵉ equippedᵉ with `yᵉ : Bᵉ x`ᵉ isᵉ
[inhabited](foundation.inhabited-types.md)_.ᵉ

Existenceᵉ ofᵉ structureᵉ isᵉ aᵉ widelyᵉ occurringᵉ notionᵉ in univalentᵉ mathematics.ᵉ
Forᵉ instance,ᵉ theᵉ conditionᵉ thatᵉ anᵉ elementᵉ `yᵉ : B`ᵉ isᵉ in theᵉ
[image](foundation.images.mdᵉ) ofᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ formulatedᵉ using existenceᵉ
ofᵉ structureᵉ: Theᵉ elementᵉ `y`ᵉ isᵉ in theᵉ imageᵉ ofᵉ `f`ᵉ ifᵉ theᵉ typeᵉ ofᵉ `xᵉ : A`ᵉ
equippedᵉ with anᵉ identificationᵉ `fᵉ xᵉ = y`ᵉ isᵉ inhabited.ᵉ

Becauseᵉ subtypesᵉ areᵉ aᵉ specialᵉ caseᵉ ofᵉ structure,ᵉ andᵉ Agdaᵉ canᵉ generallyᵉ inferᵉ
structuresᵉ forᵉ us,ᵉ weᵉ willᵉ continueᵉ to conflateᵉ theᵉ twoᵉ in ourᵉ formalizationsᵉ
forᵉ theᵉ benefitᵉ thatᵉ weᵉ haveᵉ to specifyᵉ theᵉ subtypeᵉ in ourᵉ codeᵉ lessᵉ often.ᵉ Forᵉ
instance,ᵉ evenᵉ thoughᵉ theᵉ introductionᵉ ruleᵉ forᵉ existentialᵉ quantificationᵉ
`intro-exists`ᵉ isᵉ phrasedᵉ in termsᵉ ofᵉ existentialᵉ quantificationᵉ onᵉ structures,ᵉ
itᵉ equallyᵉ appliesᵉ to existentialᵉ quantificationᵉ onᵉ subtypes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  exists-structure-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  exists-structure-Propᵉ = trunc-Propᵉ (Σᵉ Aᵉ Bᵉ)

  exists-structureᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  exists-structureᵉ = type-Propᵉ exists-structure-Propᵉ

  is-prop-exists-structureᵉ : is-propᵉ exists-structureᵉ
  is-prop-exists-structureᵉ = is-prop-type-Propᵉ exists-structure-Propᵉ
```

### Existential quantification

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Pᵉ : Aᵉ → Propᵉ l2ᵉ)
  where

  exists-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  exists-Propᵉ = exists-structure-Propᵉ Aᵉ (type-Propᵉ ∘ᵉ Pᵉ)

  existsᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  existsᵉ = type-Propᵉ exists-Propᵉ

  abstract
    is-prop-existsᵉ : is-propᵉ existsᵉ
    is-prop-existsᵉ = is-prop-type-Propᵉ exists-Propᵉ

  ∃ᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  ∃ᵉ = exists-Propᵉ
```

### The introduction rule for existential quantification

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  intro-existsᵉ : (aᵉ : Aᵉ) (bᵉ : Bᵉ aᵉ) → exists-structureᵉ Aᵉ Bᵉ
  intro-existsᵉ aᵉ bᵉ = unit-trunc-Propᵉ (aᵉ ,ᵉ bᵉ)
```

**Note.**ᵉ Evenᵉ thoughᵉ theᵉ introductionᵉ ruleᵉ isᵉ formalizedᵉ in termsᵉ ofᵉ
existentialᵉ quantificationᵉ onᵉ structures,ᵉ itᵉ equallyᵉ appliesᵉ to existentialᵉ
quantificationᵉ onᵉ subtypes.ᵉ Thisᵉ isᵉ becauseᵉ subtypesᵉ areᵉ aᵉ specialᵉ caseᵉ ofᵉ
structure.ᵉ Theᵉ benefitᵉ ofᵉ thisᵉ approachᵉ isᵉ thatᵉ Agdaᵉ canᵉ inferᵉ structuresᵉ forᵉ
us,ᵉ butᵉ notᵉ generallyᵉ subtypes.ᵉ

### The universal property of existential quantification

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Sᵉ : Propᵉ l3ᵉ)
  where

  universal-property-exists-structureᵉ : UUωᵉ
  universal-property-exists-structureᵉ =
    {lᵉ : Level} (Qᵉ : Propᵉ lᵉ) →
    (type-Propᵉ Sᵉ → type-Propᵉ Qᵉ) ↔ᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ → type-Propᵉ Qᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Pᵉ : Aᵉ → Propᵉ l2ᵉ) (Sᵉ : Propᵉ l3ᵉ)
  where

  universal-property-existsᵉ : UUωᵉ
  universal-property-existsᵉ =
    universal-property-exists-structureᵉ Aᵉ (type-Propᵉ ∘ᵉ Pᵉ) Sᵉ
```

## Properties

### The elimination rule of existential quantification

Theᵉ
{{#conceptᵉ "universalᵉ property"ᵉ Disambiguation="ofᵉ existentialᵉ quantification"ᵉ}}
ofᵉ existentialᵉ quantificationᵉ statesᵉ `∃ᵉ Aᵉ P`ᵉ isᵉ theᵉ leastᵉ upperᵉ boundᵉ onᵉ theᵉ
predicateᵉ `P`ᵉ in theᵉ localeᵉ ofᵉ propositions.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  ev-intro-existsᵉ :
    {Cᵉ : UUᵉ l3ᵉ} → (exists-structureᵉ Aᵉ Bᵉ → Cᵉ) → (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ
  ev-intro-existsᵉ Hᵉ xᵉ pᵉ = Hᵉ (intro-existsᵉ xᵉ pᵉ)

  elim-existsᵉ :
    (Qᵉ : Propᵉ l3ᵉ) →
    ((xᵉ : Aᵉ) → Bᵉ xᵉ → type-Propᵉ Qᵉ) → (exists-structureᵉ Aᵉ Bᵉ → type-Propᵉ Qᵉ)
  elim-existsᵉ Qᵉ fᵉ = map-universal-property-trunc-Propᵉ Qᵉ (ind-Σᵉ fᵉ)

  abstract
    is-equiv-ev-intro-existsᵉ :
      (Qᵉ : Propᵉ l3ᵉ) → is-equivᵉ (ev-intro-existsᵉ {type-Propᵉ Qᵉ})
    is-equiv-ev-intro-existsᵉ Qᵉ =
      is-equiv-has-converseᵉ
        ( function-Propᵉ (exists-structureᵉ Aᵉ Bᵉ) Qᵉ)
        ( Π-Propᵉ Aᵉ (λ xᵉ → function-Propᵉ (Bᵉ xᵉ) Qᵉ))
        ( elim-existsᵉ Qᵉ)
```

### The existential quantification satisfies the universal property of existential quantification

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  up-existsᵉ :
    universal-property-exists-structureᵉ Aᵉ Bᵉ (exists-structure-Propᵉ Aᵉ Bᵉ)
  up-existsᵉ Qᵉ = (ev-intro-existsᵉ ,ᵉ elim-existsᵉ Qᵉ)
```

### Propositions that satisfy the universal property of a existential quantification are equivalent to the existential quantification

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Qᵉ : Propᵉ l3ᵉ)
  (up-Qᵉ : universal-property-exists-structureᵉ Aᵉ Bᵉ Qᵉ)
  where

  forward-implication-iff-universal-property-existsᵉ :
    exists-structureᵉ Aᵉ Bᵉ → type-Propᵉ Qᵉ
  forward-implication-iff-universal-property-existsᵉ =
    elim-existsᵉ Qᵉ (forward-implicationᵉ (up-Qᵉ Qᵉ) idᵉ)

  backward-implication-iff-universal-property-existsᵉ :
    type-Propᵉ Qᵉ → exists-structureᵉ Aᵉ Bᵉ
  backward-implication-iff-universal-property-existsᵉ =
    backward-implicationᵉ (up-Qᵉ (exists-structure-Propᵉ Aᵉ Bᵉ)) intro-existsᵉ

  iff-universal-property-existsᵉ :
    exists-structureᵉ Aᵉ Bᵉ ↔ᵉ type-Propᵉ Qᵉ
  iff-universal-property-existsᵉ =
    ( forward-implication-iff-universal-property-existsᵉ ,ᵉ
      backward-implication-iff-universal-property-existsᵉ)
```

### Existential quantification of structure is the same as existential quantification over its propositional reflection

Weᵉ proceedᵉ byᵉ showingᵉ thatᵉ theᵉ latterᵉ satisfiesᵉ theᵉ universalᵉ propertyᵉ ofᵉ theᵉ
former.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  universal-property-exists-structure-exists-trunc-Propᵉ :
    universal-property-exists-structureᵉ Aᵉ Bᵉ (exists-Propᵉ Aᵉ (trunc-Propᵉ ∘ᵉ Bᵉ))
  universal-property-exists-structure-exists-trunc-Propᵉ Qᵉ =
    ( λ fᵉ aᵉ bᵉ → fᵉ (unit-trunc-Propᵉ (aᵉ ,ᵉ unit-trunc-Propᵉ bᵉ))) ,ᵉ
    ( λ fᵉ → rec-trunc-Propᵉ Qᵉ (λ (aᵉ ,ᵉ |b|ᵉ) → rec-trunc-Propᵉ Qᵉ (fᵉ aᵉ) |b|ᵉ))

  compute-exists-trunc-Propᵉ : exists-structureᵉ Aᵉ Bᵉ ↔ᵉ existsᵉ Aᵉ (trunc-Propᵉ ∘ᵉ Bᵉ)
  compute-exists-trunc-Propᵉ =
    iff-universal-property-existsᵉ
      ( exists-Propᵉ Aᵉ (trunc-Propᵉ ∘ᵉ Bᵉ))
      ( universal-property-exists-structure-exists-trunc-Propᵉ)
```

### Taking the cartesian product with a proposition distributes over existential quantification of structures

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  map-distributive-product-exists-structureᵉ :
    type-Propᵉ Pᵉ ×ᵉ exists-structureᵉ Aᵉ Bᵉ →
    exists-structureᵉ Aᵉ (λ xᵉ → type-Propᵉ Pᵉ ×ᵉ Bᵉ xᵉ)
  map-distributive-product-exists-structureᵉ (pᵉ ,ᵉ eᵉ) =
    elim-existsᵉ
      ( exists-structure-Propᵉ Aᵉ (λ xᵉ → type-Propᵉ Pᵉ ×ᵉ Bᵉ xᵉ))
      ( λ xᵉ qᵉ → intro-existsᵉ xᵉ (pᵉ ,ᵉ qᵉ))
      ( eᵉ)

  map-inv-distributive-product-exists-structureᵉ :
    exists-structureᵉ Aᵉ (λ xᵉ → type-Propᵉ Pᵉ ×ᵉ Bᵉ xᵉ) →
    type-Propᵉ Pᵉ ×ᵉ exists-structureᵉ Aᵉ Bᵉ
  map-inv-distributive-product-exists-structureᵉ =
    elim-existsᵉ
      ( Pᵉ ∧ᵉ exists-structure-Propᵉ Aᵉ Bᵉ)
      ( λ xᵉ (pᵉ ,ᵉ qᵉ) → (pᵉ ,ᵉ intro-existsᵉ xᵉ qᵉ))

  iff-distributive-product-exists-structureᵉ :
    ( type-Propᵉ Pᵉ ×ᵉ exists-structureᵉ Aᵉ Bᵉ) ↔ᵉ
    ( exists-structureᵉ Aᵉ (λ xᵉ → type-Propᵉ Pᵉ ×ᵉ Bᵉ xᵉ))
  iff-distributive-product-exists-structureᵉ =
    ( map-distributive-product-exists-structureᵉ ,ᵉ
      map-inv-distributive-product-exists-structureᵉ)

  eq-distributive-product-exists-structureᵉ :
    Pᵉ ∧ᵉ exists-structure-Propᵉ Aᵉ Bᵉ ＝ᵉ
    exists-structure-Propᵉ Aᵉ (λ xᵉ → type-Propᵉ Pᵉ ×ᵉ Bᵉ xᵉ)
  eq-distributive-product-exists-structureᵉ =
    eq-iff'ᵉ
      ( Pᵉ ∧ᵉ exists-structure-Propᵉ Aᵉ Bᵉ)
      ( exists-structure-Propᵉ Aᵉ (λ xᵉ → type-Propᵉ Pᵉ ×ᵉ Bᵉ xᵉ))
      ( iff-distributive-product-exists-structureᵉ)
```

### Conjunction distributes over existential quantification

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) {Aᵉ : UUᵉ l2ᵉ} (Qᵉ : Aᵉ → Propᵉ l3ᵉ)
  where

  map-distributive-conjunction-existsᵉ :
    type-Propᵉ (Pᵉ ∧ᵉ (∃ᵉ Aᵉ Qᵉ) ⇒ᵉ ∃ᵉ Aᵉ (λ xᵉ → Pᵉ ∧ᵉ Qᵉ xᵉ))
  map-distributive-conjunction-existsᵉ =
    map-distributive-product-exists-structureᵉ Pᵉ

  map-inv-distributive-conjunction-existsᵉ :
    type-Propᵉ (∃ᵉ Aᵉ (λ xᵉ → Pᵉ ∧ᵉ Qᵉ xᵉ) ⇒ᵉ Pᵉ ∧ᵉ (∃ᵉ Aᵉ Qᵉ))
  map-inv-distributive-conjunction-existsᵉ =
    map-inv-distributive-product-exists-structureᵉ Pᵉ

  iff-distributive-conjunction-existsᵉ :
    type-Propᵉ (Pᵉ ∧ᵉ ∃ᵉ Aᵉ Qᵉ ⇔ᵉ ∃ᵉ Aᵉ (λ xᵉ → Pᵉ ∧ᵉ Qᵉ xᵉ))
  iff-distributive-conjunction-existsᵉ =
    iff-distributive-product-exists-structureᵉ Pᵉ

  eq-distributive-conjunction-existsᵉ :
    Pᵉ ∧ᵉ (∃ᵉ Aᵉ Qᵉ) ＝ᵉ ∃ᵉ Aᵉ (λ xᵉ → Pᵉ ∧ᵉ Qᵉ xᵉ)
  eq-distributive-conjunction-existsᵉ =
    eq-distributive-product-exists-structureᵉ Pᵉ
```

## See also

-ᵉ Existentialᵉ quantificationᵉ isᵉ theᵉ indexedᵉ counterpartᵉ to
  [disjunction](foundation.disjunction.mdᵉ)

## Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}

## External links

-ᵉ [existentialᵉ quantifier](https://ncatlab.org/nlab/show/existential+quantifierᵉ)
  atᵉ $n$Labᵉ