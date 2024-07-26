# Conjunction

```agda
module foundation.conjunctionᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universal-property-cartesian-product-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.decidable-propositionsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "conjunction"ᵉ Disambiguation="ofᵉ propositions"ᵉ WDID=Q191081ᵉ WD="logicalᵉ conjunction"ᵉ Agda=conjunction-Propᵉ}}
`Pᵉ ∧ᵉ Q`ᵉ ofᵉ twoᵉ [propositions](foundation-core.propositions.mdᵉ) `P`ᵉ andᵉ `Q`ᵉ isᵉ
theᵉ propositionᵉ thatᵉ bothᵉ `P`ᵉ andᵉ `Q`ᵉ holdᵉ andᵉ isᵉ thusᵉ definedᵉ byᵉ theᵉ
[cartesianᵉ product](foundation-core.cartesian-product-types.mdᵉ) ofᵉ theirᵉ
underlyingᵉ typesᵉ

```text
  Pᵉ ∧ᵉ Qᵉ :=ᵉ Pᵉ ×ᵉ Qᵉ
```

Theᵉ conjunctionᵉ ofᵉ twoᵉ propositionsᵉ satisfiesᵉ theᵉ universalᵉ propertyᵉ ofᵉ theᵉ
[meet](order-theory.greatest-lower-bounds-large-posets.mdᵉ) in theᵉ
[localeᵉ ofᵉ propositions](foundation.large-locale-of-propositions.md).ᵉ Thisᵉ meansᵉ
thatᵉ anyᵉ spanᵉ ofᵉ propositionsᵉ overᵉ `P`ᵉ andᵉ `Q`ᵉ factorᵉ (uniquelyᵉ) throughᵉ theᵉ
conjunctionᵉ

```text
           Rᵉ
        /ᵉ  ∶ᵉ  \ᵉ
      /ᵉ    ∶ᵉ    \ᵉ
    ∨ᵉ      ∨ᵉ      ∨ᵉ
  Pᵉ <---ᵉ Pᵉ ∧ᵉ Qᵉ --->ᵉ Q.ᵉ
```

Inᵉ otherᵉ words,ᵉ weᵉ haveᵉ aᵉ
[logicalᵉ equivalence](foundation.logical-equivalences.mdᵉ)

```text
  (Rᵉ → Pᵉ) ∧ᵉ (Rᵉ → Qᵉ) ↔ᵉ (Rᵉ → Pᵉ ∧ᵉ Qᵉ)
```

forᵉ everyᵉ propositionᵉ `R`.ᵉ Inᵉ fact,ᵉ `R`ᵉ canᵉ beᵉ anyᵉ type.ᵉ

Theᵉ
{{#conceptᵉ "recursionᵉ principle"ᵉ Disambiguation"ofᵉ theᵉ conjunctionᵉ ofᵉ propositions"ᵉ Agda=elimination-principle-conjunction-Propᵉ}}
ofᵉ theᵉ conjunctionᵉ ofᵉ propositionsᵉ statesᵉ thatᵉ to defineᵉ aᵉ functionᵉ `Pᵉ ∧ᵉ Qᵉ → R`ᵉ
intoᵉ aᵉ propositionᵉ `R`,ᵉ orᵉ indeedᵉ anyᵉ type,ᵉ isᵉ equivalentᵉ to definingᵉ aᵉ functionᵉ
`Pᵉ → Qᵉ → R`.ᵉ

## Definitions

### The conjunction

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ)
  where

  conjunction-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  conjunction-Propᵉ = product-Propᵉ Pᵉ Qᵉ

  type-conjunction-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-conjunction-Propᵉ = type-Propᵉ conjunction-Propᵉ

  is-prop-conjunction-Propᵉ :
    is-propᵉ type-conjunction-Propᵉ
  is-prop-conjunction-Propᵉ = is-prop-type-Propᵉ conjunction-Propᵉ

  infixr 15 _∧ᵉ_
  _∧ᵉ_ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  _∧ᵉ_ = conjunction-Propᵉ
```

**Note**ᵉ: Theᵉ symbolᵉ usedᵉ forᵉ theᵉ conjunctionᵉ `_∧_`ᵉ isᵉ theᵉ
[logicalᵉ and](https://codepoints.net/U+2227ᵉ) `∧`ᵉ (agda-inputᵉ: `\wedge`ᵉ orᵉ
`\and`).ᵉ

### The conjunction of decidable propositions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Decidable-Propᵉ l1ᵉ) (Qᵉ : Decidable-Propᵉ l2ᵉ)
  where

  is-decidable-conjunction-Decidable-Propᵉ :
    is-decidableᵉ
      ( type-conjunction-Propᵉ (prop-Decidable-Propᵉ Pᵉ) (prop-Decidable-Propᵉ Qᵉ))
  is-decidable-conjunction-Decidable-Propᵉ =
    is-decidable-productᵉ
      ( is-decidable-Decidable-Propᵉ Pᵉ)
      ( is-decidable-Decidable-Propᵉ Qᵉ)

  conjunction-Decidable-Propᵉ : Decidable-Propᵉ (l1ᵉ ⊔ l2ᵉ)
  conjunction-Decidable-Propᵉ =
    ( type-conjunction-Propᵉ (prop-Decidable-Propᵉ Pᵉ) (prop-Decidable-Propᵉ Qᵉ) ,ᵉ
      is-prop-conjunction-Propᵉ (prop-Decidable-Propᵉ Pᵉ) (prop-Decidable-Propᵉ Qᵉ) ,ᵉ
      is-decidable-conjunction-Decidable-Propᵉ)
```

### The introduction rule and projections for the conjunction of propositions

Whileᵉ weᵉ defineᵉ theᵉ introductionᵉ ruleᵉ andᵉ projectionsᵉ forᵉ theᵉ conjunctionᵉ below,ᵉ
weᵉ adviceᵉ usersᵉ to useᵉ theᵉ standardᵉ pairingᵉ andᵉ projectionᵉ functionsᵉ forᵉ theᵉ
cartesianᵉ productᵉ typesᵉ: `pair`,ᵉ `pr1`ᵉ andᵉ `pr2`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ)
  where

  intro-conjunction-Propᵉ : type-Propᵉ Pᵉ → type-Propᵉ Qᵉ → type-conjunction-Propᵉ Pᵉ Qᵉ
  intro-conjunction-Propᵉ = pairᵉ

  pr1-conjunction-Propᵉ : type-conjunction-Propᵉ Pᵉ Qᵉ → type-Propᵉ Pᵉ
  pr1-conjunction-Propᵉ = pr1ᵉ

  pr2-conjunction-Propᵉ : type-conjunction-Propᵉ Pᵉ Qᵉ → type-Propᵉ Qᵉ
  pr2-conjunction-Propᵉ = pr2ᵉ
```

### The elimination principle of the conjunction

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ)
  where

  ev-conjunction-Propᵉ :
    {lᵉ : Level} (Rᵉ : Propᵉ lᵉ) → type-Propᵉ (((Pᵉ ∧ᵉ Qᵉ) ⇒ᵉ Rᵉ) ⇒ᵉ Pᵉ ⇒ᵉ Qᵉ ⇒ᵉ Rᵉ)
  ev-conjunction-Propᵉ Rᵉ = ev-pairᵉ

  elimination-principle-conjunction-Propᵉ : UUωᵉ
  elimination-principle-conjunction-Propᵉ =
    {lᵉ : Level} (Rᵉ : Propᵉ lᵉ) → has-converseᵉ (ev-conjunction-Propᵉ Rᵉ)
```

## Properties

### The conjunction satisfies the recursion principle of the conjunction

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ)
  where

  elim-conjunction-Propᵉ : elimination-principle-conjunction-Propᵉ Pᵉ Qᵉ
  elim-conjunction-Propᵉ Rᵉ fᵉ (pᵉ ,ᵉ qᵉ) = fᵉ pᵉ qᵉ
```

### The conjunction is the meet in the locale of propositions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ) (Cᵉ : UUᵉ l3ᵉ)
  where

  map-distributive-conjunction-Propᵉ :
    type-conjunction-Propᵉ (function-Propᵉ Cᵉ Pᵉ) (function-Propᵉ Cᵉ Qᵉ) →
    Cᵉ → type-conjunction-Propᵉ Pᵉ Qᵉ
  map-distributive-conjunction-Propᵉ (fᵉ ,ᵉ gᵉ) yᵉ = (fᵉ yᵉ ,ᵉ gᵉ yᵉ)

  map-inv-distributive-conjunction-Propᵉ :
    (Cᵉ → type-conjunction-Propᵉ Pᵉ Qᵉ) →
    type-conjunction-Propᵉ (function-Propᵉ Cᵉ Pᵉ) (function-Propᵉ Cᵉ Qᵉ)
  map-inv-distributive-conjunction-Propᵉ fᵉ = (pr1ᵉ ∘ᵉ fᵉ ,ᵉ pr2ᵉ ∘ᵉ fᵉ)

  is-equiv-map-distributive-conjunction-Propᵉ :
    is-equivᵉ map-distributive-conjunction-Propᵉ
  is-equiv-map-distributive-conjunction-Propᵉ =
    is-equiv-has-converseᵉ
      ( conjunction-Propᵉ (function-Propᵉ Cᵉ Pᵉ) (function-Propᵉ Cᵉ Qᵉ))
      ( function-Propᵉ Cᵉ (conjunction-Propᵉ Pᵉ Qᵉ))
      ( map-inv-distributive-conjunction-Propᵉ)

  distributive-conjunction-Propᵉ :
    type-conjunction-Propᵉ (function-Propᵉ Cᵉ Pᵉ) (function-Propᵉ Cᵉ Qᵉ) ≃ᵉ
    (Cᵉ → type-conjunction-Propᵉ Pᵉ Qᵉ)
  distributive-conjunction-Propᵉ =
    ( map-distributive-conjunction-Propᵉ ,ᵉ
      is-equiv-map-distributive-conjunction-Propᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ) (Rᵉ : Propᵉ l3ᵉ)
  where

  is-greatest-binary-lower-bound-conjunction-Propᵉ :
    type-Propᵉ (((Rᵉ ⇒ᵉ Pᵉ) ∧ᵉ (Rᵉ ⇒ᵉ Qᵉ)) ⇔ᵉ (Rᵉ ⇒ᵉ Pᵉ ∧ᵉ Qᵉ))
  is-greatest-binary-lower-bound-conjunction-Propᵉ =
    ( map-distributive-conjunction-Propᵉ Pᵉ Qᵉ (type-Propᵉ Rᵉ) ,ᵉ
      map-inv-distributive-conjunction-Propᵉ Pᵉ Qᵉ (type-Propᵉ Rᵉ))
```

## See also

-ᵉ Theᵉ indexedᵉ counterpartᵉ to conjunctionᵉ isᵉ
  [universalᵉ quantification](foundation.universal-quantification.md).ᵉ

## Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}

## External links

-ᵉ [logicalᵉ conjunction](https://ncatlab.org/nlab/show/logical+conjunctionᵉ) atᵉ
  $n$Labᵉ
-ᵉ [Logicalᵉ conjunction](https://en.wikipedia.org/wiki/Logical_conjunctionᵉ) atᵉ
  Wikipediaᵉ