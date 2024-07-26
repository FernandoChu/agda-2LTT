# Propositions

```agda
module foundation.propositionsᵉ where

open import foundation-core.propositionsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Properties

### Propositions are `k+1`-truncated for any `k`

```agda
abstract
  is-trunc-is-propᵉ :
    {lᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ lᵉ} → is-propᵉ Aᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ
  is-trunc-is-propᵉ kᵉ is-prop-Aᵉ xᵉ yᵉ = is-trunc-is-contrᵉ kᵉ (is-prop-Aᵉ xᵉ yᵉ)

truncated-type-Propᵉ : {lᵉ : Level} (kᵉ : 𝕋ᵉ) → Propᵉ lᵉ → Truncated-Typeᵉ lᵉ (succ-𝕋ᵉ kᵉ)
pr1ᵉ (truncated-type-Propᵉ kᵉ Pᵉ) = type-Propᵉ Pᵉ
pr2ᵉ (truncated-type-Propᵉ kᵉ Pᵉ) = is-trunc-is-propᵉ kᵉ (is-prop-type-Propᵉ Pᵉ)
```

### Propositions are closed under retracts

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : UUᵉ l2ᵉ)
  where

  is-prop-retract-ofᵉ : Aᵉ retract-ofᵉ Bᵉ → is-propᵉ Bᵉ → is-propᵉ Aᵉ
  is-prop-retract-ofᵉ = is-trunc-retract-ofᵉ
```

### If a type embeds into a proposition, then it is a proposition

```agda
abstract
  is-prop-is-embᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-embᵉ fᵉ → is-propᵉ Bᵉ → is-propᵉ Aᵉ
  is-prop-is-embᵉ = is-trunc-is-embᵉ neg-two-𝕋ᵉ

abstract
  is-prop-embᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ ↪ᵉ Bᵉ) → is-propᵉ Bᵉ → is-propᵉ Aᵉ
  is-prop-embᵉ = is-trunc-embᵉ neg-two-𝕋ᵉ
```

### Two equivalent types are equivalently propositions

```agda
equiv-is-prop-equivᵉ : {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  Aᵉ ≃ᵉ Bᵉ → is-propᵉ Aᵉ ≃ᵉ is-propᵉ Bᵉ
equiv-is-prop-equivᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} eᵉ =
  equiv-iff-is-propᵉ
    ( is-prop-is-propᵉ Aᵉ)
    ( is-prop-is-propᵉ Bᵉ)
    ( is-prop-equiv'ᵉ eᵉ)
    ( is-prop-equivᵉ eᵉ)
```

## See also

### Operations on propositions

Thereᵉ isᵉ aᵉ wideᵉ rangeᵉ ofᵉ operationsᵉ onᵉ propositionsᵉ dueᵉ to theᵉ richᵉ structureᵉ ofᵉ
intuitionisticᵉ logic.ᵉ Belowᵉ weᵉ giveᵉ aᵉ structuredᵉ overviewᵉ ofᵉ aᵉ notableᵉ selectionᵉ
ofᵉ suchᵉ operationsᵉ andᵉ theirᵉ notationᵉ in theᵉ library.ᵉ

Theᵉ listᵉ isᵉ splitᵉ intoᵉ twoᵉ sections,ᵉ theᵉ firstᵉ consistsᵉ ofᵉ operationsᵉ thatᵉ
generalizeᵉ to arbitraryᵉ typesᵉ andᵉ evenᵉ sufficientlyᵉ niceᵉ
[subuniverses](foundation.subuniverses.md),ᵉ suchᵉ asᵉ
$n$-[types](foundation-core.truncated-types.md).ᵉ

| Nameᵉ                                                        | Operatorᵉ onᵉ typesᵉ | Operatorᵉ onᵉ propositions/subtypesᵉ |
| -----------------------------------------------------------ᵉ | -----------------ᵉ | ---------------------------------ᵉ |
| [Dependentᵉ sum](foundation.dependent-pair-types.mdᵉ)         | `Σ`ᵉ               | `Σ-Prop`ᵉ                          |
| [Dependentᵉ product](foundation.dependent-function-types.mdᵉ) | `Π`ᵉ               | `Π-Prop`ᵉ                          |
| [Functions](foundation-core.function-types.mdᵉ)              | `→`ᵉ               | `⇒`ᵉ                               |
| [Logicalᵉ equivalence](foundation.logical-equivalences.mdᵉ)   | `↔`ᵉ               | `⇔`ᵉ                               |
| [Product](foundation-core.cartesian-product-types.mdᵉ)       | `×`ᵉ               | `product-Prop`ᵉ                    |
| [Join](synthetic-homotopy-theory.joins-of-types.mdᵉ)         | `*`ᵉ               | `join-Prop`ᵉ                       |
| [Exclusiveᵉ sum](foundation.exclusive-sum.mdᵉ)                | `exclusive-sum`ᵉ   | `exclusive-sum-Prop`ᵉ              |
| [Coproduct](foundation-core.coproduct-types.mdᵉ)             | `+`ᵉ               | _N/Aᵉ_                             |

Noteᵉ thatᵉ forᵉ manyᵉ operationsᵉ in theᵉ secondᵉ section,ᵉ thereᵉ isᵉ anᵉ equivalentᵉ
operationᵉ onᵉ propositionsᵉ in theᵉ first.ᵉ

| Nameᵉ                                                                         | Operatorᵉ onᵉ typesᵉ           | Operatorᵉ onᵉ propositions/subtypesᵉ        |
| ----------------------------------------------------------------------------ᵉ | ---------------------------ᵉ | ----------------------------------------ᵉ |
| [Initialᵉ object](foundation-core.empty-types.mdᵉ)                             | `empty`ᵉ                     | `empty-Prop`ᵉ                             |
| [Terminalᵉ object](foundation.unit-type.mdᵉ)                                   | `unit`ᵉ                      | `unit-Prop`ᵉ                              |
| [Existentialᵉ quantification](foundation.existential-quantification.mdᵉ)       | `exists-structure`ᵉ          | `∃`ᵉ                                      |
| [Uniqueᵉ existentialᵉ quantification](foundation.uniqueness-quantification.mdᵉ) | `uniquely-exists-structure`ᵉ | `∃!`ᵉ                                     |
| [Universalᵉ quantification](foundation.universal-quantification.mdᵉ)           |                             | `∀'`ᵉ (equivalentᵉ to `Π-Prop`ᵉ)            |
| [Conjunction](foundation.conjunction.mdᵉ)                                     |                             | `∧`ᵉ (equivalentᵉ to `product-Prop`ᵉ)       |
| [Disjunction](foundation.disjunction.mdᵉ)                                     | `disjunction-type`ᵉ          | `∨`ᵉ (equivalentᵉ to `join-Prop`ᵉ)          |
| [Exclusiveᵉ disjunction](foundation.exclusive-disjunction.mdᵉ)                 | `xor-type`ᵉ                  | `⊻`ᵉ (equivalentᵉ to `exclusive-sum-Prop`ᵉ) |
| [Negation](foundation.negation.mdᵉ)                                           | `¬`ᵉ                         | `¬'`ᵉ                                     |
| [Doubleᵉ negation](foundation.double-negation.mdᵉ)                             | `¬¬`ᵉ                        | `¬¬'`ᵉ                                    |

Weᵉ canᵉ alsoᵉ organizeᵉ theseᵉ operationsᵉ byᵉ indexedᵉ andᵉ binaryᵉ variants,ᵉ givingᵉ usᵉ
theᵉ followingᵉ tableᵉ:

| Nameᵉ                   | Binaryᵉ | Indexedᵉ |
| ----------------------ᵉ | ------ᵉ | -------ᵉ |
| Productᵉ                | `×`ᵉ    | `Π`ᵉ     |
| Conjunctionᵉ            | `∧`ᵉ    | `∀'`ᵉ    |
| Constructiveᵉ existenceᵉ | `+`ᵉ    | `Σ`ᵉ     |
| Existenceᵉ              | `∨`ᵉ    | `∃`ᵉ     |
| Uniqueᵉ existenceᵉ       | `⊻`ᵉ    | `∃!`ᵉ    |

### Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}