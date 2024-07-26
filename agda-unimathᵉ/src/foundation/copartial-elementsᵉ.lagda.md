# Copartial elements

```agda
module foundation.copartial-elementsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.negationᵉ
open import foundation.partial-elementsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ

open import orthogonal-factorization-systems.closed-modalitiesᵉ

open import synthetic-homotopy-theory.joins-of-typesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "copartialᵉ element"ᵉ Agda=copartial-elementᵉ}} ofᵉ aᵉ typeᵉ `A`ᵉ isᵉ anᵉ
elementᵉ ofᵉ typeᵉ

```text
  Σᵉ (Qᵉ : Prop),ᵉ Aᵉ *ᵉ Qᵉ
```

where theᵉ typeᵉ `Aᵉ *ᵉ Q`ᵉ isᵉ theᵉ
[join](synthetic-homotopy-theory.joins-of-types.mdᵉ) ofᵉ `Q`ᵉ andᵉ `A`.ᵉ Weᵉ sayᵉ thatᵉ
evaluationᵉ ofᵉ aᵉ copartialᵉ elementᵉ `(Qᵉ ,ᵉ u)`ᵉ isᵉ
{{#conceptᵉ "denied"ᵉ Disambiguation="copartialᵉ element"ᵉ Agda=is-denied-copartial-elementᵉ}}
ifᵉ theᵉ propositionᵉ `Q`ᵉ holds.ᵉ

Inᵉ orderᵉ to compareᵉ copartialᵉ elementsᵉ with
[partialᵉ elements](foundation.partial-elements.md),ᵉ noteᵉ thatᵉ weᵉ haveᵉ theᵉ
followingᵉ [pullback](foundation.pullbacks.mdᵉ) squaresᵉ

```text
  Aᵉ ----->ᵉ Σᵉ (Qᵉ : Prop),ᵉ Aᵉ *ᵉ Qᵉ        1 ----->ᵉ Σᵉ (Pᵉ : Prop),ᵉ (Pᵉ → Aᵉ)
  | ⌟ᵉ              |                  | ⌟ᵉ              |
  |                |                  |                |
  ∨ᵉ                ∨ᵉ                  ∨ᵉ                ∨ᵉ
  1 ----------->ᵉ Propᵉ                 1 ----------->ᵉ Propᵉ
          Fᵉ                                   Fᵉ

  1 ----->ᵉ Σᵉ (Qᵉ : Prop),ᵉ Aᵉ *ᵉ Qᵉ        Aᵉ ----->ᵉ Σᵉ (Pᵉ : Prop),ᵉ (Pᵉ → Aᵉ)
  | ⌟ᵉ              |                  | ⌟ᵉ              |
  |                |                  |                |
  ∨ᵉ                ∨ᵉ                  ∨ᵉ                ∨ᵉ
  1 ----------->ᵉ Propᵉ                 1 ----------->ᵉ Propᵉ
          Tᵉ                                   Tᵉ
```

Noteᵉ thatᵉ weᵉ makeᵉ useᵉ ofᵉ theᵉ
[closedᵉ modalities](orthogonal-factorization-systems.closed-modalities.mdᵉ)
`Aᵉ ↦ᵉ Aᵉ *ᵉ Q`ᵉ in theᵉ formulationᵉ ofᵉ copartialᵉ element,ᵉ whereasᵉ theᵉ formulationᵉ ofᵉ
partialᵉ elementsᵉ makesᵉ useᵉ ofᵉ theᵉ
[openᵉ modalities](orthogonal-factorization-systems.open-modalities.md).ᵉ Theᵉ
conceptsᵉ ofᵉ partialᵉ andᵉ copartialᵉ elementsᵉ areᵉ dualᵉ in thatᵉ sense.ᵉ

Alternatively,ᵉ theᵉ typeᵉ ofᵉ copartialᵉ elementsᵉ ofᵉ aᵉ typeᵉ `A`ᵉ canᵉ beᵉ definedᵉ asᵉ
theᵉ [pushout-product](synthetic-homotopy-theory.pushout-products.mdᵉ)

```text
    Aᵉ   1
    |   |
  !ᵉ | □ᵉ | Tᵉ
    ∨ᵉ   ∨ᵉ
    1  Propᵉ
```

Thisᵉ pointᵉ ofᵉ viewᵉ isᵉ usefulᵉ in orderᵉ to establishᵉ thatᵉ copartialᵉ elementsᵉ ofᵉ
copartialᵉ elementsᵉ induceᵉ copartialᵉ elements.ᵉ Indeed,ᵉ noteᵉ thatᵉ
`(Aᵉ □ᵉ Tᵉ) □ᵉ Tᵉ ＝ᵉ Aᵉ □ᵉ (Tᵉ □ᵉ T)`ᵉ byᵉ associativityᵉ ofᵉ theᵉ pushoutᵉ product,ᵉ andᵉ thatᵉ
`T`ᵉ isᵉ aᵉ pushout-productᵉ algebraᵉ in theᵉ senseᵉ thatᵉ

```text
                                         Pᵉ Qᵉ xᵉ ↦ᵉ (Pᵉ *ᵉ Qᵉ ,ᵉ xᵉ)
    1     1       Σᵉ (Pᵉ Qᵉ : Prop),ᵉ Pᵉ *ᵉ Qᵉ --------------------->ᵉ 1
    |     |               |                                    |
  Tᵉ |  □ᵉ  | Tᵉ   =   Tᵉ □ᵉ Tᵉ |                                    |
    ∨ᵉ     ∨ᵉ               ∨ᵉ                                    ∨ᵉ
  Propᵉ   Propᵉ           Prop²ᵉ ------------------------------>ᵉ Propᵉ
                                       Pᵉ Qᵉ ↦ᵉ Pᵉ *ᵉ Qᵉ
```

Byᵉ thisᵉ [morphismᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ) itᵉ followsᵉ thatᵉ
thereᵉ isᵉ aᵉ morphismᵉ ofᵉ arrowsᵉ

```text
  join-copartial-elementᵉ : (Aᵉ □ᵉ Tᵉ) □ᵉ Tᵉ → Aᵉ □ᵉ T,ᵉ
```

i.e.,ᵉ thatᵉ copartialᵉ copartialᵉ elementsᵉ induceᵉ copartialᵉ elements.ᵉ Theseᵉ
considerationsᵉ allowᵉ usᵉ to composeᵉ
[copartialᵉ functions](foundation.copartial-functions.md).ᵉ

**Note:**ᵉ Theᵉ topicᵉ ofᵉ copartialᵉ functionsᵉ wasᵉ notᵉ knownᵉ to usᵉ in theᵉ
literature,ᵉ andᵉ ourᵉ formalizationᵉ onᵉ thisᵉ topicᵉ shouldᵉ beᵉ consideredᵉ
experimental.ᵉ

## Definition

### Copartial elements

```agda
copartial-elementᵉ : {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
copartial-elementᵉ l2ᵉ Aᵉ =
  Σᵉ (Propᵉ l2ᵉ) (λ Qᵉ → operator-closed-modalityᵉ Qᵉ Aᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : copartial-elementᵉ l2ᵉ Aᵉ)
  where

  is-denied-prop-copartial-elementᵉ : Propᵉ l2ᵉ
  is-denied-prop-copartial-elementᵉ = pr1ᵉ aᵉ

  is-denied-copartial-elementᵉ : UUᵉ l2ᵉ
  is-denied-copartial-elementᵉ =
    type-Propᵉ is-denied-prop-copartial-elementᵉ

  value-copartial-elementᵉ :
    operator-closed-modalityᵉ is-denied-prop-copartial-elementᵉ Aᵉ
  value-copartial-elementᵉ = pr2ᵉ aᵉ
```

### The unit of the copartial element operator

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ)
  where

  is-denied-prop-unit-copartial-elementᵉ : Propᵉ lzero
  is-denied-prop-unit-copartial-elementᵉ = empty-Propᵉ

  is-denied-unit-copartial-elementᵉ : UUᵉ lzero
  is-denied-unit-copartial-elementᵉ = emptyᵉ

  unit-copartial-elementᵉ : copartial-elementᵉ lzero Aᵉ
  pr1ᵉ unit-copartial-elementᵉ = is-denied-prop-unit-copartial-elementᵉ
  pr2ᵉ unit-copartial-elementᵉ = unit-closed-modalityᵉ empty-Propᵉ aᵉ
```

## Properties

### Forgetful map from copartial elements to partial elements

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : copartial-elementᵉ l2ᵉ Aᵉ)
  where

  is-defined-prop-partial-element-copartial-elementᵉ : Propᵉ l2ᵉ
  is-defined-prop-partial-element-copartial-elementᵉ =
    neg-Propᵉ (is-denied-prop-copartial-elementᵉ aᵉ)

  is-defined-partial-element-copartial-elementᵉ : UUᵉ l2ᵉ
  is-defined-partial-element-copartial-elementᵉ =
    type-Propᵉ is-defined-prop-partial-element-copartial-elementᵉ

  value-partial-element-copartial-elementᵉ :
    is-defined-partial-element-copartial-elementᵉ → Aᵉ
  value-partial-element-copartial-elementᵉ fᵉ =
    map-inv-right-unit-law-join-is-emptyᵉ fᵉ (value-copartial-elementᵉ aᵉ)

  partial-element-copartial-elementᵉ : partial-elementᵉ l2ᵉ Aᵉ
  pr1ᵉ partial-element-copartial-elementᵉ =
    is-defined-prop-partial-element-copartial-elementᵉ
  pr2ᵉ partial-element-copartial-elementᵉ =
    value-partial-element-copartial-elementᵉ
```