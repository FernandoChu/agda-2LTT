# Partial elements

```agda
module foundation.partial-elementsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "partialᵉ element"ᵉ Agda=partial-elementᵉ}} ofᵉ `X`ᵉ consistsᵉ ofᵉ aᵉ
[proposition](foundation-core.propositions.mdᵉ) `P`ᵉ andᵉ aᵉ mapᵉ `Pᵉ → X`.ᵉ Thatᵉ is,ᵉ
theᵉ typeᵉ ofᵉ partialᵉ elementsᵉ ofᵉ `X`ᵉ isᵉ definedᵉ to beᵉ

```text
  Σᵉ (Pᵉ : Prop),ᵉ (Pᵉ → X).ᵉ
```

Weᵉ sayᵉ thatᵉ aᵉ partialᵉ elementᵉ `(P,ᵉ f)`ᵉ isᵉ
{{#conceptᵉ "defined"ᵉ Disambiguation="partialᵉ element"ᵉ}} ifᵉ theᵉ propositionᵉ `P`ᵉ
holds.ᵉ

Alternatively,ᵉ theᵉ typeᵉ ofᵉ partialᵉ elementsᵉ ofᵉ `X`ᵉ canᵉ beᵉ descibedᵉ asᵉ theᵉ
codomainᵉ ofᵉ theᵉ
[composition](species.composition-cauchy-series-species-of-types.mdᵉ)

```text
    1   ∅ᵉ     ∅ᵉ
    |   |     |
  Tᵉ | ∘ᵉ |  =  |
    ∨ᵉ   ∨ᵉ     ∨ᵉ
  Propᵉ  Xᵉ   Pᵉ Tᵉ Xᵉ
```

ofᵉ [polynomial-endofunctors.md](trees.polynomial-endofunctors.md).ᵉ Indeed,ᵉ theᵉ
codomainᵉ ofᵉ thisᵉ compositionᵉ operationᵉ ofᵉ morphismsᵉ isᵉ theᵉ polynomialᵉ
endofunctorᵉ `Pᵉ T`ᵉ ofᵉ theᵉ mapᵉ `Tᵉ : 1 → Prop`ᵉ evaluatedᵉ atᵉ `X`,ᵉ whichᵉ isᵉ exactlyᵉ
theᵉ typeᵉ ofᵉ partialᵉ elementsᵉ ofᵉ `X`.ᵉ

## Definitions

### Partial elements of a type

```agda
partial-elementᵉ : {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
partial-elementᵉ l2ᵉ Xᵉ = Σᵉ (Propᵉ l2ᵉ) (λ Pᵉ → type-Propᵉ Pᵉ → Xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (xᵉ : partial-elementᵉ l2ᵉ Xᵉ)
  where

  is-defined-prop-partial-elementᵉ : Propᵉ l2ᵉ
  is-defined-prop-partial-elementᵉ = pr1ᵉ xᵉ

  is-defined-partial-elementᵉ : UUᵉ l2ᵉ
  is-defined-partial-elementᵉ = type-Propᵉ is-defined-prop-partial-elementᵉ
```

### The unit of the partial element operator

```agda
unit-partial-elementᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → Xᵉ → partial-elementᵉ lzero Xᵉ
pr1ᵉ (unit-partial-elementᵉ xᵉ) = unit-Propᵉ
pr2ᵉ (unit-partial-elementᵉ xᵉ) yᵉ = xᵉ
```

## Properties

### The type of partial elements is a directed complete poset

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#734](https://github.com/UniMath/agda-unimath/issues/734ᵉ)

## See also

-ᵉ [Copartialᵉ elements](foundation.copartial-elements.mdᵉ)
-ᵉ [Partialᵉ functions](foundation.partial-functions.mdᵉ)
-ᵉ [Partialᵉ sequences](foundation.partial-sequences.mdᵉ)
-ᵉ [Totalᵉ partialᵉ functions](foundation.total-partial-functions.mdᵉ)