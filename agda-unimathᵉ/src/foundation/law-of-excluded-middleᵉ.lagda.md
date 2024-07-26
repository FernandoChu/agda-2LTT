# The law of excluded middle

```agda
module foundation.law-of-excluded-middleᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.decidable-propositionsᵉ
open import foundation-core.negationᵉ
open import foundation-core.propositionsᵉ

open import univalent-combinatorics.2-element-typesᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "lawᵉ ofᵉ excludedᵉ middle"ᵉ Agda=LEMᵉ}} assertsᵉ thatᵉ anyᵉ
[proposition](foundation-core.propositions.mdᵉ) `P`ᵉ isᵉ
[decidable](foundation.decidable-types.md).ᵉ

## Definition

```agda
LEMᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
LEMᵉ lᵉ = (Pᵉ : Propᵉ lᵉ) → is-decidableᵉ (type-Propᵉ Pᵉ)
```

## Properties

### Given LEM, we obtain a map from the type of propositions to the type of decidable propositions

```agda
decidable-prop-Propᵉ :
  {lᵉ : Level} → LEMᵉ lᵉ → Propᵉ lᵉ → Decidable-Propᵉ lᵉ
pr1ᵉ (decidable-prop-Propᵉ lemᵉ Pᵉ) = type-Propᵉ Pᵉ
pr1ᵉ (pr2ᵉ (decidable-prop-Propᵉ lemᵉ Pᵉ)) = is-prop-type-Propᵉ Pᵉ
pr2ᵉ (pr2ᵉ (decidable-prop-Propᵉ lemᵉ Pᵉ)) = lemᵉ Pᵉ
```

### The unrestricted law of excluded middle does not hold

```agda
abstract
  no-global-decidabilityᵉ :
    {lᵉ : Level} → ¬ᵉ ((Xᵉ : UUᵉ lᵉ) → is-decidableᵉ Xᵉ)
  no-global-decidabilityᵉ {lᵉ} dᵉ =
    is-not-decidable-type-2-Element-Typeᵉ (λ Xᵉ → dᵉ (pr1ᵉ Xᵉ))
```