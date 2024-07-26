# The crisp law of excluded middle

```agda
{-# OPTIONSᵉ --cohesionᵉ --flat-splitᵉ #-}

module modal-type-theory.crisp-law-of-excluded-middleᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.decidable-propositionsᵉ
open import foundation-core.negationᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Theᵉ **crispᵉ lawᵉ ofᵉ excludedᵉ middle**ᵉ assertsᵉ thatᵉ anyᵉ crispᵉ
[proposition](foundation-core.propositions.mdᵉ) `P`ᵉ isᵉ
[decidable](foundation.decidable-types.md).ᵉ

## Definition

```agda
Crisp-LEMᵉ : (@♭ᵉ lᵉ : Level) → UUᵉ (lsuc lᵉ)
Crisp-LEMᵉ lᵉ = (@♭ᵉ Pᵉ : Propᵉ lᵉ) → is-decidableᵉ (type-Propᵉ Pᵉ)
```

## Properties

### Given crisp LEM, we obtain a map from crisp propositions to decidable propositions

```agda
decidable-prop-Crisp-Propᵉ :
  {@♭ᵉ lᵉ : Level} → Crisp-LEMᵉ lᵉ → @♭ᵉ Propᵉ lᵉ → Decidable-Propᵉ lᵉ
pr1ᵉ (decidable-prop-Crisp-Propᵉ lemᵉ Pᵉ) = type-Propᵉ Pᵉ
pr1ᵉ (pr2ᵉ (decidable-prop-Crisp-Propᵉ lemᵉ Pᵉ)) = is-prop-type-Propᵉ Pᵉ
pr2ᵉ (pr2ᵉ (decidable-prop-Crisp-Propᵉ lemᵉ Pᵉ)) = lemᵉ Pᵉ
```

## See also

-ᵉ [Theᵉ lawᵉ ofᵉ excludedᵉ middle](foundation.law-of-excluded-middle.mdᵉ)