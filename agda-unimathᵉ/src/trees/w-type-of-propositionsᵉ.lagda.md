# The W-type of the type of propositions

```agda
module trees.w-type-of-propositionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import trees.extensional-w-typesᵉ
open import trees.w-typesᵉ
```

</details>

## Idea

Theᵉ W-typeᵉ ofᵉ theᵉ typeᵉ ofᵉ propositionsᵉ isᵉ definedᵉ using theᵉ typeᵉ ofᵉ propositionsᵉ
andᵉ theᵉ canonicalᵉ typeᵉ familyᵉ overᵉ it.ᵉ

## Definition

```agda
𝕎-Propᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
𝕎-Propᵉ lᵉ = 𝕎ᵉ (Propᵉ lᵉ) type-Propᵉ

zero-𝕎-Propᵉ : {lᵉ : Level} → 𝕎-Propᵉ lᵉ
zero-𝕎-Propᵉ {lᵉ} = constant-𝕎ᵉ (raise-empty-Propᵉ lᵉ) is-empty-raise-emptyᵉ

succ-𝕎-Propᵉ : {lᵉ : Level} → 𝕎-Propᵉ lᵉ → 𝕎-Propᵉ lᵉ
succ-𝕎-Propᵉ {lᵉ} Pᵉ = tree-𝕎ᵉ (raise-unit-Propᵉ lᵉ) (λ xᵉ → Pᵉ)
```

### Standard subfinite types(?)

```agda
standard-subfinite-typeᵉ : {lᵉ : Level} → 𝕎-Propᵉ lᵉ → UUᵉ lᵉ
standard-subfinite-typeᵉ (tree-𝕎ᵉ Pᵉ αᵉ) =
  Σᵉ (type-Propᵉ Pᵉ) (λ pᵉ → standard-subfinite-typeᵉ (αᵉ pᵉ)) +ᵉ type-Propᵉ Pᵉ
```

## Properties

### 𝕎-Prop is extensional

```agda
is-extensional-𝕎-Propᵉ : {lᵉ : Level} → is-extensional-𝕎ᵉ (Propᵉ lᵉ) type-Propᵉ
is-extensional-𝕎-Propᵉ = is-extensional-is-univalent-𝕎ᵉ is-univalent-type-Propᵉ
```

### 𝕎-Prop is a set

```agda
is-set-𝕎-Propᵉ : {lᵉ : Level} → is-setᵉ (𝕎-Propᵉ lᵉ)
is-set-𝕎-Propᵉ = is-set-𝕎ᵉ is-set-type-Propᵉ
```