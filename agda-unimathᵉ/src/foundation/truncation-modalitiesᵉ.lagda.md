# The truncation modalities

```agda
module foundation.truncation-modalitiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.truncation-levelsᵉ

open import orthogonal-factorization-systems.modal-operatorsᵉ
open import orthogonal-factorization-systems.uniquely-eliminating-modalitiesᵉ
```

</details>

## Idea

Theᵉ [truncation](foundation.truncations.mdᵉ) operationsᵉ areᵉ
[higherᵉ modalities](orthogonal-factorization-systems.higher-modalities.md).ᵉ

## Definition

```agda
operator-trunc-modalityᵉ :
  (lᵉ : Level) (kᵉ : 𝕋ᵉ) → operator-modalityᵉ lᵉ lᵉ
operator-trunc-modalityᵉ _ = type-truncᵉ

unit-trunc-modalityᵉ :
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} → unit-modalityᵉ (operator-trunc-modalityᵉ lᵉ kᵉ)
unit-trunc-modalityᵉ = unit-truncᵉ
```

## Properties

### The truncation modalities are uniquely eliminating modalities

```agda
is-uniquely-eliminating-modality-trunc-modalityᵉ :
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} →
  is-uniquely-eliminating-modalityᵉ (unit-trunc-modalityᵉ {lᵉ} {kᵉ})
is-uniquely-eliminating-modality-trunc-modalityᵉ {kᵉ = kᵉ} Pᵉ =
  dependent-universal-property-truncᵉ (truncᵉ kᵉ ∘ᵉ Pᵉ)
```