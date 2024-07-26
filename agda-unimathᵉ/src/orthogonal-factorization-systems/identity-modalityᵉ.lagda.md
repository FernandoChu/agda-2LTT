# The identity modality

```agda
module orthogonal-factorization-systems.identity-modalityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.local-typesᵉ
open import orthogonal-factorization-systems.modal-operatorsᵉ
open import orthogonal-factorization-systems.uniquely-eliminating-modalitiesᵉ
```

</details>

## Idea

Theᵉ identityᵉ operationᵉ onᵉ typesᵉ isᵉ triviallyᵉ aᵉ
[higherᵉ modality](orthogonal-factorization-systems.higher-modalities.md).ᵉ

## Definition

```agda
operator-id-modalityᵉ :
  (lᵉ : Level) → operator-modalityᵉ lᵉ lᵉ
operator-id-modalityᵉ lᵉ = idᵉ

unit-id-modalityᵉ :
  {lᵉ : Level} → unit-modalityᵉ (operator-id-modalityᵉ lᵉ)
unit-id-modalityᵉ = idᵉ
```

## Properties

### The identity modality is a uniquely eliminating modality

```agda
is-uniquely-eliminating-modality-id-modalityᵉ :
  {lᵉ : Level} → is-uniquely-eliminating-modalityᵉ (unit-id-modalityᵉ {lᵉ})
is-uniquely-eliminating-modality-id-modalityᵉ {lᵉ} Pᵉ =
  is-local-dependent-type-is-equivᵉ
    ( unit-id-modalityᵉ)
    ( is-equiv-idᵉ)
    ( operator-id-modalityᵉ lᵉ ∘ᵉ Pᵉ)
```