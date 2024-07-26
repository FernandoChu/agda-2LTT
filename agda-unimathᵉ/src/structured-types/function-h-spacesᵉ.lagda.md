# Function H-spaces

```agda
module structured-types.function-h-spacesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.dependent-products-h-spacesᵉ
open import structured-types.h-spacesᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ [H-space](structured-types.h-spaces.mdᵉ) `M`ᵉ andᵉ aᵉ typeᵉ `I`,ᵉ theᵉ
**functionᵉ H-space**ᵉ `M^I`ᵉ consistsᵉ ofᵉ functionsᵉ fromᵉ `I`ᵉ to theᵉ underlyingᵉ typeᵉ
ofᵉ `M`.ᵉ Everyᵉ componentᵉ ofᵉ theᵉ structureᵉ isᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Mᵉ : H-Spaceᵉ l2ᵉ)
  where

  function-H-Spaceᵉ : H-Spaceᵉ (l1ᵉ ⊔ l2ᵉ)
  function-H-Spaceᵉ = Π-H-Spaceᵉ Iᵉ (λ _ → Mᵉ)

  pointed-type-function-H-Spaceᵉ : Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  pointed-type-function-H-Spaceᵉ =
    pointed-type-H-Spaceᵉ function-H-Spaceᵉ

  type-function-H-Spaceᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-function-H-Spaceᵉ =
    type-H-Spaceᵉ function-H-Spaceᵉ

  unit-function-H-Spaceᵉ : type-function-H-Spaceᵉ
  unit-function-H-Spaceᵉ =
    unit-H-Spaceᵉ function-H-Spaceᵉ

  mul-function-H-Spaceᵉ :
    type-function-H-Spaceᵉ →
    type-function-H-Spaceᵉ →
    type-function-H-Spaceᵉ
  mul-function-H-Spaceᵉ = mul-H-Spaceᵉ function-H-Spaceᵉ

  left-unit-law-mul-function-H-Spaceᵉ :
    (fᵉ : type-function-H-Spaceᵉ) →
    mul-function-H-Spaceᵉ unit-function-H-Spaceᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-mul-function-H-Spaceᵉ =
    left-unit-law-mul-H-Spaceᵉ function-H-Spaceᵉ

  right-unit-law-mul-function-H-Spaceᵉ :
    (fᵉ : type-function-H-Spaceᵉ) →
    mul-function-H-Spaceᵉ fᵉ unit-function-H-Spaceᵉ ＝ᵉ fᵉ
  right-unit-law-mul-function-H-Spaceᵉ =
    right-unit-law-mul-H-Spaceᵉ function-H-Spaceᵉ

  is-unital-mul-function-H-Spaceᵉ :
    is-unitalᵉ mul-function-H-Spaceᵉ
  is-unital-mul-function-H-Spaceᵉ =
    is-unital-mul-H-Spaceᵉ function-H-Spaceᵉ

  coh-unit-laws-mul-function-H-Spaceᵉ :
    coh-unit-lawsᵉ
      ( mul-function-H-Spaceᵉ)
      ( unit-function-H-Spaceᵉ)
      ( left-unit-law-mul-function-H-Spaceᵉ)
      ( right-unit-law-mul-function-H-Spaceᵉ)
  coh-unit-laws-mul-function-H-Spaceᵉ =
    coh-unit-laws-mul-H-Spaceᵉ function-H-Spaceᵉ

  coherent-unit-laws-mul-function-H-Spaceᵉ :
    coherent-unit-lawsᵉ
      ( mul-function-H-Spaceᵉ)
      ( unit-function-H-Spaceᵉ)
  coherent-unit-laws-mul-function-H-Spaceᵉ =
    coherent-unit-laws-mul-H-Spaceᵉ function-H-Spaceᵉ

  is-coherently-unital-mul-function-H-Spaceᵉ :
    is-coherently-unitalᵉ mul-function-H-Spaceᵉ
  is-coherently-unital-mul-function-H-Spaceᵉ =
    is-coherently-unital-mul-H-Spaceᵉ function-H-Spaceᵉ

  coherent-unital-mul-function-H-Spaceᵉ :
    coherent-unital-mul-Pointed-Typeᵉ pointed-type-function-H-Spaceᵉ
  coherent-unital-mul-function-H-Spaceᵉ =
    coherent-unital-mul-H-Spaceᵉ function-H-Spaceᵉ
```