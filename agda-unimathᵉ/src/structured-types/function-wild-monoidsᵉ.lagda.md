# Function wild monoids

```agda
module structured-types.function-wild-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.dependent-products-wild-monoidsᵉ
open import structured-types.h-spacesᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.wild-monoidsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [wildᵉ monoid](structured-types.wild-monoids.mdᵉ) `M`ᵉ andᵉ aᵉ typeᵉ `I`,ᵉ theᵉ
**functionᵉ wildᵉ monoid**ᵉ `M^I`ᵉ consistsᵉ ofᵉ functionsᵉ fromᵉ `I`ᵉ to theᵉ underlyingᵉ
typeᵉ ofᵉ `M`.ᵉ Everyᵉ componentᵉ ofᵉ theᵉ structureᵉ isᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Mᵉ : Wild-Monoidᵉ l2ᵉ)
  where

  function-Wild-Monoidᵉ : Wild-Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  function-Wild-Monoidᵉ = Π-Wild-Monoidᵉ Iᵉ (λ _ → Mᵉ)

  h-space-function-Wild-Monoidᵉ : H-Spaceᵉ (l1ᵉ ⊔ l2ᵉ)
  h-space-function-Wild-Monoidᵉ =
      h-space-Wild-Monoidᵉ function-Wild-Monoidᵉ

  pointed-type-function-Wild-Monoidᵉ : Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  pointed-type-function-Wild-Monoidᵉ =
    pointed-type-Wild-Monoidᵉ function-Wild-Monoidᵉ

  type-function-Wild-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-function-Wild-Monoidᵉ = type-Wild-Monoidᵉ function-Wild-Monoidᵉ

  unit-function-Wild-Monoidᵉ : type-function-Wild-Monoidᵉ
  unit-function-Wild-Monoidᵉ = unit-Wild-Monoidᵉ function-Wild-Monoidᵉ

  mul-function-Wild-Monoidᵉ :
    type-function-Wild-Monoidᵉ →
    type-function-Wild-Monoidᵉ →
    type-function-Wild-Monoidᵉ
  mul-function-Wild-Monoidᵉ = mul-Wild-Monoidᵉ function-Wild-Monoidᵉ

  left-unit-law-mul-function-Wild-Monoidᵉ :
    ( fᵉ : type-function-Wild-Monoidᵉ) →
    ( mul-function-Wild-Monoidᵉ (unit-function-Wild-Monoidᵉ) fᵉ) ＝ᵉ fᵉ
  left-unit-law-mul-function-Wild-Monoidᵉ =
    left-unit-law-mul-Wild-Monoidᵉ function-Wild-Monoidᵉ

  right-unit-law-mul-function-Wild-Monoidᵉ :
    ( fᵉ : type-function-Wild-Monoidᵉ) →
    ( mul-function-Wild-Monoidᵉ fᵉ (unit-function-Wild-Monoidᵉ)) ＝ᵉ fᵉ
  right-unit-law-mul-function-Wild-Monoidᵉ =
    right-unit-law-mul-Wild-Monoidᵉ function-Wild-Monoidᵉ

  associator-function-Wild-Monoidᵉ :
    associator-H-Spaceᵉ h-space-function-Wild-Monoidᵉ
  associator-function-Wild-Monoidᵉ = associator-Wild-Monoidᵉ function-Wild-Monoidᵉ

  unital-associator-function-Wild-Monoidᵉ :
    unital-associatorᵉ (h-space-Wild-Monoidᵉ function-Wild-Monoidᵉ)
  unital-associator-function-Wild-Monoidᵉ =
    unital-associator-Wild-Monoidᵉ function-Wild-Monoidᵉ
```