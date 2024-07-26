# Function magmas

```agda
module structured-types.function-magmasᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.magmasᵉ
```

</details>

## Idea

Givenᵉ aᵉ magmaᵉ `M`ᵉ andᵉ aᵉ typeᵉ `X`,ᵉ theᵉ functionᵉ magmaᵉ `M^X`ᵉ consistsᵉ ofᵉ functionsᵉ
fromᵉ `X`ᵉ intoᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `M`.ᵉ Theᵉ operationᵉ onᵉ `M^X`ᵉ isᵉ definedᵉ
pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Magmaᵉ l1ᵉ) (Xᵉ : UUᵉ l2ᵉ)
  where

  type-function-Magmaᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-function-Magmaᵉ = Xᵉ → type-Magmaᵉ Mᵉ

  mul-function-Magmaᵉ :
    type-function-Magmaᵉ → type-function-Magmaᵉ → type-function-Magmaᵉ
  mul-function-Magmaᵉ fᵉ gᵉ xᵉ = mul-Magmaᵉ Mᵉ (fᵉ xᵉ) (gᵉ xᵉ)

  function-Magmaᵉ : Magmaᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ function-Magmaᵉ = type-function-Magmaᵉ
  pr2ᵉ function-Magmaᵉ = mul-function-Magmaᵉ
```