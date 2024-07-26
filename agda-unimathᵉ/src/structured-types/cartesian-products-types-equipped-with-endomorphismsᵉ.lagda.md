# Cartesian products of types equipped with endomorphisms

```agda
module structured-types.cartesian-products-types-equipped-with-endomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.types-equipped-with-endomorphismsᵉ
```

</details>

## Idea

Theᵉ **cartesianᵉ product**ᵉ ofᵉ twoᵉ
[typesᵉ equippedᵉ with anᵉ endomorphism](structured-types.types-equipped-with-endomorphisms.mdᵉ)
`(Aᵉ ,ᵉ f)`ᵉ andᵉ `(Bᵉ ,ᵉ g)`ᵉ isᵉ definedᵉ asᵉ `(Aᵉ ×ᵉ Bᵉ ,ᵉ fᵉ ×ᵉ g)`ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : Type-With-Endomorphismᵉ l1ᵉ) (Bᵉ : Type-With-Endomorphismᵉ l2ᵉ)
  where

  type-product-Type-With-Endomorphismᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-product-Type-With-Endomorphismᵉ =
    type-Type-With-Endomorphismᵉ Aᵉ ×ᵉ type-Type-With-Endomorphismᵉ Bᵉ

  endomorphism-product-Type-With-Endomorphismᵉ :
    type-product-Type-With-Endomorphismᵉ → type-product-Type-With-Endomorphismᵉ
  endomorphism-product-Type-With-Endomorphismᵉ =
    map-productᵉ
      ( endomorphism-Type-With-Endomorphismᵉ Aᵉ)
      ( endomorphism-Type-With-Endomorphismᵉ Bᵉ)

  product-Type-With-Endomorphismᵉ :
    Type-With-Endomorphismᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ product-Type-With-Endomorphismᵉ =
    type-product-Type-With-Endomorphismᵉ
  pr2ᵉ product-Type-With-Endomorphismᵉ =
    endomorphism-product-Type-With-Endomorphismᵉ
```