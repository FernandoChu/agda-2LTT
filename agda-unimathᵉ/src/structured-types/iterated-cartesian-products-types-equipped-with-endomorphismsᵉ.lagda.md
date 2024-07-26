# Iterated cartesian products of types equipped with endomorphisms

```agda
module
  structured-types.iterated-cartesian-products-types-equipped-with-endomorphismsᵉ
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import lists.listsᵉ

open import structured-types.cartesian-products-types-equipped-with-endomorphismsᵉ
open import structured-types.types-equipped-with-endomorphismsᵉ
```

</details>

## Idea

Fromᵉ aᵉ listᵉ ofᵉ aᵉ typesᵉ equippedᵉ with endomorphisms,ᵉ weᵉ defineᵉ itsᵉ iteratedᵉ
cartesianᵉ productᵉ recursivelyᵉ viaᵉ theᵉ cartesianᵉ productᵉ ofᵉ typesᵉ equippedᵉ with
endomorphism.ᵉ

## Definitions

```agda
iterated-product-list-Type-With-Endomorphismᵉ :
  {lᵉ : Level} → listᵉ (Type-With-Endomorphismᵉ lᵉ) → Type-With-Endomorphismᵉ lᵉ
iterated-product-list-Type-With-Endomorphismᵉ nilᵉ =
  trivial-Type-With-Endomorphismᵉ
iterated-product-list-Type-With-Endomorphismᵉ (consᵉ Aᵉ Lᵉ) =
  product-Type-With-Endomorphismᵉ Aᵉ
    ( iterated-product-list-Type-With-Endomorphismᵉ Lᵉ)
```