# Iterated cartesian products of pointed types

```agda
module structured-types.iterated-pointed-cartesian-product-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import lists.listsᵉ

open import structured-types.pointed-cartesian-product-typesᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ listᵉ ofᵉ pointedᵉ typesᵉ `l`ᵉ weᵉ defineᵉ recursivelyᵉ theᵉ iteratedᵉ pointedᵉ
cartesianᵉ productᵉ ofᵉ `l`.ᵉ

## Definition

```agda
iterated-product-Pointed-Typeᵉ :
  {lᵉ : Level} → (Lᵉ : listᵉ (Pointed-Typeᵉ lᵉ)) → Pointed-Typeᵉ lᵉ
iterated-product-Pointed-Typeᵉ nilᵉ = raise-unitᵉ _ ,ᵉ raise-starᵉ
iterated-product-Pointed-Typeᵉ (consᵉ xᵉ Lᵉ) =
  xᵉ ×∗ᵉ (iterated-product-Pointed-Typeᵉ Lᵉ)
```