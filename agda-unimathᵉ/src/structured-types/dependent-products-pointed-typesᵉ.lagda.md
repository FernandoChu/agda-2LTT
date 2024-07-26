# Dependent products of pointed types

```agda
module structured-types.dependent-products-pointed-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ [pointedᵉ types](structured-types.pointed-types.mdᵉ) `Mᵢ`ᵉ
indexedᵉ byᵉ `iᵉ : I`,ᵉ theᵉ dependentᵉ productᵉ `Π(iᵉ : I),ᵉ Mᵢ`ᵉ isᵉ aᵉ pointedᵉ typeᵉ
consistingᵉ ofᵉ dependentᵉ functionsᵉ takingᵉ `iᵉ : I`ᵉ to anᵉ elementᵉ ofᵉ theᵉ underlyingᵉ
typeᵉ ofᵉ `Mᵢ`.ᵉ Theᵉ baseᵉ pointᵉ isᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
Π-Pointed-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Pᵉ : Iᵉ → Pointed-Typeᵉ l2ᵉ) → Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (Π-Pointed-Typeᵉ Iᵉ Pᵉ) = (xᵉ : Iᵉ) → type-Pointed-Typeᵉ (Pᵉ xᵉ)
pr2ᵉ (Π-Pointed-Typeᵉ Iᵉ Pᵉ) xᵉ = point-Pointed-Typeᵉ (Pᵉ xᵉ)
```