# Dependent products of H-spaces

```agda
module structured-types.dependent-products-h-spacesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.dependent-products-pointed-typesᵉ
open import structured-types.h-spacesᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ [H-spaces](structured-types.h-spaces.mdᵉ) `Mᵢ`ᵉ indexedᵉ byᵉ
`iᵉ : I`,ᵉ theᵉ dependentᵉ productᵉ `Π(iᵉ : I),ᵉ Mᵢ`ᵉ isᵉ aᵉ H-spaceᵉ consistingᵉ ofᵉ
dependentᵉ functionsᵉ takingᵉ `iᵉ : I`ᵉ to anᵉ elementᵉ ofᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `Mᵢ`.ᵉ
Theᵉ multiplicativeᵉ operationᵉ andᵉ theᵉ unitᵉ areᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Mᵉ : Iᵉ → H-Spaceᵉ l2ᵉ)
  where

  pointed-type-Π-H-Spaceᵉ : Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  pointed-type-Π-H-Spaceᵉ =
    Π-Pointed-Typeᵉ Iᵉ (λ xᵉ → pointed-type-H-Spaceᵉ (Mᵉ xᵉ))

  type-Π-H-Spaceᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Π-H-Spaceᵉ = type-Pointed-Typeᵉ pointed-type-Π-H-Spaceᵉ

  unit-Π-H-Spaceᵉ : type-Π-H-Spaceᵉ
  unit-Π-H-Spaceᵉ = point-Pointed-Typeᵉ (pointed-type-Π-H-Spaceᵉ)

  mul-Π-H-Spaceᵉ :
    type-Π-H-Spaceᵉ → type-Π-H-Spaceᵉ → type-Π-H-Spaceᵉ
  mul-Π-H-Spaceᵉ fᵉ gᵉ iᵉ = mul-H-Spaceᵉ (Mᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ)

  left-unit-law-mul-Π-H-Spaceᵉ :
    (fᵉ : type-Π-H-Spaceᵉ) →
    mul-Π-H-Spaceᵉ unit-Π-H-Spaceᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-mul-Π-H-Spaceᵉ fᵉ =
    eq-htpyᵉ (λ iᵉ → left-unit-law-mul-H-Spaceᵉ (Mᵉ iᵉ) (fᵉ iᵉ))

  right-unit-law-mul-Π-H-Spaceᵉ :
    (fᵉ : type-Π-H-Spaceᵉ) →
    mul-Π-H-Spaceᵉ fᵉ unit-Π-H-Spaceᵉ ＝ᵉ fᵉ
  right-unit-law-mul-Π-H-Spaceᵉ fᵉ =
    eq-htpyᵉ (λ iᵉ → right-unit-law-mul-H-Spaceᵉ (Mᵉ iᵉ) (fᵉ iᵉ))

  is-unital-mul-Π-H-Spaceᵉ : is-unitalᵉ mul-Π-H-Spaceᵉ
  pr1ᵉ is-unital-mul-Π-H-Spaceᵉ = unit-Π-H-Spaceᵉ
  pr1ᵉ (pr2ᵉ is-unital-mul-Π-H-Spaceᵉ) =
    left-unit-law-mul-Π-H-Spaceᵉ
  pr2ᵉ (pr2ᵉ is-unital-mul-Π-H-Spaceᵉ) =
    right-unit-law-mul-Π-H-Spaceᵉ

  coh-unit-laws-mul-Π-H-Spaceᵉ :
    coh-unit-lawsᵉ
      ( mul-Π-H-Spaceᵉ)
      ( unit-Π-H-Spaceᵉ)
      ( left-unit-law-mul-Π-H-Spaceᵉ)
      ( right-unit-law-mul-Π-H-Spaceᵉ)
  coh-unit-laws-mul-Π-H-Spaceᵉ =
    apᵉ eq-htpyᵉ (eq-htpyᵉ (λ iᵉ → coh-unit-laws-mul-H-Spaceᵉ (Mᵉ iᵉ)))

  coherent-unit-laws-mul-Π-H-Spaceᵉ :
    coherent-unit-lawsᵉ mul-Π-H-Spaceᵉ unit-Π-H-Spaceᵉ
  pr1ᵉ coherent-unit-laws-mul-Π-H-Spaceᵉ =
    left-unit-law-mul-Π-H-Spaceᵉ
  pr1ᵉ (pr2ᵉ coherent-unit-laws-mul-Π-H-Spaceᵉ) =
    right-unit-law-mul-Π-H-Spaceᵉ
  pr2ᵉ (pr2ᵉ coherent-unit-laws-mul-Π-H-Spaceᵉ) =
    coh-unit-laws-mul-Π-H-Spaceᵉ

  is-coherently-unital-mul-Π-H-Spaceᵉ :
    is-coherently-unitalᵉ mul-Π-H-Spaceᵉ
  pr1ᵉ is-coherently-unital-mul-Π-H-Spaceᵉ = unit-Π-H-Spaceᵉ
  pr2ᵉ is-coherently-unital-mul-Π-H-Spaceᵉ =
    coherent-unit-laws-mul-Π-H-Spaceᵉ

  coherent-unital-mul-Π-H-Spaceᵉ :
    coherent-unital-mul-Pointed-Typeᵉ pointed-type-Π-H-Spaceᵉ
  pr1ᵉ coherent-unital-mul-Π-H-Spaceᵉ = mul-Π-H-Spaceᵉ
  pr2ᵉ coherent-unital-mul-Π-H-Spaceᵉ =
    coherent-unit-laws-mul-Π-H-Spaceᵉ

  Π-H-Spaceᵉ : H-Spaceᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ Π-H-Spaceᵉ = pointed-type-Π-H-Spaceᵉ
  pr2ᵉ Π-H-Spaceᵉ = coherent-unital-mul-Π-H-Spaceᵉ
```