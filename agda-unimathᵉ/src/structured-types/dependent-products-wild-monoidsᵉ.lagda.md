# Dependent products of wild monoids

```agda
module structured-types.dependent-products-wild-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import structured-types.dependent-products-h-spacesᵉ
open import structured-types.h-spacesᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.wild-monoidsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ [wildᵉ monoids](structured-types.wild-monoids.mdᵉ) `Mᵢ`ᵉ indexedᵉ
byᵉ `iᵉ : I`,ᵉ theᵉ dependentᵉ productᵉ `Π(iᵉ : I),ᵉ Mᵢ`ᵉ isᵉ aᵉ wildᵉ monoidᵉ consistingᵉ ofᵉ
dependentᵉ functionsᵉ takingᵉ `iᵉ : I`ᵉ to anᵉ elementᵉ ofᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `Mᵢ`.ᵉ
Everyᵉ componentᵉ ofᵉ theᵉ structureᵉ isᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Mᵉ : Iᵉ → Wild-Monoidᵉ l2ᵉ)
  where

  h-space-Π-Wild-Monoidᵉ : H-Spaceᵉ (l1ᵉ ⊔ l2ᵉ)
  h-space-Π-Wild-Monoidᵉ =
    Π-H-Spaceᵉ Iᵉ (λ iᵉ → h-space-Wild-Monoidᵉ (Mᵉ iᵉ))

  pointed-type-Π-Wild-Monoidᵉ : Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  pointed-type-Π-Wild-Monoidᵉ =
    pointed-type-H-Spaceᵉ h-space-Π-Wild-Monoidᵉ

  type-Π-Wild-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Π-Wild-Monoidᵉ = type-H-Spaceᵉ h-space-Π-Wild-Monoidᵉ

  unit-Π-Wild-Monoidᵉ : type-Π-Wild-Monoidᵉ
  unit-Π-Wild-Monoidᵉ = unit-H-Spaceᵉ h-space-Π-Wild-Monoidᵉ

  mul-Π-Wild-Monoidᵉ :
    type-Π-Wild-Monoidᵉ → type-Π-Wild-Monoidᵉ → type-Π-Wild-Monoidᵉ
  mul-Π-Wild-Monoidᵉ = mul-H-Spaceᵉ h-space-Π-Wild-Monoidᵉ

  left-unit-law-mul-Π-Wild-Monoidᵉ :
    (fᵉ : type-Π-Wild-Monoidᵉ) → (mul-Π-Wild-Monoidᵉ (unit-Π-Wild-Monoidᵉ) fᵉ) ＝ᵉ fᵉ
  left-unit-law-mul-Π-Wild-Monoidᵉ =
    left-unit-law-mul-H-Spaceᵉ h-space-Π-Wild-Monoidᵉ

  right-unit-law-mul-Π-Wild-Monoidᵉ :
    (fᵉ : type-Π-Wild-Monoidᵉ) → (mul-Π-Wild-Monoidᵉ fᵉ (unit-Π-Wild-Monoidᵉ)) ＝ᵉ fᵉ
  right-unit-law-mul-Π-Wild-Monoidᵉ =
    right-unit-law-mul-H-Spaceᵉ h-space-Π-Wild-Monoidᵉ

  associator-Π-Wild-Monoidᵉ :
    associator-H-Spaceᵉ h-space-Π-Wild-Monoidᵉ
  associator-Π-Wild-Monoidᵉ fᵉ gᵉ hᵉ =
    eq-htpyᵉ (λ iᵉ → associator-Wild-Monoidᵉ (Mᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ) (hᵉ iᵉ))

  unital-associator-Π-Wild-Monoidᵉ :
    unital-associatorᵉ h-space-Π-Wild-Monoidᵉ
  pr1ᵉ unital-associator-Π-Wild-Monoidᵉ = associator-Π-Wild-Monoidᵉ
  pr1ᵉ (pr2ᵉ unital-associator-Π-Wild-Monoidᵉ) gᵉ hᵉ =
    ( invᵉ
      ( eq-htpy-concat-htpyᵉ
        ( λ iᵉ → associator-Wild-Monoidᵉ (Mᵉ iᵉ) (unit-Π-Wild-Monoidᵉ iᵉ) (gᵉ iᵉ) (hᵉ iᵉ))
        ( λ iᵉ →
          left-unit-law-mul-Wild-Monoidᵉ (Mᵉ iᵉ) (mul-Π-Wild-Monoidᵉ gᵉ hᵉ iᵉ)))) ∙ᵉ
    ( apᵉ
      ( eq-htpyᵉ)
      ( eq-htpyᵉ
        ( λ iᵉ →
          pr1ᵉ (pr2ᵉ (unital-associator-Wild-Monoidᵉ (Mᵉ iᵉ))) (gᵉ iᵉ) (hᵉ iᵉ)))) ∙ᵉ
    ( compute-eq-htpy-apᵉ (λ iᵉ → left-unit-law-mul-Wild-Monoidᵉ (Mᵉ iᵉ) (gᵉ iᵉ)))
  pr1ᵉ (pr2ᵉ (pr2ᵉ unital-associator-Π-Wild-Monoidᵉ)) fᵉ hᵉ =
    ( apᵉ
      ( associator-Π-Wild-Monoidᵉ fᵉ unit-Π-Wild-Monoidᵉ hᵉ ∙ᵉ_)
      ( invᵉ
        ( compute-eq-htpy-apᵉ
          ( λ iᵉ → left-unit-law-mul-Wild-Monoidᵉ (Mᵉ iᵉ) (hᵉ iᵉ))))) ∙ᵉ
    ( invᵉ
      ( eq-htpy-concat-htpyᵉ
        ( λ iᵉ →
          associator-Wild-Monoidᵉ (Mᵉ iᵉ) (fᵉ iᵉ) (unit-Π-Wild-Monoidᵉ iᵉ) (hᵉ iᵉ))
        ( λ iᵉ →
          apᵉ
            ( mul-Wild-Monoidᵉ (Mᵉ iᵉ) (fᵉ iᵉ))
            ( left-unit-law-mul-Wild-Monoidᵉ (Mᵉ iᵉ) (hᵉ iᵉ))))) ∙ᵉ
    ( apᵉ
      ( eq-htpyᵉ)
      ( eq-htpyᵉ
        ( λ iᵉ →
          pr1ᵉ (pr2ᵉ (pr2ᵉ (unital-associator-Wild-Monoidᵉ (Mᵉ iᵉ)))) (fᵉ iᵉ) (hᵉ iᵉ)))) ∙ᵉ
    ( compute-eq-htpy-apᵉ (λ iᵉ → right-unit-law-mul-Wild-Monoidᵉ (Mᵉ iᵉ) (fᵉ iᵉ)))
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ unital-associator-Π-Wild-Monoidᵉ))) fᵉ gᵉ =
    ( apᵉ
      ( associator-Π-Wild-Monoidᵉ fᵉ gᵉ unit-Π-Wild-Monoidᵉ ∙ᵉ_)
      ( invᵉ
        ( compute-eq-htpy-apᵉ
          ( λ iᵉ → right-unit-law-mul-Wild-Monoidᵉ (Mᵉ iᵉ) (gᵉ iᵉ))))) ∙ᵉ
    ( invᵉ
      ( eq-htpy-concat-htpyᵉ
        ( λ iᵉ → associator-Wild-Monoidᵉ (Mᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ) (unit-Π-Wild-Monoidᵉ iᵉ))
        ( λ iᵉ →
          apᵉ
            ( mul-Wild-Monoidᵉ (Mᵉ iᵉ) (fᵉ iᵉ))
            ( right-unit-law-mul-Wild-Monoidᵉ (Mᵉ iᵉ) (gᵉ iᵉ))))) ∙ᵉ
    ( apᵉ
      ( eq-htpyᵉ)
      ( eq-htpyᵉ
        ( λ iᵉ →
          pr1ᵉ
            ( pr2ᵉ (pr2ᵉ (pr2ᵉ (unital-associator-Wild-Monoidᵉ (Mᵉ iᵉ)))))
            ( fᵉ iᵉ)
            ( gᵉ iᵉ))))
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ unital-associator-Π-Wild-Monoidᵉ))) = starᵉ

  Π-Wild-Monoidᵉ : Wild-Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ Π-Wild-Monoidᵉ = h-space-Π-Wild-Monoidᵉ
  pr2ᵉ Π-Wild-Monoidᵉ = unital-associator-Π-Wild-Monoidᵉ
```