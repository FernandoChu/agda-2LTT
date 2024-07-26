# The universal property of the natural numbers

```agda
module elementary-number-theory.universal-property-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ
```

</details>

## Idea

Theᵉ universalᵉ propertyᵉ ofᵉ theᵉ naturalᵉ numbersᵉ assertsᵉ thatᵉ forᵉ anyᵉ typeᵉ `X`ᵉ
equippedᵉ with aᵉ pointᵉ `xᵉ : X`ᵉ andᵉ anᵉ endomorphismᵉ `fᵉ : Xᵉ → X`,ᵉ theᵉ typeᵉ ofᵉ
structureᵉ preservingᵉ mapsᵉ fromᵉ `ℕ`ᵉ to `X`ᵉ isᵉ contractible.ᵉ

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (xᵉ : Xᵉ) (fᵉ : Xᵉ → Xᵉ)
  where

  structure-preserving-map-ℕᵉ : UUᵉ lᵉ
  structure-preserving-map-ℕᵉ =
    Σᵉ (ℕᵉ → Xᵉ) (λ hᵉ → (hᵉ zero-ℕᵉ ＝ᵉ xᵉ) ×ᵉ ((hᵉ ∘ᵉ succ-ℕᵉ) ~ᵉ (fᵉ ∘ᵉ hᵉ)))

  htpy-structure-preserving-map-ℕᵉ :
    (hᵉ kᵉ : structure-preserving-map-ℕᵉ) → UUᵉ lᵉ
  htpy-structure-preserving-map-ℕᵉ hᵉ kᵉ =
    Σᵉ ( pr1ᵉ hᵉ ~ᵉ pr1ᵉ kᵉ)
      ( λ Hᵉ →
        ( pr1ᵉ (pr2ᵉ hᵉ) ＝ᵉ (Hᵉ zero-ℕᵉ ∙ᵉ pr1ᵉ (pr2ᵉ kᵉ))) ×ᵉ
        ( (nᵉ : ℕᵉ) →
          (pr2ᵉ (pr2ᵉ hᵉ) nᵉ ∙ᵉ apᵉ fᵉ (Hᵉ nᵉ)) ＝ᵉ (Hᵉ (succ-ℕᵉ nᵉ) ∙ᵉ pr2ᵉ (pr2ᵉ kᵉ) nᵉ)))

  refl-htpy-structure-preserving-map-ℕᵉ :
    (hᵉ : structure-preserving-map-ℕᵉ) → htpy-structure-preserving-map-ℕᵉ hᵉ hᵉ
  refl-htpy-structure-preserving-map-ℕᵉ hᵉ =
    tripleᵉ refl-htpyᵉ reflᵉ (λ nᵉ → right-unitᵉ)

  htpy-eq-structure-preserving-map-ℕᵉ :
    {hᵉ kᵉ : structure-preserving-map-ℕᵉ} → hᵉ ＝ᵉ kᵉ →
    htpy-structure-preserving-map-ℕᵉ hᵉ kᵉ
  htpy-eq-structure-preserving-map-ℕᵉ {hᵉ} reflᵉ =
    refl-htpy-structure-preserving-map-ℕᵉ hᵉ

  is-torsorial-htpy-structure-preserving-map-ℕᵉ :
    (hᵉ : structure-preserving-map-ℕᵉ) →
    is-torsorialᵉ (htpy-structure-preserving-map-ℕᵉ hᵉ)
  is-torsorial-htpy-structure-preserving-map-ℕᵉ hᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (pr1ᵉ hᵉ))
      ( pairᵉ (pr1ᵉ hᵉ) refl-htpyᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-Idᵉ (pr1ᵉ (pr2ᵉ hᵉ)))
        ( pairᵉ (pr1ᵉ (pr2ᵉ hᵉ)) reflᵉ)
        ( is-torsorial-htpyᵉ (λ nᵉ → (pr2ᵉ (pr2ᵉ hᵉ) nᵉ ∙ᵉ reflᵉ))))

  is-equiv-htpy-eq-structure-preserving-map-ℕᵉ :
    (hᵉ kᵉ : structure-preserving-map-ℕᵉ) →
    is-equivᵉ (htpy-eq-structure-preserving-map-ℕᵉ {hᵉ} {kᵉ})
  is-equiv-htpy-eq-structure-preserving-map-ℕᵉ hᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-structure-preserving-map-ℕᵉ hᵉ)
      ( λ kᵉ → htpy-eq-structure-preserving-map-ℕᵉ {hᵉ} {kᵉ})

  eq-htpy-structure-preserving-map-ℕᵉ :
    {hᵉ kᵉ : structure-preserving-map-ℕᵉ} →
    htpy-structure-preserving-map-ℕᵉ hᵉ kᵉ → hᵉ ＝ᵉ kᵉ
  eq-htpy-structure-preserving-map-ℕᵉ {hᵉ} {kᵉ} =
    map-inv-is-equivᵉ (is-equiv-htpy-eq-structure-preserving-map-ℕᵉ hᵉ kᵉ)

  center-structure-preserving-map-ℕᵉ : structure-preserving-map-ℕᵉ
  pr1ᵉ center-structure-preserving-map-ℕᵉ =
    hᵉ
    where
    hᵉ : ℕᵉ → Xᵉ
    hᵉ zero-ℕᵉ = xᵉ
    hᵉ (succ-ℕᵉ nᵉ) = fᵉ (hᵉ nᵉ)
  pr1ᵉ (pr2ᵉ center-structure-preserving-map-ℕᵉ) = reflᵉ
  pr2ᵉ (pr2ᵉ center-structure-preserving-map-ℕᵉ) = refl-htpyᵉ

  contraction-structure-preserving-map-ℕᵉ :
    (hᵉ : structure-preserving-map-ℕᵉ) → center-structure-preserving-map-ℕᵉ ＝ᵉ hᵉ
  contraction-structure-preserving-map-ℕᵉ hᵉ =
    eq-htpy-structure-preserving-map-ℕᵉ (tripleᵉ αᵉ βᵉ γᵉ)
    where
    αᵉ : pr1ᵉ center-structure-preserving-map-ℕᵉ ~ᵉ pr1ᵉ hᵉ
    αᵉ zero-ℕᵉ = invᵉ (pr1ᵉ (pr2ᵉ hᵉ))
    αᵉ (succ-ℕᵉ nᵉ) = apᵉ fᵉ (αᵉ nᵉ) ∙ᵉ invᵉ (pr2ᵉ (pr2ᵉ hᵉ) nᵉ)
    βᵉ : pr1ᵉ (pr2ᵉ center-structure-preserving-map-ℕᵉ) ＝ᵉ (αᵉ zero-ℕᵉ ∙ᵉ pr1ᵉ (pr2ᵉ hᵉ))
    βᵉ = invᵉ (left-invᵉ (pr1ᵉ (pr2ᵉ hᵉ)))
    γᵉ :
      (nᵉ : ℕᵉ) →
      ( pr2ᵉ (pr2ᵉ center-structure-preserving-map-ℕᵉ) nᵉ ∙ᵉ apᵉ fᵉ (αᵉ nᵉ)) ＝ᵉ
      ( αᵉ (succ-ℕᵉ nᵉ) ∙ᵉ pr2ᵉ (pr2ᵉ hᵉ) nᵉ)
    γᵉ nᵉ = ( ( invᵉ right-unitᵉ) ∙ᵉ
            ( left-whisker-concatᵉ
              ( apᵉ fᵉ (αᵉ nᵉ))
              ( invᵉ (left-invᵉ (pr2ᵉ (pr2ᵉ hᵉ) nᵉ))))) ∙ᵉ
          ( invᵉ
            ( assocᵉ (apᵉ fᵉ (αᵉ nᵉ)) (invᵉ (pr2ᵉ (pr2ᵉ hᵉ) nᵉ)) (pr2ᵉ (pr2ᵉ hᵉ) nᵉ)))

  is-contr-structure-preserving-map-ℕᵉ : is-contrᵉ structure-preserving-map-ℕᵉ
  pr1ᵉ is-contr-structure-preserving-map-ℕᵉ = center-structure-preserving-map-ℕᵉ
  pr2ᵉ is-contr-structure-preserving-map-ℕᵉ =
    contraction-structure-preserving-map-ℕᵉ
```