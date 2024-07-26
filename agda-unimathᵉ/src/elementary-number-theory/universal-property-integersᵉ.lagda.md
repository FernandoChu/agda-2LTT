# The universal property of the integers

```agda
module elementary-number-theory.universal-property-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ universalᵉ propertyᵉ ofᵉ [theᵉ integers](elementary-number-theory.integers.mdᵉ)
statesᵉ thatᵉ givenᵉ anyᵉ typeᵉ `X`ᵉ equippedᵉ with aᵉ pointᵉ `xᵉ : X`ᵉ andᵉ anᵉ
[automorphism](foundation.automorphisms.mdᵉ) `eᵉ : Xᵉ ≃ᵉ X`,ᵉ thereᵉ isᵉ aᵉ
[unique](foundation.contractible-types.mdᵉ) structureᵉ preservingᵉ mapᵉ fromᵉ `ℤ`ᵉ to
`X`.ᵉ

```agda
abstract
  elim-ℤᵉ :
    { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ)
    ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) →
    ( kᵉ : ℤᵉ) → Pᵉ kᵉ
  elim-ℤᵉ Pᵉ p0ᵉ pSᵉ (inlᵉ zero-ℕᵉ) =
    map-inv-is-equivᵉ (is-equiv-map-equivᵉ (pSᵉ neg-one-ℤᵉ)) p0ᵉ
  elim-ℤᵉ Pᵉ p0ᵉ pSᵉ (inlᵉ (succ-ℕᵉ xᵉ)) =
    map-inv-is-equivᵉ
      ( is-equiv-map-equivᵉ (pSᵉ (inlᵉ (succ-ℕᵉ xᵉ))))
      ( elim-ℤᵉ Pᵉ p0ᵉ pSᵉ (inlᵉ xᵉ))
  elim-ℤᵉ Pᵉ p0ᵉ pSᵉ (inrᵉ (inlᵉ _)) = p0ᵉ
  elim-ℤᵉ Pᵉ p0ᵉ pSᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) = map-equivᵉ (pSᵉ zero-ℤᵉ) p0ᵉ
  elim-ℤᵉ Pᵉ p0ᵉ pSᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) =
    map-equivᵉ
      ( pSᵉ (inrᵉ (inrᵉ xᵉ)))
      ( elim-ℤᵉ Pᵉ p0ᵉ pSᵉ (inrᵉ (inrᵉ xᵉ)))

  compute-zero-elim-ℤᵉ :
    { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ)
    ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) →
    Idᵉ (elim-ℤᵉ Pᵉ p0ᵉ pSᵉ zero-ℤᵉ) p0ᵉ
  compute-zero-elim-ℤᵉ Pᵉ p0ᵉ pSᵉ = reflᵉ

  compute-succ-elim-ℤᵉ :
    { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ)
    ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) (kᵉ : ℤᵉ) →
    Idᵉ (elim-ℤᵉ Pᵉ p0ᵉ pSᵉ (succ-ℤᵉ kᵉ)) (map-equivᵉ (pSᵉ kᵉ) (elim-ℤᵉ Pᵉ p0ᵉ pSᵉ kᵉ))
  compute-succ-elim-ℤᵉ Pᵉ p0ᵉ pSᵉ (inlᵉ zero-ℕᵉ) =
    invᵉ
      ( is-section-map-inv-is-equivᵉ
        ( is-equiv-map-equivᵉ (pSᵉ (inlᵉ zero-ℕᵉ)))
        ( elim-ℤᵉ Pᵉ p0ᵉ pSᵉ (succ-ℤᵉ (inlᵉ zero-ℕᵉ))))
  compute-succ-elim-ℤᵉ Pᵉ p0ᵉ pSᵉ (inlᵉ (succ-ℕᵉ xᵉ)) =
    invᵉ
      ( is-section-map-inv-is-equivᵉ
        ( is-equiv-map-equivᵉ (pSᵉ (inlᵉ (succ-ℕᵉ xᵉ))))
        ( elim-ℤᵉ Pᵉ p0ᵉ pSᵉ (succ-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)))))
  compute-succ-elim-ℤᵉ Pᵉ p0ᵉ pSᵉ (inrᵉ (inlᵉ _)) = reflᵉ
  compute-succ-elim-ℤᵉ Pᵉ p0ᵉ pSᵉ (inrᵉ (inrᵉ _)) = reflᵉ

ELIM-ℤᵉ :
  { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ)
  ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) → UUᵉ l1ᵉ
ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ =
  Σᵉ ( (kᵉ : ℤᵉ) → Pᵉ kᵉ)
    ( λ fᵉ →
      ( ( Idᵉ (fᵉ zero-ℤᵉ) p0ᵉ) ×ᵉ
        ( (kᵉ : ℤᵉ) → Idᵉ (fᵉ (succ-ℤᵉ kᵉ)) ((map-equivᵉ (pSᵉ kᵉ)) (fᵉ kᵉ)))))

Elim-ℤᵉ :
  { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ)
  ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) → ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ
pr1ᵉ (Elim-ℤᵉ Pᵉ p0ᵉ pSᵉ) = elim-ℤᵉ Pᵉ p0ᵉ pSᵉ
pr1ᵉ (pr2ᵉ (Elim-ℤᵉ Pᵉ p0ᵉ pSᵉ)) = compute-zero-elim-ℤᵉ Pᵉ p0ᵉ pSᵉ
pr2ᵉ (pr2ᵉ (Elim-ℤᵉ Pᵉ p0ᵉ pSᵉ)) = compute-succ-elim-ℤᵉ Pᵉ p0ᵉ pSᵉ

equiv-comparison-map-Eq-ELIM-ℤᵉ :
  { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ)
  ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) →
  ( sᵉ tᵉ : ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ) (kᵉ : ℤᵉ) →
  Idᵉ ((pr1ᵉ sᵉ) kᵉ) ((pr1ᵉ tᵉ) kᵉ) ≃ᵉ Idᵉ ((pr1ᵉ sᵉ) (succ-ℤᵉ kᵉ)) ((pr1ᵉ tᵉ) (succ-ℤᵉ kᵉ))
equiv-comparison-map-Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ tᵉ kᵉ =
  ( ( equiv-concatᵉ (pr2ᵉ (pr2ᵉ sᵉ) kᵉ) (pr1ᵉ tᵉ (succ-ℤᵉ kᵉ))) ∘eᵉ
    ( equiv-concat'ᵉ (map-equivᵉ (pSᵉ kᵉ) (pr1ᵉ sᵉ kᵉ)) (invᵉ (pr2ᵉ (pr2ᵉ tᵉ) kᵉ)))) ∘eᵉ
  ( equiv-apᵉ (pSᵉ kᵉ) (pr1ᵉ sᵉ kᵉ) (pr1ᵉ tᵉ kᵉ))

zero-Eq-ELIM-ℤᵉ :
  { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ)
  ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) →
  ( sᵉ tᵉ : ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ) (Hᵉ : (pr1ᵉ sᵉ) ~ᵉ (pr1ᵉ tᵉ)) → UUᵉ l1ᵉ
zero-Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ tᵉ Hᵉ =
  Idᵉ (Hᵉ zero-ℤᵉ) ((pr1ᵉ (pr2ᵉ sᵉ)) ∙ᵉ (invᵉ (pr1ᵉ (pr2ᵉ tᵉ))))

succ-Eq-ELIM-ℤᵉ :
  { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ)
  ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) →
  ( sᵉ tᵉ : ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ) (Hᵉ : (pr1ᵉ sᵉ) ~ᵉ (pr1ᵉ tᵉ)) → UUᵉ l1ᵉ
succ-Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ tᵉ Hᵉ =
  ( kᵉ : ℤᵉ) →
  Idᵉ
    ( Hᵉ (succ-ℤᵉ kᵉ))
    ( map-equivᵉ (equiv-comparison-map-Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ tᵉ kᵉ) (Hᵉ kᵉ))

Eq-ELIM-ℤᵉ :
  { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ)
  ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) →
  ( sᵉ tᵉ : ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ) → UUᵉ l1ᵉ
Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ tᵉ =
  ELIM-ℤᵉ
    ( λ kᵉ → Idᵉ (pr1ᵉ sᵉ kᵉ) (pr1ᵉ tᵉ kᵉ))
    ( (pr1ᵉ (pr2ᵉ sᵉ)) ∙ᵉ (invᵉ (pr1ᵉ (pr2ᵉ tᵉ))))
    ( equiv-comparison-map-Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ tᵉ)

reflexive-Eq-ELIM-ℤᵉ :
  { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ)
  ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) →
  ( sᵉ : ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ) → Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ sᵉ
pr1ᵉ (reflexive-Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ (fᵉ ,ᵉ pᵉ ,ᵉ Hᵉ)) = refl-htpyᵉ
pr1ᵉ (pr2ᵉ (reflexive-Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ (fᵉ ,ᵉ pᵉ ,ᵉ Hᵉ))) = invᵉ (right-invᵉ pᵉ)
pr2ᵉ (pr2ᵉ (reflexive-Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ (fᵉ ,ᵉ pᵉ ,ᵉ Hᵉ))) = invᵉ ∘ᵉ (right-invᵉ ∘ᵉ Hᵉ)

Eq-ELIM-ℤ-eqᵉ :
  { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ) →
  ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) →
  ( sᵉ tᵉ : ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ) → Idᵉ sᵉ tᵉ → Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ tᵉ
Eq-ELIM-ℤ-eqᵉ Pᵉ p0ᵉ pSᵉ sᵉ .sᵉ reflᵉ = reflexive-Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ

abstract
  is-torsorial-Eq-ELIM-ℤᵉ :
    { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ) →
    ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) →
    ( sᵉ : ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ) → is-torsorialᵉ (Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ)
  is-torsorial-Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (pr1ᵉ sᵉ))
      ( pairᵉ (pr1ᵉ sᵉ) refl-htpyᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-contr-is-equiv'ᵉ
          ( Σᵉ (Idᵉ (pr1ᵉ sᵉ zero-ℤᵉ) p0ᵉ) (λ αᵉ → Idᵉ αᵉ (pr1ᵉ (pr2ᵉ sᵉ))))
          ( totᵉ (λ αᵉ → right-transpose-eq-concatᵉ reflᵉ αᵉ (pr1ᵉ (pr2ᵉ sᵉ))))
          ( is-equiv-tot-is-fiberwise-equivᵉ
            ( λ αᵉ → is-equiv-right-transpose-eq-concatᵉ reflᵉ αᵉ (pr1ᵉ (pr2ᵉ sᵉ))))
          ( is-torsorial-Id'ᵉ (pr1ᵉ (pr2ᵉ sᵉ))))
        ( pairᵉ (pr1ᵉ (pr2ᵉ sᵉ)) (invᵉ (right-invᵉ (pr1ᵉ (pr2ᵉ sᵉ)))))
        ( is-contr-is-equiv'ᵉ
          ( Σᵉ ( ( kᵉ : ℤᵉ) → Idᵉ (pr1ᵉ sᵉ (succ-ℤᵉ kᵉ)) (pr1ᵉ (pSᵉ kᵉ) (pr1ᵉ sᵉ kᵉ)))
              ( λ βᵉ → βᵉ ~ᵉ (pr2ᵉ (pr2ᵉ sᵉ))))
          ( totᵉ (λ βᵉ → right-transpose-htpy-concatᵉ refl-htpyᵉ βᵉ (pr2ᵉ (pr2ᵉ sᵉ))))
          ( is-equiv-tot-is-fiberwise-equivᵉ
            ( λ βᵉ →
              is-equiv-right-transpose-htpy-concatᵉ refl-htpyᵉ βᵉ (pr2ᵉ (pr2ᵉ sᵉ))))
          ( is-torsorial-htpy'ᵉ (pr2ᵉ (pr2ᵉ sᵉ)))))

abstract
  is-equiv-Eq-ELIM-ℤ-eqᵉ :
    { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ) →
    ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) →
    ( sᵉ tᵉ : ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ) → is-equivᵉ (Eq-ELIM-ℤ-eqᵉ Pᵉ p0ᵉ pSᵉ sᵉ tᵉ)
  is-equiv-Eq-ELIM-ℤ-eqᵉ Pᵉ p0ᵉ pSᵉ sᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ)
      ( Eq-ELIM-ℤ-eqᵉ Pᵉ p0ᵉ pSᵉ sᵉ)

eq-Eq-ELIM-ℤᵉ :
  { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ) →
  ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) →
  ( sᵉ tᵉ : ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ) → Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ tᵉ → Idᵉ sᵉ tᵉ
eq-Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ tᵉ = map-inv-is-equivᵉ (is-equiv-Eq-ELIM-ℤ-eqᵉ Pᵉ p0ᵉ pSᵉ sᵉ tᵉ)

abstract
  is-prop-ELIM-ℤᵉ :
    { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ) →
    ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) →
    is-propᵉ (ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ)
  is-prop-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ =
    is-prop-all-elements-equalᵉ
      ( λ sᵉ tᵉ → eq-Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ tᵉ
        ( Elim-ℤᵉ
          ( λ kᵉ → Idᵉ (pr1ᵉ sᵉ kᵉ) (pr1ᵉ tᵉ kᵉ))
          ( (pr1ᵉ (pr2ᵉ sᵉ)) ∙ᵉ (invᵉ (pr1ᵉ (pr2ᵉ tᵉ))))
          ( equiv-comparison-map-Eq-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ sᵉ tᵉ)))
```

### The dependent universal property of the integers

```agda
abstract
  is-contr-ELIM-ℤᵉ :
    { l1ᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ l1ᵉ) →
    ( p0ᵉ : Pᵉ zero-ℤᵉ) (pSᵉ : (kᵉ : ℤᵉ) → (Pᵉ kᵉ) ≃ᵉ (Pᵉ (succ-ℤᵉ kᵉ))) →
    is-contrᵉ (ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ)
  is-contr-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ =
    is-proof-irrelevant-is-propᵉ (is-prop-ELIM-ℤᵉ Pᵉ p0ᵉ pSᵉ) (Elim-ℤᵉ Pᵉ p0ᵉ pSᵉ)
```

### The universal property of the integers

Theᵉ nondependentᵉ universalᵉ propertyᵉ ofᵉ theᵉ integersᵉ isᵉ aᵉ specialᵉ caseᵉ ofᵉ theᵉ
dependentᵉ universalᵉ propertyᵉ appliedᵉ to constantᵉ typeᵉ families.ᵉ

```agda
ELIM-ℤ'ᵉ :
  { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (xᵉ : Xᵉ) (eᵉ : Xᵉ ≃ᵉ Xᵉ) → UUᵉ l1ᵉ
ELIM-ℤ'ᵉ {Xᵉ = Xᵉ} xᵉ eᵉ = ELIM-ℤᵉ (λ kᵉ → Xᵉ) xᵉ (λ kᵉ → eᵉ)

abstract
  universal-property-ℤᵉ :
    { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (xᵉ : Xᵉ) (eᵉ : Xᵉ ≃ᵉ Xᵉ) → is-contrᵉ (ELIM-ℤ'ᵉ xᵉ eᵉ)
  universal-property-ℤᵉ {Xᵉ = Xᵉ} xᵉ eᵉ = is-contr-ELIM-ℤᵉ (λ kᵉ → Xᵉ) xᵉ (λ kᵉ → eᵉ)
```