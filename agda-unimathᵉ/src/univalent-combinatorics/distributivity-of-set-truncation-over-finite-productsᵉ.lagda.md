# Distributivity of set truncation over finite products

```agda
module univalent-combinatorics.distributivity-of-set-truncation-over-finite-productsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-function-typesᵉ
open import foundation.functoriality-set-truncationᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.precomposition-dependent-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.set-truncationsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universal-property-empty-typeᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universal-property-maybeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Theorem

`trunc-Set`ᵉ distributesᵉ overᵉ `Π`ᵉ indexedᵉ byᵉ `Fin`.ᵉ

```agda
abstract
  distributive-trunc-Π-Fin-Setᵉ :
    {lᵉ : Level} (kᵉ : ℕᵉ) (Aᵉ : Finᵉ kᵉ → UUᵉ lᵉ) →
    is-contrᵉ
      ( Σᵉ ( ( type-trunc-Setᵉ ((xᵉ : Finᵉ kᵉ) → Aᵉ xᵉ)) ≃ᵉ
            ( (xᵉ : Finᵉ kᵉ) → type-trunc-Setᵉ (Aᵉ xᵉ)))
          ( λ eᵉ →
            ( map-equivᵉ eᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
            ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ))))
  distributive-trunc-Π-Fin-Setᵉ zero-ℕᵉ Aᵉ =
    uniqueness-trunc-Setᵉ
      ( Π-Setᵉ empty-Setᵉ (λ xᵉ → trunc-Setᵉ (Aᵉ xᵉ)))
      ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ))
      ( λ {lᵉ} Bᵉ →
        is-equiv-precomp-is-equivᵉ
          ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ))
          ( is-equiv-is-contrᵉ
            ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ))
            ( dependent-universal-property-empty'ᵉ Aᵉ)
            ( dependent-universal-property-empty'ᵉ (type-trunc-Setᵉ ∘ᵉ Aᵉ)))
          ( type-Setᵉ Bᵉ))
  distributive-trunc-Π-Fin-Setᵉ (succ-ℕᵉ kᵉ) Aᵉ =
    uniqueness-trunc-Setᵉ
      ( Π-Setᵉ (Fin-Setᵉ (succ-ℕᵉ kᵉ)) (λ xᵉ → trunc-Setᵉ (Aᵉ xᵉ)))
      ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ))
      ( λ {lᵉ} Bᵉ →
        is-equiv-left-factorᵉ
          ( precompᵉ (map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ)) (type-Setᵉ Bᵉ))
          ( precompᵉ (ev-Maybeᵉ {Bᵉ = type-trunc-Setᵉ ∘ᵉ Aᵉ}) (type-Setᵉ Bᵉ))
          ( is-equiv-compᵉ
            ( precompᵉ ev-Maybeᵉ (type-Setᵉ Bᵉ))
            ( precompᵉ
              ( map-productᵉ (map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ)) unit-trunc-Setᵉ)
              ( type-Setᵉ Bᵉ))
            ( is-equiv-right-factorᵉ
              ( ev-pairᵉ)
              ( precompᵉ
                ( map-productᵉ (map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ)) unit-trunc-Setᵉ)
                ( type-Setᵉ Bᵉ))
              ( is-equiv-ev-pairᵉ)
              ( is-equiv-map-equivᵉ
                ( ( ( pairᵉ
                      ( precompᵉ
                        ( (map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ)))
                        ( Aᵉ (inrᵉ starᵉ) → type-Setᵉ Bᵉ))
                      ( is-set-truncation-is-equivᵉ
                        ( Π-Setᵉ (Fin-Setᵉ kᵉ) (λ xᵉ → trunc-Setᵉ (Aᵉ (inlᵉ xᵉ))))
                        ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ))
                        ( pr2ᵉ
                          ( centerᵉ (distributive-trunc-Π-Fin-Setᵉ kᵉ (Aᵉ ∘ᵉ inlᵉ))))
                        ( is-equiv-map-equivᵉ
                          ( pr1ᵉ
                            ( centerᵉ
                              ( distributive-trunc-Π-Fin-Setᵉ kᵉ (Aᵉ ∘ᵉ inlᵉ)))))
                        ( Π-Set'ᵉ (Aᵉ (inrᵉ starᵉ)) (λ aᵉ → Bᵉ)))) ∘eᵉ
                    ( equiv-postcompᵉ
                      ( (xᵉ : Finᵉ kᵉ) → type-trunc-Setᵉ (Aᵉ (inlᵉ xᵉ)))
                      ( equiv-universal-property-trunc-Setᵉ Bᵉ))) ∘eᵉ
                  ( equiv-ev-pairᵉ))))
            ( is-equiv-precomp-is-equivᵉ
              ( ev-Maybeᵉ)
              ( dependent-universal-property-Maybeᵉ)
              ( type-Setᵉ Bᵉ)))
          ( is-equiv-precomp-is-equivᵉ
            ( ev-Maybeᵉ)
            ( dependent-universal-property-Maybeᵉ)
            ( type-Setᵉ Bᵉ)))

module _
  {lᵉ : Level} (kᵉ : ℕᵉ) (Aᵉ : Finᵉ kᵉ → UUᵉ lᵉ)
  where

  equiv-distributive-trunc-Π-Fin-Setᵉ :
    type-trunc-Setᵉ ((xᵉ : Finᵉ kᵉ) → Aᵉ xᵉ) ≃ᵉ ((xᵉ : Finᵉ kᵉ) → type-trunc-Setᵉ (Aᵉ xᵉ))
  equiv-distributive-trunc-Π-Fin-Setᵉ =
    pr1ᵉ (centerᵉ (distributive-trunc-Π-Fin-Setᵉ kᵉ Aᵉ))

  map-equiv-distributive-trunc-Π-Fin-Setᵉ :
    type-trunc-Setᵉ ((xᵉ : Finᵉ kᵉ) → Aᵉ xᵉ) → ((xᵉ : Finᵉ kᵉ) → type-trunc-Setᵉ (Aᵉ xᵉ))
  map-equiv-distributive-trunc-Π-Fin-Setᵉ =
    map-equivᵉ equiv-distributive-trunc-Π-Fin-Setᵉ

  triangle-distributive-trunc-Π-Fin-Setᵉ :
    ( map-equiv-distributive-trunc-Π-Fin-Setᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
    ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ))
  triangle-distributive-trunc-Π-Fin-Setᵉ =
    pr2ᵉ (centerᵉ (distributive-trunc-Π-Fin-Setᵉ kᵉ Aᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  abstract
    distributive-trunc-Π-count-Setᵉ :
      countᵉ Aᵉ →
      is-contrᵉ
        ( Σᵉ ( ( type-trunc-Setᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)) ≃ᵉ
              ( (xᵉ : Aᵉ) → type-trunc-Setᵉ (Bᵉ xᵉ)))
            ( λ eᵉ →
              ( map-equivᵉ eᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
              ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ))))
    distributive-trunc-Π-count-Setᵉ (pairᵉ kᵉ eᵉ) =
      is-contr-equivᵉ
        ( Σᵉ ( ( type-trunc-Setᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)) ≃ᵉ
              ( (xᵉ : Finᵉ kᵉ) → type-trunc-Setᵉ (Bᵉ (map-equivᵉ eᵉ xᵉ))))
            ( λ fᵉ →
              ( map-equivᵉ fᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
              ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ) ∘ᵉ precomp-Πᵉ (map-equivᵉ eᵉ) Bᵉ)))
        ( equiv-Σᵉ
          ( λ fᵉ →
            ( map-equivᵉ fᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
            ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ) ∘ᵉ precomp-Πᵉ (map-equivᵉ eᵉ) Bᵉ))
          ( equiv-postcomp-equivᵉ
            ( equiv-precomp-Πᵉ eᵉ (type-trunc-Setᵉ ∘ᵉ Bᵉ))
            ( type-trunc-Setᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)))
          ( λ fᵉ →
            equiv-Π-equiv-familyᵉ
              ( λ hᵉ →
                ( ( inv-equivᵉ equiv-funextᵉ) ∘eᵉ
                  ( equiv-precomp-Πᵉ eᵉ
                    ( λ xᵉ → Idᵉ ((map-equivᵉ fᵉ ∘ᵉ unit-trunc-Setᵉ) hᵉ xᵉ)
                    ( map-Πᵉ (λ yᵉ → unit-trunc-Setᵉ) hᵉ xᵉ)))) ∘eᵉ
                ( equiv-funextᵉ))))
        ( is-contr-equiv'ᵉ
          ( Σᵉ ( ( type-trunc-Setᵉ ((xᵉ : Finᵉ kᵉ) → Bᵉ (map-equivᵉ eᵉ xᵉ))) ≃ᵉ
                ( (xᵉ : Finᵉ kᵉ) → type-trunc-Setᵉ (Bᵉ (map-equivᵉ eᵉ xᵉ))))
              ( λ fᵉ →
                ( map-equivᵉ fᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
                ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ))))
          ( equiv-Σᵉ
            ( λ fᵉ →
              ( map-equivᵉ fᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
              ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ) ∘ᵉ precomp-Πᵉ (map-equivᵉ eᵉ) Bᵉ))
            ( equiv-precomp-equivᵉ
              ( equiv-trunc-Setᵉ (equiv-precomp-Πᵉ eᵉ Bᵉ))
              ( (xᵉ : Finᵉ kᵉ) → type-trunc-Setᵉ (Bᵉ (map-equivᵉ eᵉ xᵉ))))
            ( λ fᵉ →
              equiv-Πᵉ
                ( λ hᵉ →
                  Idᵉ
                    ( map-equivᵉ fᵉ
                      ( map-equivᵉ
                        ( equiv-trunc-Setᵉ (equiv-precomp-Πᵉ eᵉ Bᵉ))
                        ( unit-trunc-Setᵉ hᵉ)))
                    ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ) (λ xᵉ → hᵉ (map-equivᵉ eᵉ xᵉ))))
                ( equiv-Πᵉ Bᵉ eᵉ (λ xᵉ → id-equivᵉ))
                ( λ hᵉ →
                  ( ( inv-equivᵉ equiv-funextᵉ) ∘eᵉ
                    ( equiv-Πᵉ
                      ( λ xᵉ →
                        Idᵉ
                          ( map-equivᵉ fᵉ
                            ( map-equiv-trunc-Setᵉ
                              ( equiv-precomp-Πᵉ eᵉ Bᵉ)
                              ( unit-trunc-Setᵉ
                                ( map-equiv-Πᵉ Bᵉ eᵉ (λ xᵉ → id-equivᵉ) hᵉ)))
                            ( xᵉ))
                          ( unit-trunc-Setᵉ
                            ( map-equiv-Πᵉ Bᵉ eᵉ
                              ( λ zᵉ → id-equivᵉ)
                              ( hᵉ)
                              ( map-equivᵉ eᵉ xᵉ))))
                      ( id-equivᵉ)
                      ( λ xᵉ →
                        ( equiv-concatᵉ
                          ( apᵉ
                            ( λ tᵉ → map-equivᵉ fᵉ tᵉ xᵉ)
                            ( ( naturality-unit-trunc-Setᵉ
                                ( precomp-Πᵉ (map-equivᵉ eᵉ) Bᵉ)
                                ( map-equiv-Πᵉ Bᵉ eᵉ (λ _ → id-equivᵉ) hᵉ)) ∙ᵉ
                              ( apᵉ
                                ( unit-trunc-Setᵉ)
                                ( eq-htpyᵉ
                                  ( compute-map-equiv-Πᵉ Bᵉ eᵉ
                                    ( λ _ → id-equivᵉ)
                                    ( hᵉ))))))
                          ( unit-trunc-Setᵉ
                            ( map-equiv-Πᵉ Bᵉ eᵉ
                              ( λ _ → id-equivᵉ)
                              ( hᵉ)
                              ( map-equivᵉ eᵉ xᵉ)))) ∘eᵉ
                        ( equiv-concat'ᵉ
                          ( map-equivᵉ fᵉ (unit-trunc-Setᵉ hᵉ) xᵉ)
                          ( apᵉ unit-trunc-Setᵉ
                            ( invᵉ
                              ( compute-map-equiv-Πᵉ Bᵉ eᵉ
                                ( λ _ → id-equivᵉ)
                                ( hᵉ)
                                ( xᵉ)))))))) ∘eᵉ
                  ( equiv-funextᵉ))))
          ( distributive-trunc-Π-Fin-Setᵉ kᵉ (Bᵉ ∘ᵉ map-equivᵉ eᵉ)))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (cᵉ : countᵉ Aᵉ)
  where

  equiv-distributive-trunc-Π-count-Setᵉ :
    ( type-trunc-Setᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)) ≃ᵉ ((xᵉ : Aᵉ) → type-trunc-Setᵉ (Bᵉ xᵉ))
  equiv-distributive-trunc-Π-count-Setᵉ =
    pr1ᵉ (centerᵉ (distributive-trunc-Π-count-Setᵉ Bᵉ cᵉ))

  map-equiv-distributive-trunc-Π-count-Setᵉ :
    ( type-trunc-Setᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)) → ((xᵉ : Aᵉ) → type-trunc-Setᵉ (Bᵉ xᵉ))
  map-equiv-distributive-trunc-Π-count-Setᵉ =
    map-equivᵉ equiv-distributive-trunc-Π-count-Setᵉ

  triangle-distributive-trunc-Π-count-Setᵉ :
    ( map-equiv-distributive-trunc-Π-count-Setᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
    ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ))
  triangle-distributive-trunc-Π-count-Setᵉ =
    pr2ᵉ (centerᵉ (distributive-trunc-Π-count-Setᵉ Bᵉ cᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Hᵉ : is-finiteᵉ Aᵉ)
  where

  abstract
    distributive-trunc-Π-is-finite-Setᵉ :
      is-contrᵉ
        ( Σᵉ ( ( type-trunc-Setᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)) ≃ᵉ
              ( (xᵉ : Aᵉ) → type-trunc-Setᵉ (Bᵉ xᵉ)))
            ( λ eᵉ →
              ( map-equivᵉ eᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
              ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ))))
    distributive-trunc-Π-is-finite-Setᵉ =
      apply-universal-property-trunc-Propᵉ Hᵉ
        ( is-contr-Propᵉ _)
        ( distributive-trunc-Π-count-Setᵉ Bᵉ)

  equiv-distributive-trunc-Π-is-finite-Setᵉ :
    ( type-trunc-Setᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)) ≃ᵉ ((xᵉ : Aᵉ) → type-trunc-Setᵉ (Bᵉ xᵉ))
  equiv-distributive-trunc-Π-is-finite-Setᵉ =
    pr1ᵉ (centerᵉ distributive-trunc-Π-is-finite-Setᵉ)

  map-equiv-distributive-trunc-Π-is-finite-Setᵉ :
    ( type-trunc-Setᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)) → ((xᵉ : Aᵉ) → type-trunc-Setᵉ (Bᵉ xᵉ))
  map-equiv-distributive-trunc-Π-is-finite-Setᵉ =
    map-equivᵉ equiv-distributive-trunc-Π-is-finite-Setᵉ

  triangle-distributive-trunc-Π-is-finite-Setᵉ :
    ( map-equiv-distributive-trunc-Π-is-finite-Setᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
    ( map-Πᵉ (λ xᵉ → unit-trunc-Setᵉ))
  triangle-distributive-trunc-Π-is-finite-Setᵉ =
    pr2ᵉ (centerᵉ distributive-trunc-Π-is-finite-Setᵉ)
```