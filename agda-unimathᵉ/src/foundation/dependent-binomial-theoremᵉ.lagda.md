# The dependent binomial theorem for types (distributivity of dependent function types over coproduct types)

```agda
module foundation.dependent-binomial-theoremᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-decompositionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universal-property-coproduct-typesᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
open import foundation-core.univalenceᵉ

open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  fam-coproductᵉ :
    Finᵉ 2 → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  fam-coproductᵉ (inlᵉ (inrᵉ _)) = raiseᵉ l2ᵉ Aᵉ
  fam-coproductᵉ (inrᵉ _) = raiseᵉ l1ᵉ Bᵉ

  map-compute-total-fam-coproductᵉ :
    Σᵉ (Finᵉ 2ᵉ) fam-coproductᵉ → Aᵉ +ᵉ Bᵉ
  map-compute-total-fam-coproductᵉ (pairᵉ (inlᵉ (inrᵉ _)) yᵉ) = inlᵉ (map-inv-raiseᵉ yᵉ)
  map-compute-total-fam-coproductᵉ (pairᵉ (inrᵉ _) yᵉ) = inrᵉ (map-inv-raiseᵉ yᵉ)

  map-inv-compute-total-fam-coproductᵉ :
    Aᵉ +ᵉ Bᵉ → Σᵉ (Finᵉ 2ᵉ) fam-coproductᵉ
  pr1ᵉ (map-inv-compute-total-fam-coproductᵉ (inlᵉ xᵉ)) = zero-Finᵉ 1
  pr2ᵉ (map-inv-compute-total-fam-coproductᵉ (inlᵉ xᵉ)) = map-raiseᵉ xᵉ
  pr1ᵉ (map-inv-compute-total-fam-coproductᵉ (inrᵉ xᵉ)) = one-Finᵉ 1
  pr2ᵉ (map-inv-compute-total-fam-coproductᵉ (inrᵉ xᵉ)) = map-raiseᵉ xᵉ

  is-section-map-inv-compute-total-fam-coproductᵉ :
    (map-compute-total-fam-coproductᵉ ∘ᵉ map-inv-compute-total-fam-coproductᵉ) ~ᵉ idᵉ
  is-section-map-inv-compute-total-fam-coproductᵉ (inlᵉ xᵉ) =
    apᵉ inlᵉ (is-retraction-map-inv-raiseᵉ {l2ᵉ} xᵉ)
  is-section-map-inv-compute-total-fam-coproductᵉ (inrᵉ xᵉ) =
    apᵉ inrᵉ (is-retraction-map-inv-raiseᵉ {l1ᵉ} xᵉ)

  is-retraction-map-inv-compute-total-fam-coproductᵉ :
    map-inv-compute-total-fam-coproductᵉ ∘ᵉ map-compute-total-fam-coproductᵉ ~ᵉ idᵉ
  is-retraction-map-inv-compute-total-fam-coproductᵉ (pairᵉ (inlᵉ (inrᵉ _)) yᵉ) =
    eq-pair-eq-fiberᵉ (is-section-map-inv-raiseᵉ yᵉ)
  is-retraction-map-inv-compute-total-fam-coproductᵉ (pairᵉ (inrᵉ _) yᵉ) =
    eq-pair-eq-fiberᵉ (is-section-map-inv-raiseᵉ yᵉ)

  is-equiv-map-compute-total-fam-coproductᵉ :
    is-equivᵉ map-compute-total-fam-coproductᵉ
  is-equiv-map-compute-total-fam-coproductᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-compute-total-fam-coproductᵉ
      is-section-map-inv-compute-total-fam-coproductᵉ
      is-retraction-map-inv-compute-total-fam-coproductᵉ

  compute-total-fam-coproductᵉ :
    (Σᵉ (Finᵉ 2ᵉ) fam-coproductᵉ) ≃ᵉ (Aᵉ +ᵉ Bᵉ)
  pr1ᵉ compute-total-fam-coproductᵉ = map-compute-total-fam-coproductᵉ
  pr2ᵉ compute-total-fam-coproductᵉ = is-equiv-map-compute-total-fam-coproductᵉ

  inv-compute-total-fam-coproductᵉ :
    (Aᵉ +ᵉ Bᵉ) ≃ᵉ Σᵉ (Finᵉ 2ᵉ) fam-coproductᵉ
  inv-compute-total-fam-coproductᵉ =
    inv-equivᵉ compute-total-fam-coproductᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : Xᵉ → UUᵉ l2ᵉ} {Bᵉ : Xᵉ → UUᵉ l3ᵉ}
  where

  type-distributive-Π-coproductᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  type-distributive-Π-coproductᵉ =
    Σᵉ ( Xᵉ → Finᵉ 2ᵉ)
      ( λ fᵉ → ((xᵉ : Xᵉ) (pᵉ : is-zero-Finᵉ 2 (fᵉ xᵉ)) → Aᵉ xᵉ) ×ᵉ
              ((xᵉ : Xᵉ) (pᵉ : is-one-Finᵉ 2 (fᵉ xᵉ)) → Bᵉ xᵉ))

  distributive-Π-coproductᵉ :
    ((xᵉ : Xᵉ) → Aᵉ xᵉ +ᵉ Bᵉ xᵉ) ≃ᵉ type-distributive-Π-coproductᵉ
  distributive-Π-coproductᵉ =
    ( ( equiv-totᵉ
        ( λ fᵉ →
          ( ( equiv-productᵉ
              ( equiv-Π-equiv-familyᵉ
                ( λ xᵉ →
                  equiv-Π-equiv-familyᵉ
                    ( λ pᵉ →
                      ( inv-equivᵉ (compute-raiseᵉ l3ᵉ (Aᵉ xᵉ))) ∘eᵉ
                      ( equiv-trᵉ (fam-coproductᵉ (Aᵉ xᵉ) (Bᵉ xᵉ)) pᵉ))))
              ( equiv-Π-equiv-familyᵉ
                ( λ xᵉ →
                  equiv-Π-equiv-familyᵉ
                    ( λ pᵉ →
                      ( inv-equivᵉ (compute-raiseᵉ l2ᵉ (Bᵉ xᵉ))) ∘eᵉ
                      ( equiv-trᵉ (fam-coproductᵉ (Aᵉ xᵉ) (Bᵉ xᵉ)) pᵉ))))) ∘eᵉ
            ( distributive-Π-Σᵉ)) ∘eᵉ
          ( equiv-Π-equiv-familyᵉ
            ( λ xᵉ →
              ( equiv-universal-property-coproductᵉ
                ( fam-coproductᵉ (Aᵉ xᵉ) (Bᵉ xᵉ) (fᵉ xᵉ))) ∘eᵉ
              ( equiv-diagonal-exponential-is-contrᵉ
                ( fam-coproductᵉ (Aᵉ xᵉ) (Bᵉ xᵉ) (fᵉ xᵉ))
                ( is-contr-is-zero-or-one-Fin-two-ℕᵉ (fᵉ xᵉ))))))) ∘eᵉ
      ( distributive-Π-Σᵉ)) ∘eᵉ
    ( equiv-Π-equiv-familyᵉ
      ( λ xᵉ → inv-compute-total-fam-coproductᵉ (Aᵉ xᵉ) (Bᵉ xᵉ)))

  type-distributive-Π-coproduct-binary-coproduct-Decompositionᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l1ᵉ)
  type-distributive-Π-coproduct-binary-coproduct-Decompositionᵉ =
    Σᵉ ( binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ)
      ( λ dᵉ →
        ( ( (uᵉ : left-summand-binary-coproduct-Decompositionᵉ dᵉ) →
            ( Aᵉ
              ( map-inv-equivᵉ
                ( matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ)
                ( inlᵉ uᵉ)))) ×ᵉ
          ( ( vᵉ : right-summand-binary-coproduct-Decompositionᵉ dᵉ) →
            ( Bᵉ
              ( map-inv-equivᵉ
                ( matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ)
                ( inrᵉ vᵉ))))))

  equiv-type-distributive-Π-coproduct-binary-coproduct-Decompositionᵉ :
    type-distributive-Π-coproductᵉ ≃ᵉ
    type-distributive-Π-coproduct-binary-coproduct-Decompositionᵉ
  equiv-type-distributive-Π-coproduct-binary-coproduct-Decompositionᵉ =
    equiv-Σᵉ
    ( λ dᵉ →
      ( (uᵉ : left-summand-binary-coproduct-Decompositionᵉ dᵉ) →
        Aᵉ
          ( map-inv-equivᵉ
            ( matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ)
            ( inlᵉ uᵉ))) ×ᵉ
      ( (vᵉ : right-summand-binary-coproduct-Decompositionᵉ dᵉ) →
        Bᵉ
          ( map-inv-equivᵉ
            ( matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ)
            ( inrᵉ vᵉ))))
      ( equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ Xᵉ)
      ( λ fᵉ →
        equiv-productᵉ
          ( equiv-Πᵉ
              ( λ zᵉ →
                  Aᵉ
                  ( map-inv-equivᵉ
                    ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                      ( Xᵉ)
                      ( fᵉ))
                    ( inlᵉ zᵉ)))
              ( id-equivᵉ)
              ( λ aᵉ →
                equiv-eqᵉ
                  ( apᵉ
                      ( Aᵉ)
                      ( compute-left-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-Two-ℕᵉ
                        ( Xᵉ)
                        ( fᵉ)
                        ( aᵉ)))) ∘eᵉ
            inv-equivᵉ equiv-ev-pairᵉ)
          ( equiv-Πᵉ
              ( λ zᵉ →
                  Bᵉ
                  ( map-inv-equivᵉ
                    ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                      Xᵉ fᵉ)
                    ( inrᵉ zᵉ)))
              ( id-equivᵉ)
              ( λ aᵉ →
                equiv-eqᵉ
                  ( apᵉ
                      ( Bᵉ)
                      ( compute-right-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-Two-ℕᵉ
                        ( Xᵉ)
                        ( fᵉ)
                        ( aᵉ)))) ∘eᵉ
            inv-equivᵉ equiv-ev-pairᵉ))

  distributive-Π-coproduct-binary-coproduct-Decompositionᵉ :
    ((xᵉ : Xᵉ) → Aᵉ xᵉ +ᵉ Bᵉ xᵉ) ≃ᵉ
    type-distributive-Π-coproduct-binary-coproduct-Decompositionᵉ
  distributive-Π-coproduct-binary-coproduct-Decompositionᵉ =
    equiv-type-distributive-Π-coproduct-binary-coproduct-Decompositionᵉ ∘eᵉ
    distributive-Π-coproductᵉ
```