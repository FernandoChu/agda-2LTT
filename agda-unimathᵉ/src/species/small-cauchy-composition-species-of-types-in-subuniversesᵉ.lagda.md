# Small Cauchy composition of species types in subuniverses

```agda
module species.small-cauchy-composition-species-of-types-in-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.relaxed-sigma-decompositionsᵉ
open import foundation.sigma-closed-subuniversesᵉ
open import foundation.sigma-decomposition-subuniverseᵉ
open import foundation.small-typesᵉ
open import foundation.subuniversesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.unit-typeᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import species.cauchy-composition-species-of-typesᵉ
open import species.species-of-types-in-subuniversesᵉ
open import species.unit-cauchy-composition-species-of-typesᵉ
```

</details>

## Idea

Aᵉ speciesᵉ `Sᵉ : Inhabited-Typeᵉ → UUᵉ l`ᵉ canᵉ beᵉ thoughtᵉ ofᵉ asᵉ theᵉ analyticᵉ
endofunctorᵉ

```text
  Xᵉ ↦ᵉ Σᵉ (Aᵉ : Inhabited-Typeᵉ) (Sᵉ Aᵉ) ×ᵉ (Aᵉ → Xᵉ)
```

Usingᵉ theᵉ formulaᵉ forᵉ compositionᵉ ofᵉ analyticᵉ endofunctors,ᵉ weᵉ obtainᵉ aᵉ wayᵉ to
composeᵉ species.ᵉ

## Definition

### Cauchy composition of species

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : subuniverseᵉ l3ᵉ l4ᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
  (Tᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
  where

  small-cauchy-composition-species-subuniverse'ᵉ :
    type-subuniverseᵉ Pᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  small-cauchy-composition-species-subuniverse'ᵉ Xᵉ =
    Σᵉ ( Σ-Decomposition-Subuniverseᵉ Pᵉ Xᵉ)
      ( λ Dᵉ →
        ( inclusion-subuniverseᵉ
          ( Qᵉ)
          ( Sᵉ (subuniverse-indexing-type-Σ-Decomposition-Subuniverseᵉ Pᵉ Xᵉ Dᵉ))) ×ᵉ
        ( (xᵉ : indexing-type-Σ-Decomposition-Subuniverseᵉ Pᵉ Xᵉ Dᵉ) →
          inclusion-subuniverseᵉ
          ( Qᵉ)
          ( Tᵉ (subuniverse-cotype-Σ-Decomposition-Subuniverseᵉ Pᵉ Xᵉ Dᵉ xᵉ))))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : subuniverseᵉ l3ᵉ l4ᵉ)
  (C1ᵉ :
    ( Sᵉ Tᵉ : species-subuniverseᵉ Pᵉ Qᵉ) → (Xᵉ : type-subuniverseᵉ Pᵉ) →
    is-smallᵉ l3ᵉ (small-cauchy-composition-species-subuniverse'ᵉ Pᵉ Qᵉ Sᵉ Tᵉ Xᵉ))
  (C2ᵉ :
    ( Sᵉ Tᵉ : species-subuniverseᵉ Pᵉ Qᵉ) → (Xᵉ : type-subuniverseᵉ Pᵉ) →
    ( is-in-subuniverseᵉ Qᵉ (type-is-smallᵉ (C1ᵉ Sᵉ Tᵉ Xᵉ))))
  (C3ᵉ : is-closed-under-Σ-subuniverseᵉ Pᵉ)
  where

  small-cauchy-composition-species-subuniverseᵉ :
    species-subuniverseᵉ Pᵉ Qᵉ →
    species-subuniverseᵉ Pᵉ Qᵉ →
    species-subuniverseᵉ Pᵉ Qᵉ
  small-cauchy-composition-species-subuniverseᵉ Sᵉ Tᵉ Xᵉ =
    type-is-smallᵉ (C1ᵉ Sᵉ Tᵉ Xᵉ) ,ᵉ C2ᵉ Sᵉ Tᵉ Xᵉ
```

## Properties

### Equivalent form with species of types

```agda
  equiv-small-cauchy-composition-Σ-extension-species-subuniverseᵉ :
    ( Sᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
    ( Tᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
    ( Xᵉ : UUᵉ l1ᵉ) →
    Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ
      ( small-cauchy-composition-species-subuniverseᵉ Sᵉ Tᵉ)
      ( Xᵉ) ≃ᵉ
    ( cauchy-composition-species-typesᵉ
      ( Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ)
      ( Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ Tᵉ)
      ( Xᵉ))
  equiv-small-cauchy-composition-Σ-extension-species-subuniverseᵉ Sᵉ Tᵉ Xᵉ =
    ( ( equiv-totᵉ
        ( λ Dᵉ →
          ( ( equiv-productᵉ id-equivᵉ (inv-equivᵉ distributive-Π-Σᵉ)) ∘eᵉ
          ( ( inv-equivᵉ right-distributive-product-Σᵉ) ∘eᵉ
          ( ( equiv-totᵉ (λ _ → inv-equivᵉ (left-distributive-product-Σᵉ)))))) ∘eᵉ
          ( ( associative-Σᵉ _ _ _)))) ∘eᵉ
      ( ( associative-Σᵉ
          ( Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ)
          ( λ Dᵉ →
              is-in-subuniverseᵉ Pᵉ (indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ) ×ᵉ
              ( (xᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ) →
                is-in-subuniverseᵉ Pᵉ (cotype-Relaxed-Σ-Decompositionᵉ Dᵉ xᵉ)))
          ( _)) ∘eᵉ
        ( ( equiv-Σ-equiv-baseᵉ
            ( _)
            ( ( inv-equivᵉ
                ( equiv-add-redundant-propᵉ
                  ( is-prop-type-Propᵉ (Pᵉ Xᵉ))
                  ( λ Dᵉ →
                    ( trᵉ
                      ( is-in-subuniverseᵉ Pᵉ)
                      ( eq-equivᵉ
                        ( inv-equivᵉ
                          ( matching-correspondence-Relaxed-Σ-Decompositionᵉ
                            (pr1ᵉ Dᵉ))))
                      ( C3ᵉ
                        ( indexing-type-Relaxed-Σ-Decompositionᵉ (pr1ᵉ Dᵉ) ,ᵉ
                          pr1ᵉ (pr2ᵉ Dᵉ))
                        ( λ xᵉ →
                          ( cotype-Relaxed-Σ-Decompositionᵉ (pr1ᵉ Dᵉ) xᵉ ,ᵉ
                            pr2ᵉ (pr2ᵉ Dᵉ) xᵉ)))))) ∘eᵉ
              ( commutative-productᵉ ∘eᵉ
              ( equiv-totᵉ
                ( λ pᵉ →
                  equiv-total-is-in-subuniverse-Σ-Decompositionᵉ
                    ( Pᵉ)
                    (Xᵉ ,ᵉ pᵉ))))))) ∘eᵉ
          ( ( inv-associative-Σᵉ
              ( is-in-subuniverseᵉ Pᵉ Xᵉ)
              ( λ pᵉ → Σ-Decomposition-Subuniverseᵉ Pᵉ (Xᵉ ,ᵉ pᵉ))
              ( _)) ∘eᵉ
            ( ( equiv-totᵉ
                ( λ pᵉ → inv-equivᵉ (equiv-is-smallᵉ (C1ᵉ Sᵉ Tᵉ (Xᵉ ,ᵉ pᵉ))))))))))
```

### Unit laws for Cauchy composition of species-subuniverse

```agda
  module _
    (C4ᵉ : is-in-subuniverseᵉ Pᵉ (raise-unitᵉ l1ᵉ))
    (C5ᵉ :
      (Xᵉ : UUᵉ l1ᵉ) →
      is-smallᵉ l3ᵉ (is-contrᵉ (Xᵉ)))
    (C6ᵉ :
      ( Xᵉ : type-subuniverseᵉ Pᵉ) →
      ( is-in-subuniverseᵉ
          ( Qᵉ)
          ( type-is-smallᵉ (C5ᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ)))))
    where

    small-cauchy-composition-unit-species-subuniverseᵉ :
      species-subuniverseᵉ Pᵉ Qᵉ
    small-cauchy-composition-unit-species-subuniverseᵉ Xᵉ =
      type-is-smallᵉ (C5ᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ)) ,ᵉ C6ᵉ Xᵉ

    equiv-Σ-extension-small-cauchy-composition-unit-subuniverseᵉ :
      (Xᵉ : UUᵉ l1ᵉ) →
      Σ-extension-species-subuniverseᵉ
        ( Pᵉ)
        ( Qᵉ)
        ( small-cauchy-composition-unit-species-subuniverseᵉ)
        ( Xᵉ) ≃ᵉ
      unit-species-typesᵉ Xᵉ
    pr1ᵉ (equiv-Σ-extension-small-cauchy-composition-unit-subuniverseᵉ Xᵉ) Sᵉ =
      map-inv-equiv-is-smallᵉ
        ( C5ᵉ Xᵉ)
        ( pr2ᵉ Sᵉ)
    pr2ᵉ (equiv-Σ-extension-small-cauchy-composition-unit-subuniverseᵉ Xᵉ) =
      is-equiv-is-invertibleᵉ
        ( λ Sᵉ →
          ( trᵉ
              ( is-in-subuniverseᵉ Pᵉ)
              ( eq-equivᵉ
                  ( ( inv-equivᵉ
                      ( terminal-mapᵉ Xᵉ ,ᵉ is-equiv-terminal-map-is-contrᵉ Sᵉ)) ∘eᵉ
                    ( inv-equivᵉ (compute-raise-unitᵉ l1ᵉ))))
              ( C4ᵉ) ,ᵉ
            map-equiv-is-smallᵉ (C5ᵉ Xᵉ) Sᵉ))
        ( λ xᵉ → eq-is-propᵉ is-property-is-contrᵉ)
        ( λ xᵉ →
          eq-pairᵉ
            ( eq-is-propᵉ (is-prop-type-Propᵉ (Pᵉ Xᵉ)))
            ( eq-is-propᵉ
                ( is-prop-equivᵉ
                    ( inv-equivᵉ (equiv-is-smallᵉ (C5ᵉ Xᵉ))) is-property-is-contrᵉ)))

    htpy-left-unit-law-small-cauchy-composition-species-subuniverseᵉ :
      ( Sᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
      ( Xᵉ : type-subuniverseᵉ Pᵉ) →
      inclusion-subuniverseᵉ
        ( Qᵉ)
        ( small-cauchy-composition-species-subuniverseᵉ
          ( small-cauchy-composition-unit-species-subuniverseᵉ)
          ( Sᵉ) Xᵉ) ≃ᵉ
      inclusion-subuniverseᵉ Qᵉ (Sᵉ Xᵉ)
    htpy-left-unit-law-small-cauchy-composition-species-subuniverseᵉ Sᵉ Xᵉ =
      ( ( inv-equivᵉ
          ( equiv-Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Xᵉ)) ∘eᵉ
        ( ( left-unit-law-cauchy-composition-species-typesᵉ
            ( Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ)
            ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
          ( ( equiv-totᵉ
              ( λ Dᵉ →
                equiv-productᵉ
                  ( equiv-Σ-extension-small-cauchy-composition-unit-subuniverseᵉ
                    ( indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ))
                  ( id-equivᵉ))) ∘eᵉ
            ( ( equiv-small-cauchy-composition-Σ-extension-species-subuniverseᵉ
                ( small-cauchy-composition-unit-species-subuniverseᵉ)
                ( Sᵉ)
                ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
              ( ( equiv-Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ
                  ( small-cauchy-composition-species-subuniverseᵉ
                    ( small-cauchy-composition-unit-species-subuniverseᵉ)
                    ( Sᵉ))
                    ( Xᵉ)))))))

    left-unit-law-small-cauchy-composition-species-subuniverseᵉ :
      ( Sᵉ : species-subuniverseᵉ Pᵉ Qᵉ) →
      small-cauchy-composition-species-subuniverseᵉ
        small-cauchy-composition-unit-species-subuniverseᵉ
        Sᵉ ＝ᵉ Sᵉ
    left-unit-law-small-cauchy-composition-species-subuniverseᵉ Sᵉ =
      eq-equiv-fam-subuniverseᵉ
      ( Qᵉ)
      ( small-cauchy-composition-species-subuniverseᵉ
        ( small-cauchy-composition-unit-species-subuniverseᵉ)
        ( Sᵉ))
      ( Sᵉ)
      ( htpy-left-unit-law-small-cauchy-composition-species-subuniverseᵉ Sᵉ)

    htpy-right-unit-law-small-cauchy-composition-species-subuniverseᵉ :
      ( Sᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
      ( Xᵉ : type-subuniverseᵉ Pᵉ) →
      inclusion-subuniverseᵉ
        ( Qᵉ)
        ( small-cauchy-composition-species-subuniverseᵉ
          ( Sᵉ)
          ( small-cauchy-composition-unit-species-subuniverseᵉ) Xᵉ) ≃ᵉ
      inclusion-subuniverseᵉ Qᵉ (Sᵉ Xᵉ)
    htpy-right-unit-law-small-cauchy-composition-species-subuniverseᵉ Sᵉ Xᵉ =
      ( ( inv-equivᵉ (equiv-Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Xᵉ)) ∘eᵉ
        ( ( right-unit-law-cauchy-composition-species-typesᵉ
            ( Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ)
            ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
          ( ( equiv-totᵉ
              ( λ Dᵉ →
                equiv-productᵉ
                  ( id-equivᵉ)
                  ( equiv-Πᵉ
                    ( _)
                    ( id-equivᵉ)
                    ( λ xᵉ →
                      equiv-Σ-extension-small-cauchy-composition-unit-subuniverseᵉ
                        ( cotype-Relaxed-Σ-Decompositionᵉ Dᵉ xᵉ))))) ∘eᵉ
            ( ( equiv-small-cauchy-composition-Σ-extension-species-subuniverseᵉ
                  ( Sᵉ)
                  ( small-cauchy-composition-unit-species-subuniverseᵉ)
                  ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
              ( ( equiv-Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ
                  ( small-cauchy-composition-species-subuniverseᵉ
                      Sᵉ
                      small-cauchy-composition-unit-species-subuniverseᵉ)
                  ( Xᵉ)))))))

    right-unit-law-small-cauchy-composition-species-subuniverseᵉ :
      ( Sᵉ : species-subuniverseᵉ Pᵉ Qᵉ) →
      small-cauchy-composition-species-subuniverseᵉ
        Sᵉ
        small-cauchy-composition-unit-species-subuniverseᵉ ＝ᵉ Sᵉ
    right-unit-law-small-cauchy-composition-species-subuniverseᵉ Sᵉ =
      eq-equiv-fam-subuniverseᵉ
      ( Qᵉ)
      ( small-cauchy-composition-species-subuniverseᵉ
        ( Sᵉ)
        ( small-cauchy-composition-unit-species-subuniverseᵉ))
      ( Sᵉ)
      ( htpy-right-unit-law-small-cauchy-composition-species-subuniverseᵉ Sᵉ)
```

### Associativity of composition of species of types in subuniverse

```agda
  htpy-associative-small-cauchy-composition-species-subuniverseᵉ :
    (Sᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
    (Tᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
    (Uᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
    (Xᵉ : type-subuniverseᵉ Pᵉ) →
    inclusion-subuniverseᵉ
      ( Qᵉ)
      ( small-cauchy-composition-species-subuniverseᵉ
        ( Sᵉ)
        ( small-cauchy-composition-species-subuniverseᵉ Tᵉ Uᵉ)
        ( Xᵉ)) ≃ᵉ
    inclusion-subuniverseᵉ
      ( Qᵉ)
      ( small-cauchy-composition-species-subuniverseᵉ
        ( small-cauchy-composition-species-subuniverseᵉ Sᵉ Tᵉ)
        ( Uᵉ)
        ( Xᵉ))
  htpy-associative-small-cauchy-composition-species-subuniverseᵉ Sᵉ Tᵉ Uᵉ Xᵉ =
    ( ( inv-equivᵉ
        ( equiv-Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ
          ( small-cauchy-composition-species-subuniverseᵉ
            ( small-cauchy-composition-species-subuniverseᵉ Sᵉ Tᵉ) Uᵉ)
          ( Xᵉ))) ∘eᵉ
      ( ( inv-equivᵉ
          ( equiv-small-cauchy-composition-Σ-extension-species-subuniverseᵉ
            ( small-cauchy-composition-species-subuniverseᵉ Sᵉ Tᵉ)
            ( Uᵉ)
            ( inclusion-subuniverseᵉ Pᵉ Xᵉ))) ∘eᵉ
        ( ( equiv-totᵉ
            ( λ Dᵉ →
              equiv-productᵉ
                ( inv-equivᵉ
                  ( equiv-small-cauchy-composition-Σ-extension-species-subuniverseᵉ
                    ( Sᵉ)
                    ( Tᵉ)
                    ( indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ)))
                ( id-equivᵉ))) ∘eᵉ
          ( ( equiv-associative-cauchy-composition-species-typesᵉ
              ( Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ)
              ( Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ Tᵉ)
              ( Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ Uᵉ)
              ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
            ( ( equiv-totᵉ
                ( λ Dᵉ →
                  equiv-productᵉ
                    ( id-equivᵉ)
                    ( equiv-Πᵉ
                      ( λ yᵉ →
                        ( cauchy-composition-species-typesᵉ
                          ( Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ Tᵉ)
                          ( Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ Uᵉ)
                          ( cotype-Relaxed-Σ-Decompositionᵉ Dᵉ yᵉ)))
                      ( id-equivᵉ)
                      ( λ yᵉ →
                        ( equiv-small-cauchy-composition-Σ-extension-species-subuniverseᵉ
                          ( Tᵉ)
                          ( Uᵉ)
                          ( cotype-Relaxed-Σ-Decompositionᵉ Dᵉ yᵉ)))))) ∘eᵉ
              ( ( equiv-small-cauchy-composition-Σ-extension-species-subuniverseᵉ
                  ( Sᵉ)
                  ( small-cauchy-composition-species-subuniverseᵉ Tᵉ Uᵉ)
                  ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
                ( ( equiv-Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ
                    ( small-cauchy-composition-species-subuniverseᵉ
                      ( Sᵉ)
                      ( small-cauchy-composition-species-subuniverseᵉ Tᵉ Uᵉ))
                    ( Xᵉ)))))))))

  associative-small-cauchy-composition-species-subuniverseᵉ :
    (Sᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
    (Tᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
    (Uᵉ : species-subuniverseᵉ Pᵉ Qᵉ) →
    small-cauchy-composition-species-subuniverseᵉ
      ( Sᵉ)
      ( small-cauchy-composition-species-subuniverseᵉ Tᵉ Uᵉ) ＝ᵉ
    small-cauchy-composition-species-subuniverseᵉ
      ( small-cauchy-composition-species-subuniverseᵉ Sᵉ Tᵉ)
      ( Uᵉ)
  associative-small-cauchy-composition-species-subuniverseᵉ Sᵉ Tᵉ Uᵉ =
    eq-equiv-fam-subuniverseᵉ
      ( Qᵉ)
      ( small-cauchy-composition-species-subuniverseᵉ
        ( Sᵉ)
        ( small-cauchy-composition-species-subuniverseᵉ Tᵉ Uᵉ))
      ( small-cauchy-composition-species-subuniverseᵉ
        ( small-cauchy-composition-species-subuniverseᵉ Sᵉ Tᵉ)
        ( Uᵉ))
      ( htpy-associative-small-cauchy-composition-species-subuniverseᵉ Sᵉ Tᵉ Uᵉ)
```