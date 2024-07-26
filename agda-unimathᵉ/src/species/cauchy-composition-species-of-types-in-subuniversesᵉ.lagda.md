# Cauchy composition of species of types in a subuniverse

```agda
module species.cauchy-composition-species-of-types-in-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.global-subuniversesᵉ
open import foundation.homotopiesᵉ
open import foundation.propositionsᵉ
open import foundation.relaxed-sigma-decompositionsᵉ
open import foundation.sigma-closed-subuniversesᵉ
open import foundation.sigma-decomposition-subuniverseᵉ
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
open import species.unit-cauchy-composition-species-of-types-in-subuniversesᵉ
```

</details>

## Idea

Aᵉ speciesᵉ `Sᵉ : type-subuniverseᵉ Pᵉ → type-subuniverseᵉ Q`ᵉ inducesᵉ itsᵉ
[Cauchyᵉ series](species.cauchy-series-species-of-types-in-subuniverses.mdᵉ)

```text
  Xᵉ ↦ᵉ Σᵉ (Aᵉ : type-subuniverseᵉ P),ᵉ (Sᵉ Aᵉ) ×ᵉ (Aᵉ → Xᵉ)
```

Theᵉ **Cauchyᵉ composition**ᵉ ofᵉ speciesᵉ `S`ᵉ andᵉ `T`ᵉ isᵉ obtainedᵉ fromᵉ theᵉ
coefficientsᵉ ofᵉ theᵉ compositeᵉ ofᵉ theᵉ Cauchyᵉ seriesᵉ ofᵉ `S`ᵉ andᵉ `T`.ᵉ

## Definition

### Cauchy composition of species

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  where

  type-cauchy-composition-species-subuniverseᵉ :
    {l3ᵉ l4ᵉ : Level} →
    (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)) →
    (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)) →
    type-subuniverseᵉ Pᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  type-cauchy-composition-species-subuniverseᵉ {l3ᵉ} {l4ᵉ} Sᵉ Tᵉ Xᵉ =
    Σᵉ ( Σ-Decomposition-Subuniverseᵉ Pᵉ Xᵉ)
      ( λ Dᵉ →
        ( inclusion-subuniverseᵉ
          ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
          ( Sᵉ (subuniverse-indexing-type-Σ-Decomposition-Subuniverseᵉ Pᵉ Xᵉ Dᵉ))) ×ᵉ
        ( (xᵉ : indexing-type-Σ-Decomposition-Subuniverseᵉ Pᵉ Xᵉ Dᵉ) →
          inclusion-subuniverseᵉ
          ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
          ( Tᵉ (subuniverse-cotype-Σ-Decomposition-Subuniverseᵉ Pᵉ Xᵉ Dᵉ xᵉ))))

  is-closed-under-cauchy-composition-species-subuniverseᵉ : UUωᵉ
  is-closed-under-cauchy-composition-species-subuniverseᵉ =
    { l3ᵉ l4ᵉ : Level}
    ( Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
    ( Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
    ( Xᵉ : type-subuniverseᵉ Pᵉ) →
    is-in-global-subuniverseᵉ Qᵉ
      ( type-cauchy-composition-species-subuniverseᵉ Sᵉ Tᵉ Xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (C1ᵉ : is-closed-under-cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ)
  (C2ᵉ : is-closed-under-Σ-subuniverseᵉ Pᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  where

  cauchy-composition-species-subuniverseᵉ :
    species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
  cauchy-composition-species-subuniverseᵉ Xᵉ =
    ( type-cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ Xᵉ ,ᵉ C1ᵉ Sᵉ Tᵉ Xᵉ)
```

## Properties

### Σ-extension of species of types in a subuniverse preserves cauchy composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (C1ᵉ : is-closed-under-cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ)
  (C2ᵉ : is-closed-under-Σ-subuniverseᵉ Pᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  where

  preserves-cauchy-composition-Σ-extension-species-subuniverseᵉ :
    ( Xᵉ : UUᵉ l1ᵉ) →
    Σ-extension-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
      ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ Sᵉ Tᵉ)
      ( Xᵉ) ≃ᵉ
    ( cauchy-composition-species-typesᵉ
      ( Σ-extension-species-subuniverseᵉ Pᵉ
        ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
        ( Sᵉ))
      ( Σ-extension-species-subuniverseᵉ Pᵉ
        ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
        ( Tᵉ))
      ( Xᵉ))
  preserves-cauchy-composition-Σ-extension-species-subuniverseᵉ Xᵉ =
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
                            ( pr1ᵉ Dᵉ))))
                      ( C2ᵉ
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
              ( _))))))
```

### Unit laws for Cauchy composition of species-subuniverse

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  ( C3ᵉ : is-in-subuniverseᵉ Pᵉ (raise-unitᵉ l1ᵉ))
  ( C4ᵉ :
    is-closed-under-is-contr-subuniversesᵉ Pᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ))
  (Xᵉ : UUᵉ l1ᵉ)
  where

  map-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ :
    Σ-extension-species-subuniverseᵉ Pᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ)
      ( cauchy-composition-unit-species-subuniverseᵉ Pᵉ Qᵉ C4ᵉ)
      ( Xᵉ) →
    unit-species-typesᵉ Xᵉ
  map-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ (pᵉ ,ᵉ Hᵉ) = Hᵉ

  map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ :
    unit-species-typesᵉ Xᵉ →
    Σ-extension-species-subuniverseᵉ Pᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ)
      ( cauchy-composition-unit-species-subuniverseᵉ Pᵉ Qᵉ C4ᵉ)
      ( Xᵉ)
  pr1ᵉ (map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ Hᵉ) =
    is-in-subuniverse-equivᵉ Pᵉ (equiv-is-contrᵉ is-contr-raise-unitᵉ Hᵉ) C3ᵉ
  pr2ᵉ (map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ Hᵉ) = Hᵉ

  is-section-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ :
    ( map-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ ∘ᵉ
      map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ) ~ᵉ idᵉ
  is-section-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ =
    refl-htpyᵉ

  is-retraction-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ :
    ( map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ ∘ᵉ
      map-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ
    xᵉ =
    eq-pairᵉ
      ( eq-is-propᵉ (is-prop-type-Propᵉ (Pᵉ Xᵉ)))
      ( eq-is-propᵉ is-property-is-contrᵉ)

  is-equiv-map-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ :
    is-equivᵉ map-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ
  is-equiv-map-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ
      is-section-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ
      is-retraction-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ

  equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ :
    Σ-extension-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ)
      ( cauchy-composition-unit-species-subuniverseᵉ Pᵉ Qᵉ C4ᵉ)
      ( Xᵉ) ≃ᵉ
    unit-species-typesᵉ Xᵉ
  pr1ᵉ equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ =
    map-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ
  pr2ᵉ equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ =
    is-equiv-map-equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ

module _
  { l1ᵉ l2ᵉ l3ᵉ : Level}
  ( Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  ( Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  ( C1ᵉ : is-closed-under-cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ)
  ( C2ᵉ : is-closed-under-Σ-subuniverseᵉ Pᵉ)
  ( C3ᵉ : is-in-subuniverseᵉ Pᵉ (raise-unitᵉ l1ᵉ))
  ( C4ᵉ :
    is-closed-under-is-contr-subuniversesᵉ Pᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ))
  ( Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  where

  equiv-left-unit-law-cauchy-composition-species-subuniverseᵉ :
    ( Xᵉ : type-subuniverseᵉ Pᵉ) →
    inclusion-subuniverseᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ))
      ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ
        ( cauchy-composition-unit-species-subuniverseᵉ Pᵉ Qᵉ C4ᵉ)
        ( Sᵉ)
        ( Xᵉ)) ≃ᵉ
    inclusion-subuniverseᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ) (Sᵉ Xᵉ)
  equiv-left-unit-law-cauchy-composition-species-subuniverseᵉ Xᵉ =
    ( ( inv-equivᵉ
        ( equiv-Σ-extension-species-subuniverseᵉ
          ( Pᵉ)
          ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
          ( Sᵉ)
          ( Xᵉ))) ∘eᵉ
      ( ( left-unit-law-cauchy-composition-species-typesᵉ
          ( Σ-extension-species-subuniverseᵉ
            ( Pᵉ)
            ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
            ( Sᵉ))
          ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
        ( ( equiv-totᵉ
            ( λ Dᵉ →
              equiv-productᵉ
                ( equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ
                  ( Pᵉ)
                  ( Qᵉ)
                  ( C3ᵉ)
                  ( C4ᵉ)
                  ( indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ))
                ( id-equivᵉ))) ∘eᵉ
          ( ( preserves-cauchy-composition-Σ-extension-species-subuniverseᵉ
              ( Pᵉ)
              ( Qᵉ)
              ( C1ᵉ)
              ( C2ᵉ)
              ( cauchy-composition-unit-species-subuniverseᵉ Pᵉ Qᵉ C4ᵉ)
              ( Sᵉ)
              ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
            ( ( equiv-Σ-extension-species-subuniverseᵉ
                ( Pᵉ)
                ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ))
                ( cauchy-composition-species-subuniverseᵉ
                  ( Pᵉ)
                  ( Qᵉ)
                  ( C1ᵉ)
                  ( C2ᵉ)
                  ( cauchy-composition-unit-species-subuniverseᵉ Pᵉ Qᵉ C4ᵉ)
                  ( Sᵉ))
                  ( Xᵉ)))))))

  equiv-right-unit-law-cauchy-composition-species-subuniverseᵉ :
    ( Xᵉ : type-subuniverseᵉ Pᵉ) →
    inclusion-subuniverseᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ))
      ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ Sᵉ
        ( cauchy-composition-unit-species-subuniverseᵉ Pᵉ Qᵉ C4ᵉ)
        ( Xᵉ)) ≃ᵉ
    inclusion-subuniverseᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ) (Sᵉ Xᵉ)
  equiv-right-unit-law-cauchy-composition-species-subuniverseᵉ Xᵉ =
    ( inv-equivᵉ
      ( equiv-Σ-extension-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
        ( Sᵉ)
        ( Xᵉ))) ∘eᵉ
    ( ( right-unit-law-cauchy-composition-species-typesᵉ
        ( Σ-extension-species-subuniverseᵉ
          ( Pᵉ)
          ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
          ( Sᵉ))
        ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
      ( ( equiv-totᵉ
          ( λ Dᵉ →
            equiv-productᵉ
              ( id-equivᵉ)
              ( equiv-Π-equiv-familyᵉ
                ( λ xᵉ →
                  equiv-Σ-extension-cauchy-composition-unit-subuniverseᵉ
                    ( Pᵉ)
                    ( Qᵉ)
                    ( C3ᵉ)
                    ( C4ᵉ)
                    ( cotype-Relaxed-Σ-Decompositionᵉ Dᵉ xᵉ))))) ∘eᵉ
        ( ( preserves-cauchy-composition-Σ-extension-species-subuniverseᵉ
            ( Pᵉ)
            ( Qᵉ)
            ( C1ᵉ)
            ( C2ᵉ)
            ( Sᵉ)
            ( cauchy-composition-unit-species-subuniverseᵉ Pᵉ Qᵉ C4ᵉ)
            ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
          ( ( equiv-Σ-extension-species-subuniverseᵉ
              ( Pᵉ)
              ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ))
              ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ Sᵉ
                ( cauchy-composition-unit-species-subuniverseᵉ Pᵉ Qᵉ C4ᵉ))
              ( Xᵉ))))))
```

### Associativity of composition of species of types in subuniverse

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  ( Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  ( Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  ( C1ᵉ : is-closed-under-cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ)
  ( C2ᵉ : is-closed-under-Σ-subuniverseᵉ Pᵉ)
  ( Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  ( Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  ( Uᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l5ᵉ))
  where

  equiv-associative-cauchy-composition-species-subuniverseᵉ :
    (Xᵉ : type-subuniverseᵉ Pᵉ) →
    inclusion-subuniverseᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ))
      ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ Sᵉ
        ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ Tᵉ Uᵉ)
        ( Xᵉ)) ≃ᵉ
    inclusion-subuniverseᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ))
      ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ
        ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ Sᵉ Tᵉ)
        ( Uᵉ)
        ( Xᵉ))
  equiv-associative-cauchy-composition-species-subuniverseᵉ Xᵉ =
    ( inv-equivᵉ
      ( equiv-Σ-extension-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ))
        ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ
          ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ Sᵉ Tᵉ)
          ( Uᵉ))
        ( Xᵉ))) ∘eᵉ
    ( ( inv-equivᵉ
        ( preserves-cauchy-composition-Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ
          ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ Sᵉ Tᵉ)
          ( Uᵉ)
          ( inclusion-subuniverseᵉ Pᵉ Xᵉ))) ∘eᵉ
      ( ( equiv-totᵉ
          ( λ Dᵉ →
            equiv-productᵉ
              ( inv-equivᵉ
                ( preserves-cauchy-composition-Σ-extension-species-subuniverseᵉ
                  ( Pᵉ)
                  ( Qᵉ)
                  ( C1ᵉ)
                  ( C2ᵉ)
                  ( Sᵉ)
                  ( Tᵉ)
                  ( indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ)))
              ( id-equivᵉ))) ∘eᵉ
        ( ( equiv-associative-cauchy-composition-species-typesᵉ
            ( Σ-extension-species-subuniverseᵉ Pᵉ
              ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
              ( Sᵉ))
            ( Σ-extension-species-subuniverseᵉ Pᵉ
              ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
              ( Tᵉ))
            ( Σ-extension-species-subuniverseᵉ Pᵉ
              ( subuniverse-global-subuniverseᵉ Qᵉ l5ᵉ)
              ( Uᵉ))
            ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
          ( equiv-totᵉ
            ( λ Dᵉ →
              equiv-productᵉ
                ( id-equivᵉ)
                ( equiv-Πᵉ
                  ( λ yᵉ →
                    cauchy-composition-species-typesᵉ
                      ( Σ-extension-species-subuniverseᵉ
                        ( Pᵉ)
                        ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
                        ( Tᵉ))
                      ( Σ-extension-species-subuniverseᵉ
                        ( Pᵉ)
                        ( subuniverse-global-subuniverseᵉ Qᵉ l5ᵉ)
                        ( Uᵉ))
                      ( cotype-Relaxed-Σ-Decompositionᵉ Dᵉ yᵉ))
                  ( id-equivᵉ)
                  ( λ yᵉ →
                    preserves-cauchy-composition-Σ-extension-species-subuniverseᵉ
                      ( Pᵉ)
                      ( Qᵉ)
                      ( C1ᵉ)
                      ( C2ᵉ)
                      ( Tᵉ)
                      ( Uᵉ)
                      ( cotype-Relaxed-Σ-Decompositionᵉ Dᵉ yᵉ)))) ∘eᵉ
            ( ( preserves-cauchy-composition-Σ-extension-species-subuniverseᵉ
                ( Pᵉ)
                ( Qᵉ)
                ( C1ᵉ)
                ( C2ᵉ)
                ( Sᵉ)
                ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ Tᵉ Uᵉ)
                ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
              ( equiv-Σ-extension-species-subuniverseᵉ Pᵉ
                ( subuniverse-global-subuniverseᵉ Qᵉ
                  ( lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ))
                ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ Sᵉ
                  ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ Tᵉ Uᵉ))
                ( Xᵉ)))))))
```