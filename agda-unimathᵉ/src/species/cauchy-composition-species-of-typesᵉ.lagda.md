# Cauchy composition of species of types

```agda
module species.cauchy-composition-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.discrete-relaxed-sigma-decompositionsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.relaxed-sigma-decompositionsᵉ
open import foundation.trivial-relaxed-sigma-decompositionsᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-function-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-typesᵉ
open import species.unit-cauchy-composition-species-of-typesᵉ
```

</details>

## Idea

Aᵉ speciesᵉ ofᵉ typesᵉ `Sᵉ : UUᵉ l1ᵉ → UUᵉ l2`ᵉ canᵉ beᵉ thoughtᵉ ofᵉ asᵉ theᵉ polynomialᵉ
endofunctorᵉ

```text
  Xᵉ ↦ᵉ Σᵉ (Aᵉ : UUᵉ l1ᵉ) (Sᵉ Aᵉ) ×ᵉ (Aᵉ → Xᵉ)
```

Usingᵉ theᵉ formulaᵉ forᵉ compositionᵉ ofᵉ analyticᵉ endofunctors,ᵉ weᵉ obtainᵉ aᵉ wayᵉ to
composeᵉ species,ᵉ whichᵉ isᵉ calledᵉ theᵉ **Cauchyᵉ composition**ᵉ ofᵉ species.ᵉ

## Definition

### Cauchy composition of species

```agda
cauchy-composition-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} → species-typesᵉ l1ᵉ l2ᵉ → species-typesᵉ l1ᵉ l3ᵉ →
  species-typesᵉ l1ᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
cauchy-composition-species-typesᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} Sᵉ Tᵉ Xᵉ =
  Σᵉ ( Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ)
    ( λ Dᵉ →
      ( Sᵉ (indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ)) ×ᵉ
      ( ( yᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ) →
        Tᵉ (cotype-Relaxed-Σ-Decompositionᵉ Dᵉ yᵉ)))
```

## Properties

### Unit laws for Cauchy composition of species

```agda
left-unit-law-cauchy-composition-species-typesᵉ :
  {l1ᵉ l2ᵉ : Level}
  (Fᵉ : species-typesᵉ l1ᵉ l2ᵉ) → (Aᵉ : UUᵉ l1ᵉ) →
  cauchy-composition-species-typesᵉ unit-species-typesᵉ Fᵉ Aᵉ ≃ᵉ Fᵉ Aᵉ
left-unit-law-cauchy-composition-species-typesᵉ {l1ᵉ} Fᵉ Aᵉ =
  ( left-unit-law-Σ-is-contrᵉ
    ( is-contr-type-trivial-Relaxed-Σ-Decompositionᵉ)
    ( trivial-Relaxed-Σ-Decompositionᵉ l1ᵉ Aᵉ ,ᵉ
      is-trivial-trivial-Relaxed-Σ-Decompositionᵉ {l1ᵉ} {l1ᵉ} {Aᵉ})) ∘eᵉ
  ( ( inv-associative-Σᵉ
      ( Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ Aᵉ)
      ( λ Dᵉ → is-contrᵉ (indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ))
      ( λ Cᵉ → Fᵉ (cotype-Relaxed-Σ-Decompositionᵉ (pr1ᵉ Cᵉ) (centerᵉ (pr2ᵉ Cᵉ))))) ∘eᵉ
    ( ( equiv-Σᵉ
        ( _)
        ( id-equivᵉ)
        ( λ Dᵉ →
          equiv-Σᵉ
            ( λ zᵉ → Fᵉ (cotype-Relaxed-Σ-Decompositionᵉ Dᵉ (centerᵉ zᵉ)))
            ( id-equivᵉ)
            ( λ Cᵉ →
              ( left-unit-law-Π-is-contrᵉ Cᵉ (centerᵉ Cᵉ)))))))

right-unit-law-cauchy-composition-species-typesᵉ :
  {l1ᵉ l2ᵉ : Level}
  (Fᵉ : species-typesᵉ l1ᵉ l2ᵉ) → (Aᵉ : UUᵉ l1ᵉ) →
  cauchy-composition-species-typesᵉ Fᵉ unit-species-typesᵉ Aᵉ ≃ᵉ Fᵉ Aᵉ
right-unit-law-cauchy-composition-species-typesᵉ {l1ᵉ} Fᵉ Aᵉ =
  ( left-unit-law-Σ-is-contrᵉ
    ( is-contr-type-discrete-Relaxed-Σ-Decompositionᵉ)
    ( ( discrete-Relaxed-Σ-Decompositionᵉ l1ᵉ Aᵉ) ,ᵉ
      is-discrete-discrete-Relaxed-Σ-Decompositionᵉ)) ∘eᵉ
  ( ( inv-associative-Σᵉ
      ( Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ Aᵉ)
      ( λ Dᵉ →
          ( yᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ) →
            is-contrᵉ (cotype-Relaxed-Σ-Decompositionᵉ Dᵉ yᵉ))
      ( λ Dᵉ → Fᵉ (indexing-type-Relaxed-Σ-Decompositionᵉ (pr1ᵉ Dᵉ)))) ∘eᵉ
    ( ( equiv-Σᵉ
        ( λ Dᵉ →
          ( ( yᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ) →
            unit-species-typesᵉ
              ( cotype-Relaxed-Σ-Decompositionᵉ Dᵉ yᵉ)) ×ᵉ
            Fᵉ ( indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ))
        ( id-equivᵉ)
        ( λ _ → commutative-productᵉ))))
```

### Associativity of composition of species

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Sᵉ : species-typesᵉ l1ᵉ l2ᵉ) (Tᵉ : species-typesᵉ l1ᵉ l3ᵉ)
  (Uᵉ : species-typesᵉ l1ᵉ l4ᵉ)
  where

  equiv-associative-cauchy-composition-species-typesᵉ :
    (Aᵉ : UUᵉ l1ᵉ) →
    cauchy-composition-species-typesᵉ
      ( Sᵉ)
      ( cauchy-composition-species-typesᵉ Tᵉ Uᵉ)
      ( Aᵉ) ≃ᵉ
    cauchy-composition-species-typesᵉ
      ( cauchy-composition-species-typesᵉ Sᵉ Tᵉ)
      ( Uᵉ)
      ( Aᵉ)
  equiv-associative-cauchy-composition-species-typesᵉ Aᵉ =
    ( equiv-Σᵉ
      ( _)
      ( id-equivᵉ)
      ( λ D1ᵉ →
        ( ( inv-equivᵉ right-distributive-product-Σᵉ) ∘eᵉ
        ( ( equiv-Σᵉ
            ( _)
            ( id-equivᵉ)
            ( λ D2ᵉ →
              ( inv-associative-Σᵉ
                ( Sᵉ (indexing-type-Relaxed-Σ-Decompositionᵉ D2ᵉ))
                ( λ _ →
                  ( xᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ D2ᵉ) →
                  Tᵉ ( cotype-Relaxed-Σ-Decompositionᵉ D2ᵉ xᵉ))
                _))) ∘eᵉ
        ( ( equiv-Σᵉ
            ( _)
            ( id-equivᵉ)
            ( λ D2ᵉ →
              ( equiv-productᵉ
                ( id-equivᵉ)
                ( ( equiv-productᵉ
                    ( id-equivᵉ)
                    ( ( inv-equivᵉ
                        ( equiv-precomp-Πᵉ
                          ( inv-equivᵉ
                            ( matching-correspondence-Relaxed-Σ-Decompositionᵉ
                              D2ᵉ))
                        ( λ xᵉ → Uᵉ ( cotype-Relaxed-Σ-Decompositionᵉ D1ᵉ xᵉ)))) ∘eᵉ
                      ( inv-equivᵉ equiv-ev-pairᵉ))) ∘eᵉ
                  ( distributive-Π-Σᵉ)))))))))) ∘eᵉ
    ( ( associative-Σᵉ
        ( Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ Aᵉ)
        ( λ Dᵉ → Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ
          ( indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ))
        ( _)) ∘eᵉ
      ( ( inv-equivᵉ
          ( equiv-Σ-equiv-baseᵉ
            ( _)
            ( equiv-displayed-fibered-Relaxed-Σ-Decompositionᵉ))) ∘eᵉ
        ( ( inv-associative-Σᵉ
            ( Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ Aᵉ)
            ( λ Dᵉ →
              ( xᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ) →
                Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ
                  ( cotype-Relaxed-Σ-Decompositionᵉ Dᵉ xᵉ))
            ( _)) ∘eᵉ
          ( ( equiv-Σᵉ
              ( _)
              ( id-equivᵉ)
              ( λ Dᵉ → left-distributive-product-Σᵉ)) ∘eᵉ
            ( ( equiv-Σᵉ
                ( _)
                ( id-equivᵉ)
                ( λ Dᵉ → equiv-productᵉ id-equivᵉ distributive-Π-Σᵉ)))))))

  htpy-associative-cauchy-composition-species-typesᵉ :
    cauchy-composition-species-typesᵉ
      ( Sᵉ)
      ( cauchy-composition-species-typesᵉ Tᵉ Uᵉ) ~ᵉ
    cauchy-composition-species-typesᵉ (cauchy-composition-species-typesᵉ Sᵉ Tᵉ) Uᵉ
  htpy-associative-cauchy-composition-species-typesᵉ Aᵉ =
    eq-equivᵉ (equiv-associative-cauchy-composition-species-typesᵉ Aᵉ)

  associative-cauchy-composition-species-typesᵉ :
    ( cauchy-composition-species-typesᵉ
      ( Sᵉ)
      ( cauchy-composition-species-typesᵉ Tᵉ Uᵉ)) ＝ᵉ
    ( cauchy-composition-species-typesᵉ (cauchy-composition-species-typesᵉ Sᵉ Tᵉ) Uᵉ)
  associative-cauchy-composition-species-typesᵉ =
    eq-htpyᵉ htpy-associative-cauchy-composition-species-typesᵉ
```