# Cauchy exponentials of species of types

```agda
module species.cauchy-exponentials-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.arithmetic-law-coproduct-and-sigma-decompositionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-decompositionsᵉ
open import foundation.dependent-binomial-theoremᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.relaxed-sigma-decompositionsᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import species.cauchy-composition-species-of-typesᵉ
open import species.cauchy-products-species-of-typesᵉ
open import species.coproducts-species-of-typesᵉ
open import species.equivalences-species-of-typesᵉ
open import species.species-of-typesᵉ
```

</details>

## Idea

Theᵉ **Cauchyᵉ exponential**ᵉ ofᵉ aᵉ speciesᵉ ofᵉ typesᵉ `S`ᵉ canᵉ beᵉ thoughtᵉ ofᵉ asᵉ theᵉ
Cauchyᵉ compositeᵉ `expᵉ ∘ᵉ S`.ᵉ Sinceᵉ theᵉ exponentᵉ speciesᵉ isᵉ definedᵉ asᵉ `Xᵉ ↦ᵉ 𝟙`,ᵉ
theᵉ coefficientsᵉ ofᵉ theᵉ Cauchyᵉ exponentialᵉ ofᵉ `S`ᵉ areᵉ definedᵉ asᵉ followsᵉ:
speciesᵉ ofᵉ typesᵉ :

```text
  Xᵉ ↦ᵉ Σᵉ ((Uᵉ ,ᵉ Vᵉ ,ᵉ eᵉ) : Relaxed-Σ-Decompositionᵉ X),ᵉ  Πᵉ (uᵉ : Uᵉ) → Sᵉ (Vᵉ u).ᵉ
```

## Definition

```agda
cauchy-exponential-species-typesᵉ :
  {l1ᵉ l2ᵉ : Level} → species-typesᵉ l1ᵉ l2ᵉ → species-typesᵉ l1ᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
cauchy-exponential-species-typesᵉ {l1ᵉ} {l2ᵉ} Sᵉ Xᵉ =
  Σᵉ ( Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ)
    ( λ Dᵉ →
      ( bᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ) →
      ( Sᵉ (cotype-Relaxed-Σ-Decompositionᵉ Dᵉ bᵉ)))
```

## Propositions

### The Cauchy exponential in term of composition

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Sᵉ : species-typesᵉ l1ᵉ l2ᵉ)
  (Xᵉ : UUᵉ l1ᵉ)
  where

  equiv-cauchy-exponential-composition-unit-species-typesᵉ :
    cauchy-composition-species-typesᵉ (λ _ → unitᵉ) Sᵉ Xᵉ ≃ᵉ
    cauchy-exponential-species-typesᵉ Sᵉ Xᵉ
  equiv-cauchy-exponential-composition-unit-species-typesᵉ =
    equiv-totᵉ λ _ → left-unit-law-product-is-contrᵉ is-contr-unitᵉ
```

### The Cauchy exponential of the sum of a species is equivalent to the Cauchy product of the exponential of the two species

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Sᵉ : species-typesᵉ l1ᵉ l2ᵉ)
  (Tᵉ : species-typesᵉ l1ᵉ l3ᵉ)
  where

  private
    reassociateᵉ :
      ( Xᵉ : UUᵉ l1ᵉ) →
      Σᵉ ( Σᵉ ( binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ)
            ( λ dᵉ →
              ( Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ
                ( left-summand-binary-coproduct-Decompositionᵉ dᵉ)) ×ᵉ
              ( Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ
                ( right-summand-binary-coproduct-Decompositionᵉ dᵉ))))
        ( λ Dᵉ →
          ( ( bᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ (pr1ᵉ (pr2ᵉ Dᵉ))) →
            Sᵉ ( cotype-Relaxed-Σ-Decompositionᵉ (pr1ᵉ (pr2ᵉ Dᵉ)) bᵉ)) ×ᵉ
          ( ( bᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ (pr2ᵉ (pr2ᵉ Dᵉ))) →
            Tᵉ ( cotype-Relaxed-Σ-Decompositionᵉ (pr2ᵉ (pr2ᵉ Dᵉ)) bᵉ))) ≃ᵉ
      cauchy-product-species-typesᵉ
        ( cauchy-exponential-species-typesᵉ Sᵉ)
        ( cauchy-exponential-species-typesᵉ Tᵉ)
        ( Xᵉ)
    pr1ᵉ (reassociateᵉ Xᵉ) ((dᵉ ,ᵉ dlᵉ ,ᵉ drᵉ) ,ᵉ sᵉ ,ᵉ tᵉ) =
      ( dᵉ ,ᵉ (dlᵉ ,ᵉ sᵉ) ,ᵉ drᵉ ,ᵉ tᵉ)
    pr2ᵉ (reassociateᵉ Xᵉ) =
      is-equiv-is-invertibleᵉ
        ( λ ( dᵉ ,ᵉ (dlᵉ ,ᵉ sᵉ) ,ᵉ drᵉ ,ᵉ tᵉ) → ((dᵉ ,ᵉ dlᵉ ,ᵉ drᵉ) ,ᵉ sᵉ ,ᵉ tᵉ))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)

  equiv-cauchy-exponential-sum-species-typesᵉ :
    equiv-species-typesᵉ
      ( cauchy-exponential-species-typesᵉ (coproduct-species-typesᵉ Sᵉ Tᵉ))
      ( cauchy-product-species-typesᵉ
        ( cauchy-exponential-species-typesᵉ Sᵉ)
        ( cauchy-exponential-species-typesᵉ Tᵉ))
  equiv-cauchy-exponential-sum-species-typesᵉ Xᵉ =
    ( reassociateᵉ Xᵉ) ∘eᵉ
    ( ( equiv-Σᵉ
        ( λ Dᵉ →
          ( ( bᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ (pr1ᵉ (pr2ᵉ Dᵉ))) →
            Sᵉ (cotype-Relaxed-Σ-Decompositionᵉ (pr1ᵉ (pr2ᵉ Dᵉ)) bᵉ)) ×ᵉ
          ( ( bᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ (pr2ᵉ (pr2ᵉ Dᵉ))) →
            Tᵉ (cotype-Relaxed-Σ-Decompositionᵉ (pr2ᵉ (pr2ᵉ Dᵉ)) bᵉ)))
        ( equiv-binary-coproduct-Decomposition-Σ-Decompositionᵉ)
        ( λ Dᵉ →
          equiv-productᵉ
            ( equiv-Π-equiv-familyᵉ
              ( λ a'ᵉ →
                equiv-eqᵉ
                  ( apᵉ Sᵉ
                    ( invᵉ
                      ( compute-left-equiv-binary-coproduct-Decomposition-Σ-Decompositionᵉ
                        ( Dᵉ)
                        ( a'ᵉ))))))
            ( equiv-Π-equiv-familyᵉ
              ( λ b'ᵉ →
                equiv-eqᵉ
                  ( apᵉ Tᵉ
                    ( invᵉ
                      ( compute-right-equiv-binary-coproduct-Decomposition-Σ-Decompositionᵉ
                        ( Dᵉ)
                        ( b'ᵉ)))))))) ∘eᵉ
      ( ( inv-associative-Σᵉ
          ( Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ)
          ( λ dᵉ →
            binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ
              ( indexing-type-Relaxed-Σ-Decompositionᵉ dᵉ))
              ( _)) ∘eᵉ
        ( equiv-totᵉ
          ( λ dᵉ → distributive-Π-coproduct-binary-coproduct-Decompositionᵉ))))
```