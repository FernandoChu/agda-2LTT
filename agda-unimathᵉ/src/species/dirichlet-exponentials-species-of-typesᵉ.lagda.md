# Dirichlet exponentials of a species of types

```agda
module species.dirichlet-exponentials-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.arithmetic-law-product-and-pi-decompositionsᵉ
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
open import foundation.pi-decompositionsᵉ
open import foundation.product-decompositionsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import species.coproducts-species-of-typesᵉ
open import species.dirichlet-products-species-of-typesᵉ
open import species.equivalences-species-of-typesᵉ
open import species.species-of-typesᵉ
```

</details>

## Idea

Theᵉ **Dirichletᵉ exponential**ᵉ ofᵉ aᵉ speciesᵉ ofᵉ typesᵉ `S`ᵉ isᵉ definedᵉ asᵉ followsᵉ:

```text
  Xᵉ ↦ᵉ Σᵉ ((Uᵉ ,ᵉ Vᵉ ,ᵉ eᵉ) : Π-Decompositionᵉ X),ᵉ  Πᵉ (uᵉ : Uᵉ) → Sᵉ (Vᵉ u).ᵉ
```

## Definition

```agda
dirichlet-exponential-species-typesᵉ :
  {l1ᵉ l2ᵉ : Level} → species-typesᵉ l1ᵉ l2ᵉ → species-typesᵉ l1ᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
dirichlet-exponential-species-typesᵉ {l1ᵉ} {l2ᵉ} Sᵉ Xᵉ =
  Σᵉ ( Π-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ)
    ( λ Dᵉ →
      ( bᵉ : indexing-type-Π-Decompositionᵉ Dᵉ) →
      ( Sᵉ (cotype-Π-Decompositionᵉ Dᵉ bᵉ)))
```

## Properties

### The Dirichlet exponential of the sum of a species is equivalent to the Dirichlet product of the exponential of the two species

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Sᵉ : species-typesᵉ l1ᵉ l2ᵉ)
  (Tᵉ : species-typesᵉ l1ᵉ l3ᵉ)
  where

  private
    reassociateᵉ :
      ( Xᵉ : UUᵉ l1ᵉ) →
      Σᵉ ( Σᵉ ( binary-product-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ)
            ( λ dᵉ →
              ( Π-Decompositionᵉ l1ᵉ l1ᵉ
                ( left-summand-binary-product-Decompositionᵉ dᵉ)) ×ᵉ
              ( Π-Decompositionᵉ l1ᵉ l1ᵉ
                ( right-summand-binary-product-Decompositionᵉ dᵉ))))
        ( λ Dᵉ →
          ( ( bᵉ : indexing-type-Π-Decompositionᵉ (pr1ᵉ (pr2ᵉ Dᵉ))) →
            Sᵉ ( cotype-Π-Decompositionᵉ (pr1ᵉ (pr2ᵉ Dᵉ)) bᵉ)) ×ᵉ
          ( ( bᵉ : indexing-type-Π-Decompositionᵉ (pr2ᵉ (pr2ᵉ Dᵉ))) →
            Tᵉ ( cotype-Π-Decompositionᵉ (pr2ᵉ (pr2ᵉ Dᵉ)) bᵉ))) ≃ᵉ
      dirichlet-product-species-typesᵉ
        ( dirichlet-exponential-species-typesᵉ Sᵉ)
        ( dirichlet-exponential-species-typesᵉ Tᵉ)
        ( Xᵉ)
    pr1ᵉ (reassociateᵉ Xᵉ) ((dᵉ ,ᵉ dlᵉ ,ᵉ drᵉ) ,ᵉ sᵉ ,ᵉ tᵉ) =
      ( dᵉ ,ᵉ (dlᵉ ,ᵉ sᵉ) ,ᵉ drᵉ ,ᵉ tᵉ)
    pr2ᵉ (reassociateᵉ Xᵉ) =
      is-equiv-is-invertibleᵉ
        ( λ ( dᵉ ,ᵉ (dlᵉ ,ᵉ sᵉ) ,ᵉ drᵉ ,ᵉ tᵉ) → ((dᵉ ,ᵉ dlᵉ ,ᵉ drᵉ) ,ᵉ sᵉ ,ᵉ tᵉ))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)

  equiv-dirichlet-exponential-sum-species-typesᵉ :
    equiv-species-typesᵉ
      ( dirichlet-exponential-species-typesᵉ (coproduct-species-typesᵉ Sᵉ Tᵉ))
      ( dirichlet-product-species-typesᵉ
        ( dirichlet-exponential-species-typesᵉ Sᵉ)
        ( dirichlet-exponential-species-typesᵉ Tᵉ))
  equiv-dirichlet-exponential-sum-species-typesᵉ Xᵉ =
    ( reassociateᵉ Xᵉ) ∘eᵉ
    ( ( equiv-Σᵉ
        ( λ Dᵉ →
          ( ( bᵉ : indexing-type-Π-Decompositionᵉ (pr1ᵉ (pr2ᵉ Dᵉ))) →
            Sᵉ (cotype-Π-Decompositionᵉ (pr1ᵉ (pr2ᵉ Dᵉ)) bᵉ)) ×ᵉ
          ( ( bᵉ : indexing-type-Π-Decompositionᵉ (pr2ᵉ (pr2ᵉ Dᵉ))) →
            Tᵉ (cotype-Π-Decompositionᵉ (pr2ᵉ (pr2ᵉ Dᵉ)) bᵉ)))
        ( equiv-binary-product-Decomposition-Π-Decompositionᵉ)
        ( λ Dᵉ →
          equiv-productᵉ
            ( equiv-Π-equiv-familyᵉ
              ( λ a'ᵉ →
                equiv-eqᵉ
                  ( apᵉ Sᵉ
                    ( invᵉ
                      ( compute-left-equiv-binary-product-Decomposition-Π-Decompositionᵉ
                        ( Dᵉ)
                        ( a'ᵉ))))))
            ( equiv-Π-equiv-familyᵉ
              ( λ b'ᵉ →
                equiv-eqᵉ
                  ( apᵉ Tᵉ
                    ( invᵉ
                      ( compute-right-equiv-binary-product-Decomposition-Π-Decompositionᵉ
                        ( Dᵉ)
                        ( b'ᵉ)))))))) ∘eᵉ
      ( ( inv-associative-Σᵉ
          ( Π-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ)
          ( λ dᵉ →
            binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ
              ( indexing-type-Π-Decompositionᵉ dᵉ))
              ( _)) ∘eᵉ
        ( equiv-totᵉ
          ( λ dᵉ → distributive-Π-coproduct-binary-coproduct-Decompositionᵉ))))
```