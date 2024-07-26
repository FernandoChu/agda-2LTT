# Cauchy products of species of types in a subuniverse

```agda
module species.cauchy-products-species-of-types-in-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-decompositionsᵉ
open import foundation.coproduct-decompositions-subuniverseᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.global-subuniversesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subuniversesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import species.cauchy-products-species-of-typesᵉ
open import species.species-of-types-in-subuniversesᵉ
```

</details>

## Idea

Theᵉ **Cauchyᵉ product**ᵉ ofᵉ twoᵉ speciesᵉ `S`ᵉ andᵉ `T`ᵉ fromᵉ `P`ᵉ to `Q`ᵉ ofᵉ typesᵉ in aᵉ
subuniverseᵉ isᵉ definedᵉ byᵉ

```text
  Xᵉ ↦ᵉ Σᵉ (kᵉ : P),ᵉ Σᵉ (k'ᵉ : P),ᵉ Σᵉ (eᵉ : kᵉ +ᵉ k'ᵉ ≃ᵉ X),ᵉ S(kᵉ) ×ᵉ T(k'ᵉ)
```

Ifᵉ `Q`ᵉ isᵉ closedᵉ underᵉ productsᵉ andᵉ dependentᵉ pairᵉ typesᵉ overᵉ typesᵉ in `P`,ᵉ thenᵉ
theᵉ Cauchyᵉ productᵉ isᵉ alsoᵉ aᵉ speciesᵉ ofᵉ subuniverseᵉ fromᵉ `P`ᵉ to `Q`.ᵉ

## Definition

### The underlying type of the Cauchy product of species in a subuniverse

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  where

  type-cauchy-product-species-subuniverseᵉ :
    (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
    (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
    (Xᵉ : type-subuniverseᵉ Pᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  type-cauchy-product-species-subuniverseᵉ Sᵉ Tᵉ Xᵉ =
    Σᵉ ( binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ)
      ( λ dᵉ →
        inclusion-subuniverseᵉ
          ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
          ( Sᵉ (left-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ dᵉ)) ×ᵉ
        inclusion-subuniverseᵉ
          ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
          ( Tᵉ (right-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ dᵉ)))
```

### Subuniverses closed under the Cauchy product of species in a subuniverse

```agda
is-closed-under-cauchy-product-species-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ)) →
  UUωᵉ
is-closed-under-cauchy-product-species-subuniverseᵉ {l1ᵉ} {l2ᵉ} Pᵉ Qᵉ =
  {l3ᵉ l4ᵉ : Level}
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  (Xᵉ : type-subuniverseᵉ Pᵉ) →
  is-in-subuniverseᵉ
    ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
    ( type-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ Xᵉ)
```

### The Cauchy product of species in a subuniverse

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  ( C1ᵉ : is-closed-under-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ)
  where

  cauchy-product-species-subuniverseᵉ :
    species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ) →
    species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ) →
    species-subuniverseᵉ Pᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
  pr1ᵉ (cauchy-product-species-subuniverseᵉ Sᵉ Tᵉ Xᵉ) =
    type-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ Xᵉ
  pr2ᵉ (cauchy-product-species-subuniverseᵉ Sᵉ Tᵉ Xᵉ) = C1ᵉ Sᵉ Tᵉ Xᵉ
```

## Properties

### Cauchy product is associative

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  ( C1ᵉ : is-closed-under-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ)
  ( C2ᵉ : is-closed-under-coproducts-subuniverseᵉ Pᵉ)
  where

  module _
    (Sᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
    (Tᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
    (Uᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l5ᵉ))
    (Xᵉ : type-subuniverseᵉ Pᵉ)
    where

    equiv-left-iterated-cauchy-product-species-subuniverseᵉ :
      type-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ
        ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
        ( Uᵉ)
        ( Xᵉ) ≃ᵉ
      Σᵉ ( ternary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ)
        ( λ dᵉ →
          inclusion-subuniverseᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
            ( Sᵉ
              ( first-summand-ternary-coproduct-Decomposition-subuniverseᵉ
                Pᵉ Xᵉ dᵉ)) ×ᵉ
            ( inclusion-subuniverseᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
              ( Tᵉ
                ( second-summand-ternary-coproduct-Decomposition-subuniverseᵉ
                  Pᵉ Xᵉ dᵉ)) ×ᵉ
              inclusion-subuniverseᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l5ᵉ)
              ( Uᵉ
                ( third-summand-ternary-coproduct-Decomposition-subuniverseᵉ
                  Pᵉ Xᵉ dᵉ))))
    equiv-left-iterated-cauchy-product-species-subuniverseᵉ =
      ( ( equiv-Σᵉ
          ( λ dᵉ →
            inclusion-subuniverseᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
            ( Sᵉ
              ( first-summand-ternary-coproduct-Decomposition-subuniverseᵉ
                  Pᵉ Xᵉ dᵉ)) ×ᵉ
            ( inclusion-subuniverseᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
              ( Tᵉ
                ( second-summand-ternary-coproduct-Decomposition-subuniverseᵉ
                    Pᵉ Xᵉ dᵉ)) ×ᵉ
              inclusion-subuniverseᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l5ᵉ)
              ( Uᵉ
                ( third-summand-ternary-coproduct-Decomposition-subuniverseᵉ
                    Pᵉ Xᵉ dᵉ)))))
          ( ( equiv-Σᵉ
              ( _)
              ( associative-productᵉ _ _ _ ∘eᵉ commutative-productᵉ)
              ( λ xᵉ →
                equiv-postcomp-equivᵉ
                  ( ( ( associative-coproductᵉ) ∘eᵉ
                    ( ( commutative-coproductᵉ _ _))))
                  ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
              equiv-ternary-left-iterated-coproduct-Decomposition-subuniverseᵉ
                Pᵉ Xᵉ C2ᵉ))
          ( λ dᵉ → associative-productᵉ _ _ _) ∘eᵉ
        ( ( inv-associative-Σᵉ
            ( binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ)
            ( λ zᵉ → binary-coproduct-Decomposition-subuniverseᵉ Pᵉ (pr1ᵉ zᵉ))
            ( _)) ∘eᵉ
          ( ( equiv-totᵉ λ dᵉ → right-distributive-product-Σᵉ))))

    equiv-right-iterated-cauchy-product-species-subuniverseᵉ :
      type-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ
        ( Sᵉ)
        ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Tᵉ Uᵉ)
        ( Xᵉ) ≃ᵉ
      Σᵉ ( ternary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ)
        ( λ dᵉ →
          inclusion-subuniverseᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
            ( Sᵉ
              ( first-summand-ternary-coproduct-Decomposition-subuniverseᵉ
                Pᵉ Xᵉ dᵉ)) ×ᵉ
            ( inclusion-subuniverseᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
              ( Tᵉ
                ( second-summand-ternary-coproduct-Decomposition-subuniverseᵉ
                  Pᵉ Xᵉ dᵉ)) ×ᵉ
              inclusion-subuniverseᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l5ᵉ)
              ( Uᵉ
                ( third-summand-ternary-coproduct-Decomposition-subuniverseᵉ
                  Pᵉ Xᵉ dᵉ))))
    equiv-right-iterated-cauchy-product-species-subuniverseᵉ =
      ( ( equiv-Σ-equiv-baseᵉ
          ( _)
          ( equiv-ternary-right-iterated-coproduct-Decomposition-subuniverseᵉ
              Pᵉ Xᵉ C2ᵉ)) ∘eᵉ
        ( ( inv-associative-Σᵉ
            ( binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ)
            ( λ zᵉ → binary-coproduct-Decomposition-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ zᵉ)))
            ( _)) ∘eᵉ
          ( ( equiv-totᵉ (λ dᵉ → left-distributive-product-Σᵉ)))))

    equiv-associative-cauchy-product-species-subuniverseᵉ :
      type-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ
        ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
        ( Uᵉ)
        ( Xᵉ) ≃ᵉ
      type-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ
        ( Sᵉ)
        ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Tᵉ Uᵉ)
        ( Xᵉ)
    equiv-associative-cauchy-product-species-subuniverseᵉ =
      inv-equivᵉ (equiv-right-iterated-cauchy-product-species-subuniverseᵉ) ∘eᵉ
      equiv-left-iterated-cauchy-product-species-subuniverseᵉ

  module _
    (Sᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
    (Tᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
    (Uᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l5ᵉ))
    where

    associative-cauchy-product-species-subuniverseᵉ :
      cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ
        ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
        ( Uᵉ) ＝ᵉ
      cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ
        ( Sᵉ)
        ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Tᵉ Uᵉ)
    associative-cauchy-product-species-subuniverseᵉ =
      eq-equiv-fam-subuniverseᵉ
        ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ))
        ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ
          ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
          ( Uᵉ))
        ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ
          ( Sᵉ)
          ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Tᵉ Uᵉ))
        ( equiv-associative-cauchy-product-species-subuniverseᵉ Sᵉ Tᵉ Uᵉ)
```

### Cauchy product is commutative

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (C1ᵉ : is-closed-under-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  where

  equiv-commutative-cauchy-product-species-subuniverseᵉ :
    (Xᵉ : type-subuniverseᵉ Pᵉ) →
    type-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ Xᵉ ≃ᵉ
    type-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ Tᵉ Sᵉ Xᵉ
  equiv-commutative-cauchy-product-species-subuniverseᵉ Xᵉ =
    equiv-Σᵉ
      ( λ dᵉ →
        inclusion-subuniverseᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
          ( Tᵉ (left-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ dᵉ)) ×ᵉ
        inclusion-subuniverseᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
          ( Sᵉ (right-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ dᵉ)))
      ( equiv-commutative-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ)
      ( λ _ → commutative-productᵉ)

  commutative-cauchy-product-species-subuniverseᵉ :
    cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ ＝ᵉ
    cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Tᵉ Sᵉ
  commutative-cauchy-product-species-subuniverseᵉ =
    eq-equiv-fam-subuniverseᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
      ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
      ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Tᵉ Sᵉ)
      ( equiv-commutative-cauchy-product-species-subuniverseᵉ)
```

### Unit laws of Cauchy product

```agda
unit-cauchy-product-species-subuniverseᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} → (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) → (Qᵉ : subuniverseᵉ l1ᵉ l3ᵉ) →
  ( (Xᵉ : type-subuniverseᵉ Pᵉ) →
    is-in-subuniverseᵉ Qᵉ ( is-emptyᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ))) →
  species-subuniverseᵉ Pᵉ Qᵉ
unit-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ Cᵉ Xᵉ =
  is-emptyᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ) ,ᵉ Cᵉ Xᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (C1ᵉ : is-closed-under-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ)
  (C2ᵉ : is-in-subuniverseᵉ Pᵉ (raise-emptyᵉ l1ᵉ))
  (C3ᵉ :
    (Xᵉ : type-subuniverseᵉ Pᵉ) →
    is-in-subuniverseᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ)
      ( is-emptyᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ)))
  (Sᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  where

  equiv-right-unit-law-cauchy-product-species-subuniverseᵉ :
    (Xᵉ : type-subuniverseᵉ Pᵉ) →
    type-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ
      ( Sᵉ)
      ( unit-cauchy-product-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ)
        ( C3ᵉ))
      ( Xᵉ) ≃ᵉ
    inclusion-subuniverseᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ) (Sᵉ Xᵉ)
  equiv-right-unit-law-cauchy-product-species-subuniverseᵉ Xᵉ =
    ( ( left-unit-law-Σ-is-contrᵉ
        ( is-torsorial-equiv-subuniverseᵉ Pᵉ Xᵉ)
        ( Xᵉ ,ᵉ id-equivᵉ)) ∘eᵉ
      ( ( equiv-Σ-equiv-baseᵉ
          ( λ pᵉ →
            inclusion-subuniverseᵉ
              ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
              ( Sᵉ (pr1ᵉ (pᵉ))))
          ( equiv-is-empty-right-summand-binary-coproduct-Decomposition-subuniverseᵉ
            Pᵉ
            Xᵉ
            C2ᵉ)) ∘eᵉ
        ( ( inv-associative-Σᵉ
            ( binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ)
            ( λ dᵉ →
              inclusion-subuniverseᵉ
                ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ)
                ( unit-cauchy-product-species-subuniverseᵉ
                  ( Pᵉ)
                  ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ)
                  ( C3ᵉ)
                  ( right-summand-binary-coproduct-Decomposition-subuniverseᵉ
                      Pᵉ Xᵉ dᵉ)))
            ( λ zᵉ →
              inclusion-subuniverseᵉ
                ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
                ( Sᵉ
                  ( left-summand-binary-coproduct-Decomposition-subuniverseᵉ
                    Pᵉ
                    Xᵉ
                    (pr1ᵉ zᵉ))))) ∘eᵉ
          ( ( equiv-totᵉ (λ _ → commutative-productᵉ))))))

  equiv-left-unit-law-cauchy-product-species-subuniverseᵉ :
    (Xᵉ : type-subuniverseᵉ Pᵉ) →
    type-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ
      ( unit-cauchy-product-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ)
        ( C3ᵉ))
      ( Sᵉ)
      ( Xᵉ) ≃ᵉ
    inclusion-subuniverseᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ) (Sᵉ Xᵉ)
  equiv-left-unit-law-cauchy-product-species-subuniverseᵉ Xᵉ =
    equiv-right-unit-law-cauchy-product-species-subuniverseᵉ Xᵉ ∘eᵉ
    equiv-commutative-cauchy-product-species-subuniverseᵉ
      ( Pᵉ)
      ( Qᵉ)
      ( C1ᵉ)
      ( unit-cauchy-product-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ)
        ( C3ᵉ))
      ( Sᵉ)
      ( Xᵉ)
```

### Equivalent form with species of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  ( C1ᵉ : is-closed-under-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ)
  ( C2ᵉ : is-closed-under-coproducts-subuniverseᵉ Pᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  (Xᵉ : UUᵉ l1ᵉ)
  where

  private
    reassociateᵉ :
      Σ-extension-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
        ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
        ( Xᵉ) ≃ᵉ
      Σᵉ ( binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ)
        ( λ (Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) →
          Σᵉ ( ( is-in-subuniverseᵉ Pᵉ Aᵉ ×ᵉ is-in-subuniverseᵉ Pᵉ Bᵉ) ×ᵉ
              is-in-subuniverseᵉ Pᵉ Xᵉ)
            ( λ ((pAᵉ ,ᵉ pBᵉ) ,ᵉ pXᵉ) →
              inclusion-subuniverseᵉ
                ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
                ( Sᵉ (Aᵉ ,ᵉ pAᵉ)) ×ᵉ
              inclusion-subuniverseᵉ
                ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
                ( Tᵉ (Bᵉ ,ᵉ pBᵉ))))
    pr1ᵉ reassociateᵉ (pXᵉ ,ᵉ ((Aᵉ ,ᵉ pAᵉ) ,ᵉ (Bᵉ ,ᵉ pBᵉ) ,ᵉ eᵉ) ,ᵉ sᵉ ,ᵉ tᵉ) =
      (Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ ((pAᵉ ,ᵉ pBᵉ) ,ᵉ pXᵉ) ,ᵉ (sᵉ ,ᵉ tᵉ)
    pr2ᵉ reassociateᵉ = is-equiv-is-invertibleᵉ
      ( λ ((Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ ((pAᵉ ,ᵉ pBᵉ) ,ᵉ pXᵉ) ,ᵉ (sᵉ ,ᵉ tᵉ)) →
        ( pXᵉ ,ᵉ ((Aᵉ ,ᵉ pAᵉ) ,ᵉ (Bᵉ ,ᵉ pBᵉ) ,ᵉ eᵉ) ,ᵉ sᵉ ,ᵉ tᵉ))
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)

    reassociate'ᵉ :
      Σᵉ ( binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ)
        ( λ dᵉ →
          Σᵉ ( Σᵉ (pr1ᵉ (Pᵉ (pr1ᵉ dᵉ))) (λ vᵉ → pr1ᵉ (Pᵉ (pr1ᵉ (pr2ᵉ dᵉ)))))
            ( λ pᵉ → pr1ᵉ (Sᵉ (pr1ᵉ dᵉ ,ᵉ pr1ᵉ pᵉ)) ×ᵉ pr1ᵉ (Tᵉ (pr1ᵉ (pr2ᵉ dᵉ) ,ᵉ pr2ᵉ pᵉ))))
      ≃ᵉ
      cauchy-product-species-typesᵉ
      ( Σ-extension-species-subuniverseᵉ Pᵉ
        ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ) Sᵉ)
      ( Σ-extension-species-subuniverseᵉ Pᵉ
        ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ) Tᵉ)
      Xᵉ
    pr1ᵉ reassociate'ᵉ (dᵉ ,ᵉ (pAᵉ ,ᵉ pBᵉ) ,ᵉ sᵉ ,ᵉ tᵉ) =
      dᵉ ,ᵉ (pAᵉ ,ᵉ sᵉ) ,ᵉ (pBᵉ ,ᵉ tᵉ)
    pr2ᵉ reassociate'ᵉ =
      is-equiv-is-invertibleᵉ
        ( λ ( dᵉ ,ᵉ (pAᵉ ,ᵉ sᵉ) ,ᵉ (pBᵉ ,ᵉ tᵉ)) → (dᵉ ,ᵉ (pAᵉ ,ᵉ pBᵉ) ,ᵉ sᵉ ,ᵉ tᵉ))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)

  equiv-cauchy-product-Σ-extension-species-subuniverseᵉ :
    Σ-extension-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
      ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
      ( Xᵉ) ≃ᵉ
    cauchy-product-species-typesᵉ
      ( Σ-extension-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
        ( Sᵉ))
      ( Σ-extension-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
        ( Tᵉ))
      ( Xᵉ)
  equiv-cauchy-product-Σ-extension-species-subuniverseᵉ =
    ( ( reassociate'ᵉ) ∘eᵉ
      ( ( equiv-totᵉ
            ( λ dᵉ →
              equiv-Σ-equiv-baseᵉ
                (λ pᵉ →
                    ( inclusion-subuniverseᵉ
                        ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
                        ( Sᵉ
                          ( left-summand-binary-coproduct-Decompositionᵉ dᵉ ,ᵉ
                            pr1ᵉ pᵉ))) ×ᵉ
                    ( inclusion-subuniverseᵉ
                        ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
                        ( Tᵉ
                          ( right-summand-binary-coproduct-Decompositionᵉ dᵉ ,ᵉ
                            pr2ᵉ pᵉ))))
                ( inv-equivᵉ
                  ( equiv-add-redundant-propᵉ
                    ( is-prop-type-Propᵉ (Pᵉ Xᵉ))
                    ( λ pᵉ →
                      trᵉ
                        ( is-in-subuniverseᵉ Pᵉ)
                        ( invᵉ
                          ( eq-equivᵉ
                            ( matching-correspondence-binary-coproduct-Decompositionᵉ
                              ( dᵉ))))
                        ( C2ᵉ
                          ( pr1ᵉ pᵉ)
                          ( pr2ᵉ pᵉ))))))) ∘eᵉ
        ( reassociateᵉ)))
```