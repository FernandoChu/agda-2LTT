# Dirichlet products of species of types in subuniverses

```agda
module species.dirichlet-products-species-of-types-in-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.global-subuniversesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.product-decompositionsᵉ
open import foundation.product-decompositions-subuniverseᵉ
open import foundation.propositionsᵉ
open import foundation.subuniversesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import species.dirichlet-products-species-of-typesᵉ
open import species.species-of-types-in-subuniversesᵉ
```

</details>

## Idea

Theᵉ Dirichletᵉ productᵉ ofᵉ twoᵉ speciesᵉ ofᵉ subuniverseᵉ `S`ᵉ andᵉ `T`ᵉ fromᵉ `P`ᵉ to `Q`ᵉ
onᵉ `X`ᵉ isᵉ definedᵉ asᵉ

```text
  Σᵉ (kᵉ : Pᵉ) (Σᵉ (k'ᵉ : Pᵉ) (Σᵉ (eᵉ : kᵉ ×ᵉ k'ᵉ ≃ᵉ Xᵉ) S(kᵉ) ×ᵉ T(k'ᵉ)))
```

Ifᵉ `Q`ᵉ isᵉ stableᵉ byᵉ productᵉ andᵉ dependentᵉ pairᵉ typeᵉ overᵉ `P`ᵉ type,ᵉ thenᵉ theᵉ
dirichletᵉ productᵉ isᵉ alsoᵉ aᵉ speciesᵉ ofᵉ subuniverseᵉ fromᵉ `P`ᵉ to `Q`ᵉ

## Definition

### The underlying type of the Dirichlet product of species in a subuniverse

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  where

  type-dirichlet-product-species-subuniverseᵉ :
    (Sᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
    (Tᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
    (Xᵉ : type-subuniverseᵉ Pᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  type-dirichlet-product-species-subuniverseᵉ Sᵉ Tᵉ Xᵉ =
    Σᵉ ( binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ)
      ( λ dᵉ →
        inclusion-subuniverseᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
          ( Sᵉ (left-summand-binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ dᵉ)) ×ᵉ
        inclusion-subuniverseᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
          ( Tᵉ (right-summand-binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ dᵉ)))
```

### Subuniverses closed under the Dirichlet product of species in a subuniverse

```agda
is-closed-under-dirichlet-product-species-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ)) →
  UUωᵉ
is-closed-under-dirichlet-product-species-subuniverseᵉ {l1ᵉ} {l2ᵉ} Pᵉ Qᵉ =
  {l3ᵉ l4ᵉ : Level}
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  (Xᵉ : type-subuniverseᵉ Pᵉ) →
  is-in-subuniverseᵉ
    ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
    ( type-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ Xᵉ)
```

### The Dirichlet product of species of types in a subuniverse

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  ( C1ᵉ : is-closed-under-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ)
  where

  dirichlet-product-species-subuniverseᵉ :
    species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ) →
    species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ) →
    species-subuniverseᵉ Pᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
  pr1ᵉ (dirichlet-product-species-subuniverseᵉ Sᵉ Tᵉ Xᵉ) =
    type-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ Xᵉ
  pr2ᵉ (dirichlet-product-species-subuniverseᵉ Sᵉ Tᵉ Xᵉ) = C1ᵉ Sᵉ Tᵉ Xᵉ
```

## Properties

### Associativity

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  ( Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  ( C1ᵉ : is-closed-under-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ)
  ( C2ᵉ : is-closed-under-products-subuniverseᵉ Pᵉ)
  where

  module _
    (Sᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
    (Tᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
    (Uᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l5ᵉ))
    (Xᵉ : type-subuniverseᵉ Pᵉ)
    where

    equiv-left-iterated-dirichlet-product-species-subuniverseᵉ :
      type-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ
        ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
        ( Uᵉ)
        ( Xᵉ) ≃ᵉ
      Σᵉ ( ternary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ)
        ( λ dᵉ →
          inclusion-subuniverseᵉ
            ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
            ( Sᵉ
              ( first-summand-ternary-product-Decomposition-Subuniverseᵉ
                Pᵉ
                Xᵉ
                dᵉ)) ×ᵉ
            ( inclusion-subuniverseᵉ
              ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
              ( Tᵉ
                ( second-summand-ternary-product-Decomposition-Subuniverseᵉ
                  Pᵉ
                  Xᵉ
                  dᵉ)) ×ᵉ
              inclusion-subuniverseᵉ
                ( subuniverse-global-subuniverseᵉ Qᵉ l5ᵉ)
                ( Uᵉ
                  ( third-summand-ternary-product-Decomposition-Subuniverseᵉ
                    Pᵉ
                    Xᵉ
                    dᵉ))))
    equiv-left-iterated-dirichlet-product-species-subuniverseᵉ =
      ( ( equiv-Σᵉ
          ( λ dᵉ →
            inclusion-subuniverseᵉ
              ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
              ( Sᵉ
                ( first-summand-ternary-product-Decomposition-Subuniverseᵉ
                  Pᵉ
                  Xᵉ
                  dᵉ)) ×ᵉ
            ( inclusion-subuniverseᵉ
              ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
              ( Tᵉ
                ( second-summand-ternary-product-Decomposition-Subuniverseᵉ
                  Pᵉ
                  Xᵉ
                  dᵉ)) ×ᵉ
              inclusion-subuniverseᵉ
                ( subuniverse-global-subuniverseᵉ Qᵉ l5ᵉ)
                ( Uᵉ
                  ( third-summand-ternary-product-Decomposition-Subuniverseᵉ
                    Pᵉ
                    Xᵉ
                    dᵉ)))))
          ( ( equiv-Σᵉ
              ( _)
              ( associative-productᵉ _ _ _ ∘eᵉ commutative-productᵉ)
              ( λ xᵉ →
                equiv-postcomp-equivᵉ
                  ( ( associative-productᵉ _ _ _ ∘eᵉ
                    ( commutative-productᵉ)))
                  ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
              equiv-ternary-left-iterated-product-Decomposition-Subuniverseᵉ
                Pᵉ
                Xᵉ
                C2ᵉ))
          ( λ dᵉ → associative-productᵉ _ _ _) ∘eᵉ
        ( ( inv-associative-Σᵉ
            ( binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ)
            ( λ zᵉ → binary-product-Decomposition-Subuniverseᵉ Pᵉ (pr1ᵉ zᵉ))
            ( _)) ∘eᵉ
          ( ( equiv-totᵉ λ dᵉ → right-distributive-product-Σᵉ))))

    equiv-right-iterated-dirichlet-product-species-subuniverseᵉ :
      type-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ
        ( Sᵉ)
        ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Tᵉ Uᵉ)
        ( Xᵉ) ≃ᵉ
      Σᵉ ( ternary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ)
        ( λ dᵉ →
          inclusion-subuniverseᵉ
            ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
            ( Sᵉ
              ( first-summand-ternary-product-Decomposition-Subuniverseᵉ
                Pᵉ
                Xᵉ
                dᵉ)) ×ᵉ
            ( inclusion-subuniverseᵉ
              ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
              ( Tᵉ
                ( second-summand-ternary-product-Decomposition-Subuniverseᵉ
                  Pᵉ
                  Xᵉ
                  dᵉ)) ×ᵉ
                inclusion-subuniverseᵉ
                  ( subuniverse-global-subuniverseᵉ Qᵉ l5ᵉ)
                  ( Uᵉ
                    ( third-summand-ternary-product-Decomposition-Subuniverseᵉ
                      Pᵉ
                      Xᵉ
                      dᵉ))))
    equiv-right-iterated-dirichlet-product-species-subuniverseᵉ =
      ( ( equiv-Σ-equiv-baseᵉ
          ( _)
          ( equiv-ternary-right-iterated-product-Decomposition-Subuniverseᵉ
            Pᵉ
            Xᵉ
            C2ᵉ)) ∘eᵉ
        ( ( inv-associative-Σᵉ
            ( binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ)
            ( λ zᵉ → binary-product-Decomposition-Subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ zᵉ)))
            ( _)) ∘eᵉ
          ( ( equiv-totᵉ (λ dᵉ → left-distributive-product-Σᵉ)))))

    equiv-associative-dirichlet-product-species-subuniverseᵉ :
      type-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ
        ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
        ( Uᵉ)
        ( Xᵉ) ≃ᵉ
      type-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ
        ( Sᵉ)
        ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Tᵉ Uᵉ)
        ( Xᵉ)
    equiv-associative-dirichlet-product-species-subuniverseᵉ =
      inv-equivᵉ (equiv-right-iterated-dirichlet-product-species-subuniverseᵉ) ∘eᵉ
      equiv-left-iterated-dirichlet-product-species-subuniverseᵉ

  module _
    (Sᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
    (Tᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
    (Uᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l5ᵉ))
    where

    associative-dirichlet-product-species-subuniverseᵉ :
      dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ
        ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
        ( Uᵉ) ＝ᵉ
      dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ
        ( Sᵉ)
        ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Tᵉ Uᵉ)
    associative-dirichlet-product-species-subuniverseᵉ =
      eq-equiv-fam-subuniverseᵉ
        ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ))
        ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ
          ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
          ( Uᵉ))
        ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ
          ( Sᵉ)
          ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Tᵉ Uᵉ))
        ( equiv-associative-dirichlet-product-species-subuniverseᵉ Sᵉ Tᵉ Uᵉ)
```

### Dirichlet product is commutative

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (C1ᵉ : is-closed-under-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  where

  equiv-commutative-dirichlet-product-species-subuniverseᵉ :
    (Xᵉ : type-subuniverseᵉ Pᵉ) →
    type-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ Xᵉ ≃ᵉ
    type-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ Tᵉ Sᵉ Xᵉ
  equiv-commutative-dirichlet-product-species-subuniverseᵉ Xᵉ =
    equiv-Σᵉ
      ( λ dᵉ →
        inclusion-subuniverseᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
          ( Tᵉ (left-summand-binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ dᵉ)) ×ᵉ
        inclusion-subuniverseᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
          ( Sᵉ (right-summand-binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ dᵉ)))
      ( equiv-commutative-binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ)
      ( λ _ → commutative-productᵉ)

  commutative-dirichlet-product-species-subuniverseᵉ :
    dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ ＝ᵉ
    dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Tᵉ Sᵉ
  commutative-dirichlet-product-species-subuniverseᵉ =
    eq-equiv-fam-subuniverseᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
      ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
      ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Tᵉ Sᵉ)
      ( equiv-commutative-dirichlet-product-species-subuniverseᵉ)
```

### Unit laws of Dirichlet product

```agda
unit-dirichlet-product-species-subuniverseᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} →
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : subuniverseᵉ l1ᵉ l3ᵉ) →
  ( (Xᵉ : type-subuniverseᵉ Pᵉ) →
    is-in-subuniverseᵉ Qᵉ ( is-contrᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ))) →
  species-subuniverseᵉ Pᵉ Qᵉ
unit-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ Cᵉ Xᵉ =
  is-contrᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ) ,ᵉ Cᵉ Xᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (C1ᵉ : is-closed-under-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ)
  (C2ᵉ : is-in-subuniverseᵉ Pᵉ (raise-unitᵉ l1ᵉ))
  (C3ᵉ :
    (Xᵉ : type-subuniverseᵉ Pᵉ) →
    is-in-subuniverseᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ)
      ( is-contrᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ)))
  (Sᵉ : species-subuniverseᵉ Pᵉ ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  where

  equiv-right-unit-law-dirichlet-product-species-subuniverseᵉ :
    (Xᵉ : type-subuniverseᵉ Pᵉ) →
    type-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ
      ( Sᵉ)
      ( unit-dirichlet-product-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ)
        ( C3ᵉ))
      ( Xᵉ) ≃ᵉ
    inclusion-subuniverseᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ) (Sᵉ Xᵉ)
  equiv-right-unit-law-dirichlet-product-species-subuniverseᵉ Xᵉ =
    ( ( left-unit-law-Σ-is-contrᵉ
        ( is-torsorial-equiv-subuniverseᵉ Pᵉ Xᵉ)
        ( Xᵉ ,ᵉ id-equivᵉ)) ∘eᵉ
      ( ( equiv-Σ-equiv-baseᵉ
          ( λ pᵉ →
            inclusion-subuniverseᵉ
              ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
              ( Sᵉ (pr1ᵉ (pᵉ))))
          (equiv-is-contr-right-summand-binary-product-Decomposition-Subuniverseᵉ
            Pᵉ
            Xᵉ
            C2ᵉ)) ∘eᵉ
        ( ( inv-associative-Σᵉ
            ( binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ)
            ( λ dᵉ →
              inclusion-subuniverseᵉ
                ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ)
                ( unit-dirichlet-product-species-subuniverseᵉ
                  ( Pᵉ)
                  ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ)
                  ( C3ᵉ)
                  ( right-summand-binary-product-Decomposition-Subuniverseᵉ
                    Pᵉ
                    Xᵉ
                    dᵉ)))
            ( λ zᵉ →
              inclusion-subuniverseᵉ
                ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
                ( Sᵉ
                  ( left-summand-binary-product-Decomposition-Subuniverseᵉ
                    Pᵉ
                    Xᵉ
                    (pr1ᵉ zᵉ))))) ∘eᵉ
          ( ( equiv-totᵉ (λ _ → commutative-productᵉ))))))

  equiv-left-unit-law-dirichlet-product-species-subuniverseᵉ :
    (Xᵉ : type-subuniverseᵉ Pᵉ) →
    type-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ
      ( unit-dirichlet-product-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ)
        ( C3ᵉ))
      ( Sᵉ)
      ( Xᵉ) ≃ᵉ
    inclusion-subuniverseᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ) (Sᵉ Xᵉ)
  equiv-left-unit-law-dirichlet-product-species-subuniverseᵉ Xᵉ =
    equiv-right-unit-law-dirichlet-product-species-subuniverseᵉ Xᵉ ∘eᵉ
    equiv-commutative-dirichlet-product-species-subuniverseᵉ
      ( Pᵉ)
      ( Qᵉ)
      ( C1ᵉ)
      ( unit-dirichlet-product-species-subuniverseᵉ
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
  ( Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  ( C1ᵉ : is-closed-under-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ)
  ( C2ᵉ : is-closed-under-products-subuniverseᵉ Pᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  (Xᵉ : UUᵉ l1ᵉ)
  where

  private
    reassociateᵉ :
      Σ-extension-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
        ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
        ( Xᵉ) ≃ᵉ
      Σᵉ ( binary-product-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ)
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
      Σᵉ ( binary-product-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ)
        ( λ dᵉ →
          Σᵉ ( Σᵉ (pr1ᵉ (Pᵉ (pr1ᵉ dᵉ))) (λ vᵉ → pr1ᵉ (Pᵉ (pr1ᵉ (pr2ᵉ dᵉ)))))
          (λ pᵉ → pr1ᵉ (Sᵉ (pr1ᵉ dᵉ ,ᵉ pr1ᵉ pᵉ)) ×ᵉ pr1ᵉ (Tᵉ (pr1ᵉ (pr2ᵉ dᵉ) ,ᵉ pr2ᵉ pᵉ))))
      ≃ᵉ
      dirichlet-product-species-typesᵉ
        ( Σ-extension-species-subuniverseᵉ Pᵉ
          ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ) Sᵉ)
        ( Σ-extension-species-subuniverseᵉ Pᵉ
          ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ) Tᵉ)
        ( Xᵉ)
    pr1ᵉ reassociate'ᵉ (dᵉ ,ᵉ (pAᵉ ,ᵉ pBᵉ) ,ᵉ sᵉ ,ᵉ tᵉ) =
      dᵉ ,ᵉ (pAᵉ ,ᵉ sᵉ) ,ᵉ (pBᵉ ,ᵉ tᵉ)
    pr2ᵉ reassociate'ᵉ =
      is-equiv-is-invertibleᵉ
        ( λ ( dᵉ ,ᵉ (pAᵉ ,ᵉ sᵉ) ,ᵉ (pBᵉ ,ᵉ tᵉ)) → (dᵉ ,ᵉ (pAᵉ ,ᵉ pBᵉ) ,ᵉ sᵉ ,ᵉ tᵉ))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)

  equiv-dirichlet-product-Σ-extension-species-subuniverseᵉ :
    Σ-extension-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
      ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
      ( Xᵉ) ≃ᵉ
    dirichlet-product-species-typesᵉ
      ( Σ-extension-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
        ( Sᵉ))
      ( Σ-extension-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
        ( Tᵉ))
      ( Xᵉ)
  equiv-dirichlet-product-Σ-extension-species-subuniverseᵉ =
    ( ( reassociate'ᵉ) ∘eᵉ
      ( ( equiv-totᵉ
          ( λ dᵉ →
            equiv-Σ-equiv-baseᵉ
              (λ pᵉ →
                  ( inclusion-subuniverseᵉ
                    ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
                    ( Sᵉ
                      ( left-summand-binary-product-Decompositionᵉ dᵉ ,ᵉ
                        pr1ᵉ pᵉ))) ×ᵉ
                  ( inclusion-subuniverseᵉ
                    ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
                    ( Tᵉ
                      ( right-summand-binary-product-Decompositionᵉ dᵉ ,ᵉ
                        pr2ᵉ pᵉ))))
              ( inv-equivᵉ
                ( equiv-add-redundant-propᵉ
                  ( is-prop-type-Propᵉ (Pᵉ Xᵉ))
                  ( λ pᵉ →
                    trᵉ
                      ( is-in-subuniverseᵉ Pᵉ)
                      ( invᵉ
                        ( eq-equivᵉ
                          ( matching-correspondence-binary-product-Decompositionᵉ
                            ( dᵉ))))
                      ( C2ᵉ
                        ( pr1ᵉ pᵉ)
                        ( pr2ᵉ pᵉ))))))) ∘eᵉ
        ( reassociateᵉ)))
```