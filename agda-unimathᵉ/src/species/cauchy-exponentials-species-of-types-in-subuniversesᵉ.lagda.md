# Cauchy exponentials of species of types in a subuniverse

```agda
module species.cauchy-exponentials-species-of-types-in-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-decompositionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
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
open import foundation.unit-typeᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import species.cauchy-composition-species-of-types-in-subuniversesᵉ
open import species.cauchy-exponentials-species-of-typesᵉ
open import species.cauchy-products-species-of-types-in-subuniversesᵉ
open import species.coproducts-species-of-typesᵉ
open import species.coproducts-species-of-types-in-subuniversesᵉ
open import species.species-of-types-in-subuniversesᵉ
```

</details>

## Idea

Theᵉ **Cauchyᵉ exponential**ᵉ ofᵉ aᵉ speciesᵉ `Sᵉ : Pᵉ → Q`ᵉ ofᵉ typesᵉ in subuniverseᵉ isᵉ
definedᵉ byᵉ

```text
  Xᵉ ↦ᵉ Σᵉ ((Uᵉ ,ᵉ Vᵉ ,ᵉ eᵉ) : Σ-Decomposition-subuniverseᵉ Pᵉ X),ᵉ  Πᵉ (uᵉ : Uᵉ) → Sᵉ (Vᵉ u).ᵉ
```

Ifᵉ `Q`ᵉ isᵉ aᵉ globalᵉ subuniverse,ᵉ andᵉ ifᵉ theᵉ previousᵉ definitionᵉ isᵉ in `Q`,ᵉ thenᵉ
theᵉ Cauchyᵉ exponentialᵉ isᵉ alsoᵉ aᵉ speciesᵉ ofᵉ typesᵉ in subuniverseᵉ fromᵉ `P`ᵉ to
`Q`.ᵉ

## Definition

### The underlying type of the Cauchy exponential of species in a subuniverse

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  where

  type-cauchy-exponential-species-subuniverseᵉ :
    (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
    (Xᵉ : type-subuniverseᵉ Pᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  type-cauchy-exponential-species-subuniverseᵉ Sᵉ Xᵉ =
    Σᵉ ( Σ-Decomposition-Subuniverseᵉ Pᵉ Xᵉ)
      ( λ Dᵉ →
        ( bᵉ : indexing-type-Σ-Decomposition-Subuniverseᵉ Pᵉ Xᵉ Dᵉ) →
        ( inclusion-subuniverseᵉ
            ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
            ( Sᵉ (subuniverse-cotype-Σ-Decomposition-Subuniverseᵉ Pᵉ Xᵉ Dᵉ bᵉ))))
```

### Subuniverses closed under the Cauchy exponential of a species in a subuniverse

```agda
is-closed-under-cauchy-exponential-species-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ)) →
  UUωᵉ
is-closed-under-cauchy-exponential-species-subuniverseᵉ {l1ᵉ} {l2ᵉ} Pᵉ Qᵉ =
  {l3ᵉ : Level}
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Xᵉ : type-subuniverseᵉ Pᵉ) →
  is-in-subuniverseᵉ
    ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ))
    ( type-cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Xᵉ)
```

### The Cauchy exponential of a species of types in a subuniverse

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  ( C1ᵉ : is-closed-under-cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ)
  where

  cauchy-exponential-species-subuniverseᵉ :
    species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ) →
    species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ))
  pr1ᵉ (cauchy-exponential-species-subuniverseᵉ Sᵉ Xᵉ) =
    type-cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Xᵉ
  pr2ᵉ (cauchy-exponential-species-subuniverseᵉ Sᵉ Xᵉ) = C1ᵉ Sᵉ Xᵉ
```

## Propositions

### The Cauchy exponential in term of composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (C1ᵉ : is-closed-under-cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ)
  (C2ᵉ : is-in-subuniverseᵉ (subuniverse-global-subuniverseᵉ Qᵉ lzero) unitᵉ)
  (C3ᵉ : is-closed-under-cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ)
  (C4ᵉ : is-closed-under-Σ-subuniverseᵉ Pᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Xᵉ : type-subuniverseᵉ Pᵉ)
  where

  equiv-cauchy-exponential-composition-unit-species-subuniverseᵉ :
    inclusion-subuniverseᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ lzero ⊔ l3ᵉ))
      ( cauchy-composition-species-subuniverseᵉ
        Pᵉ Qᵉ C3ᵉ C4ᵉ (λ _ → unitᵉ ,ᵉ C2ᵉ) Sᵉ Xᵉ) ≃ᵉ
    inclusion-subuniverseᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ))
      ( cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Xᵉ)
  equiv-cauchy-exponential-composition-unit-species-subuniverseᵉ =
    equiv-totᵉ λ _ → left-unit-law-product-is-contrᵉ is-contr-unitᵉ
```

### Equivalence form with species of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  ( C1ᵉ : is-closed-under-cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ)
  ( C2ᵉ :
    ( Uᵉ : UUᵉ l1ᵉ) →
    ( Vᵉ : Uᵉ → UUᵉ l1ᵉ) →
    ( (uᵉ : Uᵉ) → is-in-subuniverseᵉ Pᵉ (Vᵉ uᵉ)) →
    is-in-subuniverseᵉ Pᵉ (Σᵉ Uᵉ Vᵉ) → is-in-subuniverseᵉ Pᵉ Uᵉ)
  ( Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  ( Xᵉ : type-subuniverseᵉ Pᵉ)
  where

  private
    reassociateᵉ :
      Σ-extension-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ))
        ( cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ)
        ( inclusion-subuniverseᵉ Pᵉ Xᵉ) ≃ᵉ
      Σᵉ ( Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ))
        ( λ (Uᵉ ,ᵉ Vᵉ ,ᵉ eᵉ) →
          Σᵉ ( ( is-in-subuniverseᵉ Pᵉ Uᵉ ×ᵉ ((uᵉ : Uᵉ) → is-in-subuniverseᵉ Pᵉ (Vᵉ uᵉ))) ×ᵉ
              is-in-subuniverseᵉ Pᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ))
            ( λ pᵉ → (uᵉ : Uᵉ) → pr1ᵉ (Sᵉ (Vᵉ uᵉ ,ᵉ (pr2ᵉ (pr1ᵉ pᵉ)) uᵉ))))
    pr1ᵉ reassociateᵉ (pXᵉ ,ᵉ ((Uᵉ ,ᵉ pUᵉ) ,ᵉ Vᵉ ,ᵉ eᵉ) ,ᵉ sᵉ) =
      ((Uᵉ ,ᵉ ((λ uᵉ → pr1ᵉ (Vᵉ uᵉ)) ,ᵉ eᵉ)) ,ᵉ ((pUᵉ ,ᵉ (λ uᵉ → pr2ᵉ (Vᵉ uᵉ))) ,ᵉ pXᵉ) ,ᵉ sᵉ)
    pr2ᵉ reassociateᵉ =
      is-equiv-is-invertibleᵉ
        ( λ ((Uᵉ ,ᵉ Vᵉ ,ᵉ eᵉ) ,ᵉ ( ((pUᵉ ,ᵉ pVᵉ) ,ᵉ pXᵉ) ,ᵉ sᵉ)) →
          ( pXᵉ ,ᵉ ((Uᵉ ,ᵉ pUᵉ) ,ᵉ (λ uᵉ → Vᵉ uᵉ ,ᵉ pVᵉ uᵉ) ,ᵉ eᵉ) ,ᵉ sᵉ))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)

    reassociate'ᵉ :
      Σᵉ ( Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ))
        ( λ dᵉ →
          Σᵉ ( ( uᵉ : (indexing-type-Relaxed-Σ-Decompositionᵉ dᵉ)) →
              is-in-subuniverseᵉ Pᵉ (cotype-Relaxed-Σ-Decompositionᵉ dᵉ uᵉ))
            ( λ pᵉ →
              ( ( uᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ dᵉ) →
                inclusion-subuniverseᵉ
                  ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
                  ( Sᵉ (cotype-Relaxed-Σ-Decompositionᵉ dᵉ uᵉ ,ᵉ pᵉ uᵉ)))))
        ≃ᵉ
        cauchy-exponential-species-typesᵉ
          ( Σ-extension-species-subuniverseᵉ
              ( Pᵉ)
              ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
              ( Sᵉ))
        ( inclusion-subuniverseᵉ Pᵉ Xᵉ)
    pr1ᵉ reassociate'ᵉ (dᵉ ,ᵉ pVᵉ ,ᵉ sᵉ) = dᵉ ,ᵉ ( λ uᵉ → (pVᵉ uᵉ) ,ᵉ (sᵉ uᵉ))
    pr2ᵉ reassociate'ᵉ =
      is-equiv-is-invertibleᵉ
        ( λ (dᵉ ,ᵉ fᵉ) → (dᵉ ,ᵉ pr1ᵉ ∘ᵉ fᵉ ,ᵉ pr2ᵉ ∘ᵉ fᵉ))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)

  equiv-cauchy-exponential-Σ-extension-species-subuniverseᵉ :
    Σ-extension-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ))
      ( cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ)
      ( inclusion-subuniverseᵉ Pᵉ Xᵉ) ≃ᵉ
    cauchy-exponential-species-typesᵉ
      ( Σ-extension-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
        ( Sᵉ))
      ( inclusion-subuniverseᵉ Pᵉ Xᵉ)
  equiv-cauchy-exponential-Σ-extension-species-subuniverseᵉ =
    ( reassociate'ᵉ) ∘eᵉ
    ( ( equiv-totᵉ
        ( λ dᵉ →
          equiv-Σ-equiv-baseᵉ
            ( λ pᵉ →
              ( uᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ dᵉ) →
              inclusion-subuniverseᵉ
                ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
                ( Sᵉ (cotype-Relaxed-Σ-Decompositionᵉ dᵉ uᵉ ,ᵉ pᵉ uᵉ)))
            ( ( inv-equivᵉ
                ( equiv-add-redundant-propᵉ
                  ( is-prop-type-Propᵉ
                    ( Pᵉ (indexing-type-Relaxed-Σ-Decompositionᵉ dᵉ)))
                  ( λ pVᵉ →
                    C2ᵉ
                      ( indexing-type-Relaxed-Σ-Decompositionᵉ dᵉ)
                      ( cotype-Relaxed-Σ-Decompositionᵉ dᵉ)
                      ( pVᵉ)
                      ( trᵉ
                        ( is-in-subuniverseᵉ Pᵉ)
                        ( eq-equivᵉ
                          ( matching-correspondence-Relaxed-Σ-Decompositionᵉ dᵉ))
                        ( pr2ᵉ Xᵉ))))) ∘eᵉ
              ( ( commutative-productᵉ) ∘eᵉ
                ( inv-equivᵉ
                  ( equiv-add-redundant-propᵉ
                    ( is-prop-type-Propᵉ (Pᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ)))
                    ( λ _ → pr2ᵉ Xᵉ))))))) ∘eᵉ
      ( reassociateᵉ))
```

### The Cauchy exponential of the sum of a species is equivalent to the Cauchy product of the exponential of the two species

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  ( Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  ( C1ᵉ : is-closed-under-cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ)
  ( C2ᵉ : is-closed-under-coproduct-species-subuniverseᵉ Pᵉ Qᵉ)
  ( C3ᵉ : is-closed-under-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ)
  ( C4ᵉ :
    ( Uᵉ : UUᵉ l1ᵉ) →
    ( Vᵉ : Uᵉ → UUᵉ l1ᵉ) →
    ( (uᵉ : Uᵉ) → is-in-subuniverseᵉ Pᵉ (Vᵉ uᵉ)) →
      ( is-in-subuniverseᵉ Pᵉ (Σᵉ Uᵉ Vᵉ)) →
      ( is-in-subuniverseᵉ Pᵉ Uᵉ))
  ( C5ᵉ : is-closed-under-coproducts-subuniverseᵉ Pᵉ)
  ( C6ᵉ :
    ( Aᵉ Bᵉ : UUᵉ l1ᵉ) →
    is-in-subuniverseᵉ Pᵉ (Aᵉ +ᵉ Bᵉ) →
    is-in-subuniverseᵉ Pᵉ Aᵉ ×ᵉ is-in-subuniverseᵉ Pᵉ Bᵉ)
  ( Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  ( Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  ( Xᵉ : type-subuniverseᵉ Pᵉ)
  where

  equiv-cauchy-exponential-sum-species-subuniverseᵉ :
    inclusion-subuniverseᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
      ( cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ
        ( coproduct-species-subuniverseᵉ Pᵉ Qᵉ C2ᵉ Sᵉ Tᵉ) Xᵉ) ≃ᵉ
    inclusion-subuniverseᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
      ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C3ᵉ
        ( cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ)
        ( cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Tᵉ)
        ( Xᵉ))
  equiv-cauchy-exponential-sum-species-subuniverseᵉ =
    ( ( inv-equivᵉ
        ( equiv-Σ-extension-species-subuniverseᵉ
          ( Pᵉ)
          ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
          ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C3ᵉ
            ( cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ)
            ( cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Tᵉ))
          ( Xᵉ))) ∘eᵉ
      ( ( inv-equivᵉ
          ( equiv-cauchy-product-Σ-extension-species-subuniverseᵉ
            ( Pᵉ)
            ( Qᵉ)
            ( C3ᵉ)
            ( C5ᵉ)
            ( cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ)
            ( cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Tᵉ)
            ( inclusion-subuniverseᵉ Pᵉ Xᵉ))) ∘eᵉ
        ( ( equiv-totᵉ
            ( λ dᵉ →
              equiv-productᵉ
                ( inv-equivᵉ
                  ( equiv-cauchy-exponential-Σ-extension-species-subuniverseᵉ
                    ( Pᵉ)
                    ( Qᵉ)
                    ( C1ᵉ)
                    ( C4ᵉ)
                    ( Sᵉ)
                    ( left-summand-binary-coproduct-Decompositionᵉ dᵉ ,ᵉ
                      pr1ᵉ (lemma-C6ᵉ dᵉ))))
                ( inv-equivᵉ
                  ( equiv-cauchy-exponential-Σ-extension-species-subuniverseᵉ
                    ( Pᵉ)
                    ( Qᵉ)
                    ( C1ᵉ)
                    ( C4ᵉ)
                    ( Tᵉ)
                    ( right-summand-binary-coproduct-Decompositionᵉ dᵉ ,ᵉ
                      pr2ᵉ (lemma-C6ᵉ dᵉ)))))) ∘eᵉ
          ( ( equiv-cauchy-exponential-sum-species-typesᵉ
              ( Σ-extension-species-subuniverseᵉ
                ( Pᵉ)
                ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
                ( Sᵉ))
              ( Σ-extension-species-subuniverseᵉ
                ( Pᵉ)
                ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
                ( Tᵉ))
              ( pr1ᵉ Xᵉ)) ∘eᵉ
            ( ( equiv-totᵉ
                ( λ dᵉ →
                  equiv-Πᵉ
                    ( λ xᵉ →
                      coproduct-species-typesᵉ
                        ( Σ-extension-species-subuniverseᵉ
                          ( Pᵉ)
                          ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
                          ( Sᵉ))
                        ( Σ-extension-species-subuniverseᵉ
                          ( Pᵉ)
                          ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
                          ( Tᵉ))
                        ( cotype-Relaxed-Σ-Decompositionᵉ dᵉ xᵉ))
                    ( id-equivᵉ)
                    ( λ xᵉ →
                      equiv-coproduct-Σ-extension-species-subuniverseᵉ
                        ( Pᵉ)
                        ( Qᵉ)
                        ( C2ᵉ)
                        ( Sᵉ)
                        ( Tᵉ)
                        ( cotype-Relaxed-Σ-Decompositionᵉ dᵉ xᵉ)))) ∘eᵉ
              ( ( equiv-cauchy-exponential-Σ-extension-species-subuniverseᵉ
                  ( Pᵉ)
                  ( Qᵉ)
                  ( C1ᵉ)
                  ( C4ᵉ)
                  ( coproduct-species-subuniverseᵉ Pᵉ Qᵉ C2ᵉ Sᵉ Tᵉ)
                  ( Xᵉ)) ∘eᵉ
                ( equiv-Σ-extension-species-subuniverseᵉ
                  ( Pᵉ)
                  ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
                  ( cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ
                    ( coproduct-species-subuniverseᵉ Pᵉ Qᵉ C2ᵉ Sᵉ Tᵉ))
                  ( Xᵉ))))))))
    where
    lemma-C6ᵉ =
      λ dᵉ →
      C6ᵉ
        ( left-summand-binary-coproduct-Decompositionᵉ dᵉ)
        ( right-summand-binary-coproduct-Decompositionᵉ dᵉ)
        ( trᵉ
          ( is-in-subuniverseᵉ Pᵉ)
          ( eq-equivᵉ (matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ))
          ( pr2ᵉ Xᵉ))
```