# Product decompositions of types in a subuniverse

```agda
module foundation.product-decompositions-subuniverseᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.subuniversesᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Definitions

### Binary product decomposition of types in a subuniverse

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : type-subuniverseᵉ Pᵉ)
  where

  binary-product-Decomposition-Subuniverseᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  binary-product-Decomposition-Subuniverseᵉ =
    Σᵉ ( type-subuniverseᵉ Pᵉ)
        ( λ k1ᵉ →
          Σᵉ ( type-subuniverseᵉ Pᵉ)
            ( λ k2ᵉ →
              ( inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
                ( (inclusion-subuniverseᵉ Pᵉ k1ᵉ) ×ᵉ
                  (inclusion-subuniverseᵉ Pᵉ k2ᵉ)))))

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : type-subuniverseᵉ Pᵉ)
  (dᵉ : binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ)
  where

  left-summand-binary-product-Decomposition-Subuniverseᵉ : type-subuniverseᵉ Pᵉ
  left-summand-binary-product-Decomposition-Subuniverseᵉ = pr1ᵉ dᵉ

  type-left-summand-binary-product-Decomposition-Subuniverseᵉ : UUᵉ l1ᵉ
  type-left-summand-binary-product-Decomposition-Subuniverseᵉ =
    inclusion-subuniverseᵉ
      Pᵉ
      left-summand-binary-product-Decomposition-Subuniverseᵉ

  right-summand-binary-product-Decomposition-Subuniverseᵉ : type-subuniverseᵉ Pᵉ
  right-summand-binary-product-Decomposition-Subuniverseᵉ = pr1ᵉ (pr2ᵉ dᵉ)

  type-right-summand-binary-product-Decomposition-Subuniverseᵉ : UUᵉ l1ᵉ
  type-right-summand-binary-product-Decomposition-Subuniverseᵉ =
    inclusion-subuniverseᵉ
      Pᵉ
      right-summand-binary-product-Decomposition-Subuniverseᵉ

  matching-correspondence-binary-product-Decomposition-Subuniverseᵉ :
    inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
    ( type-left-summand-binary-product-Decomposition-Subuniverseᵉ ×ᵉ
      type-right-summand-binary-product-Decomposition-Subuniverseᵉ)
  matching-correspondence-binary-product-Decomposition-Subuniverseᵉ = pr2ᵉ (pr2ᵉ dᵉ)
```

### Iterated binary product decompositions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : type-subuniverseᵉ Pᵉ)
  where

  left-iterated-binary-product-Decomposition-Subuniverseᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  left-iterated-binary-product-Decomposition-Subuniverseᵉ =
    Σᵉ ( binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ)
      ( λ dᵉ →
        binary-product-Decomposition-Subuniverseᵉ
          ( Pᵉ)
          ( left-summand-binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ dᵉ))

  right-iterated-binary-product-Decomposition-Subuniverseᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  right-iterated-binary-product-Decomposition-Subuniverseᵉ =
    Σᵉ ( binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ)
      ( λ dᵉ →
        binary-product-Decomposition-Subuniverseᵉ
          ( Pᵉ)
          ( right-summand-binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ dᵉ))
```

### Ternary product Decomposition-subuniverses

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : type-subuniverseᵉ Pᵉ)
  where

  ternary-product-Decomposition-Subuniverseᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  ternary-product-Decomposition-Subuniverseᵉ =
    Σᵉ ( type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ))
      ( λ xᵉ →
        inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
        ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ xᵉ) ×ᵉ
          ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) ×ᵉ
            inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ)))))

  module _
    (dᵉ : ternary-product-Decomposition-Subuniverseᵉ)
    where

    types-ternary-product-Decomposition-Subuniverseᵉ :
      type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ)
    types-ternary-product-Decomposition-Subuniverseᵉ = pr1ᵉ dᵉ

    first-summand-ternary-product-Decomposition-Subuniverseᵉ : type-subuniverseᵉ Pᵉ
    first-summand-ternary-product-Decomposition-Subuniverseᵉ =
      (pr1ᵉ types-ternary-product-Decomposition-Subuniverseᵉ)

    second-summand-ternary-product-Decomposition-Subuniverseᵉ :
      type-subuniverseᵉ Pᵉ
    second-summand-ternary-product-Decomposition-Subuniverseᵉ =
      (pr1ᵉ (pr2ᵉ types-ternary-product-Decomposition-Subuniverseᵉ))

    third-summand-ternary-product-Decomposition-Subuniverseᵉ : type-subuniverseᵉ Pᵉ
    third-summand-ternary-product-Decomposition-Subuniverseᵉ =
      (pr2ᵉ (pr2ᵉ types-ternary-product-Decomposition-Subuniverseᵉ))

    matching-correspondence-ternary-productuct-Decomposition-Subuniverseᵉ :
      inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
      ( inclusion-subuniverseᵉ
        Pᵉ
        first-summand-ternary-product-Decomposition-Subuniverseᵉ ×ᵉ
        ( ( inclusion-subuniverseᵉ
            Pᵉ
            second-summand-ternary-product-Decomposition-Subuniverseᵉ) ×ᵉ
          inclusion-subuniverseᵉ
            Pᵉ
            third-summand-ternary-product-Decomposition-Subuniverseᵉ))
    matching-correspondence-ternary-productuct-Decomposition-Subuniverseᵉ = pr2ᵉ dᵉ
```

## Propositions

### Equivalence between binary product Decomposition-Subuniverse induce by

commutativiyᵉ ofᵉ productᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : type-subuniverseᵉ Pᵉ)
  where

  equiv-commutative-binary-product-Decomposition-Subuniverseᵉ :
    binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
    binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ
  equiv-commutative-binary-product-Decomposition-Subuniverseᵉ =
    ( ( associative-Σᵉ
        ( type-subuniverseᵉ Pᵉ)
        ( λ _ → type-subuniverseᵉ Pᵉ)
        ( _)) ∘eᵉ
      ( ( equiv-Σᵉ
          ( _)
          ( commutative-productᵉ)
          ( λ xᵉ →
            equiv-postcomp-equivᵉ
              ( commutative-productᵉ)
              (inclusion-subuniverseᵉ Pᵉ Xᵉ))) ∘eᵉ
        ( ( inv-associative-Σᵉ
            ( type-subuniverseᵉ Pᵉ)
            ( λ _ → type-subuniverseᵉ Pᵉ)
            ( _)))))
```

### Equivalence between iterated product and ternary product decomposition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : type-subuniverseᵉ Pᵉ)
  (C1ᵉ : is-closed-under-products-subuniverseᵉ Pᵉ)
  where

  private
    map-reassociate-left-iterated-product-Decomposition-Subuniverseᵉ :
      left-iterated-binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ →
      Σᵉ ( type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ))
        ( λ xᵉ →
          Σᵉ ( Σᵉ ( type-subuniverseᵉ Pᵉ)
                ( λ Aᵉ →
                  inclusion-subuniverseᵉ Pᵉ Aᵉ ≃ᵉ
                  ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) ×ᵉ
                    inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ)))))
            ( λ Aᵉ →
              inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
              ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ Aᵉ) ×ᵉ
                inclusion-subuniverseᵉ Pᵉ (pr1ᵉ xᵉ))))
    map-reassociate-left-iterated-product-Decomposition-Subuniverseᵉ
      ( (Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ Cᵉ ,ᵉ Dᵉ ,ᵉ fᵉ) =
      ( (Bᵉ ,ᵉ Cᵉ ,ᵉ Dᵉ) ,ᵉ (Aᵉ ,ᵉ fᵉ) ,ᵉ eᵉ)

    map-inv-reassociate-left-iterated-product-Decomposition-Subuniverseᵉ :
      Σᵉ ( type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ))
        ( λ xᵉ →
          Σᵉ ( Σᵉ ( type-subuniverseᵉ Pᵉ)
                ( λ Aᵉ →
                  inclusion-subuniverseᵉ Pᵉ Aᵉ ≃ᵉ
                  ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) ×ᵉ
                    inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ)))))
            ( λ Aᵉ →
              inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
              ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ Aᵉ) ×ᵉ
                inclusion-subuniverseᵉ Pᵉ (pr1ᵉ xᵉ)))) →
      left-iterated-binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ
    map-inv-reassociate-left-iterated-product-Decomposition-Subuniverseᵉ
      ( (Bᵉ ,ᵉ Cᵉ ,ᵉ Dᵉ) ,ᵉ (Aᵉ ,ᵉ fᵉ) ,ᵉ eᵉ) =
      ( (Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ Cᵉ ,ᵉ Dᵉ ,ᵉ fᵉ)

    equiv-reassociate-left-iterated-product-Decomposition-Subuniverseᵉ :
      left-iterated-binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
      Σᵉ ( type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ))
        ( λ xᵉ →
          Σᵉ ( Σᵉ ( type-subuniverseᵉ Pᵉ)
                ( λ Aᵉ →
                  inclusion-subuniverseᵉ Pᵉ Aᵉ ≃ᵉ
                  ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) ×ᵉ
                    inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ)))))
            ( λ Aᵉ →
              inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
              ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ Aᵉ) ×ᵉ
                inclusion-subuniverseᵉ Pᵉ (pr1ᵉ xᵉ))))
    pr1ᵉ equiv-reassociate-left-iterated-product-Decomposition-Subuniverseᵉ =
      map-reassociate-left-iterated-product-Decomposition-Subuniverseᵉ
    pr2ᵉ equiv-reassociate-left-iterated-product-Decomposition-Subuniverseᵉ =
      is-equiv-is-invertibleᵉ
        map-inv-reassociate-left-iterated-product-Decomposition-Subuniverseᵉ
        refl-htpyᵉ
        refl-htpyᵉ

  equiv-ternary-left-iterated-product-Decomposition-Subuniverseᵉ :
    left-iterated-binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
    ternary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ
  equiv-ternary-left-iterated-product-Decomposition-Subuniverseᵉ =
    ( ( equiv-totᵉ
        ( λ xᵉ →
          ( ( equiv-postcomp-equivᵉ
              ( commutative-productᵉ)
              ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
            ( ( left-unit-law-Σ-is-contrᵉ
                ( is-torsorial-equiv-subuniverse'ᵉ
                  ( Pᵉ)
                  ( ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) ×ᵉ
                      inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ))) ,ᵉ
                    C1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ xᵉ))) (pr2ᵉ (pr2ᵉ (pr2ᵉ xᵉ))))))
                ( ( ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) ×ᵉ
                      inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ))) ,ᵉ
                    C1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ xᵉ))) (pr2ᵉ (pr2ᵉ (pr2ᵉ xᵉ)))) ,ᵉ
                  id-equivᵉ))))) ∘eᵉ
      ( ( equiv-reassociate-left-iterated-product-Decomposition-Subuniverseᵉ)))

  private
    map-reassociate-right-iterated-product-Decomposition-Subuniverseᵉ :
      right-iterated-binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ →
      Σᵉ ( type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ))
        ( λ xᵉ →
          Σᵉ ( Σᵉ ( type-subuniverseᵉ Pᵉ)
                ( λ Bᵉ →
                  inclusion-subuniverseᵉ Pᵉ Bᵉ ≃ᵉ
                  ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) ×ᵉ
                    inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ)))))
            ( λ Bᵉ →
              inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
              ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ xᵉ) ×ᵉ
                inclusion-subuniverseᵉ Pᵉ (pr1ᵉ Bᵉ))))
    map-reassociate-right-iterated-product-Decomposition-Subuniverseᵉ
      ( (Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ Cᵉ ,ᵉ Dᵉ ,ᵉ fᵉ) =
      ( (Aᵉ ,ᵉ Cᵉ ,ᵉ Dᵉ) ,ᵉ (Bᵉ ,ᵉ fᵉ) ,ᵉ eᵉ)

    map-inv-reassociate-right-iterated-product-Decomposition-Subuniverseᵉ :
      Σᵉ ( type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ))
        ( λ xᵉ →
          Σᵉ ( Σᵉ ( type-subuniverseᵉ Pᵉ)
                ( λ Bᵉ →
                  inclusion-subuniverseᵉ Pᵉ Bᵉ ≃ᵉ
                  ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) ×ᵉ
                    inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ)))))
            ( λ Bᵉ →
              inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
              ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ xᵉ) ×ᵉ
                inclusion-subuniverseᵉ Pᵉ (pr1ᵉ Bᵉ)))) →
      right-iterated-binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ
    map-inv-reassociate-right-iterated-product-Decomposition-Subuniverseᵉ
      ( (Aᵉ ,ᵉ Cᵉ ,ᵉ Dᵉ) ,ᵉ (Bᵉ ,ᵉ fᵉ) ,ᵉ eᵉ) =
      ( (Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ Cᵉ ,ᵉ Dᵉ ,ᵉ fᵉ)

    equiv-reassociate-right-iterated-product-Decomposition-Subuniverseᵉ :
      right-iterated-binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
      Σᵉ ( type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ))
        ( λ xᵉ →
          Σᵉ ( Σᵉ ( type-subuniverseᵉ Pᵉ)
                ( λ Bᵉ →
                  inclusion-subuniverseᵉ Pᵉ Bᵉ ≃ᵉ
                  ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) ×ᵉ
                    inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ)))))
            ( λ Bᵉ →
              inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
              ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ xᵉ) ×ᵉ
                inclusion-subuniverseᵉ Pᵉ (pr1ᵉ Bᵉ))))
    pr1ᵉ equiv-reassociate-right-iterated-product-Decomposition-Subuniverseᵉ =
      map-reassociate-right-iterated-product-Decomposition-Subuniverseᵉ
    pr2ᵉ equiv-reassociate-right-iterated-product-Decomposition-Subuniverseᵉ =
      is-equiv-is-invertibleᵉ
        map-inv-reassociate-right-iterated-product-Decomposition-Subuniverseᵉ
        refl-htpyᵉ
        refl-htpyᵉ

  equiv-ternary-right-iterated-product-Decomposition-Subuniverseᵉ :
    right-iterated-binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
    ternary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ
  equiv-ternary-right-iterated-product-Decomposition-Subuniverseᵉ =
    ( ( equiv-totᵉ
        ( λ xᵉ →
          left-unit-law-Σ-is-contrᵉ
            ( is-torsorial-equiv-subuniverse'ᵉ
              ( Pᵉ)
              ( ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) ×ᵉ
                  inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ))) ,ᵉ
                ( C1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ xᵉ))) (pr2ᵉ (pr2ᵉ (pr2ᵉ xᵉ))))))
            ( ( ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) ×ᵉ
                  inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ))) ,ᵉ
                ( C1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ xᵉ))) (pr2ᵉ (pr2ᵉ (pr2ᵉ xᵉ))))) ,ᵉ
              id-equivᵉ))) ∘eᵉ
      ( ( equiv-reassociate-right-iterated-product-Decomposition-Subuniverseᵉ)))
```

### Product-decomposition with contractible right summand

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : type-subuniverseᵉ Pᵉ)
  (C1ᵉ : is-in-subuniverseᵉ Pᵉ (raise-unitᵉ l1ᵉ))
  where

  equiv-is-contr-right-summand-binary-product-Decomposition-Subuniverseᵉ :
    ( Σᵉ ( binary-product-Decomposition-Subuniverseᵉ Pᵉ Xᵉ)
        ( λ dᵉ →
          is-contrᵉ
            ( inclusion-subuniverseᵉ Pᵉ
              ( right-summand-binary-product-Decomposition-Subuniverseᵉ
                Pᵉ
                Xᵉ
                dᵉ)))) ≃ᵉ
    Σᵉ ( type-subuniverseᵉ Pᵉ)
      ( λ Yᵉ → inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ pr1ᵉ Yᵉ)
  equiv-is-contr-right-summand-binary-product-Decomposition-Subuniverseᵉ =
    ( ( equiv-totᵉ
          ( λ xᵉ →
            ( ( equiv-postcomp-equivᵉ
                ( right-unit-law-product-is-contrᵉ is-contr-raise-unitᵉ)
                ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
              ( ( left-unit-law-Σ-is-contrᵉ
                  ( ( ( ( raise-unitᵉ l1ᵉ) ,ᵉ
                        C1ᵉ) ,ᵉ
                      is-contr-raise-unitᵉ) ,ᵉ
                    ( λ xᵉ →
                      eq-pair-Σᵉ
                        ( eq-pair-Σᵉ
                          ( eq-equivᵉ
                            ( equiv-is-contrᵉ is-contr-raise-unitᵉ (pr2ᵉ xᵉ)))
                          ( eq-is-propᵉ (is-prop-type-Propᵉ (Pᵉ (pr1ᵉ (pr1ᵉ xᵉ))))))
                        ( eq-is-propᵉ is-property-is-contrᵉ)))
                  ( ( raise-unitᵉ l1ᵉ ,ᵉ C1ᵉ) ,ᵉ
                    is-contr-raise-unitᵉ)) ∘eᵉ
                ( ( inv-associative-Σᵉ _ _ _) ∘eᵉ
                  ( ( equiv-totᵉ (λ _ → commutative-productᵉ)) ∘eᵉ
                    ( ( associative-Σᵉ _ _ _)))))))) ∘eᵉ
        ( ( associative-Σᵉ _ _ _)))
```