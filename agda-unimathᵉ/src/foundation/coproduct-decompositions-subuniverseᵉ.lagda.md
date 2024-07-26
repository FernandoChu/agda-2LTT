# Coproduct decompositions in a subuniverse

```agda
module foundation.coproduct-decompositions-subuniverseᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.subuniversesᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Letᵉ `P`ᵉ beᵉ aᵉ subuniverseᵉ andᵉ `X`ᵉ aᵉ typeᵉ in `P`.ᵉ Aᵉ binaryᵉ coproductᵉ decompositionᵉ
ofᵉ `X`ᵉ isᵉ definedᵉ to beᵉ twoᵉ typesᵉ `A`ᵉ andᵉ `B`ᵉ in `P`ᵉ andᵉ anᵉ equivalenceᵉ fromᵉ `X`ᵉ
to `A+B`.ᵉ

## Definitions

### Binary coproduct decomposition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : type-subuniverseᵉ Pᵉ)
  where

  binary-coproduct-Decomposition-subuniverseᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  binary-coproduct-Decomposition-subuniverseᵉ =
    Σᵉ ( type-subuniverseᵉ Pᵉ)
      ( λ k1ᵉ →
        Σᵉ ( type-subuniverseᵉ Pᵉ)
          ( λ k2ᵉ →
            ( inclusion-subuniverseᵉ Pᵉ Xᵉ) ≃ᵉ
            ( inclusion-subuniverseᵉ Pᵉ k1ᵉ +ᵉ inclusion-subuniverseᵉ Pᵉ k2ᵉ)))

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : type-subuniverseᵉ Pᵉ)
  (dᵉ : binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ)
  where

  left-summand-binary-coproduct-Decomposition-subuniverseᵉ : type-subuniverseᵉ Pᵉ
  left-summand-binary-coproduct-Decomposition-subuniverseᵉ = pr1ᵉ dᵉ

  type-left-summand-binary-coproduct-Decomposition-subuniverseᵉ : UUᵉ l1ᵉ
  type-left-summand-binary-coproduct-Decomposition-subuniverseᵉ =
    inclusion-subuniverseᵉ Pᵉ
      left-summand-binary-coproduct-Decomposition-subuniverseᵉ

  right-summand-binary-coproduct-Decomposition-subuniverseᵉ : type-subuniverseᵉ Pᵉ
  right-summand-binary-coproduct-Decomposition-subuniverseᵉ = pr1ᵉ (pr2ᵉ dᵉ)

  type-right-summand-binary-coproduct-Decomposition-subuniverseᵉ : UUᵉ l1ᵉ
  type-right-summand-binary-coproduct-Decomposition-subuniverseᵉ =
    inclusion-subuniverseᵉ Pᵉ
      right-summand-binary-coproduct-Decomposition-subuniverseᵉ

  matching-correspondence-binary-coproduct-Decomposition-subuniverseᵉ :
    inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
    ( type-left-summand-binary-coproduct-Decomposition-subuniverseᵉ +ᵉ
      type-right-summand-binary-coproduct-Decomposition-subuniverseᵉ)
  matching-correspondence-binary-coproduct-Decomposition-subuniverseᵉ =
    pr2ᵉ (pr2ᵉ dᵉ)
```

### Iterated binary coproduct decompositions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : type-subuniverseᵉ Pᵉ)
  where

  left-iterated-binary-coproduct-Decomposition-subuniverseᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  left-iterated-binary-coproduct-Decomposition-subuniverseᵉ =
    Σᵉ ( binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ)
      ( λ dᵉ →
        binary-coproduct-Decomposition-subuniverseᵉ Pᵉ
          ( left-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ dᵉ))

  right-iterated-binary-coproduct-Decomposition-subuniverseᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  right-iterated-binary-coproduct-Decomposition-subuniverseᵉ =
    Σᵉ ( binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ)
      ( λ dᵉ →
        binary-coproduct-Decomposition-subuniverseᵉ Pᵉ
          ( right-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ dᵉ))
```

### Ternary coproduct Decomposition-subuniverses

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : type-subuniverseᵉ Pᵉ)
  where

  ternary-coproduct-Decomposition-subuniverseᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  ternary-coproduct-Decomposition-subuniverseᵉ =
    Σᵉ ( type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ))
      ( λ xᵉ →
        inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
        ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ xᵉ) +ᵉ
          ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) +ᵉ
            inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ)))))

  module _
    (dᵉ : ternary-coproduct-Decomposition-subuniverseᵉ)
    where

    types-ternary-coproduct-Decomposition-subuniverseᵉ :
      type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ)
    types-ternary-coproduct-Decomposition-subuniverseᵉ = pr1ᵉ dᵉ

    first-summand-ternary-coproduct-Decomposition-subuniverseᵉ :
      type-subuniverseᵉ Pᵉ
    first-summand-ternary-coproduct-Decomposition-subuniverseᵉ =
      ( pr1ᵉ types-ternary-coproduct-Decomposition-subuniverseᵉ)

    second-summand-ternary-coproduct-Decomposition-subuniverseᵉ :
      type-subuniverseᵉ Pᵉ
    second-summand-ternary-coproduct-Decomposition-subuniverseᵉ =
      ( pr1ᵉ (pr2ᵉ types-ternary-coproduct-Decomposition-subuniverseᵉ))

    third-summand-ternary-coproduct-Decomposition-subuniverseᵉ :
      type-subuniverseᵉ Pᵉ
    third-summand-ternary-coproduct-Decomposition-subuniverseᵉ =
      ( pr2ᵉ (pr2ᵉ types-ternary-coproduct-Decomposition-subuniverseᵉ))

    matching-correspondence-ternary-coproductuct-Decomposition-subuniverseᵉ :
      ( inclusion-subuniverseᵉ Pᵉ Xᵉ) ≃ᵉ
      ( ( inclusion-subuniverseᵉ Pᵉ
          first-summand-ternary-coproduct-Decomposition-subuniverseᵉ) +ᵉ
        ( ( inclusion-subuniverseᵉ Pᵉ
            second-summand-ternary-coproduct-Decomposition-subuniverseᵉ) +ᵉ
          ( inclusion-subuniverseᵉ Pᵉ
            third-summand-ternary-coproduct-Decomposition-subuniverseᵉ)))
    matching-correspondence-ternary-coproductuct-Decomposition-subuniverseᵉ =
      pr2ᵉ dᵉ
```

## Propositions

### Characterization of equality of binary coproduct Decomposition of subuniverse

```agda
equiv-binary-coproduct-Decomposition-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Aᵉ : type-subuniverseᵉ Pᵉ)
  (Xᵉ : binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ)
  (Yᵉ : binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ) →
  UUᵉ (l1ᵉ)
equiv-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ Yᵉ =
  Σᵉ ( type-left-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ ≃ᵉ
      type-left-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Yᵉ)
    ( λ elᵉ →
      Σᵉ ( type-right-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ ≃ᵉ
          type-right-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Yᵉ)
        ( λ erᵉ →
          ( map-coproductᵉ (map-equivᵉ elᵉ) (map-equivᵉ erᵉ) ∘ᵉ
            map-equivᵉ
              ( matching-correspondence-binary-coproduct-Decomposition-subuniverseᵉ
                  Pᵉ Aᵉ Xᵉ)) ~ᵉ
          ( map-equivᵉ
            ( matching-correspondence-binary-coproduct-Decomposition-subuniverseᵉ
                Pᵉ Aᵉ Yᵉ))))

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Aᵉ : type-subuniverseᵉ Pᵉ)
  (Xᵉ : binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ)
  (Yᵉ : binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ)
  (eᵉ : equiv-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ Yᵉ)
  where

  equiv-left-summand-equiv-binary-coproduct-Decomposition-subuniverseᵉ :
    type-left-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ ≃ᵉ
    type-left-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Yᵉ
  equiv-left-summand-equiv-binary-coproduct-Decomposition-subuniverseᵉ = pr1ᵉ eᵉ

  map-equiv-left-summand-equiv-binary-coproduct-Decomposition-subuniverseᵉ :
    type-left-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ →
    type-left-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Yᵉ
  map-equiv-left-summand-equiv-binary-coproduct-Decomposition-subuniverseᵉ =
    map-equivᵉ
      equiv-left-summand-equiv-binary-coproduct-Decomposition-subuniverseᵉ

  equiv-right-summand-equiv-binary-coproduct-Decomposition-subuniverseᵉ :
    type-right-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ ≃ᵉ
    type-right-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Yᵉ
  equiv-right-summand-equiv-binary-coproduct-Decomposition-subuniverseᵉ =
    pr1ᵉ (pr2ᵉ eᵉ)

  map-equiv-right-summand-equiv-binary-coproduct-Decomposition-subuniverseᵉ :
    type-right-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ →
    type-right-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Yᵉ
  map-equiv-right-summand-equiv-binary-coproduct-Decomposition-subuniverseᵉ =
    map-equivᵉ
      equiv-right-summand-equiv-binary-coproduct-Decomposition-subuniverseᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Aᵉ : type-subuniverseᵉ Pᵉ)
  (Xᵉ : binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ)
  where

  id-equiv-binary-coproduct-Decomposition-subuniverseᵉ :
    equiv-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ Xᵉ
  pr1ᵉ id-equiv-binary-coproduct-Decomposition-subuniverseᵉ = id-equivᵉ
  pr1ᵉ (pr2ᵉ id-equiv-binary-coproduct-Decomposition-subuniverseᵉ) = id-equivᵉ
  pr2ᵉ (pr2ᵉ id-equiv-binary-coproduct-Decomposition-subuniverseᵉ) xᵉ =
    id-map-coproductᵉ
      ( type-left-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ)
      ( type-right-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ)
      ( map-equivᵉ
        ( matching-correspondence-binary-coproduct-Decomposition-subuniverseᵉ
          Pᵉ Aᵉ Xᵉ)
        ( xᵉ))

  is-torsorial-equiv-binary-coproduct-Decomposition-subuniverseᵉ :
    is-torsorialᵉ (equiv-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ)
  is-torsorial-equiv-binary-coproduct-Decomposition-subuniverseᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equiv-subuniverseᵉ Pᵉ
        ( left-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ))
      ( left-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ ,ᵉ
        id-equivᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-equiv-subuniverseᵉ Pᵉ
          ( right-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ))
        ( right-summand-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ ,ᵉ
          id-equivᵉ)
        ( is-torsorial-htpy-equivᵉ
          ( equiv-coproductᵉ id-equivᵉ id-equivᵉ ∘eᵉ
            matching-correspondence-binary-coproduct-Decomposition-subuniverseᵉ
              Pᵉ Aᵉ Xᵉ)))

  equiv-eq-binary-coproduct-Decomposition-subuniverseᵉ :
    (Yᵉ : binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ) → (Xᵉ ＝ᵉ Yᵉ) →
    equiv-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ Yᵉ
  equiv-eq-binary-coproduct-Decomposition-subuniverseᵉ .Xᵉ reflᵉ =
    id-equiv-binary-coproduct-Decomposition-subuniverseᵉ

  is-equiv-equiv-eq-binary-coproduct-Decomposition-subuniverseᵉ :
    (Yᵉ : binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ) →
    is-equivᵉ (equiv-eq-binary-coproduct-Decomposition-subuniverseᵉ Yᵉ)
  is-equiv-equiv-eq-binary-coproduct-Decomposition-subuniverseᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-binary-coproduct-Decomposition-subuniverseᵉ
      equiv-eq-binary-coproduct-Decomposition-subuniverseᵉ

  extensionality-binary-coproduct-Decomposition-subuniverseᵉ :
    (Yᵉ : binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ Yᵉ
  pr1ᵉ (extensionality-binary-coproduct-Decomposition-subuniverseᵉ Yᵉ) =
    equiv-eq-binary-coproduct-Decomposition-subuniverseᵉ Yᵉ
  pr2ᵉ (extensionality-binary-coproduct-Decomposition-subuniverseᵉ Yᵉ) =
    is-equiv-equiv-eq-binary-coproduct-Decomposition-subuniverseᵉ Yᵉ

  eq-equiv-binary-coproduct-Decomposition-subuniverseᵉ :
    (Yᵉ : binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ) →
    equiv-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Aᵉ Xᵉ Yᵉ → (Xᵉ ＝ᵉ Yᵉ)
  eq-equiv-binary-coproduct-Decomposition-subuniverseᵉ Yᵉ =
    map-inv-equivᵉ (extensionality-binary-coproduct-Decomposition-subuniverseᵉ Yᵉ)
```

### Equivalence between binary coproduct Decomposition-subuniverse induce by commutativiy of coproduct

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : type-subuniverseᵉ Pᵉ)
  where

  equiv-commutative-binary-coproduct-Decomposition-subuniverseᵉ :
    binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
    binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ
  equiv-commutative-binary-coproduct-Decomposition-subuniverseᵉ =
    ( associative-Σᵉ
      ( type-subuniverseᵉ Pᵉ)
      ( λ _ → type-subuniverseᵉ Pᵉ)
      ( _)) ∘eᵉ
    ( ( equiv-Σᵉ
        ( _)
        ( commutative-productᵉ)
        ( λ xᵉ →
          equiv-postcomp-equivᵉ
            ( commutative-coproductᵉ
              ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ xᵉ))
              ( inclusion-subuniverseᵉ Pᵉ (pr2ᵉ xᵉ)))
            (inclusion-subuniverseᵉ Pᵉ Xᵉ))) ∘eᵉ
      ( ( inv-associative-Σᵉ
          ( type-subuniverseᵉ Pᵉ)
          ( λ _ → type-subuniverseᵉ Pᵉ)
          ( _))))
```

### Equivalence between iterated coproduct and ternary coproduct decomposition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : type-subuniverseᵉ Pᵉ)
  (C1ᵉ : is-closed-under-coproducts-subuniverseᵉ Pᵉ)
  where

  private
    map-reassociate-left-iterated-coproduct-Decomposition-subuniverseᵉ :
      left-iterated-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ →
      Σᵉ ( type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ))
        ( λ xᵉ →
          Σᵉ ( Σᵉ ( type-subuniverseᵉ Pᵉ)
                ( λ Aᵉ →
                  ( inclusion-subuniverseᵉ Pᵉ Aᵉ) ≃ᵉ
                  ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) +ᵉ
                    inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ)))))
            ( λ Aᵉ →
              ( inclusion-subuniverseᵉ Pᵉ Xᵉ) ≃ᵉ
              ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ Aᵉ) +ᵉ
                inclusion-subuniverseᵉ Pᵉ (pr1ᵉ xᵉ))))
    map-reassociate-left-iterated-coproduct-Decomposition-subuniverseᵉ
      ( (Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ Cᵉ ,ᵉ Dᵉ ,ᵉ fᵉ) =
      ( (Bᵉ ,ᵉ Cᵉ ,ᵉ Dᵉ) ,ᵉ (Aᵉ ,ᵉ fᵉ) ,ᵉ eᵉ)

    map-inv-reassociate-left-iterated-coproduct-Decomposition-subuniverseᵉ :
      Σᵉ ( type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ))
        ( λ xᵉ →
          Σᵉ ( Σᵉ ( type-subuniverseᵉ Pᵉ)
                ( λ Aᵉ →
                  inclusion-subuniverseᵉ Pᵉ Aᵉ ≃ᵉ
                  ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) +ᵉ
                    inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ)))))
            ( λ Aᵉ →
              inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
              ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ Aᵉ) +ᵉ
                inclusion-subuniverseᵉ Pᵉ (pr1ᵉ xᵉ)))) →
      left-iterated-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ
    map-inv-reassociate-left-iterated-coproduct-Decomposition-subuniverseᵉ
      ( (Bᵉ ,ᵉ Cᵉ ,ᵉ Dᵉ) ,ᵉ (Aᵉ ,ᵉ fᵉ) ,ᵉ eᵉ) =
      ( (Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ Cᵉ ,ᵉ Dᵉ ,ᵉ fᵉ)

    equiv-reassociate-left-iterated-coproduct-Decomposition-subuniverseᵉ :
      left-iterated-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
      Σᵉ ( type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ))
        ( λ xᵉ →
          Σᵉ ( Σᵉ ( type-subuniverseᵉ Pᵉ)
                ( λ Aᵉ →
                  inclusion-subuniverseᵉ Pᵉ Aᵉ ≃ᵉ
                  ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) +ᵉ
                    inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ)))))
            ( λ Aᵉ →
              inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
              ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ Aᵉ) +ᵉ
                inclusion-subuniverseᵉ Pᵉ (pr1ᵉ xᵉ))))
    pr1ᵉ equiv-reassociate-left-iterated-coproduct-Decomposition-subuniverseᵉ =
      map-reassociate-left-iterated-coproduct-Decomposition-subuniverseᵉ
    pr2ᵉ equiv-reassociate-left-iterated-coproduct-Decomposition-subuniverseᵉ =
      is-equiv-is-invertibleᵉ
        map-inv-reassociate-left-iterated-coproduct-Decomposition-subuniverseᵉ
        refl-htpyᵉ
        refl-htpyᵉ

  equiv-ternary-left-iterated-coproduct-Decomposition-subuniverseᵉ :
    left-iterated-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
    ternary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ
  equiv-ternary-left-iterated-coproduct-Decomposition-subuniverseᵉ =
    ( equiv-totᵉ
      ( λ xᵉ →
        ( ( equiv-postcomp-equivᵉ
            ( commutative-coproductᵉ _ _)
            ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
        ( ( left-unit-law-Σ-is-contrᵉ
            ( is-torsorial-equiv-subuniverse'ᵉ Pᵉ
              ( ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) +ᵉ
                  inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ))) ,ᵉ
                ( C1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ xᵉ))) (pr2ᵉ (pr2ᵉ (pr2ᵉ xᵉ)))))))
            ( ( ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) +ᵉ
                  inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ))) ,ᵉ
                ( C1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ xᵉ))) (pr2ᵉ (pr2ᵉ (pr2ᵉ xᵉ))))) ,ᵉ
              ( id-equivᵉ)))))) ∘eᵉ
    ( equiv-reassociate-left-iterated-coproduct-Decomposition-subuniverseᵉ)

  private
    map-reassociate-right-iterated-coproduct-Decomposition-subuniverseᵉ :
      right-iterated-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ →
      Σᵉ ( type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ))
        ( λ xᵉ →
          Σᵉ ( Σᵉ ( type-subuniverseᵉ Pᵉ)
                ( λ Bᵉ →
                  ( inclusion-subuniverseᵉ Pᵉ Bᵉ) ≃ᵉ
                  ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) +ᵉ
                    inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ)))))
            ( λ Bᵉ →
              ( inclusion-subuniverseᵉ Pᵉ Xᵉ) ≃ᵉ
              ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ xᵉ) +ᵉ
                inclusion-subuniverseᵉ Pᵉ (pr1ᵉ Bᵉ))))
    map-reassociate-right-iterated-coproduct-Decomposition-subuniverseᵉ
      ( (Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ Cᵉ ,ᵉ Dᵉ ,ᵉ fᵉ) =
      ( (Aᵉ ,ᵉ Cᵉ ,ᵉ Dᵉ) ,ᵉ (Bᵉ ,ᵉ fᵉ) ,ᵉ eᵉ)

    map-inv-reassociate-right-iterated-coproduct-Decomposition-subuniverseᵉ :
      Σᵉ ( type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ))
        ( λ xᵉ →
          Σᵉ ( Σᵉ ( type-subuniverseᵉ Pᵉ)
                ( λ Bᵉ →
                  ( inclusion-subuniverseᵉ Pᵉ Bᵉ) ≃ᵉ
                  ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) +ᵉ
                    inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ)))))
            ( λ Bᵉ →
              ( inclusion-subuniverseᵉ Pᵉ Xᵉ) ≃ᵉ
              ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ xᵉ) +ᵉ
                inclusion-subuniverseᵉ Pᵉ (pr1ᵉ Bᵉ)))) →
      right-iterated-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ
    map-inv-reassociate-right-iterated-coproduct-Decomposition-subuniverseᵉ
      ( (Aᵉ ,ᵉ Cᵉ ,ᵉ Dᵉ) ,ᵉ (Bᵉ ,ᵉ fᵉ) ,ᵉ eᵉ) =
      ( (Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ Cᵉ ,ᵉ Dᵉ ,ᵉ fᵉ)

    equiv-reassociate-right-iterated-coproduct-Decomposition-subuniverseᵉ :
      right-iterated-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
      Σᵉ ( type-subuniverseᵉ Pᵉ ×ᵉ (type-subuniverseᵉ Pᵉ ×ᵉ type-subuniverseᵉ Pᵉ))
        ( λ xᵉ →
          Σᵉ ( Σᵉ ( type-subuniverseᵉ Pᵉ)
                ( λ Bᵉ →
                  ( inclusion-subuniverseᵉ Pᵉ Bᵉ) ≃ᵉ
                  ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) +ᵉ
                    inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ)))))
            ( λ Bᵉ →
              ( inclusion-subuniverseᵉ Pᵉ Xᵉ) ≃ᵉ
              ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ xᵉ) +ᵉ
                inclusion-subuniverseᵉ Pᵉ (pr1ᵉ Bᵉ))))
    pr1ᵉ equiv-reassociate-right-iterated-coproduct-Decomposition-subuniverseᵉ =
      map-reassociate-right-iterated-coproduct-Decomposition-subuniverseᵉ
    pr2ᵉ equiv-reassociate-right-iterated-coproduct-Decomposition-subuniverseᵉ =
      is-equiv-is-invertibleᵉ
        map-inv-reassociate-right-iterated-coproduct-Decomposition-subuniverseᵉ
        refl-htpyᵉ
        refl-htpyᵉ

  equiv-ternary-right-iterated-coproduct-Decomposition-subuniverseᵉ :
    right-iterated-binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ
    ternary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ
  equiv-ternary-right-iterated-coproduct-Decomposition-subuniverseᵉ =
    ( equiv-totᵉ
      ( λ xᵉ →
        left-unit-law-Σ-is-contrᵉ
          ( is-torsorial-equiv-subuniverse'ᵉ Pᵉ
            ( ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) +ᵉ
                inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ))) ,ᵉ
              ( C1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ xᵉ))) (pr2ᵉ (pr2ᵉ (pr2ᵉ xᵉ))))))
          ( ( ( inclusion-subuniverseᵉ Pᵉ (pr1ᵉ (pr2ᵉ xᵉ)) +ᵉ
                inclusion-subuniverseᵉ Pᵉ (pr2ᵉ (pr2ᵉ xᵉ))) ,ᵉ
              ( C1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ xᵉ))) (pr2ᵉ (pr2ᵉ (pr2ᵉ xᵉ))))) ,ᵉ
            ( id-equivᵉ)))) ∘eᵉ
    ( equiv-reassociate-right-iterated-coproduct-Decomposition-subuniverseᵉ)
```

### Coproduct-decomposition with empty right summand

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : type-subuniverseᵉ Pᵉ)
  (C1ᵉ : is-in-subuniverseᵉ Pᵉ (raise-emptyᵉ l1ᵉ))
  where

  equiv-is-empty-right-summand-binary-coproduct-Decomposition-subuniverseᵉ :
    Σᵉ ( binary-coproduct-Decomposition-subuniverseᵉ Pᵉ Xᵉ)
      ( λ dᵉ →
        is-emptyᵉ
          ( inclusion-subuniverseᵉ Pᵉ
            ( right-summand-binary-coproduct-Decomposition-subuniverseᵉ
              Pᵉ Xᵉ dᵉ))) ≃ᵉ
    Σᵉ ( type-subuniverseᵉ Pᵉ)
      ( λ Yᵉ → inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ pr1ᵉ Yᵉ)
  equiv-is-empty-right-summand-binary-coproduct-Decomposition-subuniverseᵉ =
    ( equiv-totᵉ
      ( λ xᵉ →
        ( equiv-postcomp-equivᵉ
          ( right-unit-law-coproduct-is-emptyᵉ
            ( inclusion-subuniverseᵉ Pᵉ xᵉ)
            ( raise-emptyᵉ l1ᵉ)
            ( is-empty-raise-emptyᵉ))
          ( inclusion-subuniverseᵉ Pᵉ Xᵉ)) ∘eᵉ
        ( ( left-unit-law-Σ-is-contrᵉ
            ( ( ( raise-emptyᵉ l1ᵉ ,ᵉ C1ᵉ) ,ᵉ is-empty-raise-emptyᵉ) ,ᵉ
              ( λ xᵉ →
                eq-pair-Σᵉ
                  ( eq-pair-Σᵉ
                    ( eq-equivᵉ (equiv-is-emptyᵉ is-empty-raise-emptyᵉ (pr2ᵉ xᵉ)))
                    ( eq-is-propᵉ (is-prop-type-Propᵉ (Pᵉ _))))
                  ( eq-is-propᵉ is-property-is-emptyᵉ)))
            ( ( raise-emptyᵉ l1ᵉ ,ᵉ C1ᵉ) ,ᵉ is-empty-raise-emptyᵉ)) ∘eᵉ
          ( ( inv-associative-Σᵉ _ _ _) ∘eᵉ
            ( ( equiv-totᵉ (λ _ → commutative-productᵉ)) ∘eᵉ
              ( ( associative-Σᵉ _ _ _))))))) ∘eᵉ
    ( ( associative-Σᵉ _ _ _))
```