# Subtypes of descent data for the circle

```agda
module synthetic-homotopy-theory.descent-circle-subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.dependent-descent-circleᵉ
open import synthetic-homotopy-theory.descent-circleᵉ
open import synthetic-homotopy-theory.descent-circle-dependent-pair-typesᵉ
open import synthetic-homotopy-theory.free-loopsᵉ
open import synthetic-homotopy-theory.sections-descent-circleᵉ
open import synthetic-homotopy-theory.universal-property-circleᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ `Aᵉ : 𝕊¹ᵉ → U`ᵉ overᵉ theᵉ
[circle](synthetic-homotopy-theory.circle.mdᵉ) andᵉ aᵉ familyᵉ
`Bᵉ : (tᵉ : 𝕊¹ᵉ) → (Aᵉ tᵉ) → U`ᵉ overᵉ `A`ᵉ with correspondingᵉ
[descentᵉ data](synthetic-homotopy-theory.descent-circle.mdᵉ) `(X,ᵉ e)`ᵉ andᵉ
dependentᵉ descentᵉ data `(R,ᵉ k)`,ᵉ where `R`ᵉ isᵉ aᵉ
[subtype](foundation-core.subtypes.mdᵉ) ofᵉ `X`,ᵉ weᵉ getᵉ thatᵉ dependentᵉ functionsᵉ
ofᵉ typeᵉ `(tᵉ : 𝕊¹ᵉ) → Σᵉ (Aᵉ tᵉ) (Bᵉ t)`ᵉ areᵉ exactlyᵉ theᵉ
[fixpoints](synthetic-homotopy-theory.sections-descent-circle.mdᵉ) ofᵉ `e`ᵉ whichᵉ
belongᵉ to `R`.ᵉ

## Properties

### Characterization of sections of families of subtypes

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  ( Bᵉ : double-family-with-dependent-descent-data-circleᵉ lᵉ Aᵉ l3ᵉ)
  ( is-subtype-Bᵉ :
    ( tᵉ : Sᵉ) →
    is-subtypeᵉ
      ( double-family-double-family-with-dependent-descent-data-circleᵉ Aᵉ Bᵉ tᵉ))
  where

  subtype-descent-data-circle-subtypeᵉ :
    subtypeᵉ l3ᵉ (type-family-with-descent-data-circleᵉ Aᵉ)
  pr1ᵉ (subtype-descent-data-circle-subtypeᵉ xᵉ) =
    type-double-family-with-dependent-descent-data-circleᵉ Aᵉ Bᵉ xᵉ
  pr2ᵉ (subtype-descent-data-circle-subtypeᵉ xᵉ) =
    is-prop-equivᵉ
      ( equiv-double-family-with-dependent-descent-data-circleᵉ Aᵉ Bᵉ xᵉ)
      ( is-subtype-Bᵉ
        ( base-free-loopᵉ lᵉ)
        ( map-equiv-family-with-descent-data-circleᵉ Aᵉ xᵉ))

  equiv-fixpoint-descent-data-circle-subtype-fixpoint-in-subtypeᵉ :
    fixpoint-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ
        ( family-with-descent-data-circle-dependent-pair-typeᵉ lᵉ Aᵉ Bᵉ)) ≃ᵉ
    ( Σᵉ ( fixpoint-descent-data-circleᵉ
          ( descent-data-family-with-descent-data-circleᵉ Aᵉ))
        ( λ xᵉ → is-in-subtypeᵉ subtype-descent-data-circle-subtypeᵉ (pr1ᵉ xᵉ)))
  equiv-fixpoint-descent-data-circle-subtype-fixpoint-in-subtypeᵉ =
    equivalence-reasoningᵉ
    fixpoint-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ
        ( family-with-descent-data-circle-dependent-pair-typeᵉ lᵉ Aᵉ Bᵉ))
    ≃ᵉ Σᵉ ( type-family-with-descent-data-circleᵉ Aᵉ)
        ( λ xᵉ →
          Σᵉ ( type-double-family-with-dependent-descent-data-circleᵉ Aᵉ Bᵉ xᵉ)
            ( λ rᵉ →
              map-Σᵉ
                ( type-double-family-with-dependent-descent-data-circleᵉ Aᵉ Bᵉ)
                ( map-aut-family-with-descent-data-circleᵉ Aᵉ)
                ( λ xᵉ →
                  map-dependent-automorphism-double-family-with-dependent-descent-data-circleᵉ
                    ( Aᵉ)
                    ( Bᵉ))
                ( xᵉ ,ᵉ rᵉ) ＝ᵉ
              ( xᵉ ,ᵉ rᵉ)))
      byᵉ
        associative-Σᵉ
          ( type-family-with-descent-data-circleᵉ Aᵉ)
          ( type-double-family-with-dependent-descent-data-circleᵉ Aᵉ Bᵉ)
          ( λ uᵉ →
            map-Σᵉ
              ( type-double-family-with-dependent-descent-data-circleᵉ Aᵉ Bᵉ)
              ( map-aut-family-with-descent-data-circleᵉ Aᵉ)
              ( λ xᵉ →
                map-dependent-automorphism-double-family-with-dependent-descent-data-circleᵉ
                  ( Aᵉ)
                  ( Bᵉ))
              ( uᵉ) ＝ᵉ
            uᵉ)
    ≃ᵉ Σᵉ ( type-family-with-descent-data-circleᵉ Aᵉ)
        ( λ xᵉ →
          ( is-in-subtypeᵉ subtype-descent-data-circle-subtypeᵉ xᵉ) ×ᵉ
          ( map-aut-family-with-descent-data-circleᵉ Aᵉ xᵉ ＝ᵉ xᵉ))
      byᵉ
        equiv-totᵉ
          ( λ xᵉ →
            equiv-totᵉ
              ( λ rᵉ →
                extensionality-type-subtype'ᵉ
                  ( subtype-descent-data-circle-subtypeᵉ)
                  ( _)
                  ( xᵉ ,ᵉ rᵉ)))
    ≃ᵉ Σᵉ ( type-family-with-descent-data-circleᵉ Aᵉ)
        ( λ xᵉ →
          ( map-aut-family-with-descent-data-circleᵉ Aᵉ xᵉ ＝ᵉ xᵉ) ×ᵉ
          ( is-in-subtypeᵉ subtype-descent-data-circle-subtypeᵉ xᵉ))
      byᵉ equiv-totᵉ (λ _ → commutative-productᵉ)
    ≃ᵉ Σᵉ ( fixpoint-descent-data-circleᵉ
          ( descent-data-family-with-descent-data-circleᵉ Aᵉ))
        ( λ xᵉ → is-in-subtypeᵉ subtype-descent-data-circle-subtypeᵉ (pr1ᵉ xᵉ))
      byᵉ
        inv-associative-Σᵉ
          ( type-family-with-descent-data-circleᵉ Aᵉ)
          ( λ xᵉ → map-aut-family-with-descent-data-circleᵉ Aᵉ xᵉ ＝ᵉ xᵉ)
          ( λ xᵉ → is-in-subtypeᵉ subtype-descent-data-circle-subtypeᵉ (pr1ᵉ xᵉ))

  equiv-section-descent-data-circle-subtype-fixpoint-in-subtypeᵉ :
    dependent-universal-property-circleᵉ lᵉ →
    ( (xᵉ : Sᵉ) → family-descent-data-circle-dependent-pair-typeᵉ lᵉ Aᵉ Bᵉ xᵉ) ≃ᵉ
    ( Σᵉ ( fixpoint-descent-data-circleᵉ
          ( descent-data-family-with-descent-data-circleᵉ Aᵉ))
        ( λ xᵉ → is-in-subtypeᵉ subtype-descent-data-circle-subtypeᵉ (pr1ᵉ xᵉ)))
  equiv-section-descent-data-circle-subtype-fixpoint-in-subtypeᵉ dup-circleᵉ =
    equiv-fixpoint-descent-data-circle-subtype-fixpoint-in-subtypeᵉ ∘eᵉ
    ( equiv-ev-fixpoint-descent-data-circleᵉ
      ( lᵉ)
      ( family-with-descent-data-circle-dependent-pair-typeᵉ lᵉ Aᵉ Bᵉ)
      ( dup-circleᵉ))
```