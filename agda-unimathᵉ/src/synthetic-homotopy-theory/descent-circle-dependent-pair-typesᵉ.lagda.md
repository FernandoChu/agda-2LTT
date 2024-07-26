# Descent data for families of dependent pair types over the circle

```agda
module synthetic-homotopy-theory.descent-circle-dependent-pair-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.dependent-descent-circleᵉ
open import synthetic-homotopy-theory.descent-circleᵉ
open import synthetic-homotopy-theory.free-loopsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ `Aᵉ : 𝕊¹ᵉ → U`ᵉ overᵉ theᵉ
[circle](synthetic-homotopy-theory.circle.mdᵉ) andᵉ aᵉ familyᵉ
`Bᵉ : (tᵉ : 𝕊¹ᵉ) → (Aᵉ tᵉ) → U`ᵉ overᵉ `A`,ᵉ theᵉ
[descentᵉ data](synthetic-homotopy-theory.descent-circle.mdᵉ) forᵉ theᵉ familyᵉ ofᵉ
[dependentᵉ pairᵉ types](foundation.dependent-pair-types.mdᵉ) `λᵉ tᵉ → Σᵉ (Aᵉ tᵉ) (Bᵉ t)`ᵉ
isᵉ `(Σᵉ Xᵉ R,ᵉ map-Σᵉ eᵉ k)`,ᵉ where `(X,ᵉ e)`ᵉ isᵉ descentᵉ data forᵉ `A`ᵉ andᵉ `(R,ᵉ k)`ᵉ isᵉ
dependentᵉ descentᵉ data forᵉ `B`.ᵉ

## Definitions

### Descent data for families of dependent pair types over the circle

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  ( Bᵉ : double-family-with-dependent-descent-data-circleᵉ lᵉ Aᵉ l3ᵉ)
  where

  descent-data-circle-dependent-pair-typeᵉ : descent-data-circleᵉ (l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ descent-data-circle-dependent-pair-typeᵉ =
    Σᵉ ( type-family-with-descent-data-circleᵉ Aᵉ)
      ( type-double-family-with-dependent-descent-data-circleᵉ Aᵉ Bᵉ)
  pr2ᵉ descent-data-circle-dependent-pair-typeᵉ =
    equiv-Σᵉ
      ( type-double-family-with-dependent-descent-data-circleᵉ Aᵉ Bᵉ)
      ( aut-family-with-descent-data-circleᵉ Aᵉ)
      ( dependent-automorphism-double-family-with-dependent-descent-data-circleᵉ
        ( Aᵉ)
        ( Bᵉ))

  family-descent-data-circle-dependent-pair-typeᵉ : Sᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  family-descent-data-circle-dependent-pair-typeᵉ xᵉ =
    Σᵉ ( family-family-with-descent-data-circleᵉ Aᵉ xᵉ)
      ( double-family-double-family-with-dependent-descent-data-circleᵉ Aᵉ Bᵉ xᵉ)
```

## Properties

### Characterization of descent data for families of dependent pair types over the circle

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  ( Bᵉ : double-family-with-dependent-descent-data-circleᵉ lᵉ Aᵉ l3ᵉ)
  where

  eq-descent-data-circle-dependent-pair-typeᵉ :
    equiv-descent-data-circleᵉ
      ( descent-data-circle-dependent-pair-typeᵉ lᵉ Aᵉ Bᵉ)
      ( descent-data-family-circleᵉ lᵉ
        ( family-descent-data-circle-dependent-pair-typeᵉ lᵉ Aᵉ Bᵉ))
  pr1ᵉ eq-descent-data-circle-dependent-pair-typeᵉ =
    equiv-Σᵉ
      ( double-family-double-family-with-dependent-descent-data-circleᵉ Aᵉ Bᵉ
        ( base-free-loopᵉ lᵉ))
      ( equiv-family-with-descent-data-circleᵉ Aᵉ)
      ( equiv-double-family-with-dependent-descent-data-circleᵉ Aᵉ Bᵉ)
  pr2ᵉ eq-descent-data-circle-dependent-pair-typeᵉ uᵉ =
    invᵉ
      ( tr-Σᵉ
          ( double-family-double-family-with-dependent-descent-data-circleᵉ Aᵉ Bᵉ)
          ( loop-free-loopᵉ lᵉ)
          ( map-Σᵉ
            ( double-family-double-family-with-dependent-descent-data-circleᵉ
              ( Aᵉ)
              ( Bᵉ)
              ( base-free-loopᵉ lᵉ))
            ( map-equiv-family-with-descent-data-circleᵉ Aᵉ)
            ( map-equiv-double-family-with-dependent-descent-data-circleᵉ Aᵉ Bᵉ)
            ( uᵉ)) ∙ᵉ
        eq-pair-Σᵉ
          ( invᵉ (coherence-square-family-with-descent-data-circleᵉ Aᵉ (pr1ᵉ uᵉ)))
          ( invᵉ
            ( coherence-square-double-family-with-dependent-descent-data-circleᵉ
              ( Aᵉ)
              ( Bᵉ)
              ( pr1ᵉ uᵉ)
              ( pr2ᵉ uᵉ) ∙ᵉ
              tr-eq-pair-Σᵉ
                ( ind-Σᵉ
                  ( double-family-double-family-with-dependent-descent-data-circleᵉ
                    ( Aᵉ)
                    ( Bᵉ)))
                ( loop-free-loopᵉ lᵉ)
                ( invᵉ
                  ( coherence-square-family-with-descent-data-circleᵉ Aᵉ (pr1ᵉ uᵉ)))
                ( map-equiv-double-family-with-dependent-descent-data-circleᵉ Aᵉ Bᵉ
                  ( pr1ᵉ uᵉ)
                  ( pr2ᵉ uᵉ)))))

  family-with-descent-data-circle-dependent-pair-typeᵉ :
    family-with-descent-data-circleᵉ lᵉ (l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ family-with-descent-data-circle-dependent-pair-typeᵉ =
    family-descent-data-circle-dependent-pair-typeᵉ lᵉ Aᵉ Bᵉ
  pr1ᵉ (pr2ᵉ family-with-descent-data-circle-dependent-pair-typeᵉ) =
    descent-data-circle-dependent-pair-typeᵉ lᵉ Aᵉ Bᵉ
  pr2ᵉ (pr2ᵉ family-with-descent-data-circle-dependent-pair-typeᵉ) =
    eq-descent-data-circle-dependent-pair-typeᵉ
```