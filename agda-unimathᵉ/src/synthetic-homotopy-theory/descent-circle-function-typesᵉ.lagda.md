# Descent data for families of function types over the circle

```agda
module synthetic-homotopy-theory.descent-circle-function-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.identity-typesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.descent-circleᵉ
open import synthetic-homotopy-theory.free-loopsᵉ
open import synthetic-homotopy-theory.morphisms-descent-data-circleᵉ
open import synthetic-homotopy-theory.sections-descent-circleᵉ
open import synthetic-homotopy-theory.universal-property-circleᵉ
```

</details>

## Idea

Givenᵉ twoᵉ familiesᵉ `A,ᵉ Bᵉ : 𝕊¹ᵉ → U`ᵉ overᵉ theᵉ
[circle](synthetic-homotopy-theory.circle.md),ᵉ theᵉ
[descentᵉ data](synthetic-homotopy-theory.descent-circle.mdᵉ) forᵉ theᵉ familyᵉ ofᵉ
functionᵉ typesᵉ `λᵉ tᵉ → (Aᵉ tᵉ → Bᵉ t)`ᵉ isᵉ `(Xᵉ → Y,ᵉ λ hᵉ → fᵉ ∘ᵉ hᵉ ∘ᵉ e⁻¹)`,ᵉ where
`(X,ᵉ e)`ᵉ isᵉ descentᵉ data forᵉ `A`ᵉ andᵉ `(Y,ᵉ f)`ᵉ isᵉ descentᵉ data forᵉ `B`.ᵉ

Thisᵉ correspondenceᵉ allowsᵉ usᵉ to characterizeᵉ sectionsᵉ ofᵉ thisᵉ familyᵉ asᵉ
homomorphismsᵉ fromᵉ `(X,ᵉ e)`ᵉ to `(Y,ᵉ f)`.ᵉ

## Definitions

### Descent data for families of function types over the circle

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  ( Bᵉ : family-with-descent-data-circleᵉ lᵉ l3ᵉ)
  where

  family-descent-data-circle-function-typeᵉ : Sᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  family-descent-data-circle-function-typeᵉ xᵉ =
    family-family-with-descent-data-circleᵉ Aᵉ xᵉ →
    family-family-with-descent-data-circleᵉ Bᵉ xᵉ

  descent-data-circle-function-typeᵉ : descent-data-circleᵉ (l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ descent-data-circle-function-typeᵉ =
    type-family-with-descent-data-circleᵉ Aᵉ →
    type-family-with-descent-data-circleᵉ Bᵉ
  pr2ᵉ descent-data-circle-function-typeᵉ =
    ( equiv-postcompᵉ
      ( type-family-with-descent-data-circleᵉ Aᵉ)
      ( aut-family-with-descent-data-circleᵉ Bᵉ)) ∘eᵉ
    ( equiv-precompᵉ
      ( inv-equivᵉ (aut-family-with-descent-data-circleᵉ Aᵉ))
      ( type-family-with-descent-data-circleᵉ Bᵉ))
```

## Properties

### Characterization of descent data for families of function types over the circle

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  ( Bᵉ : family-with-descent-data-circleᵉ lᵉ l3ᵉ)
  where

  eq-descent-data-circle-function-typeᵉ :
    equiv-descent-data-circleᵉ
      ( descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ)
      ( descent-data-family-circleᵉ
        ( lᵉ)
        ( family-descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ))
  pr1ᵉ eq-descent-data-circle-function-typeᵉ =
    ( equiv-postcompᵉ
      ( family-family-with-descent-data-circleᵉ Aᵉ (base-free-loopᵉ lᵉ))
      ( equiv-family-with-descent-data-circleᵉ Bᵉ)) ∘eᵉ
    ( equiv-precompᵉ
      ( inv-equivᵉ (equiv-family-with-descent-data-circleᵉ Aᵉ))
      ( type-family-with-descent-data-circleᵉ Bᵉ))
  pr2ᵉ eq-descent-data-circle-function-typeᵉ hᵉ =
    ( eq-htpyᵉ
      ( horizontal-concat-htpyᵉ
        ( coherence-square-family-with-descent-data-circleᵉ Bᵉ)
        ( hᵉ ·lᵉ
          inv-htpyᵉ
            ( coherence-square-maps-inv-equivᵉ
              ( equiv-family-with-descent-data-circleᵉ Aᵉ)
              ( aut-family-with-descent-data-circleᵉ Aᵉ)
              ( equiv-trᵉ
                ( family-family-with-descent-data-circleᵉ Aᵉ)
                ( loop-free-loopᵉ lᵉ))
              ( equiv-family-with-descent-data-circleᵉ Aᵉ)
              ( coherence-square-family-with-descent-data-circleᵉ Aᵉ))))) ∙ᵉ
    ( invᵉ
      ( ( tr-function-typeᵉ
          ( family-family-with-descent-data-circleᵉ Aᵉ)
          ( family-family-with-descent-data-circleᵉ Bᵉ) (loop-free-loopᵉ lᵉ))
        ( map-equiv-descent-data-circleᵉ
          ( descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ)
          ( descent-data-family-circleᵉ
            ( lᵉ)
            ( family-descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ))
          ( eq-descent-data-circle-function-typeᵉ)
          ( hᵉ))))

  family-with-descent-data-circle-function-typeᵉ :
    family-with-descent-data-circleᵉ lᵉ (l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ family-with-descent-data-circle-function-typeᵉ =
    family-descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ
  pr1ᵉ (pr2ᵉ family-with-descent-data-circle-function-typeᵉ) =
    descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ
  pr2ᵉ (pr2ᵉ family-with-descent-data-circle-function-typeᵉ) =
    eq-descent-data-circle-function-typeᵉ
```

### Maps between families over the circle are equivalent to homomorphisms between the families' descent data

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  ( Bᵉ : family-with-descent-data-circleᵉ lᵉ l3ᵉ)
  where

  equiv-fixpoint-descent-data-circle-function-type-homᵉ :
    fixpoint-descent-data-circleᵉ (descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ) ≃ᵉ
    hom-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
      ( descent-data-family-with-descent-data-circleᵉ Bᵉ)
  equiv-fixpoint-descent-data-circle-function-type-homᵉ =
    equiv-totᵉ
      ( λ hᵉ →
        ( equiv-inv-htpyᵉ
          ( map-aut-family-with-descent-data-circleᵉ Bᵉ ∘ᵉ hᵉ)
          ( hᵉ ∘ᵉ map-aut-family-with-descent-data-circleᵉ Aᵉ)) ∘eᵉ
        ( inv-equivᵉ
          ( equiv-coherence-triangle-maps-inv-topᵉ
            ( map-aut-family-with-descent-data-circleᵉ Bᵉ ∘ᵉ hᵉ)
            ( hᵉ)
            ( aut-family-with-descent-data-circleᵉ Aᵉ))) ∘eᵉ
        ( equiv-inv-htpyᵉ _ _) ∘eᵉ
        ( equiv-funextᵉ))

  equiv-descent-data-family-circle-function-type-homᵉ :
    dependent-universal-property-circleᵉ lᵉ →
    ( (xᵉ : Sᵉ) → family-descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ xᵉ) ≃ᵉ
    hom-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
      ( descent-data-family-with-descent-data-circleᵉ Bᵉ)
  equiv-descent-data-family-circle-function-type-homᵉ dup-circleᵉ =
    equiv-fixpoint-descent-data-circle-function-type-homᵉ ∘eᵉ
    ( equiv-ev-fixpoint-descent-data-circleᵉ
      ( lᵉ)
      ( family-with-descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ)
      ( dup-circleᵉ))
```