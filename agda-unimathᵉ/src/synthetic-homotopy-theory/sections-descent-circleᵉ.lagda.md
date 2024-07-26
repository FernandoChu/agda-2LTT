# Sections of families over the circle

```agda
module synthetic-homotopy-theory.sections-descent-circleᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.commuting-triangles-of-identificationsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.path-algebraᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.descent-circleᵉ
open import synthetic-homotopy-theory.free-loopsᵉ
open import synthetic-homotopy-theory.universal-property-circleᵉ
```

</details>

## Idea

Sectionsᵉ ofᵉ typeᵉ familiesᵉ overᵉ theᵉ [circle](synthetic-homotopy-theory.circle.mdᵉ)
areᵉ exactlyᵉ theᵉ fixpointsᵉ ofᵉ theᵉ [automorphism](foundation.automorphisms.mdᵉ)
fromᵉ theᵉ correspondingᵉ
[descentᵉ data](synthetic-homotopy-theory.descent-circle.md).ᵉ

## Definitions

### Fixpoints of descent data

Aᵉ fixpointᵉ ofᵉ `(X,ᵉ e)`ᵉ isᵉ aᵉ fixpointᵉ ofᵉ `e`.ᵉ

```agda
fixpoint-descent-data-circleᵉ :
  { l1ᵉ : Level}
  ( Pᵉ : descent-data-circleᵉ l1ᵉ) → UUᵉ l1ᵉ
fixpoint-descent-data-circleᵉ Pᵉ =
  Σᵉ ( type-descent-data-circleᵉ Pᵉ)
    ( λ xᵉ → (map-descent-data-circleᵉ Pᵉ xᵉ) ＝ᵉ xᵉ)
```

## Properties

### Characterization of sections of type families over the circle

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  where

  map-compute-dependent-identification-loop-circleᵉ :
    ( xᵉ yᵉ : type-family-with-descent-data-circleᵉ Aᵉ) →
    map-aut-family-with-descent-data-circleᵉ Aᵉ xᵉ ＝ᵉ yᵉ →
    dependent-identificationᵉ (family-family-with-descent-data-circleᵉ Aᵉ)
      ( loop-free-loopᵉ lᵉ)
      ( map-equiv-family-with-descent-data-circleᵉ Aᵉ xᵉ)
      ( map-equiv-family-with-descent-data-circleᵉ Aᵉ yᵉ)
  map-compute-dependent-identification-loop-circleᵉ xᵉ yᵉ qᵉ =
    invᵉ (coherence-square-family-with-descent-data-circleᵉ Aᵉ xᵉ) ∙ᵉ
    ( apᵉ (map-equiv-family-with-descent-data-circleᵉ Aᵉ) qᵉ)

  is-equiv-map-compute-dependent-identification-loop-circleᵉ :
    ( xᵉ yᵉ : type-family-with-descent-data-circleᵉ Aᵉ) →
    is-equivᵉ (map-compute-dependent-identification-loop-circleᵉ xᵉ yᵉ)
  is-equiv-map-compute-dependent-identification-loop-circleᵉ xᵉ yᵉ =
    fundamental-theorem-idᵉ
      ( is-contr-equiv'ᵉ
        ( fiberᵉ
          ( map-equiv-family-with-descent-data-circleᵉ Aᵉ)
          ( trᵉ
            ( family-family-with-descent-data-circleᵉ Aᵉ)
            ( loop-free-loopᵉ lᵉ)
            ( map-equiv-family-with-descent-data-circleᵉ Aᵉ xᵉ)))
        ( equiv-fiberᵉ _ _)
        ( is-contr-map-is-equivᵉ
          ( is-equiv-map-equivᵉ (equiv-family-with-descent-data-circleᵉ Aᵉ))
          ( trᵉ
            ( family-family-with-descent-data-circleᵉ Aᵉ)
            ( loop-free-loopᵉ lᵉ)
            ( map-equiv-family-with-descent-data-circleᵉ Aᵉ xᵉ))))
      ( map-compute-dependent-identification-loop-circleᵉ xᵉ)
      ( yᵉ)

  compute-dependent-identification-loop-circleᵉ :
    ( xᵉ yᵉ : type-family-with-descent-data-circleᵉ Aᵉ) →
    ( map-aut-family-with-descent-data-circleᵉ Aᵉ xᵉ ＝ᵉ yᵉ) ≃ᵉ
    ( dependent-identificationᵉ
      ( family-family-with-descent-data-circleᵉ Aᵉ)
      ( loop-free-loopᵉ lᵉ)
      ( map-equiv-family-with-descent-data-circleᵉ Aᵉ xᵉ)
      ( map-equiv-family-with-descent-data-circleᵉ Aᵉ yᵉ))
  pr1ᵉ (compute-dependent-identification-loop-circleᵉ xᵉ yᵉ) =
    map-compute-dependent-identification-loop-circleᵉ xᵉ yᵉ
  pr2ᵉ (compute-dependent-identification-loop-circleᵉ xᵉ yᵉ) =
    is-equiv-map-compute-dependent-identification-loop-circleᵉ xᵉ yᵉ
```

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  where

  ev-fixpoint-descent-data-circleᵉ :
    ( (xᵉ : Sᵉ) → family-family-with-descent-data-circleᵉ Aᵉ xᵉ) →
    ( fixpoint-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ Aᵉ))
  pr1ᵉ (ev-fixpoint-descent-data-circleᵉ sᵉ) =
    map-inv-equivᵉ
      ( equiv-family-with-descent-data-circleᵉ Aᵉ)
      ( sᵉ (base-free-loopᵉ lᵉ))
  pr2ᵉ (ev-fixpoint-descent-data-circleᵉ sᵉ) =
    map-inv-equivᵉ
      ( compute-dependent-identification-loop-circleᵉ
        ( lᵉ)
        ( Aᵉ)
        ( map-inv-equivᵉ
          ( equiv-family-with-descent-data-circleᵉ Aᵉ)
          ( sᵉ (base-free-loopᵉ lᵉ)))
        ( map-inv-equivᵉ
          ( equiv-family-with-descent-data-circleᵉ Aᵉ)
          ( sᵉ (base-free-loopᵉ lᵉ))))
      ( ( apᵉ
          ( trᵉ (family-family-with-descent-data-circleᵉ Aᵉ) (loop-free-loopᵉ lᵉ))
          ( is-section-map-inv-equivᵉ
            ( equiv-family-with-descent-data-circleᵉ Aᵉ)
            ( sᵉ (base-free-loopᵉ lᵉ)))) ∙ᵉ
        ( ( apdᵉ sᵉ (loop-free-loopᵉ lᵉ)) ∙ᵉ
          ( invᵉ
            ( is-section-map-inv-equivᵉ
              ( equiv-family-with-descent-data-circleᵉ Aᵉ)
              ( sᵉ (base-free-loopᵉ lᵉ))))))

  equiv-fixpoint-descent-data-circle-free-dependent-loopᵉ :
    ( fixpoint-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ Aᵉ)) ≃ᵉ
    ( free-dependent-loopᵉ lᵉ (family-family-with-descent-data-circleᵉ Aᵉ))
  equiv-fixpoint-descent-data-circle-free-dependent-loopᵉ =
    equiv-Σᵉ
      ( λ xᵉ →
        dependent-identificationᵉ
          ( family-family-with-descent-data-circleᵉ Aᵉ)
          ( loop-free-loopᵉ lᵉ)
          ( xᵉ)
          ( xᵉ))
      ( equiv-family-with-descent-data-circleᵉ Aᵉ)
      ( λ xᵉ →
        compute-dependent-identification-loop-circleᵉ lᵉ Aᵉ xᵉ xᵉ)

  comparison-fixpoint-descent-data-circleᵉ :
    ( fixpoint-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ Aᵉ)) →
    ( free-dependent-loopᵉ lᵉ (family-family-with-descent-data-circleᵉ Aᵉ))
  comparison-fixpoint-descent-data-circleᵉ =
    map-equivᵉ equiv-fixpoint-descent-data-circle-free-dependent-loopᵉ

  triangle-comparison-fixpoint-descent-data-circleᵉ :
    coherence-triangle-mapsᵉ
      ( ev-free-loop-Πᵉ lᵉ (family-family-with-descent-data-circleᵉ Aᵉ))
      ( comparison-fixpoint-descent-data-circleᵉ)
      ( ev-fixpoint-descent-data-circleᵉ)
  triangle-comparison-fixpoint-descent-data-circleᵉ sᵉ =
    eq-Eq-free-dependent-loopᵉ lᵉ
      ( family-family-with-descent-data-circleᵉ Aᵉ)
      ( ev-free-loop-Πᵉ lᵉ (family-family-with-descent-data-circleᵉ Aᵉ) sᵉ)
      ( ( comparison-fixpoint-descent-data-circleᵉ ∘ᵉ
          ev-fixpoint-descent-data-circleᵉ)
        ( sᵉ))
      ( invᵉ is-section-inv-αᵉ ,ᵉ
        invᵉ
        ( ( horizontal-concat-Id²ᵉ
            ( reflᵉ
              { xᵉ =
                apᵉ
                  ( trᵉ
                    ( family-family-with-descent-data-circleᵉ Aᵉ)
                    ( loop-free-loopᵉ lᵉ))
                  ( invᵉ is-section-inv-αᵉ)})
            ( is-section-map-inv-is-equivᵉ
              ( is-equiv-map-compute-dependent-identification-loop-circleᵉ
                ( lᵉ)
                ( Aᵉ)
                ( map-inv-equivᵉ
                  ( equiv-family-with-descent-data-circleᵉ Aᵉ)
                  ( sᵉ (base-free-loopᵉ lᵉ)))
                ( pr1ᵉ (ev-fixpoint-descent-data-circleᵉ sᵉ)))
              ( _))) ∙ᵉ
          ( ( invᵉ (assocᵉ (apᵉ _ (invᵉ is-section-inv-αᵉ)) _ _)) ∙ᵉ
            ( horizontal-concat-Id²ᵉ
              ( invᵉ
                ( map-coherence-triangle-identificationsᵉ
                  ( trᵉ
                    ( family-family-with-descent-data-circleᵉ Aᵉ)
                    ( loop-free-loopᵉ lᵉ))
                  ( reflᵉ)
                  ( is-section-inv-αᵉ)
                  ( invᵉ is-section-inv-αᵉ)
                  ( invᵉ (left-invᵉ is-section-inv-αᵉ))))
              ( reflᵉ)))))
    where
    is-section-inv-αᵉ :
      eq-valueᵉ
        ( map-equiv-family-with-descent-data-circleᵉ Aᵉ ∘ᵉ
          map-inv-equivᵉ (equiv-family-with-descent-data-circleᵉ Aᵉ))
        ( idᵉ)
        ( sᵉ (base-free-loopᵉ lᵉ))
    is-section-inv-αᵉ =
      is-section-map-inv-equivᵉ
        ( equiv-family-with-descent-data-circleᵉ Aᵉ)
        ( sᵉ (base-free-loopᵉ lᵉ))

  is-equiv-comparison-fixpoint-descent-data-circleᵉ :
    is-equivᵉ comparison-fixpoint-descent-data-circleᵉ
  is-equiv-comparison-fixpoint-descent-data-circleᵉ =
    is-equiv-map-equivᵉ equiv-fixpoint-descent-data-circle-free-dependent-loopᵉ

  is-equiv-ev-fixpoint-descent-data-circleᵉ :
    dependent-universal-property-circleᵉ lᵉ →
    is-equivᵉ ev-fixpoint-descent-data-circleᵉ
  is-equiv-ev-fixpoint-descent-data-circleᵉ dup-circleᵉ =
    is-equiv-top-map-triangleᵉ
      ( ev-free-loop-Πᵉ lᵉ (family-family-with-descent-data-circleᵉ Aᵉ))
      ( comparison-fixpoint-descent-data-circleᵉ)
      ( ev-fixpoint-descent-data-circleᵉ)
      ( triangle-comparison-fixpoint-descent-data-circleᵉ)
      ( is-equiv-comparison-fixpoint-descent-data-circleᵉ)
      ( dup-circleᵉ (family-family-with-descent-data-circleᵉ Aᵉ))

  equiv-ev-fixpoint-descent-data-circleᵉ :
    dependent-universal-property-circleᵉ lᵉ →
    ( (xᵉ : Sᵉ) → (family-family-with-descent-data-circleᵉ Aᵉ) xᵉ) ≃ᵉ
    ( fixpoint-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ Aᵉ))
  pr1ᵉ (equiv-ev-fixpoint-descent-data-circleᵉ dup-circleᵉ) =
    ev-fixpoint-descent-data-circleᵉ
  pr2ᵉ (equiv-ev-fixpoint-descent-data-circleᵉ dup-circleᵉ) =
    is-equiv-ev-fixpoint-descent-data-circleᵉ dup-circleᵉ

  compute-ev-fixpoint-descent-data-circleᵉ :
    coherence-square-mapsᵉ
      ( ev-fixpoint-descent-data-circleᵉ)
      ( ev-pointᵉ (base-free-loopᵉ lᵉ))
      ( pr1ᵉ)
      ( map-inv-equivᵉ (equiv-family-with-descent-data-circleᵉ Aᵉ))
  compute-ev-fixpoint-descent-data-circleᵉ = refl-htpyᵉ
```