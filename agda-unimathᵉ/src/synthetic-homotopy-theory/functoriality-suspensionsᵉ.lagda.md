# Functoriality of suspensions

```agda
module synthetic-homotopy-theory.functoriality-suspensionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.retractionsᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.sectionsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.suspension-structuresᵉ
open import synthetic-homotopy-theory.suspensions-of-typesᵉ
```

</details>

## Idea

Anyᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ inducesᵉ aᵉ mapᵉ
`map-suspensionᵉ fᵉ : suspensionᵉ Aᵉ → suspensionᵉ B`ᵉ onᵉ theᵉ
[suspensions](synthetic-homotopy-theory.suspensions-of-types.mdᵉ) suspensionsᵉ ofᵉ
`A`ᵉ andᵉ `B`.ᵉ

Furthermore,ᵉ thisᵉ operationᵉ isᵉ functorialᵉ: itᵉ preservesᵉ identitiesᵉ andᵉ functionᵉ
composition.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  map-suspension-structureᵉ : suspension-structureᵉ Aᵉ (suspensionᵉ Bᵉ)
  pr1ᵉ map-suspension-structureᵉ = north-suspensionᵉ
  pr1ᵉ (pr2ᵉ map-suspension-structureᵉ) = south-suspensionᵉ
  pr2ᵉ (pr2ᵉ map-suspension-structureᵉ) = meridian-suspensionᵉ ∘ᵉ fᵉ

  map-suspensionᵉ : suspensionᵉ Aᵉ → suspensionᵉ Bᵉ
  map-suspensionᵉ =
    cogap-suspensionᵉ map-suspension-structureᵉ

  compute-north-map-suspensionᵉ :
    map-suspensionᵉ (north-suspensionᵉ) ＝ᵉ north-suspensionᵉ
  compute-north-map-suspensionᵉ =
    compute-north-cogap-suspensionᵉ map-suspension-structureᵉ

  compute-south-map-suspensionᵉ :
    map-suspensionᵉ (south-suspensionᵉ) ＝ᵉ south-suspensionᵉ
  compute-south-map-suspensionᵉ =
    compute-south-cogap-suspensionᵉ map-suspension-structureᵉ

  compute-meridian-map-suspensionᵉ :
    (aᵉ : Aᵉ) →
    coherence-square-identificationsᵉ
      ( compute-north-map-suspensionᵉ)
      ( apᵉ map-suspensionᵉ (meridian-suspensionᵉ aᵉ))
      ( meridian-suspensionᵉ (fᵉ aᵉ))
      ( compute-south-map-suspensionᵉ)
  compute-meridian-map-suspensionᵉ =
    compute-meridian-cogap-suspensionᵉ
      ( map-suspension-structureᵉ)
```

## Properties

### The induced map on suspensions of the identity is the identity again

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  htpy-function-out-of-suspension-id-map-suspensionᵉ :
    htpy-function-out-of-suspensionᵉ Aᵉ (map-suspensionᵉ idᵉ) idᵉ
  pr1ᵉ htpy-function-out-of-suspension-id-map-suspensionᵉ =
    compute-north-map-suspensionᵉ idᵉ
  pr1ᵉ (pr2ᵉ htpy-function-out-of-suspension-id-map-suspensionᵉ) =
    compute-south-map-suspensionᵉ idᵉ
  pr2ᵉ (pr2ᵉ htpy-function-out-of-suspension-id-map-suspensionᵉ) aᵉ =
    concat-right-identification-coherence-square-identificationsᵉ
      ( compute-north-map-suspensionᵉ idᵉ)
      ( apᵉ (map-suspensionᵉ idᵉ) (meridian-suspensionᵉ aᵉ))
      ( meridian-suspensionᵉ aᵉ)
      ( compute-south-map-suspensionᵉ idᵉ)
      ( invᵉ (ap-idᵉ (meridian-suspensionᵉ aᵉ)))
      ( compute-meridian-map-suspensionᵉ idᵉ aᵉ)

  id-map-suspensionᵉ : map-suspensionᵉ (idᵉ {Aᵉ = Aᵉ}) ~ᵉ idᵉ
  id-map-suspensionᵉ =
    htpy-htpy-function-out-of-suspensionᵉ Aᵉ
      ( map-suspensionᵉ idᵉ)
      ( idᵉ)
      ( htpy-function-out-of-suspension-id-map-suspensionᵉ)
```

### The induced map on suspensions of a composition is the composition of the induced maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Bᵉ → Cᵉ)
  where

  preserves-comp-map-suspension-northᵉ :
    (map-suspensionᵉ gᵉ ∘ᵉ map-suspensionᵉ fᵉ) north-suspensionᵉ ＝ᵉ
    map-suspensionᵉ (gᵉ ∘ᵉ fᵉ) north-suspensionᵉ
  preserves-comp-map-suspension-northᵉ =
    apᵉ (map-suspensionᵉ gᵉ) (compute-north-map-suspensionᵉ fᵉ) ∙ᵉ
    ( compute-north-map-suspensionᵉ gᵉ ∙ᵉ
      ( invᵉ (compute-north-map-suspensionᵉ (gᵉ ∘ᵉ fᵉ))))

  preserves-comp-map-suspension-southᵉ :
    (map-suspensionᵉ gᵉ ∘ᵉ map-suspensionᵉ fᵉ) south-suspensionᵉ ＝ᵉ
    map-suspensionᵉ (gᵉ ∘ᵉ fᵉ) south-suspensionᵉ
  preserves-comp-map-suspension-southᵉ =
    apᵉ (map-suspensionᵉ gᵉ) (compute-south-map-suspensionᵉ fᵉ) ∙ᵉ
    ( compute-south-map-suspensionᵉ gᵉ ∙ᵉ
      ( invᵉ (compute-south-map-suspensionᵉ (gᵉ ∘ᵉ fᵉ))))

  coherence-square-identifications-comp-map-suspensionᵉ :
    (aᵉ : Aᵉ) →
    coherence-square-identificationsᵉ
      ( preserves-comp-map-suspension-northᵉ)
      ( apᵉ (map-suspensionᵉ gᵉ ∘ᵉ map-suspensionᵉ fᵉ) (meridian-suspensionᵉ aᵉ))
      ( apᵉ (map-suspensionᵉ (gᵉ ∘ᵉ fᵉ)) (meridian-suspensionᵉ aᵉ))
      ( preserves-comp-map-suspension-southᵉ)
  coherence-square-identifications-comp-map-suspensionᵉ aᵉ =
    horizontal-pasting-coherence-square-identificationsᵉ _ _
      ( apᵉ (map-suspensionᵉ gᵉ ∘ᵉ map-suspensionᵉ fᵉ) (meridian-suspensionᵉ aᵉ))
      ( apᵉ (map-suspensionᵉ gᵉ) (meridian-suspensionᵉ (fᵉ aᵉ)))
      ( apᵉ (map-suspensionᵉ (gᵉ ∘ᵉ fᵉ)) (meridian-suspensionᵉ aᵉ))
      ( _)
      ( _)
      ( concat-left-identification-coherence-square-identificationsᵉ
        ( apᵉ (map-suspensionᵉ gᵉ) (compute-north-map-suspensionᵉ fᵉ))
        ( apᵉ (map-suspensionᵉ gᵉ) (apᵉ (map-suspensionᵉ fᵉ) (meridian-suspensionᵉ aᵉ)))
        ( apᵉ (map-suspensionᵉ gᵉ) (meridian-suspensionᵉ (fᵉ aᵉ)))
        ( apᵉ (map-suspensionᵉ gᵉ) (compute-south-map-suspensionᵉ fᵉ))
        ( invᵉ
          ( ap-compᵉ
            ( map-suspensionᵉ gᵉ)
            ( map-suspensionᵉ fᵉ)
            ( meridian-suspensionᵉ aᵉ)))
        ( map-coherence-square-identificationsᵉ
          ( map-suspensionᵉ gᵉ)
          ( compute-north-map-suspensionᵉ fᵉ)
          ( apᵉ (map-suspensionᵉ fᵉ) (meridian-suspensionᵉ aᵉ))
          ( meridian-suspensionᵉ (fᵉ aᵉ))
          ( compute-south-map-suspensionᵉ fᵉ)
          ( compute-meridian-map-suspensionᵉ fᵉ aᵉ)))
      ( horizontal-pasting-coherence-square-identificationsᵉ _ _
        ( apᵉ (map-suspensionᵉ gᵉ) (meridian-suspensionᵉ (fᵉ aᵉ)))
        ( meridian-suspensionᵉ (gᵉ (fᵉ aᵉ)))
        ( apᵉ (map-suspensionᵉ (gᵉ ∘ᵉ fᵉ)) (meridian-suspensionᵉ aᵉ))
        ( _)
        ( _)
        ( compute-meridian-map-suspensionᵉ gᵉ (fᵉ aᵉ))
        ( horizontal-inv-coherence-square-identificationsᵉ
          ( compute-north-map-suspensionᵉ (gᵉ ∘ᵉ fᵉ))
          ( apᵉ (map-suspensionᵉ (gᵉ ∘ᵉ fᵉ)) (meridian-suspensionᵉ aᵉ))
          ( meridian-suspensionᵉ (gᵉ (fᵉ aᵉ)))
          ( compute-south-map-suspensionᵉ (gᵉ ∘ᵉ fᵉ))
          ( compute-meridian-map-suspensionᵉ (gᵉ ∘ᵉ fᵉ) aᵉ)))

  htpy-function-out-of-suspension-comp-map-suspensionᵉ :
    htpy-function-out-of-suspensionᵉ Aᵉ
      ( map-suspensionᵉ gᵉ ∘ᵉ map-suspensionᵉ fᵉ)
      ( map-suspensionᵉ (gᵉ ∘ᵉ fᵉ))
  pr1ᵉ htpy-function-out-of-suspension-comp-map-suspensionᵉ =
    preserves-comp-map-suspension-northᵉ
  pr1ᵉ (pr2ᵉ htpy-function-out-of-suspension-comp-map-suspensionᵉ) =
    preserves-comp-map-suspension-southᵉ
  pr2ᵉ (pr2ᵉ htpy-function-out-of-suspension-comp-map-suspensionᵉ) =
    coherence-square-identifications-comp-map-suspensionᵉ

  inv-preserves-comp-map-suspensionᵉ :
    map-suspensionᵉ gᵉ ∘ᵉ map-suspensionᵉ fᵉ ~ᵉ map-suspensionᵉ (gᵉ ∘ᵉ fᵉ)
  inv-preserves-comp-map-suspensionᵉ =
    htpy-htpy-function-out-of-suspensionᵉ Aᵉ
      ( map-suspensionᵉ gᵉ ∘ᵉ map-suspensionᵉ fᵉ)
      ( map-suspensionᵉ (gᵉ ∘ᵉ fᵉ))
      ( htpy-function-out-of-suspension-comp-map-suspensionᵉ)

  preserves-comp-map-suspensionᵉ :
    map-suspensionᵉ (gᵉ ∘ᵉ fᵉ) ~ᵉ map-suspensionᵉ gᵉ ∘ᵉ map-suspensionᵉ fᵉ
  preserves-comp-map-suspensionᵉ = inv-htpyᵉ inv-preserves-comp-map-suspensionᵉ
```

### Suspensions preserve retracts

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  section-map-suspension-sectionᵉ :
    (fᵉ : Aᵉ → Bᵉ) → sectionᵉ fᵉ → sectionᵉ (map-suspensionᵉ fᵉ)
  pr1ᵉ (section-map-suspension-sectionᵉ fᵉ Sᵉ) =
    map-suspensionᵉ (map-sectionᵉ fᵉ Sᵉ)
  pr2ᵉ (section-map-suspension-sectionᵉ fᵉ (sᵉ ,ᵉ hᵉ)) =
    homotopy-reasoningᵉ
      map-suspensionᵉ fᵉ ∘ᵉ map-suspensionᵉ sᵉ
      ~ᵉ map-suspensionᵉ (fᵉ ∘ᵉ sᵉ)
        byᵉ inv-preserves-comp-map-suspensionᵉ sᵉ fᵉ
      ~ᵉ map-suspensionᵉ idᵉ
        byᵉ htpy-eqᵉ (apᵉ map-suspensionᵉ (eq-htpyᵉ hᵉ))
      ~ᵉ idᵉ
        byᵉ id-map-suspensionᵉ Bᵉ

  retraction-map-suspension-retractionᵉ :
    (fᵉ : Aᵉ → Bᵉ) → retractionᵉ fᵉ → retractionᵉ (map-suspensionᵉ fᵉ)
  pr1ᵉ (retraction-map-suspension-retractionᵉ fᵉ Sᵉ) =
    map-suspensionᵉ (map-retractionᵉ fᵉ Sᵉ)
  pr2ᵉ (retraction-map-suspension-retractionᵉ fᵉ (rᵉ ,ᵉ hᵉ)) =
    homotopy-reasoningᵉ
      map-suspensionᵉ rᵉ ∘ᵉ map-suspensionᵉ fᵉ
      ~ᵉ map-suspensionᵉ (rᵉ ∘ᵉ fᵉ)
        byᵉ inv-preserves-comp-map-suspensionᵉ fᵉ rᵉ
      ~ᵉ map-suspensionᵉ idᵉ
        byᵉ htpy-eqᵉ (apᵉ map-suspensionᵉ (eq-htpyᵉ hᵉ))
      ~ᵉ idᵉ
        byᵉ id-map-suspensionᵉ Aᵉ

  retract-of-suspension-retract-ofᵉ :
    Aᵉ retract-ofᵉ Bᵉ → (suspensionᵉ Aᵉ) retract-ofᵉ (suspensionᵉ Bᵉ)
  pr1ᵉ (retract-of-suspension-retract-ofᵉ Rᵉ) =
    map-suspensionᵉ (inclusion-retractᵉ Rᵉ)
  pr2ᵉ (retract-of-suspension-retract-ofᵉ Rᵉ) =
    retraction-map-suspension-retractionᵉ
      ( inclusion-retractᵉ Rᵉ)
      ( retraction-retractᵉ Rᵉ)
```

### Equivalent types have equivalent suspensions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-equiv-map-suspension-is-equivᵉ :
    (fᵉ : Aᵉ → Bᵉ) → is-equivᵉ fᵉ → is-equivᵉ (map-suspensionᵉ fᵉ)
  pr1ᵉ (is-equiv-map-suspension-is-equivᵉ fᵉ eᵉ) =
    section-map-suspension-sectionᵉ fᵉ (section-is-equivᵉ eᵉ)
  pr2ᵉ (is-equiv-map-suspension-is-equivᵉ fᵉ eᵉ) =
    retraction-map-suspension-retractionᵉ fᵉ (retraction-is-equivᵉ eᵉ)

  equiv-suspensionᵉ : Aᵉ ≃ᵉ Bᵉ → suspensionᵉ Aᵉ ≃ᵉ suspensionᵉ Bᵉ
  pr1ᵉ (equiv-suspensionᵉ eᵉ) =
    map-suspensionᵉ (map-equivᵉ eᵉ)
  pr2ᵉ (equiv-suspensionᵉ eᵉ) =
    is-equiv-map-suspension-is-equivᵉ (map-equivᵉ eᵉ) (is-equiv-map-equivᵉ eᵉ)
```