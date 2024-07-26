# Dependent products of pullbacks

```agda
module foundation.dependent-products-pullbacksᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.pullbacksᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.universal-property-pullbacksᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ pullbackᵉ squaresᵉ

```text
    Cᵢᵉ ----->ᵉ Bᵢᵉ
    | ⌟ᵉ       |
    |         | gᵢᵉ
    ∨ᵉ         ∨ᵉ
    Aᵢᵉ ----->ᵉ Xᵢᵉ
         fᵢᵉ
```

indexedᵉ byᵉ `iᵉ : I`,ᵉ theirᵉ dependentᵉ productᵉ

```text
  Πᵢᵉ Cᵢᵉ ----->ᵉ Πᵢᵉ Bᵢᵉ
    | ⌟ᵉ          |
    |            | Πᵢᵉ gᵢᵉ
    ∨ᵉ            ∨ᵉ
  Πᵢᵉ Aᵢᵉ ----->ᵉ Πᵢᵉ Xᵢᵉ
         Πᵢᵉ fᵢᵉ
```

isᵉ againᵉ aᵉ pullbackᵉ square.ᵉ

## Definitions

### Dependent products of cones

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
  {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ} {Xᵉ : Iᵉ → UUᵉ l4ᵉ} {Cᵉ : Iᵉ → UUᵉ l5ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Xᵉ iᵉ) (gᵉ : (iᵉ : Iᵉ) → Bᵉ iᵉ → Xᵉ iᵉ)
  (cᵉ : (iᵉ : Iᵉ) → coneᵉ (fᵉ iᵉ) (gᵉ iᵉ) (Cᵉ iᵉ))
  where

  cone-Πᵉ : coneᵉ (map-Πᵉ fᵉ) (map-Πᵉ gᵉ) ((iᵉ : Iᵉ) → Cᵉ iᵉ)
  pr1ᵉ cone-Πᵉ = map-Πᵉ (λ iᵉ → pr1ᵉ (cᵉ iᵉ))
  pr1ᵉ (pr2ᵉ cone-Πᵉ) = map-Πᵉ (λ iᵉ → pr1ᵉ (pr2ᵉ (cᵉ iᵉ)))
  pr2ᵉ (pr2ᵉ cone-Πᵉ) = htpy-map-Πᵉ (λ iᵉ → pr2ᵉ (pr2ᵉ (cᵉ iᵉ)))
```

## Properties

### Computing the standard pullback of a dependent product

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
  {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ} {Xᵉ : Iᵉ → UUᵉ l4ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Xᵉ iᵉ) (gᵉ : (iᵉ : Iᵉ) → Bᵉ iᵉ → Xᵉ iᵉ)
  where

  map-standard-pullback-Πᵉ :
    standard-pullbackᵉ (map-Πᵉ fᵉ) (map-Πᵉ gᵉ) →
    (iᵉ : Iᵉ) → standard-pullbackᵉ (fᵉ iᵉ) (gᵉ iᵉ)
  pr1ᵉ (map-standard-pullback-Πᵉ (αᵉ ,ᵉ βᵉ ,ᵉ γᵉ) iᵉ) = αᵉ iᵉ
  pr1ᵉ (pr2ᵉ (map-standard-pullback-Πᵉ (αᵉ ,ᵉ βᵉ ,ᵉ γᵉ) iᵉ)) = βᵉ iᵉ
  pr2ᵉ (pr2ᵉ (map-standard-pullback-Πᵉ (αᵉ ,ᵉ βᵉ ,ᵉ γᵉ) iᵉ)) = htpy-eqᵉ γᵉ iᵉ

  map-inv-standard-pullback-Πᵉ :
    ((iᵉ : Iᵉ) → standard-pullbackᵉ (fᵉ iᵉ) (gᵉ iᵉ)) →
    standard-pullbackᵉ (map-Πᵉ fᵉ) (map-Πᵉ gᵉ)
  pr1ᵉ (map-inv-standard-pullback-Πᵉ hᵉ) iᵉ = pr1ᵉ (hᵉ iᵉ)
  pr1ᵉ (pr2ᵉ (map-inv-standard-pullback-Πᵉ hᵉ)) iᵉ = pr1ᵉ (pr2ᵉ (hᵉ iᵉ))
  pr2ᵉ (pr2ᵉ (map-inv-standard-pullback-Πᵉ hᵉ)) = eq-htpyᵉ (λ iᵉ → pr2ᵉ (pr2ᵉ (hᵉ iᵉ)))

  abstract
    is-section-map-inv-standard-pullback-Πᵉ :
      is-sectionᵉ (map-standard-pullback-Πᵉ) (map-inv-standard-pullback-Πᵉ)
    is-section-map-inv-standard-pullback-Πᵉ hᵉ =
      eq-htpyᵉ
        ( λ iᵉ →
          map-extensionality-standard-pullbackᵉ (fᵉ iᵉ) (gᵉ iᵉ) reflᵉ reflᵉ
            ( invᵉ
              ( ( right-unitᵉ) ∙ᵉ
                ( htpy-eqᵉ (is-section-eq-htpyᵉ (λ iᵉ → pr2ᵉ (pr2ᵉ (hᵉ iᵉ)))) iᵉ))))

  abstract
    is-retraction-map-inv-standard-pullback-Πᵉ :
      is-retractionᵉ (map-standard-pullback-Πᵉ) (map-inv-standard-pullback-Πᵉ)
    is-retraction-map-inv-standard-pullback-Πᵉ (αᵉ ,ᵉ βᵉ ,ᵉ γᵉ) =
      map-extensionality-standard-pullbackᵉ
        ( map-Πᵉ fᵉ)
        ( map-Πᵉ gᵉ)
        ( reflᵉ)
        ( reflᵉ)
        ( invᵉ (right-unitᵉ ∙ᵉ is-retraction-eq-htpyᵉ γᵉ))

  abstract
    is-equiv-map-standard-pullback-Πᵉ :
      is-equivᵉ (map-standard-pullback-Πᵉ)
    is-equiv-map-standard-pullback-Πᵉ =
      is-equiv-is-invertibleᵉ
        ( map-inv-standard-pullback-Πᵉ)
        ( is-section-map-inv-standard-pullback-Πᵉ)
        ( is-retraction-map-inv-standard-pullback-Πᵉ)

  compute-standard-pullback-Πᵉ :
    ( standard-pullbackᵉ (map-Πᵉ fᵉ) (map-Πᵉ gᵉ)) ≃ᵉ
    ( (iᵉ : Iᵉ) → standard-pullbackᵉ (fᵉ iᵉ) (gᵉ iᵉ))
  compute-standard-pullback-Πᵉ =
    map-standard-pullback-Πᵉ ,ᵉ is-equiv-map-standard-pullback-Πᵉ
```

### A dependent product of gap maps computes as the gap map of the dependent product

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
  {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ} {Xᵉ : Iᵉ → UUᵉ l4ᵉ} {Cᵉ : Iᵉ → UUᵉ l5ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Xᵉ iᵉ) (gᵉ : (iᵉ : Iᵉ) → Bᵉ iᵉ → Xᵉ iᵉ)
  (cᵉ : (iᵉ : Iᵉ) → coneᵉ (fᵉ iᵉ) (gᵉ iᵉ) (Cᵉ iᵉ))
  where

  triangle-map-standard-pullback-Πᵉ :
    map-Πᵉ (λ iᵉ → gapᵉ (fᵉ iᵉ) (gᵉ iᵉ) (cᵉ iᵉ)) ~ᵉ
    map-standard-pullback-Πᵉ fᵉ gᵉ ∘ᵉ gapᵉ (map-Πᵉ fᵉ) (map-Πᵉ gᵉ) (cone-Πᵉ fᵉ gᵉ cᵉ)
  triangle-map-standard-pullback-Πᵉ hᵉ =
    eq-htpyᵉ
      ( λ iᵉ →
        map-extensionality-standard-pullbackᵉ
          ( fᵉ iᵉ)
          ( gᵉ iᵉ)
          ( reflᵉ)
          ( reflᵉ)
          ( htpy-eqᵉ (is-section-eq-htpyᵉ _) iᵉ ∙ᵉ invᵉ right-unitᵉ))
```

### Dependent products of pullbacks are pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
  {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ} {Xᵉ : Iᵉ → UUᵉ l4ᵉ} {Cᵉ : Iᵉ → UUᵉ l5ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Xᵉ iᵉ) (gᵉ : (iᵉ : Iᵉ) → Bᵉ iᵉ → Xᵉ iᵉ)
  (cᵉ : (iᵉ : Iᵉ) → coneᵉ (fᵉ iᵉ) (gᵉ iᵉ) (Cᵉ iᵉ))
  where

  abstract
    is-pullback-Πᵉ :
      ((iᵉ : Iᵉ) → is-pullbackᵉ (fᵉ iᵉ) (gᵉ iᵉ) (cᵉ iᵉ)) →
      is-pullbackᵉ (map-Πᵉ fᵉ) (map-Πᵉ gᵉ) (cone-Πᵉ fᵉ gᵉ cᵉ)
    is-pullback-Πᵉ is-pb-cᵉ =
      is-equiv-top-map-triangleᵉ
        ( map-Πᵉ (λ iᵉ → gapᵉ (fᵉ iᵉ) (gᵉ iᵉ) (cᵉ iᵉ)))
        ( map-standard-pullback-Πᵉ fᵉ gᵉ)
        ( gapᵉ (map-Πᵉ fᵉ) (map-Πᵉ gᵉ) (cone-Πᵉ fᵉ gᵉ cᵉ))
        ( triangle-map-standard-pullback-Πᵉ fᵉ gᵉ cᵉ)
        ( is-equiv-map-standard-pullback-Πᵉ fᵉ gᵉ)
        ( is-equiv-map-Π-is-fiberwise-equivᵉ is-pb-cᵉ)
```

### Cones satisfying the universal property of pullbacks are closed under dependent products

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
  {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ} {Xᵉ : Iᵉ → UUᵉ l4ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Xᵉ iᵉ) (gᵉ : (iᵉ : Iᵉ) → Bᵉ iᵉ → Xᵉ iᵉ)
  {Cᵉ : Iᵉ → UUᵉ l5ᵉ} (cᵉ : (iᵉ : Iᵉ) → coneᵉ (fᵉ iᵉ) (gᵉ iᵉ) (Cᵉ iᵉ))
  where

  universal-property-pullback-Πᵉ :
    ((iᵉ : Iᵉ) → universal-property-pullbackᵉ (fᵉ iᵉ) (gᵉ iᵉ) (cᵉ iᵉ)) →
    universal-property-pullbackᵉ (map-Πᵉ fᵉ) (map-Πᵉ gᵉ) (cone-Πᵉ fᵉ gᵉ cᵉ)
  universal-property-pullback-Πᵉ Hᵉ =
    universal-property-pullback-is-pullbackᵉ
      ( map-Πᵉ fᵉ)
      ( map-Πᵉ gᵉ)
      ( cone-Πᵉ fᵉ gᵉ cᵉ)
      ( is-pullback-Πᵉ fᵉ gᵉ cᵉ
        ( λ iᵉ →
          is-pullback-universal-property-pullbackᵉ (fᵉ iᵉ) (gᵉ iᵉ) (cᵉ iᵉ) (Hᵉ iᵉ)))
```

## Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}