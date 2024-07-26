# Postcomposition of pullbacks

```agda
module foundation.postcomposition-pullbacksᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.postcomposition-functionsᵉ
open import foundation-core.pullbacksᵉ
open import foundation-core.universal-property-pullbacksᵉ
```

</details>

## Idea

Givenᵉ aᵉ [pullback](foundation-core.pullbacks.mdᵉ) squareᵉ

```text
         f'ᵉ
    Cᵉ ------->ᵉ Bᵉ
    | ⌟ᵉ        |
  g'|ᵉ          | gᵉ
    ∨ᵉ          ∨ᵉ
    Aᵉ ------->ᵉ Xᵉ
         fᵉ
```

thenᵉ theᵉ exponentiatedᵉ squareᵉ givenᵉ byᵉ
[postcomposition](foundation-core.postcomposition-functions.mdᵉ)

```text
                f'ᵉ ∘ᵉ -ᵉ
      (Tᵉ → Cᵉ) --------->ᵉ (Tᵉ → Bᵉ)
         |                  |
  g'ᵉ ∘ᵉ -ᵉ |                  | gᵉ ∘ᵉ -ᵉ
         |                  |
         ∨ᵉ                  ∨ᵉ
      (Tᵉ → Aᵉ) --------->ᵉ (Tᵉ → Xᵉ)
                fᵉ ∘ᵉ -ᵉ
```

isᵉ aᵉ pullbackᵉ squareᵉ forᵉ anyᵉ typeᵉ `T`.ᵉ

## Definitions

### Postcomposition cones

```agda
postcomp-coneᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} (Tᵉ : UUᵉ l5ᵉ)
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
  coneᵉ (postcompᵉ Tᵉ fᵉ) (postcompᵉ Tᵉ gᵉ) (Tᵉ → Cᵉ)
pr1ᵉ (postcomp-coneᵉ Tᵉ fᵉ gᵉ cᵉ) hᵉ = vertical-map-coneᵉ fᵉ gᵉ cᵉ ∘ᵉ hᵉ
pr1ᵉ (pr2ᵉ (postcomp-coneᵉ Tᵉ fᵉ gᵉ cᵉ)) hᵉ = horizontal-map-coneᵉ fᵉ gᵉ cᵉ ∘ᵉ hᵉ
pr2ᵉ (pr2ᵉ (postcomp-coneᵉ Tᵉ fᵉ gᵉ cᵉ)) hᵉ = eq-htpyᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ ·rᵉ hᵉ)
```

## Properties

### The standard pullback of a postcomposition exponential computes as the type of cones

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  (Tᵉ : UUᵉ l4ᵉ)
  where

  map-standard-pullback-postcompᵉ :
    standard-pullbackᵉ (postcompᵉ Tᵉ fᵉ) (postcompᵉ Tᵉ gᵉ) → coneᵉ fᵉ gᵉ Tᵉ
  map-standard-pullback-postcompᵉ = totᵉ (λ _ → totᵉ (λ _ → htpy-eqᵉ))

  abstract
    is-equiv-map-standard-pullback-postcompᵉ :
      is-equivᵉ map-standard-pullback-postcompᵉ
    is-equiv-map-standard-pullback-postcompᵉ =
      is-equiv-tot-is-fiberwise-equivᵉ
        ( λ pᵉ → is-equiv-tot-is-fiberwise-equivᵉ (λ qᵉ → funextᵉ (fᵉ ∘ᵉ pᵉ) (gᵉ ∘ᵉ qᵉ)))

  compute-standard-pullback-postcompᵉ :
    standard-pullbackᵉ (postcompᵉ Tᵉ fᵉ) (postcompᵉ Tᵉ gᵉ) ≃ᵉ coneᵉ fᵉ gᵉ Tᵉ
  compute-standard-pullback-postcompᵉ =
    ( map-standard-pullback-postcompᵉ ,ᵉ
      is-equiv-map-standard-pullback-postcompᵉ)
```

### The precomposition action on cones computes as the gap map of a postcomposition cone

```agda
triangle-map-standard-pullback-postcompᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (Tᵉ : UUᵉ l5ᵉ) (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
  coherence-triangle-mapsᵉ
    ( cone-mapᵉ fᵉ gᵉ cᵉ {Tᵉ})
    ( map-standard-pullback-postcompᵉ fᵉ gᵉ Tᵉ)
    ( gapᵉ (postcompᵉ Tᵉ fᵉ) (postcompᵉ Tᵉ gᵉ) (postcomp-coneᵉ Tᵉ fᵉ gᵉ cᵉ))
triangle-map-standard-pullback-postcompᵉ Tᵉ fᵉ gᵉ cᵉ hᵉ =
  eq-pair-eq-fiberᵉ
    ( eq-pair-eq-fiberᵉ
      ( invᵉ (is-section-eq-htpyᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ ·rᵉ hᵉ))))
```

### Pullbacks are closed under postcomposition exponentiation

```agda
abstract
  is-pullback-postcomp-is-pullbackᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) → is-pullbackᵉ fᵉ gᵉ cᵉ →
    (Tᵉ : UUᵉ l5ᵉ) →
    is-pullbackᵉ (postcompᵉ Tᵉ fᵉ) (postcompᵉ Tᵉ gᵉ) (postcomp-coneᵉ Tᵉ fᵉ gᵉ cᵉ)
  is-pullback-postcomp-is-pullbackᵉ fᵉ gᵉ cᵉ is-pb-cᵉ Tᵉ =
    is-equiv-top-map-triangleᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ)
      ( map-standard-pullback-postcompᵉ fᵉ gᵉ Tᵉ)
      ( gapᵉ (fᵉ ∘ᵉ_) (gᵉ ∘ᵉ_) (postcomp-coneᵉ Tᵉ fᵉ gᵉ cᵉ))
      ( triangle-map-standard-pullback-postcompᵉ Tᵉ fᵉ gᵉ cᵉ)
      ( is-equiv-map-standard-pullback-postcompᵉ fᵉ gᵉ Tᵉ)
      ( universal-property-pullback-is-pullbackᵉ fᵉ gᵉ cᵉ is-pb-cᵉ Tᵉ)

abstract
  is-pullback-is-pullback-postcompᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
    ( {l5ᵉ : Level} (Tᵉ : UUᵉ l5ᵉ) →
      is-pullbackᵉ (postcompᵉ Tᵉ fᵉ) (postcompᵉ Tᵉ gᵉ) (postcomp-coneᵉ Tᵉ fᵉ gᵉ cᵉ)) →
    is-pullbackᵉ fᵉ gᵉ cᵉ
  is-pullback-is-pullback-postcompᵉ fᵉ gᵉ cᵉ is-pb-postcompᵉ =
    is-pullback-universal-property-pullbackᵉ fᵉ gᵉ cᵉ
      ( λ Tᵉ →
        is-equiv-left-map-triangleᵉ
          ( cone-mapᵉ fᵉ gᵉ cᵉ)
          ( map-standard-pullback-postcompᵉ fᵉ gᵉ Tᵉ)
          ( gapᵉ (fᵉ ∘ᵉ_) (gᵉ ∘ᵉ_) (postcomp-coneᵉ Tᵉ fᵉ gᵉ cᵉ))
          ( triangle-map-standard-pullback-postcompᵉ Tᵉ fᵉ gᵉ cᵉ)
          ( is-pb-postcompᵉ Tᵉ)
          ( is-equiv-map-standard-pullback-postcompᵉ fᵉ gᵉ Tᵉ))
```

### Cones satisfying the universal property of pullbacks are closed under postcomposition exponentiation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (Tᵉ : UUᵉ l5ᵉ)
  where

  universal-property-pullback-postcomp-universal-property-pullbackᵉ :
    universal-property-pullbackᵉ fᵉ gᵉ cᵉ →
    universal-property-pullbackᵉ
      ( postcompᵉ Tᵉ fᵉ)
      ( postcompᵉ Tᵉ gᵉ)
      ( postcomp-coneᵉ Tᵉ fᵉ gᵉ cᵉ)
  universal-property-pullback-postcomp-universal-property-pullbackᵉ Hᵉ =
    universal-property-pullback-is-pullbackᵉ
      ( postcompᵉ Tᵉ fᵉ)
      ( postcompᵉ Tᵉ gᵉ)
      ( postcomp-coneᵉ Tᵉ fᵉ gᵉ cᵉ)
      ( is-pullback-postcomp-is-pullbackᵉ fᵉ gᵉ cᵉ
        ( is-pullback-universal-property-pullbackᵉ fᵉ gᵉ cᵉ Hᵉ)
        ( Tᵉ))
```

## Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}