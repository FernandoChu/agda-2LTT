# Precomposition of functions

```agda
module foundation.precomposition-functionsᵉ where

open import foundation-core.precomposition-functionsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.precomposition-dependent-functionsᵉ
open import foundation.sectionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
```

</details>

## Idea

Givenᵉ aᵉ functionᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ aᵉ typeᵉ `X`,ᵉ theᵉ **precompositionᵉ function**ᵉ byᵉ
`f`ᵉ

```text
  -ᵉ ∘ᵉ fᵉ : (Bᵉ → Xᵉ) → (Aᵉ → Xᵉ)
```

isᵉ definedᵉ byᵉ `λᵉ hᵉ xᵉ → hᵉ (fᵉ x)`.ᵉ

Theᵉ precompositionᵉ functionᵉ wasᵉ alreadyᵉ definedᵉ in
[`foundation-core.precomposition-functions`](foundation-core.precomposition-functions.md).ᵉ
Inᵉ thisᵉ fileᵉ weᵉ deriveᵉ someᵉ furtherᵉ propertiesᵉ ofᵉ theᵉ precompositionᵉ function.ᵉ

## Properties

### Precomposition preserves homotopies

```agda
htpy-precompᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  {fᵉ gᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) (Cᵉ : UUᵉ l3ᵉ) →
  precompᵉ fᵉ Cᵉ ~ᵉ precompᵉ gᵉ Cᵉ
htpy-precompᵉ Hᵉ Cᵉ hᵉ = eq-htpyᵉ (hᵉ ·lᵉ Hᵉ)

compute-htpy-precomp-refl-htpyᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Cᵉ : UUᵉ l3ᵉ) →
  htpy-precompᵉ (refl-htpy'ᵉ fᵉ) Cᵉ ~ᵉ refl-htpyᵉ
compute-htpy-precomp-refl-htpyᵉ fᵉ Cᵉ hᵉ = eq-htpy-refl-htpyᵉ (hᵉ ∘ᵉ fᵉ)
```

### Precomposition preserves concatenation of homotopies

```agda
compute-concat-htpy-precompᵉ :
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  { fᵉ gᵉ hᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) (Cᵉ : UUᵉ l3ᵉ) →
  htpy-precompᵉ (Hᵉ ∙hᵉ Kᵉ) Cᵉ ~ᵉ htpy-precompᵉ Hᵉ Cᵉ ∙hᵉ htpy-precompᵉ Kᵉ Cᵉ
compute-concat-htpy-precompᵉ Hᵉ Kᵉ Cᵉ kᵉ =
  ( apᵉ
    ( eq-htpyᵉ)
    ( eq-htpyᵉ (distributive-left-whisker-comp-concatᵉ kᵉ Hᵉ Kᵉ))) ∙ᵉ
  ( eq-htpy-concat-htpyᵉ (kᵉ ·lᵉ Hᵉ) (kᵉ ·lᵉ Kᵉ))
```

### If precomposition `- ∘ f : (Y → X) → (X → X)` has a section, then `f` has a retraction

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ)
  where

  retraction-section-precomp-domainᵉ : sectionᵉ (precompᵉ fᵉ Xᵉ) → retractionᵉ fᵉ
  pr1ᵉ (retraction-section-precomp-domainᵉ sᵉ) =
    map-sectionᵉ (precompᵉ fᵉ Xᵉ) sᵉ idᵉ
  pr2ᵉ (retraction-section-precomp-domainᵉ sᵉ) =
    htpy-eqᵉ (is-section-map-sectionᵉ (precompᵉ fᵉ Xᵉ) sᵉ idᵉ)
```

### Equivalences induce an equivalence from the type of homotopies between two maps to the type of homotopies between their precomposites

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  equiv-htpy-precomp-htpyᵉ :
    (fᵉ gᵉ : Bᵉ → Cᵉ) (eᵉ : Aᵉ ≃ᵉ Bᵉ) → (fᵉ ~ᵉ gᵉ) ≃ᵉ (fᵉ ∘ᵉ map-equivᵉ eᵉ ~ᵉ gᵉ ∘ᵉ map-equivᵉ eᵉ)
  equiv-htpy-precomp-htpyᵉ fᵉ gᵉ eᵉ =
    equiv-htpy-precomp-htpy-Πᵉ fᵉ gᵉ eᵉ
```

### Computations of the fibers of `precomp`

Theᵉ fiberᵉ ofᵉ `-ᵉ ∘ᵉ fᵉ : (Bᵉ → Xᵉ) → (Aᵉ → X)`ᵉ atᵉ `gᵉ ∘ᵉ fᵉ : Bᵉ → X`ᵉ isᵉ equivalentᵉ to theᵉ
typeᵉ ofᵉ mapsᵉ `hᵉ : Bᵉ → X`ᵉ equippedᵉ with aᵉ homotopyᵉ witnessingᵉ thatᵉ theᵉ squareᵉ

```text
        fᵉ
    Aᵉ ----->ᵉ Bᵉ
    |        |
  fᵉ |        | hᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Xᵉ
        gᵉ
```

commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Xᵉ : UUᵉ l3ᵉ)
  where

  compute-coherence-triangle-fiber-precomp'ᵉ :
    (gᵉ : Aᵉ → Xᵉ) →
    fiberᵉ (precompᵉ fᵉ Xᵉ) gᵉ ≃ᵉ Σᵉ (Bᵉ → Xᵉ) (λ hᵉ → coherence-triangle-maps'ᵉ gᵉ hᵉ fᵉ)
  compute-coherence-triangle-fiber-precomp'ᵉ gᵉ = equiv-totᵉ (λ _ → equiv-funextᵉ)

  compute-coherence-triangle-fiber-precompᵉ :
    (gᵉ : Aᵉ → Xᵉ) →
    fiberᵉ (precompᵉ fᵉ Xᵉ) gᵉ ≃ᵉ Σᵉ (Bᵉ → Xᵉ) (λ hᵉ → coherence-triangle-mapsᵉ gᵉ hᵉ fᵉ)
  compute-coherence-triangle-fiber-precompᵉ gᵉ =
    equiv-totᵉ (λ _ → equiv-funextᵉ) ∘eᵉ equiv-fiberᵉ (precompᵉ fᵉ Xᵉ) gᵉ

  compute-fiber-precompᵉ :
    (gᵉ : Bᵉ → Xᵉ) →
    fiberᵉ (precompᵉ fᵉ Xᵉ) (gᵉ ∘ᵉ fᵉ) ≃ᵉ
    Σᵉ (Bᵉ → Xᵉ) (λ hᵉ → coherence-square-mapsᵉ fᵉ fᵉ hᵉ gᵉ)
  compute-fiber-precompᵉ gᵉ = compute-coherence-triangle-fiber-precompᵉ (gᵉ ∘ᵉ fᵉ)

  compute-total-fiber-precompᵉ :
    Σᵉ (Bᵉ → Xᵉ) (λ gᵉ → fiberᵉ (precompᵉ fᵉ Xᵉ) (gᵉ ∘ᵉ fᵉ)) ≃ᵉ
    Σᵉ (Bᵉ → Xᵉ) (λ uᵉ → Σᵉ (Bᵉ → Xᵉ) (λ vᵉ → uᵉ ∘ᵉ fᵉ ~ᵉ vᵉ ∘ᵉ fᵉ))
  compute-total-fiber-precompᵉ = equiv-totᵉ compute-fiber-precompᵉ

  diagonal-into-fibers-precompᵉ :
    (Bᵉ → Xᵉ) → Σᵉ (Bᵉ → Xᵉ) (λ gᵉ → fiberᵉ (precompᵉ fᵉ Xᵉ) (gᵉ ∘ᵉ fᵉ))
  diagonal-into-fibers-precompᵉ = map-section-familyᵉ (λ gᵉ → gᵉ ,ᵉ reflᵉ)
```

### The action on identifications of precomposition by a map

Considerᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ twoᵉ functionsᵉ `gᵉ hᵉ : Bᵉ → C`.ᵉ Thenᵉ theᵉ
[actionᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ)
ofᵉ `precompᵉ fᵉ C`ᵉ fitsᵉ in aᵉ
[commutingᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ)

```text
                     apᵉ (precompᵉ fᵉ Cᵉ)
       (gᵉ = hᵉ) -------------------------->ᵉ (gᵉ ∘ᵉ fᵉ = hᵉ ∘ᵉ fᵉ)
          |                                       |
  htpy-eqᵉ |                                       | htpy-eqᵉ
          ∨ᵉ                                       ∨ᵉ
       (gᵉ ~ᵉ hᵉ) -------------------------->ᵉ (gᵉ ∘ᵉ fᵉ ~ᵉ hᵉ ∘ᵉ f).ᵉ
                precompᵉ fᵉ (eq-valueᵉ gᵉ hᵉ)
```

Similarly,ᵉ theᵉ actionᵉ onᵉ identificationsᵉ ofᵉ `precompᵉ fᵉ C`ᵉ alsoᵉ fitsᵉ in aᵉ
commutingᵉ squareᵉ

```text
                precompᵉ fᵉ (eq-valueᵉ gᵉ hᵉ)
       (gᵉ ~ᵉ hᵉ) -------------------------->ᵉ (gᵉ ∘ᵉ fᵉ ~ᵉ hᵉ ∘ᵉ fᵉ)
          |                                       |
  eq-htpyᵉ |                                       | eq-htpyᵉ
          ∨ᵉ                                       ∨ᵉ
       (gᵉ = hᵉ) -------------------------->ᵉ (gᵉ ∘ᵉ fᵉ = hᵉ ∘ᵉ f).ᵉ
                     apᵉ (precompᵉ fᵉ Cᵉ)
```

commutes.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Bᵉ) {gᵉ hᵉ : Bᵉ → Cᵉ}
  where

  compute-htpy-eq-ap-precompᵉ :
    coherence-square-mapsᵉ
      ( apᵉ (precompᵉ fᵉ Cᵉ))
      ( htpy-eqᵉ)
      ( htpy-eqᵉ)
      ( precomp-Πᵉ fᵉ (eq-valueᵉ gᵉ hᵉ))
  compute-htpy-eq-ap-precompᵉ =
    compute-htpy-eq-ap-precomp-Πᵉ fᵉ

  compute-eq-htpy-ap-precompᵉ :
    coherence-square-mapsᵉ
      ( precomp-Πᵉ fᵉ (eq-valueᵉ gᵉ hᵉ))
      ( eq-htpyᵉ)
      ( eq-htpyᵉ)
      ( apᵉ (precompᵉ fᵉ Cᵉ))
  compute-eq-htpy-ap-precompᵉ =
    vertical-inv-equiv-coherence-square-mapsᵉ
      ( apᵉ (precompᵉ fᵉ Cᵉ))
      ( equiv-funextᵉ)
      ( equiv-funextᵉ)
      ( precomp-Πᵉ fᵉ (eq-valueᵉ gᵉ hᵉ))
      ( compute-htpy-eq-ap-precompᵉ)
```