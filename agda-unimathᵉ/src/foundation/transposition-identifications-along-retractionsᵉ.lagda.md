# Transposing identifications along retractions

```agda
module foundation.transposition-identifications-along-retractionsᵉ where
```

<details><summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
```

</details>

## Idea

Considerᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ aᵉ mapᵉ `gᵉ : Bᵉ → A`ᵉ in theᵉ converseᵉ direction.ᵉ Thenᵉ
thereᵉ isᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ)

```text
  is-retractionᵉ fᵉ gᵉ ≃ᵉ ((xᵉ : Aᵉ) (yᵉ : Bᵉ) → (fᵉ xᵉ ＝ᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ gᵉ yᵉ))
```

Inᵉ otherᵉ words,ᵉ anyᵉ [retractingᵉ homotopy](foundation-core.retractions.mdᵉ)
`gᵉ ∘ᵉ fᵉ ~ᵉ id`ᵉ inducesᵉ aᵉ uniqueᵉ familyᵉ ofᵉ
{{#conceptᵉ "transposition"ᵉ Disambiguation="identificationsᵉ alongᵉ retractions"ᵉ Agda=eq-transpose-is-retractionᵉ}}
mapsᵉ

```text
  fᵉ xᵉ ＝ᵉ yᵉ → xᵉ ＝ᵉ gᵉ yᵉ
```

indexedᵉ byᵉ `xᵉ : A`ᵉ andᵉ `yᵉ : B`.ᵉ

## Definitions

### Transposing identifications along retractions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (gᵉ : Bᵉ → Aᵉ)
  where

  eq-transpose-is-retractionᵉ :
    is-retractionᵉ fᵉ gᵉ → {xᵉ : Bᵉ} {yᵉ : Aᵉ} → xᵉ ＝ᵉ fᵉ yᵉ → gᵉ xᵉ ＝ᵉ yᵉ
  eq-transpose-is-retractionᵉ Hᵉ {xᵉ} {yᵉ} pᵉ = apᵉ gᵉ pᵉ ∙ᵉ Hᵉ yᵉ

  eq-transpose-is-retraction'ᵉ :
    is-retractionᵉ fᵉ gᵉ → {xᵉ : Aᵉ} {yᵉ : Bᵉ} → fᵉ xᵉ ＝ᵉ yᵉ → xᵉ ＝ᵉ gᵉ yᵉ
  eq-transpose-is-retraction'ᵉ Hᵉ {xᵉ} reflᵉ = invᵉ (Hᵉ xᵉ)
```

## Properties

### The map that assings to each retracting homotopy a family of transposition functions of identifications is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (gᵉ : Bᵉ → Aᵉ)
  where

  is-retraction-eq-transposeᵉ :
    ({xᵉ : Bᵉ} {yᵉ : Aᵉ} → xᵉ ＝ᵉ fᵉ yᵉ → gᵉ xᵉ ＝ᵉ yᵉ) → is-retractionᵉ fᵉ gᵉ
  is-retraction-eq-transposeᵉ Hᵉ xᵉ = Hᵉ reflᵉ

  is-retraction-eq-transpose'ᵉ :
    ({xᵉ : Aᵉ} {yᵉ : Bᵉ} → fᵉ xᵉ ＝ᵉ yᵉ → xᵉ ＝ᵉ gᵉ yᵉ) → is-retractionᵉ fᵉ gᵉ
  is-retraction-eq-transpose'ᵉ Hᵉ xᵉ = invᵉ (Hᵉ reflᵉ)

  is-retraction-is-retraction-eq-transposeᵉ :
    is-retraction-eq-transposeᵉ ∘ᵉ eq-transpose-is-retractionᵉ fᵉ gᵉ ~ᵉ idᵉ
  is-retraction-is-retraction-eq-transposeᵉ Hᵉ = reflᵉ

  htpy-is-section-is-retraction-eq-transposeᵉ :
    (Hᵉ : {xᵉ : Bᵉ} {yᵉ : Aᵉ} → xᵉ ＝ᵉ fᵉ yᵉ → gᵉ xᵉ ＝ᵉ yᵉ)
    (xᵉ : Bᵉ) (yᵉ : Aᵉ) →
    eq-transpose-is-retractionᵉ fᵉ gᵉ (is-retraction-eq-transposeᵉ Hᵉ) {xᵉ} {yᵉ} ~ᵉ
    Hᵉ {xᵉ} {yᵉ}
  htpy-is-section-is-retraction-eq-transposeᵉ Hᵉ xᵉ yᵉ reflᵉ = reflᵉ

  abstract
    is-section-is-retraction-eq-transposeᵉ :
      eq-transpose-is-retractionᵉ fᵉ gᵉ ∘ᵉ is-retraction-eq-transposeᵉ ~ᵉ idᵉ
    is-section-is-retraction-eq-transposeᵉ Hᵉ =
      eq-htpy-implicitᵉ
        ( λ xᵉ →
          eq-htpy-implicitᵉ
            ( λ yᵉ → eq-htpyᵉ (htpy-is-section-is-retraction-eq-transposeᵉ Hᵉ xᵉ yᵉ)))

  is-equiv-eq-transpose-is-retractionᵉ :
    is-equivᵉ (eq-transpose-is-retractionᵉ fᵉ gᵉ)
  is-equiv-eq-transpose-is-retractionᵉ =
    is-equiv-is-invertibleᵉ
      ( is-retraction-eq-transposeᵉ)
      ( is-section-is-retraction-eq-transposeᵉ)
      ( is-retraction-is-retraction-eq-transposeᵉ)

  equiv-eq-transpose-is-retractionᵉ :
    is-retractionᵉ fᵉ gᵉ ≃ᵉ ({xᵉ : Bᵉ} {yᵉ : Aᵉ} → xᵉ ＝ᵉ fᵉ yᵉ → gᵉ xᵉ ＝ᵉ yᵉ)
  equiv-eq-transpose-is-retractionᵉ =
    ( eq-transpose-is-retractionᵉ fᵉ gᵉ ,ᵉ is-equiv-eq-transpose-is-retractionᵉ)
```