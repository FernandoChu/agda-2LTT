# Transposing identifications along sections

```agda
module foundation.transposition-identifications-along-sectionsᵉ where
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
open import foundation-core.sectionsᵉ
```

</details>

## Idea

Considerᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ aᵉ mapᵉ `gᵉ : Bᵉ → A`ᵉ in theᵉ converseᵉ direction.ᵉ Thenᵉ
thereᵉ isᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ)

```text
  is-sectionᵉ fᵉ gᵉ ≃ᵉ ((xᵉ : Aᵉ) (yᵉ : Bᵉ) → (xᵉ ＝ᵉ gᵉ yᵉ) ≃ᵉ (fᵉ xᵉ ＝ᵉ yᵉ))
```

Inᵉ otherᵉ words,ᵉ anyᵉ [sectionᵉ homotopy](foundation-core.sections.mdᵉ) `fᵉ ∘ᵉ gᵉ ~ᵉ id`ᵉ
inducesᵉ aᵉ uniqueᵉ familyᵉ ofᵉ
{{#conceptᵉ "transposition"ᵉ Disambiguation="identificationsᵉ alongᵉ sections"ᵉ Agda=eq-transpose-is-sectionᵉ}}
mapsᵉ

```text
  xᵉ ＝ᵉ gᵉ yᵉ → fᵉ xᵉ ＝ᵉ yᵉ
```

indexedᵉ byᵉ `xᵉ : A`ᵉ andᵉ `yᵉ : B`.ᵉ

### Transposing identifications along sections

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (gᵉ : Bᵉ → Aᵉ)
  where

  eq-transpose-is-sectionᵉ :
    fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ → {xᵉ : Aᵉ} {yᵉ : Bᵉ} → xᵉ ＝ᵉ gᵉ yᵉ → fᵉ xᵉ ＝ᵉ yᵉ
  eq-transpose-is-sectionᵉ Hᵉ {xᵉ} {yᵉ} pᵉ = apᵉ fᵉ pᵉ ∙ᵉ Hᵉ yᵉ

  eq-transpose-is-section'ᵉ :
    fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ → {xᵉ : Bᵉ} {yᵉ : Aᵉ} → gᵉ xᵉ ＝ᵉ yᵉ → xᵉ ＝ᵉ fᵉ yᵉ
  eq-transpose-is-section'ᵉ Hᵉ {xᵉ} reflᵉ = invᵉ (Hᵉ xᵉ)
```

## Properties

### The map that assings to each section homotopy a family of transposition functions of identifications is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (gᵉ : Bᵉ → Aᵉ)
  where

  is-section-eq-transposeᵉ :
    ({xᵉ : Aᵉ} {yᵉ : Bᵉ} → xᵉ ＝ᵉ gᵉ yᵉ → fᵉ xᵉ ＝ᵉ yᵉ) → fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ
  is-section-eq-transposeᵉ Hᵉ xᵉ = Hᵉ reflᵉ

  is-section-eq-transpose'ᵉ :
    ({xᵉ : Bᵉ} {yᵉ : Aᵉ} → gᵉ xᵉ ＝ᵉ yᵉ → xᵉ ＝ᵉ fᵉ yᵉ) → fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ
  is-section-eq-transpose'ᵉ Hᵉ xᵉ = invᵉ (Hᵉ reflᵉ)

  is-retraction-is-section-eq-transposeᵉ :
    is-section-eq-transposeᵉ ∘ᵉ eq-transpose-is-sectionᵉ fᵉ gᵉ ~ᵉ idᵉ
  is-retraction-is-section-eq-transposeᵉ Hᵉ = reflᵉ

  htpy-is-section-is-section-eq-transposeᵉ :
    (Hᵉ : {xᵉ : Aᵉ} {yᵉ : Bᵉ} → xᵉ ＝ᵉ gᵉ yᵉ → fᵉ xᵉ ＝ᵉ yᵉ) →
    (xᵉ : Aᵉ) (yᵉ : Bᵉ) →
    eq-transpose-is-sectionᵉ fᵉ gᵉ (is-section-eq-transposeᵉ Hᵉ) {xᵉ} {yᵉ} ~ᵉ Hᵉ {xᵉ} {yᵉ}
  htpy-is-section-is-section-eq-transposeᵉ Hᵉ xᵉ yᵉ reflᵉ = reflᵉ

  abstract
    is-section-is-section-eq-transposeᵉ :
      eq-transpose-is-sectionᵉ fᵉ gᵉ ∘ᵉ is-section-eq-transposeᵉ ~ᵉ idᵉ
    is-section-is-section-eq-transposeᵉ Hᵉ =
      eq-htpy-implicitᵉ
        ( λ xᵉ →
          eq-htpy-implicitᵉ
          ( λ yᵉ →
            eq-htpyᵉ (htpy-is-section-is-section-eq-transposeᵉ Hᵉ xᵉ yᵉ)))

  is-equiv-eq-transpose-is-sectionᵉ :
    is-equivᵉ (eq-transpose-is-sectionᵉ fᵉ gᵉ)
  is-equiv-eq-transpose-is-sectionᵉ =
    is-equiv-is-invertibleᵉ
      ( is-section-eq-transposeᵉ)
      ( is-section-is-section-eq-transposeᵉ)
      ( is-retraction-is-section-eq-transposeᵉ)

  equiv-eq-transpose-is-sectionᵉ :
    (fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ) ≃ᵉ ({xᵉ : Aᵉ} {yᵉ : Bᵉ} → xᵉ ＝ᵉ gᵉ yᵉ → fᵉ xᵉ ＝ᵉ yᵉ)
  equiv-eq-transpose-is-sectionᵉ =
    (eq-transpose-is-sectionᵉ fᵉ gᵉ ,ᵉ is-equiv-eq-transpose-is-sectionᵉ)
```