# Precomposition of functions into subuniverses

```agda
module foundation.precomposition-functions-into-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.precomposition-functionsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Theorem

### A map between structured types is an equivalence if precomposition of functions into structured types by that map is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (αᵉ : Level → Level) (Pᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ (αᵉ lᵉ))
  (Aᵉ : Σᵉ (UUᵉ l1ᵉ) (Pᵉ {l1ᵉ})) (Bᵉ : Σᵉ (UUᵉ l2ᵉ) (Pᵉ {l2ᵉ})) (fᵉ : pr1ᵉ Aᵉ → pr1ᵉ Bᵉ)
  where

  universal-property-equiv-structured-typeᵉ : UUωᵉ
  universal-property-equiv-structured-typeᵉ =
    {lᵉ : Level} (Cᵉ : Σᵉ (UUᵉ lᵉ) (Pᵉ {lᵉ})) → is-equivᵉ (precompᵉ fᵉ (pr1ᵉ Cᵉ))

  map-inv-is-equiv-precomp-structured-typeᵉ :
    universal-property-equiv-structured-typeᵉ → pr1ᵉ Bᵉ → pr1ᵉ Aᵉ
  map-inv-is-equiv-precomp-structured-typeᵉ Hᵉ =
    pr1ᵉ (centerᵉ (is-contr-map-is-equivᵉ (Hᵉ Aᵉ) idᵉ))

  is-section-map-inv-is-equiv-precomp-structured-typeᵉ :
    (Hᵉ : universal-property-equiv-structured-typeᵉ) →
    is-sectionᵉ fᵉ (map-inv-is-equiv-precomp-structured-typeᵉ Hᵉ)
  is-section-map-inv-is-equiv-precomp-structured-typeᵉ Hᵉ =
    htpy-eqᵉ
      ( apᵉ
        ( pr1ᵉ)
        ( eq-is-contr'ᵉ
          ( is-contr-map-is-equivᵉ (Hᵉ Bᵉ) fᵉ)
          ( ( fᵉ ∘ᵉ (pr1ᵉ (centerᵉ (is-contr-map-is-equivᵉ (Hᵉ Aᵉ) idᵉ)))) ,ᵉ
            ( apᵉ
              ( λ (gᵉ : pr1ᵉ Aᵉ → pr1ᵉ Aᵉ) → fᵉ ∘ᵉ gᵉ)
              ( pr2ᵉ (centerᵉ (is-contr-map-is-equivᵉ (Hᵉ Aᵉ) idᵉ)))))
          ( idᵉ ,ᵉ reflᵉ)))

  is-retraction-map-inv-is-equiv-precomp-structured-typeᵉ :
    (Hᵉ : universal-property-equiv-structured-typeᵉ) →
    is-retractionᵉ fᵉ (map-inv-is-equiv-precomp-structured-typeᵉ Hᵉ)
  is-retraction-map-inv-is-equiv-precomp-structured-typeᵉ Hᵉ =
    htpy-eqᵉ (pr2ᵉ (centerᵉ (is-contr-map-is-equivᵉ (Hᵉ Aᵉ) idᵉ)))

  abstract
    is-equiv-is-equiv-precomp-structured-typeᵉ :
      universal-property-equiv-structured-typeᵉ → is-equivᵉ fᵉ
    is-equiv-is-equiv-precomp-structured-typeᵉ Hᵉ =
      is-equiv-is-invertibleᵉ
        ( map-inv-is-equiv-precomp-structured-typeᵉ Hᵉ)
        ( is-section-map-inv-is-equiv-precomp-structured-typeᵉ Hᵉ)
        ( is-retraction-map-inv-is-equiv-precomp-structured-typeᵉ Hᵉ)
```

## Corollaries

### A map between propositions is an equivalence if precomposition of functions into propositions by that map is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ) (fᵉ : type-Propᵉ Pᵉ → type-Propᵉ Qᵉ)
  where

  universal-property-equiv-Propᵉ : UUωᵉ
  universal-property-equiv-Propᵉ =
    {lᵉ : Level} (Rᵉ : Propᵉ lᵉ) → is-equivᵉ (precompᵉ fᵉ (type-Propᵉ Rᵉ))

  is-equiv-is-equiv-precomp-Propᵉ :
    universal-property-equiv-Propᵉ → is-equivᵉ fᵉ
  is-equiv-is-equiv-precomp-Propᵉ =
    is-equiv-is-equiv-precomp-structured-typeᵉ (λ lᵉ → lᵉ) is-propᵉ Pᵉ Qᵉ fᵉ
```

### A map between sets is an equivalence if precomposition of functions into sets by that map is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ) (Bᵉ : Setᵉ l2ᵉ) (fᵉ : type-Setᵉ Aᵉ → type-Setᵉ Bᵉ)
  where

  universal-property-equiv-Setᵉ : UUωᵉ
  universal-property-equiv-Setᵉ =
    {lᵉ : Level} (Cᵉ : Setᵉ lᵉ) → is-equivᵉ (precompᵉ fᵉ (type-Setᵉ Cᵉ))

  is-equiv-is-equiv-precomp-Setᵉ :
    universal-property-equiv-Setᵉ → is-equivᵉ fᵉ
  is-equiv-is-equiv-precomp-Setᵉ =
    is-equiv-is-equiv-precomp-structured-typeᵉ (λ lᵉ → lᵉ) is-setᵉ Aᵉ Bᵉ fᵉ
```

### A map between truncated types is an equivalence if precomposition of functions into truncated types by that map is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ)
  (Aᵉ : Truncated-Typeᵉ l1ᵉ kᵉ) (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ)
  (fᵉ : type-Truncated-Typeᵉ Aᵉ → type-Truncated-Typeᵉ Bᵉ)
  where

  universal-property-equiv-Truncated-Typeᵉ : UUωᵉ
  universal-property-equiv-Truncated-Typeᵉ =
    {lᵉ : Level} (Cᵉ : Truncated-Typeᵉ lᵉ kᵉ) →
    is-equivᵉ (precompᵉ fᵉ (type-Truncated-Typeᵉ Cᵉ))

  is-equiv-is-equiv-precomp-Truncated-Typeᵉ :
    universal-property-equiv-Truncated-Typeᵉ → is-equivᵉ fᵉ
  is-equiv-is-equiv-precomp-Truncated-Typeᵉ =
    is-equiv-is-equiv-precomp-structured-typeᵉ (λ lᵉ → lᵉ) (is-truncᵉ kᵉ) Aᵉ Bᵉ fᵉ
```