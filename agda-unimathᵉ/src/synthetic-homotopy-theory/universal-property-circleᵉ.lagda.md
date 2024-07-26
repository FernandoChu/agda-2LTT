# The universal property of the circle

```agda
module synthetic-homotopy-theory.universal-property-circleᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.constant-type-familiesᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.sectionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.free-loopsᵉ
```

</details>

## Definitions

### Evaluating an ordinary function at a free loop

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (αᵉ : free-loopᵉ Xᵉ) (Yᵉ : UUᵉ l2ᵉ)
  where

  ev-free-loopᵉ : (Xᵉ → Yᵉ) → free-loopᵉ Yᵉ
  pr1ᵉ (ev-free-loopᵉ fᵉ) = fᵉ (base-free-loopᵉ αᵉ)
  pr2ᵉ (ev-free-loopᵉ fᵉ) = apᵉ fᵉ (loop-free-loopᵉ αᵉ)
```

### The universal property of the circle

```agda
module _
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (αᵉ : free-loopᵉ Xᵉ)
  where

  universal-property-circleᵉ : UUωᵉ
  universal-property-circleᵉ =
    {lᵉ : Level} (Yᵉ : UUᵉ lᵉ) → is-equivᵉ (ev-free-loopᵉ αᵉ Yᵉ)
```

### Evaluating a dependent function at a free loop

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (αᵉ : free-loopᵉ Xᵉ) (Pᵉ : Xᵉ → UUᵉ l2ᵉ)
  where

  ev-free-loop-Πᵉ : ((xᵉ : Xᵉ) → Pᵉ xᵉ) → free-dependent-loopᵉ αᵉ Pᵉ
  pr1ᵉ (ev-free-loop-Πᵉ fᵉ) = fᵉ (base-free-loopᵉ αᵉ)
  pr2ᵉ (ev-free-loop-Πᵉ fᵉ) = apdᵉ fᵉ (loop-free-loopᵉ αᵉ)
```

### The induction principle of the circle

```agda
module _
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (αᵉ : free-loopᵉ Xᵉ)
  where

  induction-principle-circleᵉ : UUωᵉ
  induction-principle-circleᵉ =
    {l2ᵉ : Level} (Pᵉ : Xᵉ → UUᵉ l2ᵉ) → sectionᵉ (ev-free-loop-Πᵉ αᵉ Pᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (αᵉ : free-loopᵉ Xᵉ)
  (Hᵉ : induction-principle-circleᵉ αᵉ) (Pᵉ : Xᵉ → UUᵉ l2ᵉ)
  (βᵉ : free-dependent-loopᵉ αᵉ Pᵉ)
  where

  function-induction-principle-circleᵉ : (xᵉ : Xᵉ) → Pᵉ xᵉ
  function-induction-principle-circleᵉ = pr1ᵉ (Hᵉ Pᵉ) βᵉ

  compute-induction-principle-circleᵉ :
    (ev-free-loop-Πᵉ αᵉ Pᵉ function-induction-principle-circleᵉ) ＝ᵉ βᵉ
  compute-induction-principle-circleᵉ = pr2ᵉ (Hᵉ Pᵉ) βᵉ
```

### The dependent universal property of the circle

```agda
module _
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (αᵉ : free-loopᵉ Xᵉ)
  where

  dependent-universal-property-circleᵉ : UUωᵉ
  dependent-universal-property-circleᵉ =
    {l2ᵉ : Level} (Pᵉ : Xᵉ → UUᵉ l2ᵉ) → is-equivᵉ (ev-free-loop-Πᵉ αᵉ Pᵉ)
```

## Properties

### The induction principle of the circle implies the dependent universal property of the circle

Toᵉ proveᵉ this,ᵉ weᵉ haveᵉ to showᵉ thatᵉ theᵉ sectionᵉ ofᵉ ev-free-loop-Πᵉ isᵉ alsoᵉ aᵉ
retraction.ᵉ Thisᵉ constructionᵉ isᵉ alsoᵉ byᵉ theᵉ inductionᵉ principleᵉ ofᵉ theᵉ circle,ᵉ
butᵉ itᵉ requiresᵉ (aᵉ minimalᵉ amountᵉ ofᵉ) preparations.ᵉ

```agda
module _
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (αᵉ : free-loopᵉ Xᵉ)
  where

  free-dependent-loop-htpyᵉ :
    {l2ᵉ : Level} {Pᵉ : Xᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ : (xᵉ : Xᵉ) → Pᵉ xᵉ} →
    ( Eq-free-dependent-loopᵉ αᵉ Pᵉ
      ( ev-free-loop-Πᵉ αᵉ Pᵉ fᵉ)
      ( ev-free-loop-Πᵉ αᵉ Pᵉ gᵉ)) →
    ( free-dependent-loopᵉ αᵉ (λ xᵉ → Idᵉ (fᵉ xᵉ) (gᵉ xᵉ)))
  pr1ᵉ (free-dependent-loop-htpyᵉ {l2ᵉ} {Pᵉ} {fᵉ} {gᵉ} (pᵉ ,ᵉ qᵉ)) = pᵉ
  pr2ᵉ (free-dependent-loop-htpyᵉ {l2ᵉ} {Pᵉ} {fᵉ} {gᵉ} (pᵉ ,ᵉ qᵉ)) =
    map-compute-dependent-identification-eq-valueᵉ fᵉ gᵉ (loop-free-loopᵉ αᵉ) pᵉ pᵉ qᵉ

  is-retraction-ind-circleᵉ :
    ( ind-circleᵉ : induction-principle-circleᵉ αᵉ)
    { l2ᵉ : Level} (Pᵉ : Xᵉ → UUᵉ l2ᵉ) →
    ( ( function-induction-principle-circleᵉ αᵉ ind-circleᵉ Pᵉ) ∘ᵉ
      ( ev-free-loop-Πᵉ αᵉ Pᵉ)) ~ᵉ
    ( idᵉ)
  is-retraction-ind-circleᵉ ind-circleᵉ Pᵉ fᵉ =
    eq-htpyᵉ
      ( function-induction-principle-circleᵉ αᵉ ind-circleᵉ
        ( eq-valueᵉ
          ( function-induction-principle-circleᵉ αᵉ ind-circleᵉ Pᵉ
            ( ev-free-loop-Πᵉ αᵉ Pᵉ fᵉ))
          ( fᵉ))
        ( free-dependent-loop-htpyᵉ
          ( Eq-free-dependent-loop-eqᵉ αᵉ Pᵉ _ _
            ( compute-induction-principle-circleᵉ αᵉ ind-circleᵉ Pᵉ
              ( ev-free-loop-Πᵉ αᵉ Pᵉ fᵉ)))))

  abstract
    dependent-universal-property-induction-principle-circleᵉ :
      induction-principle-circleᵉ αᵉ →
      dependent-universal-property-circleᵉ αᵉ
    dependent-universal-property-induction-principle-circleᵉ ind-circleᵉ Pᵉ =
      is-equiv-is-invertibleᵉ
        ( function-induction-principle-circleᵉ αᵉ ind-circleᵉ Pᵉ)
        ( compute-induction-principle-circleᵉ αᵉ ind-circleᵉ Pᵉ)
        ( is-retraction-ind-circleᵉ ind-circleᵉ Pᵉ)
```

### Uniqueness of the maps obtained from the universal property of the circle

```agda
module _
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (αᵉ : free-loopᵉ Xᵉ)
  where

  abstract
    uniqueness-universal-property-circleᵉ :
      universal-property-circleᵉ αᵉ →
      {l2ᵉ : Level} (Yᵉ : UUᵉ l2ᵉ) (α'ᵉ : free-loopᵉ Yᵉ) →
      is-contrᵉ (Σᵉ (Xᵉ → Yᵉ) (λ fᵉ → Eq-free-loopᵉ (ev-free-loopᵉ αᵉ Yᵉ fᵉ) α'ᵉ))
    uniqueness-universal-property-circleᵉ up-circleᵉ Yᵉ α'ᵉ =
      is-contr-is-equiv'ᵉ
        ( fiberᵉ (ev-free-loopᵉ αᵉ Yᵉ) α'ᵉ)
        ( totᵉ (λ fᵉ → Eq-eq-free-loopᵉ (ev-free-loopᵉ αᵉ Yᵉ fᵉ) α'ᵉ))
        ( is-equiv-tot-is-fiberwise-equivᵉ
          ( λ fᵉ → is-equiv-Eq-eq-free-loopᵉ (ev-free-loopᵉ αᵉ Yᵉ fᵉ) α'ᵉ))
        ( is-contr-map-is-equivᵉ (up-circleᵉ Yᵉ) α'ᵉ)
```

### Uniqueness of the dependent functions obtained from the dependent universal property of the circle

```agda
module _
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (αᵉ : free-loopᵉ Xᵉ)
  where

  uniqueness-dependent-universal-property-circleᵉ :
    dependent-universal-property-circleᵉ αᵉ →
    {l2ᵉ : Level} {Pᵉ : Xᵉ → UUᵉ l2ᵉ} (kᵉ : free-dependent-loopᵉ αᵉ Pᵉ) →
    is-contrᵉ
      ( Σᵉ ( (xᵉ : Xᵉ) → Pᵉ xᵉ)
          ( λ hᵉ → Eq-free-dependent-loopᵉ αᵉ Pᵉ (ev-free-loop-Πᵉ αᵉ Pᵉ hᵉ) kᵉ))
  uniqueness-dependent-universal-property-circleᵉ dup-circleᵉ {l2ᵉ} {Pᵉ} kᵉ =
    is-contr-is-equiv'ᵉ
      ( fiberᵉ (ev-free-loop-Πᵉ αᵉ Pᵉ) kᵉ)
      ( totᵉ (λ hᵉ → Eq-free-dependent-loop-eqᵉ αᵉ Pᵉ (ev-free-loop-Πᵉ αᵉ Pᵉ hᵉ) kᵉ))
      ( is-equiv-tot-is-fiberwise-equivᵉ
        (λ hᵉ → is-equiv-Eq-free-dependent-loop-eqᵉ αᵉ Pᵉ (ev-free-loop-Πᵉ αᵉ Pᵉ hᵉ) kᵉ))
      ( is-contr-map-is-equivᵉ (dup-circleᵉ Pᵉ) kᵉ)
```

### The dependent universal property of the circle implies the universal property of the circle

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (αᵉ : free-loopᵉ Xᵉ) (Yᵉ : UUᵉ l2ᵉ)
  where

  triangle-comparison-free-loopᵉ :
    map-compute-free-dependent-loop-constant-type-familyᵉ αᵉ Yᵉ ∘ᵉ
    ev-free-loopᵉ αᵉ Yᵉ ~ᵉ
    ev-free-loop-Πᵉ αᵉ (λ _ → Yᵉ)
  triangle-comparison-free-loopᵉ fᵉ =
    eq-Eq-free-dependent-loopᵉ αᵉ
      ( λ xᵉ → Yᵉ)
      ( map-compute-free-dependent-loop-constant-type-familyᵉ αᵉ Yᵉ
        ( ev-free-loopᵉ αᵉ Yᵉ fᵉ))
      ( ev-free-loop-Πᵉ αᵉ (λ xᵉ → Yᵉ) fᵉ)
      ( reflᵉ ,ᵉ
        right-unitᵉ ∙ᵉ (invᵉ (apd-constant-type-familyᵉ fᵉ (loop-free-loopᵉ αᵉ))))

module _
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (αᵉ : free-loopᵉ Xᵉ)
  where

  abstract
    universal-property-dependent-universal-property-circleᵉ :
      dependent-universal-property-circleᵉ αᵉ →
      universal-property-circleᵉ αᵉ
    universal-property-dependent-universal-property-circleᵉ dup-circleᵉ Yᵉ =
      is-equiv-top-map-triangleᵉ
        ( ev-free-loop-Πᵉ αᵉ (λ xᵉ → Yᵉ))
        ( map-compute-free-dependent-loop-constant-type-familyᵉ αᵉ Yᵉ)
        ( ev-free-loopᵉ αᵉ Yᵉ)
        ( inv-htpyᵉ (triangle-comparison-free-loopᵉ αᵉ Yᵉ))
        ( is-equiv-map-equivᵉ
          ( compute-free-dependent-loop-constant-type-familyᵉ αᵉ Yᵉ))
        ( dup-circleᵉ (λ xᵉ → Yᵉ))
```

### The induction principle of the circle implies the universal property of the circle

```agda
module _
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (αᵉ : free-loopᵉ Xᵉ)
  where

  abstract
    universal-property-induction-principle-circleᵉ :
      induction-principle-circleᵉ αᵉ →
      universal-property-circleᵉ αᵉ
    universal-property-induction-principle-circleᵉ Xᵉ =
      universal-property-dependent-universal-property-circleᵉ αᵉ
        ( dependent-universal-property-induction-principle-circleᵉ αᵉ Xᵉ)
```

### The dependent universal property of the circle with respect to propositions

```agda
abstract
  is-connected-circle'ᵉ :
    { l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ) →
    ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ)
    ( Pᵉ : Xᵉ → UUᵉ l2ᵉ) (is-prop-Pᵉ : (xᵉ : Xᵉ) → is-propᵉ (Pᵉ xᵉ)) →
    Pᵉ (base-free-loopᵉ lᵉ) → (xᵉ : Xᵉ) → Pᵉ xᵉ
  is-connected-circle'ᵉ lᵉ dup-circleᵉ Pᵉ is-prop-Pᵉ pᵉ =
    map-inv-is-equivᵉ
      ( dup-circleᵉ Pᵉ)
      ( pairᵉ pᵉ (centerᵉ (is-prop-Pᵉ _ (trᵉ Pᵉ (loop-free-loopᵉ lᵉ) pᵉ) pᵉ)))
```