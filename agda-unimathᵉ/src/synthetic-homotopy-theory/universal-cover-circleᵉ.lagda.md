# The universal cover of the circle

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module synthetic-homotopy-theory.universal-cover-circleᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.nonzero-integersᵉ
open import elementary-number-theory.universal-property-integersᵉ

open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.precomposition-dependent-functionsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.setsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.descent-circleᵉ
open import synthetic-homotopy-theory.free-loopsᵉ
open import synthetic-homotopy-theory.loop-spacesᵉ
open import synthetic-homotopy-theory.universal-property-circleᵉ
```

</details>

### 12.2 The universal cover of the circle

Weᵉ showᵉ thatᵉ ifᵉ aᵉ typeᵉ with aᵉ freeᵉ loopᵉ satisfiesᵉ theᵉ inductionᵉ principleᵉ ofᵉ theᵉ
circleᵉ with respectᵉ to anyᵉ universeᵉ level,ᵉ thenᵉ itᵉ satisfiesᵉ theᵉ inductionᵉ
principleᵉ with respectᵉ to theᵉ zerothᵉ universeᵉ level.ᵉ

```agda
functor-free-dependent-loopᵉ :
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ)
  { Pᵉ : Xᵉ → UUᵉ l2ᵉ} {Qᵉ : Xᵉ → UUᵉ l3ᵉ} (fᵉ : (xᵉ : Xᵉ) → Pᵉ xᵉ → Qᵉ xᵉ) →
  free-dependent-loopᵉ lᵉ Pᵉ → free-dependent-loopᵉ lᵉ Qᵉ
functor-free-dependent-loopᵉ lᵉ {Pᵉ} {Qᵉ} fᵉ =
  map-Σᵉ
    ( λ qᵉ → dependent-identificationᵉ Qᵉ (loop-free-loopᵉ lᵉ) qᵉ qᵉ)
    ( fᵉ (base-free-loopᵉ lᵉ))
    ( λ pᵉ αᵉ →
      invᵉ (preserves-trᵉ fᵉ (loop-free-loopᵉ lᵉ) pᵉ) ∙ᵉ
      ( apᵉ (fᵉ (base-free-loopᵉ lᵉ)) αᵉ))

coherence-square-functor-free-dependent-loopᵉ :
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Pᵉ : Xᵉ → UUᵉ l2ᵉ} {Qᵉ : Xᵉ → UUᵉ l3ᵉ}
  ( fᵉ : (xᵉ : Xᵉ) → Pᵉ xᵉ → Qᵉ xᵉ) {xᵉ yᵉ : Xᵉ} (αᵉ : Idᵉ xᵉ yᵉ)
  ( hᵉ : (xᵉ : Xᵉ) → Pᵉ xᵉ) →
  Idᵉ
    ( invᵉ ( preserves-trᵉ fᵉ αᵉ (hᵉ xᵉ)) ∙ᵉ
      ( apᵉ (fᵉ yᵉ) (apdᵉ hᵉ αᵉ)))
    ( apdᵉ (map-Πᵉ fᵉ hᵉ) αᵉ)
coherence-square-functor-free-dependent-loopᵉ fᵉ reflᵉ hᵉ = reflᵉ

square-functor-free-dependent-loopᵉ :
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ)
  { Pᵉ : Xᵉ → UUᵉ l2ᵉ} {Qᵉ : Xᵉ → UUᵉ l3ᵉ} (fᵉ : (xᵉ : Xᵉ) → Pᵉ xᵉ → Qᵉ xᵉ) →
  ( (functor-free-dependent-loopᵉ lᵉ fᵉ) ∘ᵉ (ev-free-loop-Πᵉ lᵉ Pᵉ)) ~ᵉ
  ( (ev-free-loop-Πᵉ lᵉ Qᵉ) ∘ᵉ (map-Πᵉ fᵉ))
square-functor-free-dependent-loopᵉ (pairᵉ xᵉ lᵉ) {Pᵉ} {Qᵉ} fᵉ hᵉ =
  eq-Eq-free-dependent-loopᵉ (pairᵉ xᵉ lᵉ) Qᵉ
    ( functor-free-dependent-loopᵉ (pairᵉ xᵉ lᵉ) fᵉ
      ( ev-free-loop-Πᵉ (pairᵉ xᵉ lᵉ) Pᵉ hᵉ))
    ( ev-free-loop-Πᵉ (pairᵉ xᵉ lᵉ) Qᵉ (map-Πᵉ fᵉ hᵉ))
    ( pairᵉ reflᵉ
      ( right-unitᵉ ∙ᵉ (coherence-square-functor-free-dependent-loopᵉ fᵉ lᵉ hᵉ)))

abstract
  is-equiv-functor-free-dependent-loop-is-fiberwise-equivᵉ :
    { l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ)
    { Pᵉ : Xᵉ → UUᵉ l2ᵉ} {Qᵉ : Xᵉ → UUᵉ l3ᵉ} {fᵉ : (xᵉ : Xᵉ) → Pᵉ xᵉ → Qᵉ xᵉ}
    ( is-equiv-fᵉ : (xᵉ : Xᵉ) → is-equivᵉ (fᵉ xᵉ)) →
    is-equivᵉ (functor-free-dependent-loopᵉ lᵉ fᵉ)
  is-equiv-functor-free-dependent-loop-is-fiberwise-equivᵉ
    (pairᵉ xᵉ lᵉ) {Pᵉ} {Qᵉ} {fᵉ} is-equiv-fᵉ =
    is-equiv-map-Σᵉ
      ( λ q₀ᵉ → Idᵉ (trᵉ Qᵉ lᵉ q₀ᵉ) q₀ᵉ)
      ( is-equiv-fᵉ xᵉ)
      ( λ p₀ᵉ →
        is-equiv-compᵉ
          ( concatᵉ
            ( invᵉ (preserves-trᵉ fᵉ lᵉ p₀ᵉ))
            ( fᵉ xᵉ p₀ᵉ))
          ( apᵉ (fᵉ xᵉ))
          ( is-emb-is-equivᵉ (is-equiv-fᵉ xᵉ) (trᵉ Pᵉ lᵉ p₀ᵉ) p₀ᵉ)
          ( is-equiv-concatᵉ
            ( invᵉ (preserves-trᵉ fᵉ lᵉ p₀ᵉ))
            ( fᵉ xᵉ p₀ᵉ)))
```

### The universal cover

```agda
module _
  { l1ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  where

  descent-data-universal-cover-circleᵉ : descent-data-circleᵉ lzero
  pr1ᵉ descent-data-universal-cover-circleᵉ = ℤᵉ
  pr2ᵉ descent-data-universal-cover-circleᵉ = equiv-succ-ℤᵉ

  module _
    ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ)
    where

    abstract
      universal-cover-family-with-descent-data-circleᵉ :
        family-with-descent-data-circleᵉ lᵉ lzero
      universal-cover-family-with-descent-data-circleᵉ =
        family-with-descent-data-circle-descent-dataᵉ lᵉ
          ( universal-property-dependent-universal-property-circleᵉ lᵉ dup-circleᵉ)
          ( descent-data-universal-cover-circleᵉ)

      universal-cover-circleᵉ : Sᵉ → UUᵉ lzero
      universal-cover-circleᵉ =
        family-family-with-descent-data-circleᵉ
          universal-cover-family-with-descent-data-circleᵉ

      compute-fiber-universal-cover-circleᵉ :
        ℤᵉ ≃ᵉ universal-cover-circleᵉ (base-free-loopᵉ lᵉ)
      compute-fiber-universal-cover-circleᵉ =
        equiv-family-with-descent-data-circleᵉ
          universal-cover-family-with-descent-data-circleᵉ

      compute-tr-universal-cover-circleᵉ :
        coherence-square-mapsᵉ
          ( map-equivᵉ compute-fiber-universal-cover-circleᵉ)
          ( succ-ℤᵉ)
          ( trᵉ universal-cover-circleᵉ (loop-free-loopᵉ lᵉ))
          ( map-equivᵉ compute-fiber-universal-cover-circleᵉ)
      compute-tr-universal-cover-circleᵉ =
        coherence-square-family-with-descent-data-circleᵉ
          universal-cover-family-with-descent-data-circleᵉ

    map-compute-fiber-universal-cover-circleᵉ :
      ℤᵉ → universal-cover-circleᵉ (base-free-loopᵉ lᵉ)
    map-compute-fiber-universal-cover-circleᵉ =
      map-equivᵉ compute-fiber-universal-cover-circleᵉ
```

### The universal cover of the circle is a family of sets

```agda
abstract
  is-set-universal-cover-circleᵉ :
    { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ) →
    ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ) →
    ( xᵉ : Xᵉ) → is-setᵉ (universal-cover-circleᵉ lᵉ dup-circleᵉ xᵉ)
  is-set-universal-cover-circleᵉ lᵉ dup-circleᵉ =
    is-connected-circle'ᵉ lᵉ
      ( dup-circleᵉ)
      ( λ xᵉ → is-setᵉ (universal-cover-circleᵉ lᵉ dup-circleᵉ xᵉ))
      ( λ xᵉ → is-prop-is-setᵉ (universal-cover-circleᵉ lᵉ dup-circleᵉ xᵉ))
      ( is-trunc-is-equiv'ᵉ zero-𝕋ᵉ ℤᵉ
        ( map-equivᵉ (compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ))
        ( is-equiv-map-equivᵉ
          ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ))
        ( is-set-ℤᵉ))
```

### Contractibility of a general total space

```agda
contraction-total-spaceᵉ :
  { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (centerᵉ : Σᵉ Aᵉ Bᵉ) →
  ( xᵉ : Aᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
contraction-total-spaceᵉ {Bᵉ = Bᵉ} centerᵉ xᵉ =
  ( yᵉ : Bᵉ xᵉ) → Idᵉ centerᵉ (pairᵉ xᵉ yᵉ)

path-total-path-fiberᵉ :
  { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (xᵉ : Aᵉ) →
  { yᵉ y'ᵉ : Bᵉ xᵉ} (qᵉ : Idᵉ y'ᵉ yᵉ) → Idᵉ {Aᵉ = Σᵉ Aᵉ Bᵉ} (pairᵉ xᵉ yᵉ) (pairᵉ xᵉ y'ᵉ)
path-total-path-fiberᵉ Bᵉ xᵉ qᵉ = eq-pair-eq-fiberᵉ (invᵉ qᵉ)

tr-path-total-path-fiberᵉ :
  { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (cᵉ : Σᵉ Aᵉ Bᵉ) (xᵉ : Aᵉ) →
  { yᵉ y'ᵉ : Bᵉ xᵉ} (qᵉ : Idᵉ y'ᵉ yᵉ) (αᵉ : Idᵉ cᵉ (pairᵉ xᵉ y'ᵉ)) →
  Idᵉ
    ( trᵉ (λ zᵉ → Idᵉ cᵉ (pairᵉ xᵉ zᵉ)) qᵉ αᵉ)
    ( αᵉ ∙ᵉ (invᵉ (path-total-path-fiberᵉ Bᵉ xᵉ qᵉ)))
tr-path-total-path-fiberᵉ cᵉ xᵉ reflᵉ αᵉ = invᵉ right-unitᵉ

segment-Σᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  { xᵉ x'ᵉ : Aᵉ} (pᵉ : Idᵉ xᵉ x'ᵉ)
  { Fᵉ : UUᵉ l3ᵉ} {F'ᵉ : UUᵉ l4ᵉ} (fᵉ : Fᵉ ≃ᵉ F'ᵉ) ( eᵉ : Fᵉ ≃ᵉ Bᵉ xᵉ) (e'ᵉ : F'ᵉ ≃ᵉ Bᵉ x'ᵉ)
  ( Hᵉ : ((map-equivᵉ e'ᵉ) ∘ᵉ (map-equivᵉ fᵉ)) ~ᵉ ((trᵉ Bᵉ pᵉ) ∘ᵉ (map-equivᵉ eᵉ))) (yᵉ : Fᵉ) →
  Idᵉ (pairᵉ xᵉ (map-equivᵉ eᵉ yᵉ)) (pairᵉ x'ᵉ (map-equivᵉ e'ᵉ (map-equivᵉ fᵉ yᵉ)))
segment-Σᵉ reflᵉ fᵉ eᵉ e'ᵉ Hᵉ yᵉ = path-total-path-fiberᵉ _ _ (Hᵉ yᵉ)

contraction-total-space'ᵉ :
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (cᵉ : Σᵉ Aᵉ Bᵉ) →
  ( xᵉ : Aᵉ) → {Fᵉ : UUᵉ l3ᵉ} (eᵉ : Fᵉ ≃ᵉ Bᵉ xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
contraction-total-space'ᵉ cᵉ xᵉ {Fᵉ} eᵉ =
  ( yᵉ : Fᵉ) → Idᵉ cᵉ (pairᵉ xᵉ (map-equivᵉ eᵉ yᵉ))

equiv-tr-contraction-total-space'ᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (cᵉ : Σᵉ Aᵉ Bᵉ) →
  { xᵉ x'ᵉ : Aᵉ} (pᵉ : Idᵉ xᵉ x'ᵉ) →
  { Fᵉ : UUᵉ l3ᵉ} {F'ᵉ : UUᵉ l4ᵉ} (fᵉ : Fᵉ ≃ᵉ F'ᵉ) (eᵉ : Fᵉ ≃ᵉ Bᵉ xᵉ) (e'ᵉ : F'ᵉ ≃ᵉ Bᵉ x'ᵉ) →
  ( Hᵉ : ((map-equivᵉ e'ᵉ) ∘ᵉ (map-equivᵉ fᵉ)) ~ᵉ ((trᵉ Bᵉ pᵉ) ∘ᵉ (map-equivᵉ eᵉ))) →
  ( contraction-total-space'ᵉ cᵉ x'ᵉ e'ᵉ) ≃ᵉ (contraction-total-space'ᵉ cᵉ xᵉ eᵉ)
equiv-tr-contraction-total-space'ᵉ cᵉ pᵉ fᵉ eᵉ e'ᵉ Hᵉ =
  ( equiv-Π-equiv-familyᵉ
    ( λ yᵉ → equiv-concat'ᵉ cᵉ (invᵉ (segment-Σᵉ pᵉ fᵉ eᵉ e'ᵉ Hᵉ yᵉ)))) ∘eᵉ
  ( equiv-precomp-Πᵉ fᵉ _)

equiv-contraction-total-spaceᵉ :
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (cᵉ : Σᵉ Aᵉ Bᵉ) →
  ( xᵉ : Aᵉ) → {Fᵉ : UUᵉ l3ᵉ} (eᵉ : Fᵉ ≃ᵉ Bᵉ xᵉ) →
  ( contraction-total-spaceᵉ cᵉ xᵉ) ≃ᵉ (contraction-total-space'ᵉ cᵉ xᵉ eᵉ)
equiv-contraction-total-spaceᵉ cᵉ xᵉ eᵉ =
  equiv-precomp-Πᵉ eᵉ (λ yᵉ → Idᵉ cᵉ (pairᵉ xᵉ yᵉ))

tr-path-total-tr-coherenceᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (cᵉ : Σᵉ Aᵉ Bᵉ) (xᵉ : Aᵉ) →
  { Fᵉ : UUᵉ l3ᵉ} {F'ᵉ : UUᵉ l4ᵉ} (fᵉ : Fᵉ ≃ᵉ F'ᵉ) ( eᵉ : Fᵉ ≃ᵉ Bᵉ xᵉ) (e'ᵉ : F'ᵉ ≃ᵉ Bᵉ xᵉ)
  ( Hᵉ : ((map-equivᵉ e'ᵉ) ∘ᵉ (map-equivᵉ fᵉ)) ~ᵉ (map-equivᵉ eᵉ)) →
  (yᵉ : Fᵉ) (αᵉ : Idᵉ cᵉ (pairᵉ xᵉ (map-equivᵉ e'ᵉ (map-equivᵉ fᵉ yᵉ)))) →
  Idᵉ
    ( trᵉ (λ zᵉ → Idᵉ cᵉ (pairᵉ xᵉ zᵉ)) (Hᵉ yᵉ) αᵉ)
    ( αᵉ ∙ᵉ (invᵉ (segment-Σᵉ reflᵉ fᵉ eᵉ e'ᵉ Hᵉ yᵉ)))
tr-path-total-tr-coherenceᵉ cᵉ xᵉ fᵉ eᵉ e'ᵉ Hᵉ yᵉ αᵉ =
  tr-path-total-path-fiberᵉ cᵉ xᵉ (Hᵉ yᵉ) αᵉ

square-tr-contraction-total-spaceᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (cᵉ : Σᵉ Aᵉ Bᵉ) →
  { xᵉ x'ᵉ : Aᵉ} (pᵉ : Idᵉ xᵉ x'ᵉ)
  { Fᵉ : UUᵉ l3ᵉ} {F'ᵉ : UUᵉ l4ᵉ} (fᵉ : Fᵉ ≃ᵉ F'ᵉ) (eᵉ : Fᵉ ≃ᵉ Bᵉ xᵉ) (e'ᵉ : F'ᵉ ≃ᵉ Bᵉ x'ᵉ)
  ( Hᵉ : ((map-equivᵉ e'ᵉ) ∘ᵉ (map-equivᵉ fᵉ)) ~ᵉ ((trᵉ Bᵉ pᵉ) ∘ᵉ (map-equivᵉ eᵉ)))
  (hᵉ : contraction-total-spaceᵉ cᵉ xᵉ) →
  ( map-equivᵉ
    ( ( equiv-tr-contraction-total-space'ᵉ cᵉ pᵉ fᵉ eᵉ e'ᵉ Hᵉ) ∘eᵉ
      ( ( equiv-contraction-total-spaceᵉ cᵉ x'ᵉ e'ᵉ) ∘eᵉ
        ( equiv-trᵉ (contraction-total-spaceᵉ cᵉ) pᵉ)))
    ( hᵉ)) ~ᵉ
  ( map-equivᵉ (equiv-contraction-total-spaceᵉ cᵉ xᵉ eᵉ) hᵉ)
square-tr-contraction-total-spaceᵉ cᵉ reflᵉ fᵉ eᵉ e'ᵉ Hᵉ hᵉ yᵉ =
  ( invᵉ (tr-path-total-tr-coherenceᵉ cᵉ _ fᵉ eᵉ e'ᵉ Hᵉ yᵉ
    ( hᵉ (map-equivᵉ e'ᵉ (map-equivᵉ fᵉ yᵉ))))) ∙ᵉ
  ( apdᵉ hᵉ (Hᵉ yᵉ))

dependent-identification-contraction-total-space'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (cᵉ : Σᵉ Aᵉ Bᵉ) →
  {xᵉ x'ᵉ : Aᵉ} (pᵉ : Idᵉ xᵉ x'ᵉ) →
  {Fᵉ : UUᵉ l3ᵉ} {F'ᵉ : UUᵉ l4ᵉ} (fᵉ : Fᵉ ≃ᵉ F'ᵉ) ( eᵉ : Fᵉ ≃ᵉ Bᵉ xᵉ) (e'ᵉ : F'ᵉ ≃ᵉ Bᵉ x'ᵉ)
  (Hᵉ : ((map-equivᵉ e'ᵉ) ∘ᵉ (map-equivᵉ fᵉ)) ~ᵉ ((trᵉ Bᵉ pᵉ) ∘ᵉ (map-equivᵉ eᵉ))) →
  (hᵉ : (yᵉ : Fᵉ) → Idᵉ cᵉ (pairᵉ xᵉ (map-equivᵉ eᵉ yᵉ))) →
  (h'ᵉ : (y'ᵉ : F'ᵉ) → Idᵉ cᵉ (pairᵉ x'ᵉ (map-equivᵉ e'ᵉ y'ᵉ))) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
dependent-identification-contraction-total-space'ᵉ
  cᵉ {xᵉ} {x'ᵉ} pᵉ {Fᵉ} {F'ᵉ} fᵉ eᵉ e'ᵉ Hᵉ hᵉ h'ᵉ =
  ( map-Πᵉ
    ( λ yᵉ → concat'ᵉ cᵉ (segment-Σᵉ pᵉ fᵉ eᵉ e'ᵉ Hᵉ yᵉ)) hᵉ) ~ᵉ
  ( precomp-Πᵉ
    ( map-equivᵉ fᵉ)
    ( λ y'ᵉ → Idᵉ cᵉ (pairᵉ x'ᵉ (map-equivᵉ e'ᵉ y'ᵉ)))
    ( h'ᵉ))

map-dependent-identification-contraction-total-space'ᵉ :
    { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (cᵉ : Σᵉ Aᵉ Bᵉ) →
    { xᵉ x'ᵉ : Aᵉ} (pᵉ : Idᵉ xᵉ x'ᵉ) →
    { Fᵉ : UUᵉ l3ᵉ} {F'ᵉ : UUᵉ l4ᵉ} (fᵉ : Fᵉ ≃ᵉ F'ᵉ) ( eᵉ : Fᵉ ≃ᵉ Bᵉ xᵉ) (e'ᵉ : F'ᵉ ≃ᵉ Bᵉ x'ᵉ)
    ( Hᵉ : ((map-equivᵉ e'ᵉ) ∘ᵉ (map-equivᵉ fᵉ)) ~ᵉ ((trᵉ Bᵉ pᵉ) ∘ᵉ (map-equivᵉ eᵉ))) →
    ( hᵉ : contraction-total-space'ᵉ cᵉ xᵉ eᵉ) →
    ( h'ᵉ : contraction-total-space'ᵉ cᵉ x'ᵉ e'ᵉ) →
    ( dependent-identification-contraction-total-space'ᵉ cᵉ pᵉ fᵉ eᵉ e'ᵉ Hᵉ hᵉ h'ᵉ) →
    ( dependent-identificationᵉ (contraction-total-spaceᵉ cᵉ) pᵉ
      ( map-inv-equivᵉ (equiv-contraction-total-spaceᵉ cᵉ xᵉ eᵉ) hᵉ)
      ( map-inv-equivᵉ (equiv-contraction-total-spaceᵉ cᵉ x'ᵉ e'ᵉ) h'ᵉ))
map-dependent-identification-contraction-total-space'ᵉ
  cᵉ {xᵉ} {.xᵉ} reflᵉ fᵉ eᵉ e'ᵉ Hᵉ hᵉ h'ᵉ αᵉ =
  map-inv-equivᵉ
    ( equiv-apᵉ
      ( ( equiv-tr-contraction-total-space'ᵉ cᵉ reflᵉ fᵉ eᵉ e'ᵉ Hᵉ) ∘eᵉ
        ( equiv-contraction-total-spaceᵉ cᵉ xᵉ e'ᵉ))
      ( map-inv-equivᵉ (equiv-contraction-total-spaceᵉ cᵉ xᵉ eᵉ) hᵉ)
      ( map-inv-equivᵉ (equiv-contraction-total-spaceᵉ cᵉ xᵉ e'ᵉ) h'ᵉ))
    ( ( ( eq-htpyᵉ
          ( square-tr-contraction-total-spaceᵉ cᵉ reflᵉ fᵉ eᵉ e'ᵉ Hᵉ
            ( map-inv-equivᵉ (equiv-contraction-total-spaceᵉ cᵉ xᵉ eᵉ) hᵉ))) ∙ᵉ
        ( is-section-map-inv-is-equivᵉ
          ( is-equiv-map-equivᵉ (equiv-contraction-total-spaceᵉ cᵉ xᵉ eᵉ))
          ( hᵉ))) ∙ᵉ
      ( ( eq-htpyᵉ
          ( right-transpose-htpy-concatᵉ hᵉ
            ( segment-Σᵉ reflᵉ fᵉ eᵉ e'ᵉ Hᵉ)
            ( precomp-Πᵉ
              ( map-equivᵉ fᵉ)
              ( λ y'ᵉ → Idᵉ cᵉ (pairᵉ xᵉ (map-equivᵉ e'ᵉ y'ᵉ)))
              ( h'ᵉ))
            ( αᵉ))) ∙ᵉ
        ( invᵉ
          ( apᵉ
            ( map-equivᵉ (equiv-tr-contraction-total-space'ᵉ cᵉ reflᵉ fᵉ eᵉ e'ᵉ Hᵉ))
            ( is-section-map-inv-is-equivᵉ
              ( is-equiv-map-equivᵉ
                ( equiv-precomp-Πᵉ e'ᵉ (λ y'ᵉ → Idᵉ cᵉ (pairᵉ xᵉ y'ᵉ))))
              ( h'ᵉ))))))

equiv-dependent-identification-contraction-total-space'ᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (cᵉ : Σᵉ Aᵉ Bᵉ) →
  { xᵉ x'ᵉ : Aᵉ} (pᵉ : Idᵉ xᵉ x'ᵉ) →
  { Fᵉ : UUᵉ l3ᵉ} {F'ᵉ : UUᵉ l4ᵉ} (fᵉ : Fᵉ ≃ᵉ F'ᵉ) ( eᵉ : Fᵉ ≃ᵉ Bᵉ xᵉ) (e'ᵉ : F'ᵉ ≃ᵉ Bᵉ x'ᵉ)
  ( Hᵉ : ((map-equivᵉ e'ᵉ) ∘ᵉ (map-equivᵉ fᵉ)) ~ᵉ ((trᵉ Bᵉ pᵉ) ∘ᵉ (map-equivᵉ eᵉ))) →
  ( hᵉ : contraction-total-space'ᵉ cᵉ xᵉ eᵉ) →
  ( h'ᵉ : contraction-total-space'ᵉ cᵉ x'ᵉ e'ᵉ) →
  ( dependent-identificationᵉ (contraction-total-spaceᵉ cᵉ) pᵉ
    ( map-inv-equivᵉ (equiv-contraction-total-spaceᵉ cᵉ xᵉ eᵉ) hᵉ)
    ( map-inv-equivᵉ (equiv-contraction-total-spaceᵉ cᵉ x'ᵉ e'ᵉ) h'ᵉ)) ≃ᵉ
  ( dependent-identification-contraction-total-space'ᵉ cᵉ pᵉ fᵉ eᵉ e'ᵉ Hᵉ hᵉ h'ᵉ)
equiv-dependent-identification-contraction-total-space'ᵉ
  cᵉ {xᵉ} {.xᵉ} reflᵉ fᵉ eᵉ e'ᵉ Hᵉ hᵉ h'ᵉ =
  ( inv-equivᵉ
    ( equiv-right-transpose-htpy-concatᵉ hᵉ
      ( segment-Σᵉ reflᵉ fᵉ eᵉ e'ᵉ Hᵉ)
      ( precomp-Πᵉ
        ( map-equivᵉ fᵉ)
        ( λ y'ᵉ → Idᵉ cᵉ (pairᵉ xᵉ (map-equivᵉ e'ᵉ y'ᵉ)))
        ( h'ᵉ)))) ∘eᵉ
  ( ( equiv-funextᵉ) ∘eᵉ
    ( ( equiv-concat'ᵉ hᵉ
        ( apᵉ
          ( map-equivᵉ (equiv-tr-contraction-total-space'ᵉ cᵉ reflᵉ fᵉ eᵉ e'ᵉ Hᵉ))
          ( is-section-map-inv-is-equivᵉ
            ( is-equiv-map-equivᵉ
              ( equiv-precomp-Πᵉ e'ᵉ (λ y'ᵉ → Idᵉ cᵉ (pairᵉ xᵉ y'ᵉ))))
            ( h'ᵉ)))) ∘eᵉ
      ( ( equiv-concatᵉ
          ( invᵉ
            ( ( eq-htpyᵉ
                ( square-tr-contraction-total-spaceᵉ cᵉ reflᵉ fᵉ eᵉ e'ᵉ Hᵉ
                  ( map-inv-equivᵉ (equiv-contraction-total-spaceᵉ cᵉ xᵉ eᵉ) hᵉ))) ∙ᵉ
              ( is-section-map-inv-is-equivᵉ
                ( is-equiv-map-equivᵉ (equiv-contraction-total-spaceᵉ cᵉ xᵉ eᵉ))
                ( hᵉ))))
          ( map-equivᵉ
            ( ( equiv-tr-contraction-total-space'ᵉ cᵉ reflᵉ fᵉ eᵉ e'ᵉ Hᵉ) ∘eᵉ
              ( ( equiv-contraction-total-spaceᵉ cᵉ xᵉ e'ᵉ) ∘eᵉ
                ( inv-equivᵉ (equiv-contraction-total-spaceᵉ cᵉ xᵉ e'ᵉ))))
            ( h'ᵉ))) ∘eᵉ
        ( equiv-apᵉ
          ( ( equiv-tr-contraction-total-space'ᵉ cᵉ reflᵉ fᵉ eᵉ e'ᵉ Hᵉ) ∘eᵉ
            ( equiv-contraction-total-spaceᵉ cᵉ xᵉ e'ᵉ))
          ( map-inv-equivᵉ (equiv-contraction-total-spaceᵉ cᵉ xᵉ eᵉ) hᵉ)
          ( map-inv-equivᵉ (equiv-contraction-total-spaceᵉ cᵉ xᵉ e'ᵉ) h'ᵉ)))))
```

Weᵉ useᵉ theᵉ aboveᵉ constructionᵉ to provideᵉ sufficientᵉ conditionsᵉ forᵉ theᵉ totalᵉ
spaceᵉ ofᵉ theᵉ universalᵉ coverᵉ to beᵉ contractible.ᵉ

```agda
center-total-universal-cover-circleᵉ :
  { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ) →
  ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ) →
  Σᵉ Xᵉ (universal-cover-circleᵉ lᵉ dup-circleᵉ)
pr1ᵉ (center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ) = base-free-loopᵉ lᵉ
pr2ᵉ (center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ) =
  map-equivᵉ ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ) zero-ℤᵉ

dependent-identification-loop-contraction-total-universal-cover-circleᵉ :
  { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ) →
  ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ) →
  ( hᵉ :
    contraction-total-space'ᵉ
      ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( base-free-loopᵉ lᵉ)
      ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)) →
  ( pᵉ :
    dependent-identification-contraction-total-space'ᵉ
      ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( loop-free-loopᵉ lᵉ)
      ( equiv-succ-ℤᵉ)
      ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( compute-tr-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( hᵉ)
      ( hᵉ)) →
  dependent-identificationᵉ
    ( contraction-total-spaceᵉ
      ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ))
    ( pr2ᵉ lᵉ)
    ( map-inv-equivᵉ
      ( equiv-contraction-total-spaceᵉ
        ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ)
        ( base-free-loopᵉ lᵉ)
        ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ))
      ( hᵉ))
    ( map-inv-equivᵉ
      ( equiv-contraction-total-spaceᵉ
        ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ)
        ( base-free-loopᵉ lᵉ)
        ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ))
      ( hᵉ))
dependent-identification-loop-contraction-total-universal-cover-circleᵉ
  lᵉ dup-circleᵉ hᵉ pᵉ =
  map-dependent-identification-contraction-total-space'ᵉ
    ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ)
    ( loop-free-loopᵉ lᵉ)
    ( equiv-succ-ℤᵉ)
    ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)
    ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)
    ( compute-tr-universal-cover-circleᵉ lᵉ dup-circleᵉ)
    ( hᵉ)
    ( hᵉ)
    ( pᵉ)

contraction-total-universal-cover-circle-dataᵉ :
  { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ) →
  ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ) →
  ( hᵉ :
    contraction-total-space'ᵉ
      ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( base-free-loopᵉ lᵉ)
      ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)) →
  ( pᵉ :
    dependent-identification-contraction-total-space'ᵉ
      ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( loop-free-loopᵉ lᵉ)
      ( equiv-succ-ℤᵉ)
      ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( compute-tr-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( hᵉ)
      ( hᵉ)) →
  ( tᵉ : Σᵉ Xᵉ (universal-cover-circleᵉ lᵉ dup-circleᵉ)) →
  Idᵉ (center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ) tᵉ
contraction-total-universal-cover-circle-dataᵉ
  {l1ᵉ} lᵉ dup-circleᵉ hᵉ pᵉ (pairᵉ xᵉ yᵉ) =
  map-inv-is-equivᵉ
    ( dup-circleᵉ
      ( contraction-total-spaceᵉ
        ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ)))
    ( pairᵉ
      ( map-inv-equivᵉ
        ( equiv-contraction-total-spaceᵉ
          ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ)
          ( base-free-loopᵉ lᵉ)
          ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ))
        ( hᵉ))
      ( dependent-identification-loop-contraction-total-universal-cover-circleᵉ
        lᵉ dup-circleᵉ hᵉ pᵉ))
    xᵉ yᵉ

is-torsorial-universal-cover-circle-dataᵉ :
  { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ) →
  ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ) →
  ( hᵉ :
    contraction-total-space'ᵉ
      ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( base-free-loopᵉ lᵉ)
      ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)) →
  ( pᵉ :
    dependent-identification-contraction-total-space'ᵉ
      ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( loop-free-loopᵉ lᵉ)
      ( equiv-succ-ℤᵉ)
      ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( compute-tr-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( hᵉ)
      ( hᵉ)) →
  is-torsorialᵉ (universal-cover-circleᵉ lᵉ dup-circleᵉ)
pr1ᵉ (is-torsorial-universal-cover-circle-dataᵉ lᵉ dup-circleᵉ hᵉ pᵉ) =
  center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ
pr2ᵉ (is-torsorial-universal-cover-circle-dataᵉ lᵉ dup-circleᵉ hᵉ pᵉ) =
  contraction-total-universal-cover-circle-dataᵉ lᵉ dup-circleᵉ hᵉ pᵉ
```

### Section 12.5 The identity type of the circle

```agda
path-total-universal-cover-circleᵉ :
  { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ) →
  ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ)
  ( kᵉ : ℤᵉ) →
  Idᵉ
    { Aᵉ = Σᵉ Xᵉ (universal-cover-circleᵉ lᵉ dup-circleᵉ)}
    ( pairᵉ
      ( base-free-loopᵉ lᵉ)
      ( map-equivᵉ (compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ) kᵉ))
    ( pairᵉ
      ( base-free-loopᵉ lᵉ)
      ( map-equivᵉ
        ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)
        ( succ-ℤᵉ kᵉ)))
path-total-universal-cover-circleᵉ lᵉ dup-circleᵉ kᵉ =
  segment-Σᵉ
    ( loop-free-loopᵉ lᵉ)
    ( equiv-succ-ℤᵉ)
    ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)
    ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)
    ( compute-tr-universal-cover-circleᵉ lᵉ dup-circleᵉ)
    kᵉ

CONTRACTION-universal-cover-circleᵉ :
  { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ) →
  ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ) →
  UUᵉ l1ᵉ
CONTRACTION-universal-cover-circleᵉ lᵉ dup-circleᵉ =
  ELIM-ℤᵉ
    ( λ kᵉ →
      Idᵉ
        ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ)
        ( pairᵉ
          ( base-free-loopᵉ lᵉ)
          ( map-equivᵉ
            ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)
            ( kᵉ))))
    ( reflᵉ)
    ( λ kᵉ → equiv-concat'ᵉ
      ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( path-total-universal-cover-circleᵉ lᵉ dup-circleᵉ kᵉ))

Contraction-universal-cover-circleᵉ :
  { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ) →
  ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ) →
  CONTRACTION-universal-cover-circleᵉ lᵉ dup-circleᵉ
Contraction-universal-cover-circleᵉ lᵉ dup-circleᵉ =
  Elim-ℤᵉ
    ( λ kᵉ →
      Idᵉ
        ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ)
        ( pairᵉ
          ( base-free-loopᵉ lᵉ)
          ( map-equivᵉ
            ( compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)
            ( kᵉ))))
    ( reflᵉ)
    ( λ kᵉ → equiv-concat'ᵉ
      ( center-total-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( path-total-universal-cover-circleᵉ lᵉ dup-circleᵉ kᵉ))

abstract
  is-torsorial-universal-cover-circleᵉ :
    { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ) →
    ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ) →
    is-torsorialᵉ (universal-cover-circleᵉ lᵉ dup-circleᵉ)
  is-torsorial-universal-cover-circleᵉ lᵉ dup-circleᵉ =
    is-torsorial-universal-cover-circle-dataᵉ lᵉ dup-circleᵉ
      ( pr1ᵉ (Contraction-universal-cover-circleᵉ lᵉ dup-circleᵉ))
      ( inv-htpyᵉ
        ( pr2ᵉ (pr2ᵉ (Contraction-universal-cover-circleᵉ lᵉ dup-circleᵉ))))

point-universal-cover-circleᵉ :
  { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ) →
  ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ) →
  universal-cover-circleᵉ lᵉ dup-circleᵉ (base-free-loopᵉ lᵉ)
point-universal-cover-circleᵉ lᵉ dup-circleᵉ =
  map-equivᵉ (compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ) zero-ℤᵉ

universal-cover-circle-eqᵉ :
  { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ) →
  ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ) →
  ( xᵉ : Xᵉ) → Idᵉ (base-free-loopᵉ lᵉ) xᵉ → universal-cover-circleᵉ lᵉ dup-circleᵉ xᵉ
universal-cover-circle-eqᵉ lᵉ dup-circleᵉ .(base-free-loopᵉ lᵉ) reflᵉ =
  point-universal-cover-circleᵉ lᵉ dup-circleᵉ

abstract
  is-equiv-universal-cover-circle-eqᵉ :
    { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ) →
    ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ) →
    ( xᵉ : Xᵉ) → is-equivᵉ (universal-cover-circle-eqᵉ lᵉ dup-circleᵉ xᵉ)
  is-equiv-universal-cover-circle-eqᵉ lᵉ dup-circleᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-universal-cover-circleᵉ lᵉ dup-circleᵉ)
      ( universal-cover-circle-eqᵉ lᵉ dup-circleᵉ)

equiv-universal-cover-circleᵉ :
  { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ) →
  ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ) →
  ( xᵉ : Xᵉ) →
  ( Idᵉ (base-free-loopᵉ lᵉ) xᵉ) ≃ᵉ (universal-cover-circleᵉ lᵉ dup-circleᵉ xᵉ)
equiv-universal-cover-circleᵉ lᵉ dup-circleᵉ xᵉ =
  pairᵉ
    ( universal-cover-circle-eqᵉ lᵉ dup-circleᵉ xᵉ)
    ( is-equiv-universal-cover-circle-eqᵉ lᵉ dup-circleᵉ xᵉ)

compute-loop-space-circleᵉ :
  { l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ) →
  ( dup-circleᵉ : dependent-universal-property-circleᵉ lᵉ) →
  type-Ωᵉ (Xᵉ ,ᵉ base-free-loopᵉ lᵉ) ≃ᵉ ℤᵉ
compute-loop-space-circleᵉ lᵉ dup-circleᵉ =
  ( inv-equivᵉ (compute-fiber-universal-cover-circleᵉ lᵉ dup-circleᵉ)) ∘eᵉ
  ( equiv-universal-cover-circleᵉ lᵉ dup-circleᵉ (base-free-loopᵉ lᵉ))
```

### The loop of the circle is nontrivial

```agda
module _
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Xᵉ)
  (Hᵉ : dependent-universal-property-circleᵉ lᵉ)
  where

  is-nontrivial-loop-dependent-universal-property-circleᵉ :
    loop-free-loopᵉ lᵉ ≠ᵉ reflᵉ
  is-nontrivial-loop-dependent-universal-property-circleᵉ pᵉ =
    is-nonzero-one-ℤᵉ
      ( is-injective-equivᵉ
        ( compute-fiber-universal-cover-circleᵉ lᵉ Hᵉ)
        ( ( compute-tr-universal-cover-circleᵉ lᵉ Hᵉ zero-ℤᵉ) ∙ᵉ
          ( apᵉ
            ( λ qᵉ →
              trᵉ
                ( universal-cover-circleᵉ lᵉ Hᵉ)
                ( qᵉ)
                ( map-compute-fiber-universal-cover-circleᵉ lᵉ Hᵉ zero-ℤᵉ))
            ( pᵉ))))
```