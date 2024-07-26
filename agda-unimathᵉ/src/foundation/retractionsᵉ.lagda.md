# Retractions

```agda
module foundation.retractionsᵉ where

open import foundation-core.retractionsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.cosliceᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retracts-of-typesᵉ
```

</details>

## Properties

### Characterizing the identity type of `retraction f`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  coherence-htpy-retractionᵉ :
    (gᵉ hᵉ : retractionᵉ fᵉ) → map-retractionᵉ fᵉ gᵉ ~ᵉ map-retractionᵉ fᵉ hᵉ → UUᵉ l1ᵉ
  coherence-htpy-retractionᵉ = coherence-htpy-hom-cosliceᵉ

  htpy-retractionᵉ : retractionᵉ fᵉ → retractionᵉ fᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-retractionᵉ = htpy-hom-cosliceᵉ

  extensionality-retractionᵉ :
    (gᵉ hᵉ : retractionᵉ fᵉ) → (gᵉ ＝ᵉ hᵉ) ≃ᵉ htpy-retractionᵉ gᵉ hᵉ
  extensionality-retractionᵉ = extensionality-hom-cosliceᵉ

  eq-htpy-retractionᵉ :
    ( gᵉ hᵉ : retractionᵉ fᵉ)
    ( Hᵉ : map-retractionᵉ fᵉ gᵉ ~ᵉ map-retractionᵉ fᵉ hᵉ)
    ( Kᵉ :
      ( is-retraction-map-retractionᵉ fᵉ gᵉ) ~ᵉ
      ( (Hᵉ ·rᵉ fᵉ) ∙hᵉ is-retraction-map-retractionᵉ fᵉ hᵉ)) →
    gᵉ ＝ᵉ hᵉ
  eq-htpy-retractionᵉ = eq-htpy-hom-cosliceᵉ
```

### If the left factor of a composite has a retraction, then the type of retractions of the right factor is a retract of the type of retractions of the composite

```agda
is-retraction-retraction-left-map-triangleᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ)
  (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ)) (rgᵉ : retractionᵉ gᵉ) →
  ( ( retraction-top-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ) ∘ᵉ
    ( retraction-left-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ rgᵉ)) ~ᵉ idᵉ
is-retraction-retraction-left-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ (lᵉ ,ᵉ Lᵉ) (kᵉ ,ᵉ Kᵉ) =
  eq-htpy-retractionᵉ
    ( ( retraction-top-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ
        ( retraction-left-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ (lᵉ ,ᵉ Lᵉ) (kᵉ ,ᵉ Kᵉ))))
    ( kᵉ ,ᵉ Kᵉ)
    ( kᵉ ·lᵉ Lᵉ)
    ( ( inv-htpy-assoc-htpyᵉ
        ( inv-htpyᵉ ((kᵉ ∘ᵉ lᵉ) ·lᵉ Hᵉ))
        ( (kᵉ ∘ᵉ lᵉ) ·lᵉ Hᵉ)
        ( (kᵉ ·lᵉ (Lᵉ ·rᵉ hᵉ)) ∙hᵉ Kᵉ)) ∙hᵉ
      ( ap-concat-htpy'ᵉ ((kᵉ ·lᵉ (Lᵉ ·rᵉ hᵉ)) ∙hᵉ Kᵉ) (left-inv-htpyᵉ ((kᵉ ∘ᵉ lᵉ) ·lᵉ Hᵉ))))

retraction-right-factor-retract-of-retraction-left-factorᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ ∘ᵉ hᵉ) →
  retractionᵉ gᵉ → (retractionᵉ hᵉ) retract-ofᵉ (retractionᵉ fᵉ)
pr1ᵉ (retraction-right-factor-retract-of-retraction-left-factorᵉ fᵉ gᵉ hᵉ Hᵉ rgᵉ) =
  retraction-left-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ rgᵉ
pr1ᵉ
  ( pr2ᵉ
    ( retraction-right-factor-retract-of-retraction-left-factorᵉ fᵉ gᵉ hᵉ Hᵉ rgᵉ)) =
  retraction-top-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ
pr2ᵉ
  ( pr2ᵉ
    ( retraction-right-factor-retract-of-retraction-left-factorᵉ fᵉ gᵉ hᵉ Hᵉ rgᵉ)) =
  is-retraction-retraction-left-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ rgᵉ
```