# Descent for dependent pair types

```agda
module foundation.descent-dependent-pair-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-fibers-of-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.pullbacksᵉ
```

</details>

## Theorem

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {A'ᵉ : Iᵉ → UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {X'ᵉ : UUᵉ l5ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Xᵉ) (hᵉ : X'ᵉ → Xᵉ)
  (cᵉ : (iᵉ : Iᵉ) → coneᵉ (fᵉ iᵉ) hᵉ (A'ᵉ iᵉ))
  where

  cone-descent-Σᵉ : coneᵉ (ind-Σᵉ fᵉ) hᵉ (Σᵉ Iᵉ A'ᵉ)
  cone-descent-Σᵉ =
    tripleᵉ
      ( totᵉ (λ iᵉ → (pr1ᵉ (cᵉ iᵉ))))
      ( ind-Σᵉ (λ iᵉ → (pr1ᵉ (pr2ᵉ (cᵉ iᵉ)))))
      ( ind-Σᵉ (λ iᵉ → (pr2ᵉ (pr2ᵉ (cᵉ iᵉ)))))

  triangle-descent-Σᵉ :
    (iᵉ : Iᵉ) (aᵉ : Aᵉ iᵉ) →
    ( map-fiber-vertical-map-coneᵉ (fᵉ iᵉ) hᵉ (cᵉ iᵉ) aᵉ) ~ᵉ
    ( ( map-fiber-vertical-map-coneᵉ (ind-Σᵉ fᵉ) hᵉ cone-descent-Σᵉ (pairᵉ iᵉ aᵉ)) ∘ᵉ
      ( map-inv-compute-fiber-totᵉ (λ iᵉ → (pr1ᵉ (cᵉ iᵉ))) (pairᵉ iᵉ aᵉ)))
  triangle-descent-Σᵉ iᵉ .(pr1ᵉ (cᵉ iᵉ) a'ᵉ) (pairᵉ a'ᵉ reflᵉ) = reflᵉ

  abstract
    descent-Σᵉ :
      ((iᵉ : Iᵉ) → is-pullbackᵉ (fᵉ iᵉ) hᵉ (cᵉ iᵉ)) →
      is-pullbackᵉ (ind-Σᵉ fᵉ) hᵉ cone-descent-Σᵉ
    descent-Σᵉ is-pb-cᵉ =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ
        ( ind-Σᵉ fᵉ)
        ( hᵉ)
        ( cone-descent-Σᵉ)
        ( ind-Σᵉ
          ( λ iᵉ aᵉ →
            is-equiv-right-map-triangleᵉ
            ( map-fiber-vertical-map-coneᵉ (fᵉ iᵉ) hᵉ (cᵉ iᵉ) aᵉ)
            ( map-fiber-vertical-map-coneᵉ (ind-Σᵉ fᵉ) hᵉ cone-descent-Σᵉ (pairᵉ iᵉ aᵉ))
            ( map-inv-compute-fiber-totᵉ (λ iᵉ → pr1ᵉ (cᵉ iᵉ)) (pairᵉ iᵉ aᵉ))
            ( triangle-descent-Σᵉ iᵉ aᵉ)
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ
              (fᵉ iᵉ) hᵉ (cᵉ iᵉ) (is-pb-cᵉ iᵉ) aᵉ)
            ( is-equiv-map-inv-compute-fiber-totᵉ (λ iᵉ → pr1ᵉ (cᵉ iᵉ)) (pairᵉ iᵉ aᵉ))))

  abstract
    descent-Σ'ᵉ :
      is-pullbackᵉ (ind-Σᵉ fᵉ) hᵉ cone-descent-Σᵉ →
      ((iᵉ : Iᵉ) → is-pullbackᵉ (fᵉ iᵉ) hᵉ (cᵉ iᵉ))
    descent-Σ'ᵉ is-pb-dsqᵉ iᵉ =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ (fᵉ iᵉ) hᵉ (cᵉ iᵉ)
        ( λ aᵉ →
          is-equiv-left-map-triangleᵉ
          ( map-fiber-vertical-map-coneᵉ (fᵉ iᵉ) hᵉ (cᵉ iᵉ) aᵉ)
          ( map-fiber-vertical-map-coneᵉ (ind-Σᵉ fᵉ) hᵉ cone-descent-Σᵉ (pairᵉ iᵉ aᵉ))
          ( map-inv-compute-fiber-totᵉ (λ iᵉ → pr1ᵉ (cᵉ iᵉ)) (pairᵉ iᵉ aᵉ))
          ( triangle-descent-Σᵉ iᵉ aᵉ)
          ( is-equiv-map-inv-compute-fiber-totᵉ (λ iᵉ → pr1ᵉ (cᵉ iᵉ)) (pairᵉ iᵉ aᵉ))
          ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ
            ( ind-Σᵉ fᵉ)
            ( hᵉ)
            ( cone-descent-Σᵉ)
            ( is-pb-dsqᵉ)
            ( pairᵉ iᵉ aᵉ)))
```