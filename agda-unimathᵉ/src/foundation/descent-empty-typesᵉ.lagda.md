# Descent for the empty type

```agda
module foundation.descent-empty-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.empty-typesᵉ
open import foundation-core.pullbacksᵉ
```

</details>

## Theorem

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Bᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (gᵉ : Bᵉ → Xᵉ)
  where

  cone-emptyᵉ : is-emptyᵉ Cᵉ → (Cᵉ → Bᵉ) → coneᵉ ex-falsoᵉ gᵉ Cᵉ
  pr1ᵉ (cone-emptyᵉ pᵉ qᵉ) = pᵉ
  pr1ᵉ (pr2ᵉ (cone-emptyᵉ pᵉ qᵉ)) = qᵉ
  pr2ᵉ (pr2ᵉ (cone-emptyᵉ pᵉ qᵉ)) cᵉ = ex-falsoᵉ (pᵉ cᵉ)

  abstract
    descent-emptyᵉ : (cᵉ : coneᵉ ex-falsoᵉ gᵉ Cᵉ) → is-pullbackᵉ ex-falsoᵉ gᵉ cᵉ
    descent-emptyᵉ cᵉ =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ _ gᵉ cᵉ ind-emptyᵉ

  abstract
    descent-empty'ᵉ :
      (pᵉ : Cᵉ → emptyᵉ) (qᵉ : Cᵉ → Bᵉ) → is-pullbackᵉ ex-falsoᵉ gᵉ (cone-emptyᵉ pᵉ qᵉ)
    descent-empty'ᵉ pᵉ qᵉ = descent-emptyᵉ (cone-emptyᵉ pᵉ qᵉ)
```