# Cantor's diagonal argument

```agda
module foundation.cantors-diagonal-argumentᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.empty-typesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Cantor'sᵉ diagonalᵉ argumentᵉ isᵉ usedᵉ to showᵉ thatᵉ thereᵉ isᵉ noᵉ surjectiveᵉ mapᵉ fromᵉ
aᵉ typeᵉ intoᵉ theᵉ typeᵉ ofᵉ itsᵉ subtypes.ᵉ

## Theorem

```agda
map-cantorᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (fᵉ : Xᵉ → (Xᵉ → Propᵉ l2ᵉ)) → (Xᵉ → Propᵉ l2ᵉ)
map-cantorᵉ Xᵉ fᵉ xᵉ = neg-Propᵉ (fᵉ xᵉ xᵉ)

abstract
  not-in-image-map-cantorᵉ :
    {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (fᵉ : Xᵉ → (Xᵉ → Propᵉ l2ᵉ)) →
    ( tᵉ : fiberᵉ fᵉ (map-cantorᵉ Xᵉ fᵉ)) → emptyᵉ
  not-in-image-map-cantorᵉ Xᵉ fᵉ (pairᵉ xᵉ αᵉ) =
    no-fixed-points-neg-Propᵉ (fᵉ xᵉ xᵉ) (iff-eqᵉ (htpy-eqᵉ αᵉ xᵉ))

abstract
  cantorᵉ :
    {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (fᵉ : Xᵉ → Xᵉ → Propᵉ l2ᵉ) → ¬ᵉ (is-surjectiveᵉ fᵉ)
  cantorᵉ Xᵉ fᵉ Hᵉ =
    ( apply-universal-property-trunc-Propᵉ
      ( Hᵉ (map-cantorᵉ Xᵉ fᵉ))
      ( empty-Propᵉ)
      ( not-in-image-map-cantorᵉ Xᵉ fᵉ))
```