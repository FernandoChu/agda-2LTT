# Functoriality of sequential limits

```agda
module foundation.functoriality-sequential-limitsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cones-over-inverse-sequential-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.inverse-sequential-diagramsᵉ
open import foundation.morphisms-inverse-sequential-diagramsᵉ
open import foundation.sequential-limitsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Theᵉ constructionᵉ ofᵉ theᵉ [sequentialᵉ limit](foundation.sequential-limits.mdᵉ) isᵉ
functorial.ᵉ

## Definitions

### The functorial action on maps of standard sequential limits

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {Aᵉ : inverse-sequential-diagramᵉ l1ᵉ} {A'ᵉ : inverse-sequential-diagramᵉ l2ᵉ}
  where

  map-hom-standard-sequential-limitᵉ :
    hom-inverse-sequential-diagramᵉ A'ᵉ Aᵉ →
    standard-sequential-limitᵉ A'ᵉ →
    standard-sequential-limitᵉ Aᵉ
  pr1ᵉ (map-hom-standard-sequential-limitᵉ (fᵉ ,ᵉ Fᵉ) (xᵉ ,ᵉ Hᵉ)) nᵉ = fᵉ nᵉ (xᵉ nᵉ)
  pr2ᵉ (map-hom-standard-sequential-limitᵉ (fᵉ ,ᵉ Fᵉ) (xᵉ ,ᵉ Hᵉ)) nᵉ =
    apᵉ (fᵉ nᵉ) (Hᵉ nᵉ) ∙ᵉ Fᵉ nᵉ (xᵉ (succ-ℕᵉ nᵉ))

  map-hom-is-sequential-limitᵉ :
    {l4ᵉ l4'ᵉ : Level} {Cᵉ : UUᵉ l4ᵉ} {C'ᵉ : UUᵉ l4'ᵉ} →
    (cᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Cᵉ)
    (c'ᵉ : cone-inverse-sequential-diagramᵉ A'ᵉ C'ᵉ) →
    is-sequential-limitᵉ Aᵉ cᵉ → is-sequential-limitᵉ A'ᵉ c'ᵉ →
    hom-inverse-sequential-diagramᵉ A'ᵉ Aᵉ → C'ᵉ → Cᵉ
  map-hom-is-sequential-limitᵉ cᵉ c'ᵉ is-lim-cᵉ is-lim-c'ᵉ hᵉ xᵉ =
    map-inv-is-equivᵉ
      ( is-lim-cᵉ)
      ( map-hom-standard-sequential-limitᵉ hᵉ
        ( gap-inverse-sequential-diagramᵉ A'ᵉ c'ᵉ xᵉ))
```

## Table of files about sequential limits

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ sequentialᵉ limitsᵉ asᵉ aᵉ generalᵉ
concept.ᵉ

{{#includeᵉ tables/sequential-limits.mdᵉ}}