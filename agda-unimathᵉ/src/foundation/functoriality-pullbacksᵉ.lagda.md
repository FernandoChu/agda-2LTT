# Functorialty of pullbacks

```agda
module foundation.functoriality-pullbacksᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.morphisms-cospan-diagramsᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.pullbacksᵉ
```

</details>

## Idea

Theᵉ constructionᵉ ofᵉ theᵉ [standardᵉ pullback](foundation-core.pullbacks.mdᵉ) isᵉ
functorial.ᵉ

## Definitions

### The functorial action on maps of pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ} (f'ᵉ : A'ᵉ → X'ᵉ) (g'ᵉ : B'ᵉ → X'ᵉ)
  where

  map-standard-pullbackᵉ :
    hom-cospan-diagramᵉ f'ᵉ g'ᵉ fᵉ gᵉ →
    standard-pullbackᵉ f'ᵉ g'ᵉ → standard-pullbackᵉ fᵉ gᵉ
  pr1ᵉ (map-standard-pullbackᵉ (hAᵉ ,ᵉ _) (a'ᵉ ,ᵉ _)) = hAᵉ a'ᵉ
  pr1ᵉ (pr2ᵉ (map-standard-pullbackᵉ (hAᵉ ,ᵉ hBᵉ ,ᵉ _) (a'ᵉ ,ᵉ b'ᵉ ,ᵉ _))) = hBᵉ b'ᵉ
  pr2ᵉ (pr2ᵉ (map-standard-pullbackᵉ (hAᵉ ,ᵉ hBᵉ ,ᵉ hXᵉ ,ᵉ HAᵉ ,ᵉ HBᵉ) (a'ᵉ ,ᵉ b'ᵉ ,ᵉ p'ᵉ))) =
    HAᵉ a'ᵉ ∙ᵉ apᵉ hXᵉ p'ᵉ ∙ᵉ invᵉ (HBᵉ b'ᵉ)

  map-is-pullbackᵉ :
    {l4ᵉ l4'ᵉ : Level} {Cᵉ : UUᵉ l4ᵉ} {C'ᵉ : UUᵉ l4'ᵉ} →
    (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ f'ᵉ g'ᵉ C'ᵉ) →
    is-pullbackᵉ fᵉ gᵉ cᵉ → is-pullbackᵉ f'ᵉ g'ᵉ c'ᵉ →
    hom-cospan-diagramᵉ f'ᵉ g'ᵉ fᵉ gᵉ → C'ᵉ → Cᵉ
  map-is-pullbackᵉ cᵉ c'ᵉ is-pb-cᵉ is-pb-c'ᵉ hᵉ xᵉ =
    map-inv-is-equivᵉ is-pb-cᵉ (map-standard-pullbackᵉ hᵉ (gapᵉ f'ᵉ g'ᵉ c'ᵉ xᵉ))
```

## Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}