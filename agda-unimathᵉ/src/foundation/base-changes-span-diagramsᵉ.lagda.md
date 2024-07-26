# Base changes of span diagrams

```agda
module foundation.base-changes-span-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-morphisms-arrowsᵉ
open import foundation.cartesian-morphisms-span-diagramsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.morphisms-span-diagramsᵉ
open import foundation.span-diagramsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Considerᵉ aᵉ [spanᵉ diagram](foundation.span-diagrams.mdᵉ) `𝒮ᵉ :=ᵉ (Aᵉ <-f-ᵉ Sᵉ -g->ᵉ B)`.ᵉ
Aᵉ
{{#conceptᵉ "baseᵉ change"ᵉ Disambiguation="spanᵉ diagram"ᵉ Agda=base-change-span-diagramᵉ}}
ofᵉ `𝒮`ᵉ consistsᵉ ofᵉ aᵉ spanᵉ diagramᵉ `𝒯`ᵉ andᵉ aᵉ
[cartesianᵉ morphism](foundation.cartesian-morphisms-span-diagrams.mdᵉ) ofᵉ spanᵉ
diagramsᵉ `𝒯ᵉ → 𝒮`.ᵉ

## Definitions

### Base changes of span diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (l4ᵉ l5ᵉ l6ᵉ : Level) (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  base-change-span-diagramᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ lsuc l4ᵉ ⊔ lsuc l5ᵉ ⊔ lsuc l6ᵉ)
  base-change-span-diagramᵉ =
    Σᵉ (span-diagramᵉ l4ᵉ l5ᵉ l6ᵉ) (λ 𝒯ᵉ → cartesian-hom-span-diagramᵉ 𝒯ᵉ 𝒮ᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  (fᵉ : base-change-span-diagramᵉ l4ᵉ l5ᵉ l6ᵉ 𝒮ᵉ)
  where

  span-diagram-base-change-span-diagramᵉ : span-diagramᵉ l4ᵉ l5ᵉ l6ᵉ
  span-diagram-base-change-span-diagramᵉ = pr1ᵉ fᵉ

  domain-span-diagram-base-change-span-diagramᵉ : UUᵉ l4ᵉ
  domain-span-diagram-base-change-span-diagramᵉ =
    domain-span-diagramᵉ span-diagram-base-change-span-diagramᵉ

  codomain-span-diagram-base-change-span-diagramᵉ : UUᵉ l5ᵉ
  codomain-span-diagram-base-change-span-diagramᵉ =
    codomain-span-diagramᵉ span-diagram-base-change-span-diagramᵉ

  spanning-type-span-diagram-base-change-span-diagramᵉ : UUᵉ l6ᵉ
  spanning-type-span-diagram-base-change-span-diagramᵉ =
    spanning-type-span-diagramᵉ span-diagram-base-change-span-diagramᵉ

  left-map-span-diagram-base-change-span-diagramᵉ :
    spanning-type-span-diagram-base-change-span-diagramᵉ →
    domain-span-diagram-base-change-span-diagramᵉ
  left-map-span-diagram-base-change-span-diagramᵉ =
    left-map-span-diagramᵉ span-diagram-base-change-span-diagramᵉ

  right-map-span-diagram-base-change-span-diagramᵉ :
    spanning-type-span-diagram-base-change-span-diagramᵉ →
    codomain-span-diagram-base-change-span-diagramᵉ
  right-map-span-diagram-base-change-span-diagramᵉ =
    right-map-span-diagramᵉ span-diagram-base-change-span-diagramᵉ

  cartesian-hom-base-change-span-diagramᵉ :
    cartesian-hom-span-diagramᵉ span-diagram-base-change-span-diagramᵉ 𝒮ᵉ
  cartesian-hom-base-change-span-diagramᵉ = pr2ᵉ fᵉ

  hom-cartesian-hom-base-change-span-diagramᵉ :
    hom-span-diagramᵉ span-diagram-base-change-span-diagramᵉ 𝒮ᵉ
  hom-cartesian-hom-base-change-span-diagramᵉ =
    hom-cartesian-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( cartesian-hom-base-change-span-diagramᵉ)

  map-domain-cartesian-hom-base-change-span-diagramᵉ :
    domain-span-diagramᵉ span-diagram-base-change-span-diagramᵉ →
    domain-span-diagramᵉ 𝒮ᵉ
  map-domain-cartesian-hom-base-change-span-diagramᵉ =
    map-domain-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( hom-cartesian-hom-base-change-span-diagramᵉ)

  map-codomain-cartesian-hom-base-change-span-diagramᵉ :
    codomain-span-diagramᵉ span-diagram-base-change-span-diagramᵉ →
    codomain-span-diagramᵉ 𝒮ᵉ
  map-codomain-cartesian-hom-base-change-span-diagramᵉ =
    map-codomain-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( hom-cartesian-hom-base-change-span-diagramᵉ)

  spanning-map-cartesian-hom-base-change-span-diagramᵉ :
    spanning-type-span-diagramᵉ span-diagram-base-change-span-diagramᵉ →
    spanning-type-span-diagramᵉ 𝒮ᵉ
  spanning-map-cartesian-hom-base-change-span-diagramᵉ =
    spanning-map-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( hom-cartesian-hom-base-change-span-diagramᵉ)

  left-square-cartesian-hom-base-change-span-diagramᵉ :
    coherence-square-mapsᵉ
      ( spanning-map-cartesian-hom-base-change-span-diagramᵉ)
      ( left-map-span-diagramᵉ span-diagram-base-change-span-diagramᵉ)
      ( left-map-span-diagramᵉ 𝒮ᵉ)
      ( map-domain-cartesian-hom-base-change-span-diagramᵉ)
  left-square-cartesian-hom-base-change-span-diagramᵉ =
    left-square-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( hom-cartesian-hom-base-change-span-diagramᵉ)

  left-hom-arrow-cartesian-hom-base-change-span-diagramᵉ :
    hom-arrowᵉ
      ( left-map-span-diagramᵉ span-diagram-base-change-span-diagramᵉ)
      ( left-map-span-diagramᵉ 𝒮ᵉ)
  left-hom-arrow-cartesian-hom-base-change-span-diagramᵉ =
    left-hom-arrow-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( hom-cartesian-hom-base-change-span-diagramᵉ)

  right-square-cartesian-hom-base-change-span-diagramᵉ :
    coherence-square-mapsᵉ
      ( spanning-map-cartesian-hom-base-change-span-diagramᵉ)
      ( right-map-span-diagramᵉ span-diagram-base-change-span-diagramᵉ)
      ( right-map-span-diagramᵉ 𝒮ᵉ)
      ( map-codomain-cartesian-hom-base-change-span-diagramᵉ)
  right-square-cartesian-hom-base-change-span-diagramᵉ =
    right-square-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( hom-cartesian-hom-base-change-span-diagramᵉ)

  right-hom-arrow-cartesian-hom-base-change-span-diagramᵉ :
    hom-arrowᵉ
      ( right-map-span-diagramᵉ span-diagram-base-change-span-diagramᵉ)
      ( right-map-span-diagramᵉ 𝒮ᵉ)
  right-hom-arrow-cartesian-hom-base-change-span-diagramᵉ =
    right-hom-arrow-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( hom-cartesian-hom-base-change-span-diagramᵉ)

  is-cartesian-cartesian-hom-base-change-span-diagramᵉ :
    is-cartesian-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( hom-cartesian-hom-base-change-span-diagramᵉ)
  is-cartesian-cartesian-hom-base-change-span-diagramᵉ =
    is-cartesian-cartesian-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( cartesian-hom-base-change-span-diagramᵉ)

  is-left-cartesian-cartesian-hom-base-change-span-diagramᵉ :
    is-left-cartesian-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( hom-cartesian-hom-base-change-span-diagramᵉ)
  is-left-cartesian-cartesian-hom-base-change-span-diagramᵉ =
    is-left-cartesian-cartesian-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( cartesian-hom-base-change-span-diagramᵉ)

  left-cartesian-hom-arrow-cartesian-hom-base-change-span-diagramᵉ :
    cartesian-hom-arrowᵉ
      ( left-map-span-diagramᵉ span-diagram-base-change-span-diagramᵉ)
      ( left-map-span-diagramᵉ 𝒮ᵉ)
  left-cartesian-hom-arrow-cartesian-hom-base-change-span-diagramᵉ =
    left-cartesian-hom-arrow-cartesian-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( cartesian-hom-base-change-span-diagramᵉ)

  is-right-cartesian-cartesian-hom-base-change-span-diagramᵉ :
    is-right-cartesian-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( hom-cartesian-hom-base-change-span-diagramᵉ)
  is-right-cartesian-cartesian-hom-base-change-span-diagramᵉ =
    is-right-cartesian-cartesian-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( cartesian-hom-base-change-span-diagramᵉ)

  right-cartesian-hom-arrow-cartesian-hom-base-change-span-diagramᵉ :
    cartesian-hom-arrowᵉ
      ( right-map-span-diagramᵉ span-diagram-base-change-span-diagramᵉ)
      ( right-map-span-diagramᵉ 𝒮ᵉ)
  right-cartesian-hom-arrow-cartesian-hom-base-change-span-diagramᵉ =
    right-cartesian-hom-arrow-cartesian-hom-span-diagramᵉ
      ( span-diagram-base-change-span-diagramᵉ)
      ( 𝒮ᵉ)
      ( cartesian-hom-base-change-span-diagramᵉ)
```