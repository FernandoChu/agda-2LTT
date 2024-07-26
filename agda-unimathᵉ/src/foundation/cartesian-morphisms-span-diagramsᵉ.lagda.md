# Cartesian morphisms of span diagrams

```agda
module foundation.cartesian-morphisms-span-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-morphisms-arrowsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.morphisms-span-diagramsᵉ
open import foundation.span-diagramsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [morphism](foundation.morphisms-span-diagrams.mdᵉ) `αᵉ : 𝒮ᵉ → 𝒯`ᵉ ofᵉ
[spanᵉ diagrams](foundation.span-diagrams.mdᵉ) isᵉ saidᵉ to beᵉ
{{#conceptᵉ "cartesian"ᵉ Disambiguation="morphismᵉ ofᵉ spanᵉ diagrams"ᵉ Agda=is-cartesian-hom-span-diagramᵉ}}
ifᵉ theᵉ twoᵉ squaresᵉ in theᵉ diagramᵉ

```text
       hᵉ       kᵉ
  Cᵉ <-----ᵉ Tᵉ ----->ᵉ Dᵉ
  |      ⌞ᵉ | ⌟ᵉ      |
  |        |        |
  ∨ᵉ        ∨ᵉ        ∨ᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
       fᵉ       gᵉ
```

areᵉ [pullbackᵉ squares](foundation-core.pullbacks.md).ᵉ

## Definitions

### The predicate of being a left cartesian morphism of span diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  (𝒯ᵉ : span-diagramᵉ l4ᵉ l5ᵉ l6ᵉ) (αᵉ : hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ)
  where

  is-left-cartesian-hom-span-diagramᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l6ᵉ)
  is-left-cartesian-hom-span-diagramᵉ =
    is-cartesian-hom-arrowᵉ
      ( left-map-span-diagramᵉ 𝒮ᵉ)
      ( left-map-span-diagramᵉ 𝒯ᵉ)
      ( left-hom-arrow-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ αᵉ)
```

### Left cartesian morphisms of span diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  (𝒯ᵉ : span-diagramᵉ l4ᵉ l5ᵉ l6ᵉ)
  where

  left-cartesian-hom-span-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  left-cartesian-hom-span-diagramᵉ =
    Σᵉ (hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ) (is-left-cartesian-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ)

  module _
    (hᵉ : left-cartesian-hom-span-diagramᵉ)
    where

    hom-left-cartesian-hom-span-diagramᵉ : hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ
    hom-left-cartesian-hom-span-diagramᵉ = pr1ᵉ hᵉ

    map-domain-left-cartesian-hom-span-diagramᵉ :
      domain-span-diagramᵉ 𝒮ᵉ → domain-span-diagramᵉ 𝒯ᵉ
    map-domain-left-cartesian-hom-span-diagramᵉ =
      map-domain-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-left-cartesian-hom-span-diagramᵉ

    map-codomain-left-cartesian-hom-span-diagramᵉ :
      codomain-span-diagramᵉ 𝒮ᵉ → codomain-span-diagramᵉ 𝒯ᵉ
    map-codomain-left-cartesian-hom-span-diagramᵉ =
      map-codomain-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-left-cartesian-hom-span-diagramᵉ

    spanning-map-left-cartesian-hom-span-diagramᵉ :
      spanning-type-span-diagramᵉ 𝒮ᵉ → spanning-type-span-diagramᵉ 𝒯ᵉ
    spanning-map-left-cartesian-hom-span-diagramᵉ =
      spanning-map-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-left-cartesian-hom-span-diagramᵉ

    left-square-left-cartesian-hom-span-diagramᵉ :
      coherence-square-mapsᵉ
        ( spanning-map-left-cartesian-hom-span-diagramᵉ)
        ( left-map-span-diagramᵉ 𝒮ᵉ)
        ( left-map-span-diagramᵉ 𝒯ᵉ)
        ( map-domain-left-cartesian-hom-span-diagramᵉ)
    left-square-left-cartesian-hom-span-diagramᵉ =
      left-square-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-left-cartesian-hom-span-diagramᵉ

    left-hom-arrow-left-cartesian-hom-span-diagramᵉ :
      hom-arrowᵉ (left-map-span-diagramᵉ 𝒮ᵉ) (left-map-span-diagramᵉ 𝒯ᵉ)
    left-hom-arrow-left-cartesian-hom-span-diagramᵉ =
      left-hom-arrow-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-left-cartesian-hom-span-diagramᵉ

    right-square-left-cartesian-hom-span-diagramᵉ :
      coherence-square-mapsᵉ
        ( spanning-map-left-cartesian-hom-span-diagramᵉ)
        ( right-map-span-diagramᵉ 𝒮ᵉ)
        ( right-map-span-diagramᵉ 𝒯ᵉ)
        ( map-codomain-left-cartesian-hom-span-diagramᵉ)
    right-square-left-cartesian-hom-span-diagramᵉ =
      right-square-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-left-cartesian-hom-span-diagramᵉ

    right-hom-arrow-left-cartesian-hom-span-diagramᵉ :
      hom-arrowᵉ (right-map-span-diagramᵉ 𝒮ᵉ) (right-map-span-diagramᵉ 𝒯ᵉ)
    right-hom-arrow-left-cartesian-hom-span-diagramᵉ =
      right-hom-arrow-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-left-cartesian-hom-span-diagramᵉ

    is-left-cartesian-left-cartesian-hom-span-diagramᵉ :
      is-left-cartesian-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-left-cartesian-hom-span-diagramᵉ
    is-left-cartesian-left-cartesian-hom-span-diagramᵉ = pr2ᵉ hᵉ
```

### The predicate of being a right cartesian morphism of span diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  (𝒯ᵉ : span-diagramᵉ l4ᵉ l5ᵉ l6ᵉ) (αᵉ : hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ)
  where

  is-right-cartesian-hom-span-diagramᵉ : UUᵉ (l2ᵉ ⊔ l3ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  is-right-cartesian-hom-span-diagramᵉ =
    is-cartesian-hom-arrowᵉ
      ( right-map-span-diagramᵉ 𝒮ᵉ)
      ( right-map-span-diagramᵉ 𝒯ᵉ)
      ( right-hom-arrow-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ αᵉ)
```

### Right cartesian morphisms of span diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  (𝒯ᵉ : span-diagramᵉ l4ᵉ l5ᵉ l6ᵉ)
  where

  right-cartesian-hom-span-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  right-cartesian-hom-span-diagramᵉ =
    Σᵉ (hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ) (is-right-cartesian-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ)

  module _
    (hᵉ : right-cartesian-hom-span-diagramᵉ)
    where

    hom-right-cartesian-hom-span-diagramᵉ : hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ
    hom-right-cartesian-hom-span-diagramᵉ = pr1ᵉ hᵉ

    map-domain-right-cartesian-hom-span-diagramᵉ :
      domain-span-diagramᵉ 𝒮ᵉ → domain-span-diagramᵉ 𝒯ᵉ
    map-domain-right-cartesian-hom-span-diagramᵉ =
      map-domain-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-right-cartesian-hom-span-diagramᵉ

    map-codomain-right-cartesian-hom-span-diagramᵉ :
      codomain-span-diagramᵉ 𝒮ᵉ → codomain-span-diagramᵉ 𝒯ᵉ
    map-codomain-right-cartesian-hom-span-diagramᵉ =
      map-codomain-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-right-cartesian-hom-span-diagramᵉ

    spanning-map-right-cartesian-hom-span-diagramᵉ :
      spanning-type-span-diagramᵉ 𝒮ᵉ → spanning-type-span-diagramᵉ 𝒯ᵉ
    spanning-map-right-cartesian-hom-span-diagramᵉ =
      spanning-map-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-right-cartesian-hom-span-diagramᵉ

    left-square-right-cartesian-hom-span-diagramᵉ :
      coherence-square-mapsᵉ
        ( spanning-map-right-cartesian-hom-span-diagramᵉ)
        ( left-map-span-diagramᵉ 𝒮ᵉ)
        ( left-map-span-diagramᵉ 𝒯ᵉ)
        ( map-domain-right-cartesian-hom-span-diagramᵉ)
    left-square-right-cartesian-hom-span-diagramᵉ =
      left-square-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-right-cartesian-hom-span-diagramᵉ

    left-hom-arrow-right-cartesian-hom-span-diagramᵉ :
      hom-arrowᵉ (left-map-span-diagramᵉ 𝒮ᵉ) (left-map-span-diagramᵉ 𝒯ᵉ)
    left-hom-arrow-right-cartesian-hom-span-diagramᵉ =
      left-hom-arrow-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-right-cartesian-hom-span-diagramᵉ

    right-square-right-cartesian-hom-span-diagramᵉ :
      coherence-square-mapsᵉ
        ( spanning-map-right-cartesian-hom-span-diagramᵉ)
        ( right-map-span-diagramᵉ 𝒮ᵉ)
        ( right-map-span-diagramᵉ 𝒯ᵉ)
        ( map-codomain-right-cartesian-hom-span-diagramᵉ)
    right-square-right-cartesian-hom-span-diagramᵉ =
      right-square-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-right-cartesian-hom-span-diagramᵉ

    right-hom-arrow-right-cartesian-hom-span-diagramᵉ :
      hom-arrowᵉ (right-map-span-diagramᵉ 𝒮ᵉ) (right-map-span-diagramᵉ 𝒯ᵉ)
    right-hom-arrow-right-cartesian-hom-span-diagramᵉ =
      right-hom-arrow-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-right-cartesian-hom-span-diagramᵉ

    is-right-cartesian-right-cartesian-hom-span-diagramᵉ :
      is-right-cartesian-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ
        ( hom-right-cartesian-hom-span-diagramᵉ)
    is-right-cartesian-right-cartesian-hom-span-diagramᵉ = pr2ᵉ hᵉ
```

### The predicate of being a cartesian morphism of span diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  (𝒯ᵉ : span-diagramᵉ l4ᵉ l5ᵉ l6ᵉ) (αᵉ : hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ)
  where

  is-cartesian-hom-span-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  is-cartesian-hom-span-diagramᵉ =
    is-left-cartesian-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ αᵉ ×ᵉ
    is-right-cartesian-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ αᵉ
```

### Cartesian morphisms of span diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  (𝒯ᵉ : span-diagramᵉ l4ᵉ l5ᵉ l6ᵉ)
  where

  cartesian-hom-span-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  cartesian-hom-span-diagramᵉ =
    Σᵉ (hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ) (is-cartesian-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ)

  module _
    (hᵉ : cartesian-hom-span-diagramᵉ)
    where

    hom-cartesian-hom-span-diagramᵉ : hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ
    hom-cartesian-hom-span-diagramᵉ = pr1ᵉ hᵉ

    map-domain-cartesian-hom-span-diagramᵉ :
      domain-span-diagramᵉ 𝒮ᵉ → domain-span-diagramᵉ 𝒯ᵉ
    map-domain-cartesian-hom-span-diagramᵉ =
      map-domain-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-cartesian-hom-span-diagramᵉ

    map-codomain-cartesian-hom-span-diagramᵉ :
      codomain-span-diagramᵉ 𝒮ᵉ → codomain-span-diagramᵉ 𝒯ᵉ
    map-codomain-cartesian-hom-span-diagramᵉ =
      map-codomain-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-cartesian-hom-span-diagramᵉ

    spanning-map-cartesian-hom-span-diagramᵉ :
      spanning-type-span-diagramᵉ 𝒮ᵉ → spanning-type-span-diagramᵉ 𝒯ᵉ
    spanning-map-cartesian-hom-span-diagramᵉ =
      spanning-map-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-cartesian-hom-span-diagramᵉ

    left-square-cartesian-hom-span-diagramᵉ :
      coherence-square-mapsᵉ
        ( spanning-map-cartesian-hom-span-diagramᵉ)
        ( left-map-span-diagramᵉ 𝒮ᵉ)
        ( left-map-span-diagramᵉ 𝒯ᵉ)
        ( map-domain-cartesian-hom-span-diagramᵉ)
    left-square-cartesian-hom-span-diagramᵉ =
      left-square-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-cartesian-hom-span-diagramᵉ

    left-hom-arrow-cartesian-hom-span-diagramᵉ :
      hom-arrowᵉ (left-map-span-diagramᵉ 𝒮ᵉ) (left-map-span-diagramᵉ 𝒯ᵉ)
    left-hom-arrow-cartesian-hom-span-diagramᵉ =
      left-hom-arrow-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-cartesian-hom-span-diagramᵉ

    right-square-cartesian-hom-span-diagramᵉ :
      coherence-square-mapsᵉ
        ( spanning-map-cartesian-hom-span-diagramᵉ)
        ( right-map-span-diagramᵉ 𝒮ᵉ)
        ( right-map-span-diagramᵉ 𝒯ᵉ)
        ( map-codomain-cartesian-hom-span-diagramᵉ)
    right-square-cartesian-hom-span-diagramᵉ =
      right-square-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-cartesian-hom-span-diagramᵉ

    right-hom-arrow-cartesian-hom-span-diagramᵉ :
      hom-arrowᵉ (right-map-span-diagramᵉ 𝒮ᵉ) (right-map-span-diagramᵉ 𝒯ᵉ)
    right-hom-arrow-cartesian-hom-span-diagramᵉ =
      right-hom-arrow-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-cartesian-hom-span-diagramᵉ

    is-cartesian-cartesian-hom-span-diagramᵉ :
      is-cartesian-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-cartesian-hom-span-diagramᵉ
    is-cartesian-cartesian-hom-span-diagramᵉ = pr2ᵉ hᵉ

    is-left-cartesian-cartesian-hom-span-diagramᵉ :
      is-left-cartesian-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-cartesian-hom-span-diagramᵉ
    is-left-cartesian-cartesian-hom-span-diagramᵉ =
      pr1ᵉ is-cartesian-cartesian-hom-span-diagramᵉ

    left-cartesian-hom-arrow-cartesian-hom-span-diagramᵉ :
      cartesian-hom-arrowᵉ
        ( left-map-span-diagramᵉ 𝒮ᵉ)
        ( left-map-span-diagramᵉ 𝒯ᵉ)
    pr1ᵉ left-cartesian-hom-arrow-cartesian-hom-span-diagramᵉ =
      left-hom-arrow-cartesian-hom-span-diagramᵉ
    pr2ᵉ left-cartesian-hom-arrow-cartesian-hom-span-diagramᵉ =
      is-left-cartesian-cartesian-hom-span-diagramᵉ

    is-right-cartesian-cartesian-hom-span-diagramᵉ :
      is-right-cartesian-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-cartesian-hom-span-diagramᵉ
    is-right-cartesian-cartesian-hom-span-diagramᵉ =
      pr2ᵉ is-cartesian-cartesian-hom-span-diagramᵉ

    right-cartesian-hom-arrow-cartesian-hom-span-diagramᵉ :
      cartesian-hom-arrowᵉ
        ( right-map-span-diagramᵉ 𝒮ᵉ)
        ( right-map-span-diagramᵉ 𝒯ᵉ)
    pr1ᵉ right-cartesian-hom-arrow-cartesian-hom-span-diagramᵉ =
      right-hom-arrow-cartesian-hom-span-diagramᵉ
    pr2ᵉ right-cartesian-hom-arrow-cartesian-hom-span-diagramᵉ =
      is-right-cartesian-cartesian-hom-span-diagramᵉ
```