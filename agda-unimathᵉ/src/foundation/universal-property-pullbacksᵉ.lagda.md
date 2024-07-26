# The universal property of pullbacks

```agda
module foundation.universal-property-pullbacksᵉ where

open import foundation-core.universal-property-pullbacksᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.pullbacksᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "universalᵉ propertyᵉ ofᵉ pullbacks"ᵉ Disambiguation="types"ᵉ}}
describesᵉ theᵉ optimalᵉ wayᵉ to completeᵉ aᵉ diagramᵉ ofᵉ theᵉ formᵉ

```text
           Bᵉ
           |
           |
           ∨ᵉ
  Aᵉ ----->ᵉ Xᵉ
```

to aᵉ squareᵉ

```text
  Cᵉ ----->ᵉ Bᵉ
  | ⌟ᵉ      |
  |        |
  ∨ᵉ        ∨ᵉ
  Aᵉ ----->ᵉ X.ᵉ
```

## Properties

### Unique uniqueness of pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) {Cᵉ : UUᵉ l4ᵉ} {C'ᵉ : UUᵉ l5ᵉ}
  where

  abstract
    uniquely-unique-universal-property-pullbackᵉ :
      ( c'ᵉ : coneᵉ fᵉ gᵉ C'ᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
      ( up-c'ᵉ : universal-property-pullbackᵉ fᵉ gᵉ c'ᵉ) →
      ( up-cᵉ : universal-property-pullbackᵉ fᵉ gᵉ cᵉ) →
      is-contrᵉ
        ( Σᵉ (C'ᵉ ≃ᵉ Cᵉ) (λ eᵉ → htpy-coneᵉ fᵉ gᵉ (cone-mapᵉ fᵉ gᵉ cᵉ (map-equivᵉ eᵉ)) c'ᵉ))
    uniquely-unique-universal-property-pullbackᵉ c'ᵉ cᵉ up-c'ᵉ up-cᵉ =
      is-torsorial-Eq-subtypeᵉ
        ( uniqueness-universal-property-pullbackᵉ fᵉ gᵉ cᵉ up-cᵉ C'ᵉ c'ᵉ)
        ( is-property-is-equivᵉ)
        ( map-universal-property-pullbackᵉ fᵉ gᵉ cᵉ up-cᵉ c'ᵉ)
        ( htpy-cone-map-universal-property-pullbackᵉ fᵉ gᵉ cᵉ up-cᵉ c'ᵉ)
        ( is-equiv-up-pullback-up-pullbackᵉ cᵉ c'ᵉ
          ( map-universal-property-pullbackᵉ fᵉ gᵉ cᵉ up-cᵉ c'ᵉ)
          ( htpy-cone-map-universal-property-pullbackᵉ fᵉ gᵉ cᵉ up-cᵉ c'ᵉ)
          up-cᵉ up-c'ᵉ)
```

### The horizontal pullback pasting property

Givenᵉ aᵉ diagramᵉ

```text
  ∙ᵉ ------->ᵉ ∙ᵉ ------->ᵉ ∙ᵉ
  |          | ⌟ᵉ        |
  |          |          |
  ∨ᵉ          ∨ᵉ          ∨ᵉ
  ∙ᵉ ------->ᵉ ∙ᵉ ------->ᵉ ∙ᵉ
```

where theᵉ right-handᵉ squareᵉ isᵉ aᵉ pullback,ᵉ thenᵉ theᵉ left-handᵉ squareᵉ isᵉ aᵉ
pullbackᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ compositeᵉ squareᵉ is.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  (iᵉ : Xᵉ → Yᵉ) (jᵉ : Yᵉ → Zᵉ) (hᵉ : Cᵉ → Zᵉ)
  where

  abstract
    universal-property-pullback-rectangle-universal-property-pullback-left-squareᵉ :
      (cᵉ : coneᵉ jᵉ hᵉ Bᵉ) (dᵉ : coneᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) Aᵉ) →
      universal-property-pullbackᵉ jᵉ hᵉ cᵉ →
      universal-property-pullbackᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) dᵉ →
      universal-property-pullbackᵉ (jᵉ ∘ᵉ iᵉ) hᵉ (pasting-horizontal-coneᵉ iᵉ jᵉ hᵉ cᵉ dᵉ)
    universal-property-pullback-rectangle-universal-property-pullback-left-squareᵉ
      cᵉ dᵉ up-pb-cᵉ up-pb-dᵉ =
      universal-property-pullback-is-pullbackᵉ (jᵉ ∘ᵉ iᵉ) hᵉ
        ( pasting-horizontal-coneᵉ iᵉ jᵉ hᵉ cᵉ dᵉ)
        ( is-pullback-rectangle-is-pullback-left-squareᵉ iᵉ jᵉ hᵉ cᵉ dᵉ
          ( is-pullback-universal-property-pullbackᵉ jᵉ hᵉ cᵉ up-pb-cᵉ)
          ( is-pullback-universal-property-pullbackᵉ iᵉ
            ( vertical-map-coneᵉ jᵉ hᵉ cᵉ) dᵉ up-pb-dᵉ))

  abstract
    universal-property-pullback-left-square-universal-property-pullback-rectangleᵉ :
      (cᵉ : coneᵉ jᵉ hᵉ Bᵉ) (dᵉ : coneᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) Aᵉ) →
      universal-property-pullbackᵉ jᵉ hᵉ cᵉ →
      universal-property-pullbackᵉ (jᵉ ∘ᵉ iᵉ) hᵉ
        ( pasting-horizontal-coneᵉ iᵉ jᵉ hᵉ cᵉ dᵉ) →
      universal-property-pullbackᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) dᵉ
    universal-property-pullback-left-square-universal-property-pullback-rectangleᵉ
      cᵉ dᵉ up-pb-cᵉ up-pb-rectᵉ =
      universal-property-pullback-is-pullbackᵉ
        ( iᵉ)
        ( vertical-map-coneᵉ jᵉ hᵉ cᵉ)
        ( dᵉ)
        ( is-pullback-left-square-is-pullback-rectangleᵉ iᵉ jᵉ hᵉ cᵉ dᵉ
          ( is-pullback-universal-property-pullbackᵉ jᵉ hᵉ cᵉ up-pb-cᵉ)
          ( is-pullback-universal-property-pullbackᵉ (jᵉ ∘ᵉ iᵉ) hᵉ
            ( pasting-horizontal-coneᵉ iᵉ jᵉ hᵉ cᵉ dᵉ) up-pb-rectᵉ))
```

### The vertical pullback pasting property

Givenᵉ aᵉ diagramᵉ

```text
  ∙ᵉ ------->ᵉ ∙ᵉ
  |          |
  |          |
  ∨ᵉ          ∨ᵉ
  ∙ᵉ ------->ᵉ ∙ᵉ
  | ⌟ᵉ        |
  |          |
  ∨ᵉ          ∨ᵉ
  ∙ᵉ ------->ᵉ ∙ᵉ
```

where theᵉ bottomᵉ squareᵉ isᵉ aᵉ pullback,ᵉ thenᵉ theᵉ topᵉ squareᵉ isᵉ aᵉ pullbackᵉ ifᵉ andᵉ
onlyᵉ ifᵉ theᵉ compositeᵉ squareᵉ is.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  (fᵉ : Cᵉ → Zᵉ) (gᵉ : Yᵉ → Zᵉ) (hᵉ : Xᵉ → Yᵉ)
  where

  abstract
    universal-property-pullback-top-universal-property-pullback-rectangleᵉ :
      (cᵉ : coneᵉ fᵉ gᵉ Bᵉ) (dᵉ : coneᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) hᵉ Aᵉ) →
      universal-property-pullbackᵉ fᵉ gᵉ cᵉ →
      universal-property-pullbackᵉ fᵉ (gᵉ ∘ᵉ hᵉ) (pasting-vertical-coneᵉ fᵉ gᵉ hᵉ cᵉ dᵉ) →
      universal-property-pullbackᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) hᵉ dᵉ
    universal-property-pullback-top-universal-property-pullback-rectangleᵉ
      cᵉ dᵉ up-pb-cᵉ up-pb-dcᵉ =
      universal-property-pullback-is-pullbackᵉ
        ( horizontal-map-coneᵉ fᵉ gᵉ cᵉ)
        ( hᵉ)
        ( dᵉ)
        ( is-pullback-top-square-is-pullback-rectangleᵉ fᵉ gᵉ hᵉ cᵉ dᵉ
          ( is-pullback-universal-property-pullbackᵉ fᵉ gᵉ cᵉ up-pb-cᵉ)
          ( is-pullback-universal-property-pullbackᵉ fᵉ (gᵉ ∘ᵉ hᵉ)
            ( pasting-vertical-coneᵉ fᵉ gᵉ hᵉ cᵉ dᵉ)
            ( up-pb-dcᵉ)))

  abstract
    universal-property-pullback-rectangle-universal-property-pullback-topᵉ :
      (cᵉ : coneᵉ fᵉ gᵉ Bᵉ) (dᵉ : coneᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) hᵉ Aᵉ) →
      universal-property-pullbackᵉ fᵉ gᵉ cᵉ →
      universal-property-pullbackᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) hᵉ dᵉ →
      universal-property-pullbackᵉ fᵉ (gᵉ ∘ᵉ hᵉ) (pasting-vertical-coneᵉ fᵉ gᵉ hᵉ cᵉ dᵉ)
    universal-property-pullback-rectangle-universal-property-pullback-topᵉ
      cᵉ dᵉ up-pb-cᵉ up-pb-dᵉ =
      universal-property-pullback-is-pullbackᵉ
        ( fᵉ)
        ( gᵉ ∘ᵉ hᵉ)
        ( pasting-vertical-coneᵉ fᵉ gᵉ hᵉ cᵉ dᵉ)
        ( is-pullback-rectangle-is-pullback-top-squareᵉ fᵉ gᵉ hᵉ cᵉ dᵉ
          ( is-pullback-universal-property-pullbackᵉ fᵉ gᵉ cᵉ up-pb-cᵉ)
          ( is-pullback-universal-property-pullbackᵉ
            ( horizontal-map-coneᵉ fᵉ gᵉ cᵉ)
            ( hᵉ)
            ( dᵉ)
            ( up-pb-dᵉ)))
```

## Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}