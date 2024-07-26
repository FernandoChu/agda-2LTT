# Commuting hexagons of identifications

```agda
module foundation.commuting-hexagons-of-identificationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Aᵉ hexagonᵉ ofᵉ identificationsᵉ isᵉ anᵉ identificationᵉ
`((αᵉ ∙ᵉ βᵉ) ∙ᵉ γᵉ) ＝ᵉ (δᵉ ∙ᵉ (εᵉ ∙ᵉ ζ))`.ᵉ

## Definition

### Hexagons of identifications

```agda
coherence-hexagonᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ uᵉ u'ᵉ vᵉ v'ᵉ yᵉ : Aᵉ}
  (αᵉ : xᵉ ＝ᵉ uᵉ) (βᵉ : uᵉ ＝ᵉ u'ᵉ) (γᵉ : u'ᵉ ＝ᵉ yᵉ)
  (δᵉ : xᵉ ＝ᵉ vᵉ) (εᵉ : vᵉ ＝ᵉ v'ᵉ) (ζᵉ : v'ᵉ ＝ᵉ yᵉ) → UUᵉ lᵉ
coherence-hexagonᵉ αᵉ βᵉ γᵉ δᵉ εᵉ ζᵉ = ((αᵉ ∙ᵉ βᵉ) ∙ᵉ γᵉ) ＝ᵉ (δᵉ ∙ᵉ (εᵉ ∙ᵉ ζᵉ))
```

### Symmetries of hexagons of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ uᵉ u'ᵉ vᵉ v'ᵉ yᵉ : Aᵉ}
  where

  hexagon-rotate-120ᵉ :
    (αᵉ : xᵉ ＝ᵉ uᵉ) (βᵉ : uᵉ ＝ᵉ u'ᵉ) (γᵉ : u'ᵉ ＝ᵉ yᵉ)
    (δᵉ : xᵉ ＝ᵉ vᵉ) (εᵉ : vᵉ ＝ᵉ v'ᵉ) (ζᵉ : v'ᵉ ＝ᵉ yᵉ) →
    coherence-hexagonᵉ αᵉ βᵉ γᵉ δᵉ εᵉ ζᵉ →
    coherence-hexagonᵉ (invᵉ εᵉ) (invᵉ δᵉ) αᵉ ζᵉ (invᵉ γᵉ) (invᵉ βᵉ)
  hexagon-rotate-120ᵉ reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ .reflᵉ reflᵉ = reflᵉ

  hexagon-rotate-240ᵉ :
    (αᵉ : xᵉ ＝ᵉ uᵉ) (βᵉ : uᵉ ＝ᵉ u'ᵉ) (γᵉ : u'ᵉ ＝ᵉ yᵉ)
    (δᵉ : xᵉ ＝ᵉ vᵉ) (εᵉ : vᵉ ＝ᵉ v'ᵉ) (ζᵉ : v'ᵉ ＝ᵉ yᵉ) →
    coherence-hexagonᵉ αᵉ βᵉ γᵉ δᵉ εᵉ ζᵉ →
    coherence-hexagonᵉ γᵉ (invᵉ ζᵉ) (invᵉ εᵉ) (invᵉ βᵉ) (invᵉ αᵉ) δᵉ
  hexagon-rotate-240ᵉ reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ .reflᵉ reflᵉ = reflᵉ

  hexagon-mirror-Aᵉ :
    (αᵉ : xᵉ ＝ᵉ uᵉ) (βᵉ : uᵉ ＝ᵉ u'ᵉ) (γᵉ : u'ᵉ ＝ᵉ yᵉ)
    (δᵉ : xᵉ ＝ᵉ vᵉ) (εᵉ : vᵉ ＝ᵉ v'ᵉ) (ζᵉ : v'ᵉ ＝ᵉ yᵉ) →
    coherence-hexagonᵉ αᵉ βᵉ γᵉ δᵉ εᵉ ζᵉ →
    coherence-hexagonᵉ εᵉ ζᵉ (invᵉ γᵉ) (invᵉ δᵉ) αᵉ βᵉ
  hexagon-mirror-Aᵉ reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ .reflᵉ reflᵉ = reflᵉ

  hexagon-mirror-Bᵉ :
    (αᵉ : xᵉ ＝ᵉ uᵉ) (βᵉ : uᵉ ＝ᵉ u'ᵉ) (γᵉ : u'ᵉ ＝ᵉ yᵉ)
    (δᵉ : xᵉ ＝ᵉ vᵉ) (εᵉ : vᵉ ＝ᵉ v'ᵉ) (ζᵉ : v'ᵉ ＝ᵉ yᵉ) →
    coherence-hexagonᵉ αᵉ βᵉ γᵉ δᵉ εᵉ ζᵉ →
    coherence-hexagonᵉ (invᵉ αᵉ) δᵉ εᵉ βᵉ γᵉ (invᵉ ζᵉ)
  hexagon-mirror-Bᵉ reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ .reflᵉ reflᵉ = reflᵉ

  hexagon-mirror-Cᵉ :
    (αᵉ : xᵉ ＝ᵉ uᵉ) (βᵉ : uᵉ ＝ᵉ u'ᵉ) (γᵉ : u'ᵉ ＝ᵉ yᵉ)
    (δᵉ : xᵉ ＝ᵉ vᵉ) (εᵉ : vᵉ ＝ᵉ v'ᵉ) (ζᵉ : v'ᵉ ＝ᵉ yᵉ) →
    coherence-hexagonᵉ αᵉ βᵉ γᵉ δᵉ εᵉ ζᵉ →
    coherence-hexagonᵉ (invᵉ γᵉ) (invᵉ βᵉ) (invᵉ αᵉ) (invᵉ ζᵉ) (invᵉ εᵉ) (invᵉ δᵉ)
  hexagon-mirror-Cᵉ reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ .reflᵉ reflᵉ = reflᵉ
```

### Inversion of a hexagon

Theᵉ definitionᵉ ofᵉ aᵉ hexagonᵉ hasᵉ anᵉ explicitᵉ asymmetricalᵉ choiceᵉ ofᵉ association,ᵉ
soᵉ `inv`ᵉ onlyᵉ givesᵉ theᵉ correctᵉ identificationᵉ upᵉ to reassociation.ᵉ

```agda
module _
  { lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ uᵉ u'ᵉ vᵉ v'ᵉ yᵉ : Aᵉ}
  where

  inv-hexagonᵉ :
    ( αᵉ : xᵉ ＝ᵉ uᵉ) (βᵉ : uᵉ ＝ᵉ u'ᵉ) (γᵉ : u'ᵉ ＝ᵉ yᵉ) →
    ( δᵉ : xᵉ ＝ᵉ vᵉ) (εᵉ : vᵉ ＝ᵉ v'ᵉ) (ζᵉ : v'ᵉ ＝ᵉ yᵉ) →
    coherence-hexagonᵉ αᵉ βᵉ γᵉ δᵉ εᵉ ζᵉ →
    coherence-hexagonᵉ δᵉ εᵉ ζᵉ αᵉ βᵉ γᵉ
  inv-hexagonᵉ reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ .reflᵉ reflᵉ = reflᵉ
```