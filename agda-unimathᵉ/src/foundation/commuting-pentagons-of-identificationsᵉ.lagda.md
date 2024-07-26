# Commuting pentagons of identifications

```agda
module foundation.commuting-pentagons-of-identificationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Aᵉ pentagonᵉ ofᵉ [identifications](foundation-core.identity-types.mdᵉ)

```text
               topᵉ
             xᵉ ---ᵉ yᵉ
   top-leftᵉ /ᵉ       \ᵉ top-rightᵉ
           /ᵉ         \ᵉ
          zᵉ           wᵉ
            \ᵉ       /ᵉ
  bottom-leftᵉ \ᵉ   /ᵉ bottom-rightᵉ
                vᵉ
```

isᵉ saidᵉ to **commute**ᵉ ifᵉ thereᵉ isᵉ anᵉ identificationᵉ

```text
  top-leftᵉ ∙ᵉ bottom-leftᵉ ＝ᵉ (topᵉ ∙ᵉ top-rightᵉ) ∙ᵉ bottom-right.ᵉ
```

Suchᵉ anᵉ identificationᵉ isᵉ calledᵉ aᵉ **coherence**ᵉ ofᵉ theᵉ pentagon.ᵉ

## Definitions

### Commuting pentagons of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ vᵉ : Aᵉ}
  where

  coherence-pentagon-identificationsᵉ :
    (topᵉ : xᵉ ＝ᵉ yᵉ)
    (top-leftᵉ : xᵉ ＝ᵉ zᵉ) (top-rightᵉ : yᵉ ＝ᵉ wᵉ)
    (bottom-leftᵉ : zᵉ ＝ᵉ vᵉ) (bottom-rightᵉ : wᵉ ＝ᵉ vᵉ) → UUᵉ lᵉ
  coherence-pentagon-identificationsᵉ
    topᵉ top-leftᵉ top-rightᵉ bottom-leftᵉ bottom-rightᵉ =
    top-leftᵉ ∙ᵉ bottom-leftᵉ ＝ᵉ (topᵉ ∙ᵉ top-rightᵉ) ∙ᵉ bottom-rightᵉ
```

### Reflections of commuting pentagons of identifications

Aᵉ pentagonᵉ mayᵉ beᵉ reflectedᵉ alongᵉ anᵉ axisᵉ connectingᵉ anᵉ edgeᵉ with itsᵉ opposingᵉ
vertex.ᵉ Forᵉ example,ᵉ weᵉ mayᵉ reflectᵉ aᵉ pentagonᵉ

```text
               topᵉ
             xᵉ ---ᵉ yᵉ
   top-leftᵉ /ᵉ       \ᵉ top-rightᵉ
           /ᵉ         \ᵉ
          zᵉ           wᵉ
            \ᵉ       /ᵉ
  bottom-leftᵉ \ᵉ   /ᵉ bottom-rightᵉ
                vᵉ
```

alongᵉ theᵉ axisᵉ connectingᵉ `top`ᵉ andᵉ `v`ᵉ to getᵉ

```text
               top⁻¹ᵉ
              yᵉ ---ᵉ xᵉ
   top-rightᵉ /ᵉ       \ᵉ top-leftᵉ
            /ᵉ         \ᵉ
           wᵉ           zᵉ
             \ᵉ       /ᵉ
  bottom-rightᵉ \ᵉ   /ᵉ bottom-leftᵉ
                 vᵉ .ᵉ
```

Theᵉ reflectionsᵉ areᵉ namedᵉ afterᵉ theᵉ edgeᵉ whichᵉ theᵉ axisᵉ passesᵉ through,ᵉ soᵉ theᵉ
aboveᵉ exampleᵉ isᵉ `reflect-top-coherence-pentagon-identifications`.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ vᵉ : Aᵉ}
  where

  reflect-top-coherence-pentagon-identificationsᵉ :
    (topᵉ : xᵉ ＝ᵉ yᵉ)
    (top-leftᵉ : xᵉ ＝ᵉ zᵉ) (top-rightᵉ : yᵉ ＝ᵉ wᵉ)
    (bottom-leftᵉ : zᵉ ＝ᵉ vᵉ) (bottom-rightᵉ : wᵉ ＝ᵉ vᵉ) →
    coherence-pentagon-identificationsᵉ
      ( topᵉ)
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ) →
    coherence-pentagon-identificationsᵉ
      ( invᵉ topᵉ)
      ( top-rightᵉ)
      ( top-leftᵉ)
      ( bottom-rightᵉ)
      ( bottom-leftᵉ)
  reflect-top-coherence-pentagon-identificationsᵉ
    reflᵉ top-leftᵉ top-rightᵉ bottom-leftᵉ bottom-rightᵉ Hᵉ = invᵉ Hᵉ

  reflect-top-left-coherence-pentagon-identificationsᵉ :
    (topᵉ : xᵉ ＝ᵉ yᵉ)
    (top-leftᵉ : xᵉ ＝ᵉ zᵉ) (top-rightᵉ : yᵉ ＝ᵉ wᵉ)
    (bottom-leftᵉ : zᵉ ＝ᵉ vᵉ) (bottom-rightᵉ : wᵉ ＝ᵉ vᵉ) →
    coherence-pentagon-identificationsᵉ
      ( topᵉ)
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ) →
    coherence-pentagon-identificationsᵉ
      ( bottom-leftᵉ)
      ( invᵉ top-leftᵉ)
      ( invᵉ bottom-rightᵉ)
      ( topᵉ)
      ( invᵉ top-rightᵉ)
  reflect-top-left-coherence-pentagon-identificationsᵉ
    reflᵉ reflᵉ reflᵉ bottom-leftᵉ reflᵉ Hᵉ =
    invᵉ (right-unitᵉ ∙ᵉ right-unitᵉ ∙ᵉ Hᵉ)

  reflect-top-right-coherence-pentagon-identificationsᵉ :
    (topᵉ : xᵉ ＝ᵉ yᵉ)
    (top-leftᵉ : xᵉ ＝ᵉ zᵉ) (top-rightᵉ : yᵉ ＝ᵉ wᵉ)
    (bottom-leftᵉ : zᵉ ＝ᵉ vᵉ) (bottom-rightᵉ : wᵉ ＝ᵉ vᵉ) →
    coherence-pentagon-identificationsᵉ
      ( topᵉ)
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ) →
    coherence-pentagon-identificationsᵉ
      ( invᵉ bottom-rightᵉ)
      ( invᵉ bottom-leftᵉ)
      ( invᵉ top-rightᵉ)
      ( invᵉ top-leftᵉ)
      ( invᵉ topᵉ)
  reflect-top-right-coherence-pentagon-identificationsᵉ
    reflᵉ top-leftᵉ reflᵉ reflᵉ reflᵉ Hᵉ =
    apᵉ invᵉ (invᵉ right-unitᵉ ∙ᵉ Hᵉ)

  reflect-bottom-left-coherence-pentagon-identificationsᵉ :
    (topᵉ : xᵉ ＝ᵉ yᵉ)
    (top-leftᵉ : xᵉ ＝ᵉ zᵉ) (top-rightᵉ : yᵉ ＝ᵉ wᵉ)
    (bottom-leftᵉ : zᵉ ＝ᵉ vᵉ) (bottom-rightᵉ : wᵉ ＝ᵉ vᵉ) →
    coherence-pentagon-identificationsᵉ
      ( topᵉ)
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ) →
    coherence-pentagon-identificationsᵉ
      ( invᵉ top-rightᵉ)
      ( bottom-rightᵉ)
      ( invᵉ topᵉ)
      ( invᵉ bottom-leftᵉ)
      ( top-leftᵉ)
  reflect-bottom-left-coherence-pentagon-identificationsᵉ
    reflᵉ reflᵉ reflᵉ reflᵉ bottom-rightᵉ Hᵉ = right-unitᵉ ∙ᵉ invᵉ Hᵉ

  reflect-bottom-right-coherence-pentagon-identificationsᵉ :
    (topᵉ : xᵉ ＝ᵉ yᵉ)
    (top-leftᵉ : xᵉ ＝ᵉ zᵉ) (top-rightᵉ : yᵉ ＝ᵉ wᵉ)
    (bottom-leftᵉ : zᵉ ＝ᵉ vᵉ) (bottom-rightᵉ : wᵉ ＝ᵉ vᵉ) →
    coherence-pentagon-identificationsᵉ
      ( topᵉ)
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ) →
    coherence-pentagon-identificationsᵉ
      ( bottom-leftᵉ)
      ( invᵉ top-leftᵉ)
      ( invᵉ bottom-rightᵉ)
      ( topᵉ)
      ( invᵉ top-rightᵉ)
  reflect-bottom-right-coherence-pentagon-identificationsᵉ
    reflᵉ reflᵉ reflᵉ bottom-leftᵉ reflᵉ Hᵉ =
    invᵉ (right-unitᵉ ∙ᵉ right-unitᵉ ∙ᵉ Hᵉ)
```