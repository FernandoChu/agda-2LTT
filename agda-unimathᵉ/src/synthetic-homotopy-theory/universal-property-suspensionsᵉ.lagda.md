# Universal property of suspensions

```agda
module synthetic-homotopy-theory.universal-property-suspensionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.suspension-structuresᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Sinceᵉ suspensionsᵉ areᵉ justᵉ [pushouts](synthetic-homotopy-theory.pushouts.md),ᵉ
theyᵉ retainᵉ theᵉ expectedᵉ
[universalᵉ property](synthetic-homotopy-theory.universal-property-pushouts.md),ᵉ
whichᵉ statesᵉ thatᵉ theᵉ mapᵉ `cocone-map`ᵉ isᵉ aᵉ equivalence.ᵉ Weᵉ denoteᵉ thisᵉ
universalᵉ propertyᵉ byᵉ `universal-property-pushout-suspension`.ᵉ But,ᵉ dueᵉ to theᵉ
specialᵉ natureᵉ ofᵉ theᵉ spanᵉ beingᵉ pushedᵉ out,ᵉ theᵉ suspensionᵉ ofᵉ aᵉ typeᵉ enjoysᵉ anᵉ
equivalentᵉ universalᵉ property,ᵉ hereᵉ denotedᵉ byᵉ `universal-property-suspension`.ᵉ
Thisᵉ universalᵉ propertyᵉ statesᵉ thatᵉ theᵉ mapᵉ `ev-suspension`ᵉ isᵉ anᵉ equivalence.ᵉ

## Definitions

### The universal property of the suspension

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  (sᵉ : suspension-structureᵉ Xᵉ Yᵉ)
  where

  ev-suspensionᵉ :
    {l3ᵉ : Level} (Zᵉ : UUᵉ l3ᵉ) → (Yᵉ → Zᵉ) → suspension-structureᵉ Xᵉ Zᵉ
  pr1ᵉ (ev-suspensionᵉ Zᵉ hᵉ) = hᵉ (north-suspension-structureᵉ sᵉ)
  pr1ᵉ (pr2ᵉ (ev-suspensionᵉ Zᵉ hᵉ)) = hᵉ (south-suspension-structureᵉ sᵉ)
  pr2ᵉ (pr2ᵉ (ev-suspensionᵉ Zᵉ hᵉ)) = hᵉ ·lᵉ meridian-suspension-structureᵉ sᵉ

  universal-property-suspensionᵉ : UUωᵉ
  universal-property-suspensionᵉ =
    {lᵉ : Level} (Zᵉ : UUᵉ lᵉ) → is-equivᵉ (ev-suspensionᵉ Zᵉ)
```

### The universal property of the suspension at a universe level as a pushout

```agda
universal-property-pushout-suspensionᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : UUᵉ l2ᵉ)
  (sᵉ : suspension-structureᵉ Xᵉ Yᵉ) → UUωᵉ
universal-property-pushout-suspensionᵉ Xᵉ Yᵉ sᵉ =
  universal-property-pushoutᵉ
    ( terminal-mapᵉ Xᵉ)
    ( terminal-mapᵉ Xᵉ)
    ( suspension-cocone-suspension-structureᵉ sᵉ)
```

## Properties

```agda
triangle-ev-suspensionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
  (sᵉ : suspension-structureᵉ Xᵉ Yᵉ) →
  (Zᵉ : UUᵉ l3ᵉ) →
  ( ( suspension-structure-suspension-coconeᵉ) ∘ᵉ
    ( cocone-mapᵉ
      ( terminal-mapᵉ Xᵉ)
      ( terminal-mapᵉ Xᵉ)
      ( suspension-cocone-suspension-structureᵉ sᵉ))) ~ᵉ
  ( ev-suspensionᵉ sᵉ Zᵉ)
triangle-ev-suspensionᵉ (Nᵉ ,ᵉ Sᵉ ,ᵉ meridᵉ) Zᵉ hᵉ = reflᵉ

is-equiv-ev-suspensionᵉ :
  { l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
  ( sᵉ : suspension-structureᵉ Xᵉ Yᵉ) →
  universal-property-pushout-suspensionᵉ Xᵉ Yᵉ sᵉ →
  { l3ᵉ : Level} (Zᵉ : UUᵉ l3ᵉ) → is-equivᵉ (ev-suspensionᵉ sᵉ Zᵉ)
is-equiv-ev-suspensionᵉ {Xᵉ = Xᵉ} sᵉ up-Yᵉ Zᵉ =
  is-equiv-left-map-triangleᵉ
    ( ev-suspensionᵉ sᵉ Zᵉ)
    ( suspension-structure-suspension-coconeᵉ)
    ( cocone-mapᵉ
      ( terminal-mapᵉ Xᵉ)
      ( terminal-mapᵉ Xᵉ)
      ( suspension-cocone-suspension-structureᵉ sᵉ))
    ( inv-htpyᵉ (triangle-ev-suspensionᵉ sᵉ Zᵉ))
    ( up-Yᵉ Zᵉ)
    ( is-equiv-suspension-structure-suspension-coconeᵉ)
```