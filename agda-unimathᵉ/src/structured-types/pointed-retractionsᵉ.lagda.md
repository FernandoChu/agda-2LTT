# Pointed retractions of pointed maps

```agda
module structured-types.pointed-retractionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.retractionsᵉ

open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "pointedᵉ retraction"ᵉ Disambiguation="pointedᵉ map"ᵉ Agda=pointed-retractionᵉ}}
ofᵉ aᵉ [pointedᵉ map](structured-types.pointed-maps.mdᵉ) `fᵉ : Aᵉ →∗ᵉ B`ᵉ consistsᵉ ofᵉ aᵉ
pointedᵉ mapᵉ `gᵉ : Bᵉ →∗ᵉ A`ᵉ equippedᵉ with aᵉ
[pointedᵉ homotopy](structured-types.pointed-homotopies.mdᵉ) `Hᵉ : gᵉ ∘∗ᵉ fᵉ ~∗ᵉ id`.ᵉ

## Definitions

### The predicate of being a pointed retraction of a pointed map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  is-pointed-retractionᵉ : (Bᵉ →∗ᵉ Aᵉ) → UUᵉ l1ᵉ
  is-pointed-retractionᵉ gᵉ = gᵉ ∘∗ᵉ fᵉ ~∗ᵉ id-pointed-mapᵉ
```

### The type of pointed retractions of a pointed map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  pointed-retractionᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  pointed-retractionᵉ =
    Σᵉ (Bᵉ →∗ᵉ Aᵉ) (is-pointed-retractionᵉ fᵉ)

  module _
    (rᵉ : pointed-retractionᵉ)
    where

    pointed-map-pointed-retractionᵉ : Bᵉ →∗ᵉ Aᵉ
    pointed-map-pointed-retractionᵉ = pr1ᵉ rᵉ

    is-pointed-retraction-pointed-retractionᵉ :
      is-pointed-retractionᵉ fᵉ pointed-map-pointed-retractionᵉ
    is-pointed-retraction-pointed-retractionᵉ = pr2ᵉ rᵉ

    map-pointed-retractionᵉ : type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Aᵉ
    map-pointed-retractionᵉ = map-pointed-mapᵉ pointed-map-pointed-retractionᵉ

    preserves-point-pointed-map-pointed-retractionᵉ :
      map-pointed-retractionᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ point-Pointed-Typeᵉ Aᵉ
    preserves-point-pointed-map-pointed-retractionᵉ =
      preserves-point-pointed-mapᵉ pointed-map-pointed-retractionᵉ

    is-retraction-pointed-retractionᵉ :
      is-retractionᵉ (map-pointed-mapᵉ fᵉ) map-pointed-retractionᵉ
    is-retraction-pointed-retractionᵉ =
      htpy-pointed-htpyᵉ is-pointed-retraction-pointed-retractionᵉ

    retraction-pointed-retractionᵉ : retractionᵉ (map-pointed-mapᵉ fᵉ)
    pr1ᵉ retraction-pointed-retractionᵉ = map-pointed-retractionᵉ
    pr2ᵉ retraction-pointed-retractionᵉ = is-retraction-pointed-retractionᵉ

    coherence-point-is-retraction-pointed-retractionᵉ :
      coherence-point-unpointed-htpy-pointed-Πᵉ
        ( pointed-map-pointed-retractionᵉ ∘∗ᵉ fᵉ)
        ( id-pointed-mapᵉ)
        ( is-retraction-pointed-retractionᵉ)
    coherence-point-is-retraction-pointed-retractionᵉ =
      coherence-point-pointed-htpyᵉ is-pointed-retraction-pointed-retractionᵉ
```

## Properties

### Any retraction of a pointed map preserves the base point in a unique way making the retracting homotopy pointed

Considerᵉ aᵉ [retraction](foundation-core.retractions.mdᵉ) `gᵉ : Bᵉ → A`ᵉ ofᵉ aᵉ pointedᵉ
mapᵉ `fᵉ :=ᵉ (f₀ᵉ ,ᵉ f₁ᵉ) : Aᵉ →∗ᵉ B`.ᵉ Thenᵉ `g`ᵉ isᵉ baseᵉ pointᵉ preserving.ᵉ

**Proof.**ᵉ Ourᵉ goalᵉ isᵉ to showᵉ thatᵉ `gᵉ *ᵉ ＝ᵉ *`.ᵉ Sinceᵉ `f`ᵉ isᵉ pointed,ᵉ weᵉ haveᵉ
`fᵉ *ᵉ ＝ᵉ *`ᵉ andᵉ henceᵉ

```text
       (apᵉ gᵉ f₁)⁻¹ᵉ              Hᵉ *ᵉ
  gᵉ *ᵉ ------------->ᵉ gᵉ (f₀ᵉ *ᵉ) ------->ᵉ *.ᵉ
```

Inᵉ orderᵉ to showᵉ thatᵉ theᵉ retractingᵉ homotopyᵉ `Hᵉ : gᵉ ∘ᵉ f₀ᵉ ~ᵉ id`ᵉ isᵉ pointed,ᵉ weᵉ
haveᵉ to showᵉ thatᵉ theᵉ triangleᵉ ofᵉ identificationsᵉ

```text
                                   Hᵉ *ᵉ
                         gᵉ (f₀ᵉ *ᵉ) ----->ᵉ *ᵉ
                                \ᵉ       /ᵉ
  apᵉ gᵉ f₁ᵉ ∙ᵉ ((apᵉ gᵉ f₁)⁻¹ᵉ ∙ᵉ Hᵉ *ᵉ)  \ᵉ     /ᵉ reflᵉ
                                  \ᵉ   /ᵉ
                                   ∨ᵉ ∨ᵉ
                                    *ᵉ
```

commutes.ᵉ Thisᵉ followsᵉ byᵉ theᵉ factᵉ thatᵉ concatenatingᵉ with anᵉ inverseᵉ
identificationᵉ isᵉ inverseᵉ to concatenatingᵉ with theᵉ originalᵉ identification,ᵉ andᵉ
theᵉ rightᵉ unitᵉ lawᵉ ofᵉ concatenation.ᵉ

Noteᵉ thatᵉ theᵉ pointingᵉ ofᵉ `g`ᵉ chosenᵉ aboveᵉ isᵉ theᵉ uniqueᵉ wayᵉ makingᵉ theᵉ
retractingᵉ homotopyᵉ pointed,ᵉ becauseᵉ theᵉ mapᵉ `pᵉ ↦ᵉ apᵉ gᵉ f₁ᵉ ∙ᵉ p`ᵉ isᵉ anᵉ equivalenceᵉ
with aᵉ contractibleᵉ fiberᵉ atᵉ `Hᵉ *ᵉ ∙ᵉ refl`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  (gᵉ : type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Aᵉ)
  (Hᵉ : is-retractionᵉ (map-pointed-mapᵉ fᵉ) gᵉ)
  where

  abstract
    uniquely-preserves-point-is-retraction-pointed-mapᵉ :
      is-contrᵉ
        ( Σᵉ ( gᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ point-Pointed-Typeᵉ Aᵉ)
            ( coherence-square-identificationsᵉ
              ( Hᵉ (point-Pointed-Typeᵉ Aᵉ))
              ( apᵉ gᵉ (preserves-point-pointed-mapᵉ fᵉ))
              ( reflᵉ)))
    uniquely-preserves-point-is-retraction-pointed-mapᵉ =
      is-contr-map-is-equivᵉ
        ( is-equiv-concatᵉ (apᵉ gᵉ (preserves-point-pointed-mapᵉ fᵉ)) _)
        ( Hᵉ (point-Pointed-Typeᵉ Aᵉ) ∙ᵉ reflᵉ)

  preserves-point-is-retraction-pointed-mapᵉ :
    gᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ point-Pointed-Typeᵉ Aᵉ
  preserves-point-is-retraction-pointed-mapᵉ =
    invᵉ (apᵉ gᵉ (preserves-point-pointed-mapᵉ fᵉ)) ∙ᵉ Hᵉ (point-Pointed-Typeᵉ Aᵉ)

  pointed-map-is-retraction-pointed-mapᵉ :
    Bᵉ →∗ᵉ Aᵉ
  pr1ᵉ pointed-map-is-retraction-pointed-mapᵉ = gᵉ
  pr2ᵉ pointed-map-is-retraction-pointed-mapᵉ =
    preserves-point-is-retraction-pointed-mapᵉ

  coherence-point-is-retraction-pointed-mapᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( pointed-map-is-retraction-pointed-mapᵉ ∘∗ᵉ fᵉ)
      ( id-pointed-mapᵉ)
      ( Hᵉ)
  coherence-point-is-retraction-pointed-mapᵉ =
    ( is-section-inv-concatᵉ (apᵉ gᵉ (preserves-point-pointed-mapᵉ fᵉ)) _) ∙ᵉ
    ( invᵉ right-unitᵉ)

  is-pointed-retraction-is-retraction-pointed-mapᵉ :
    is-pointed-retractionᵉ fᵉ pointed-map-is-retraction-pointed-mapᵉ
  pr1ᵉ is-pointed-retraction-is-retraction-pointed-mapᵉ =
    Hᵉ
  pr2ᵉ is-pointed-retraction-is-retraction-pointed-mapᵉ =
    coherence-point-is-retraction-pointed-mapᵉ
```