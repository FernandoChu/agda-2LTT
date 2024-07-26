# Contractible maps

```agda
module foundation-core.contractible-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.coherently-invertible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
```

</details>

## Idea

Aᵉ mapᵉ isᵉ oftenᵉ saidᵉ to satisfyᵉ aᵉ propertyᵉ `P`ᵉ ifᵉ eachᵉ ofᵉ itsᵉ fibersᵉ satisfyᵉ
propertyᵉ `P`.ᵉ Thus,ᵉ weᵉ defineᵉ contractibleᵉ mapsᵉ to beᵉ mapsᵉ ofᵉ whichᵉ eachᵉ fiberᵉ
isᵉ contractible.ᵉ Inᵉ otherᵉ words,ᵉ contractibleᵉ mapsᵉ areᵉ mapsᵉ `fᵉ : Aᵉ → B`ᵉ suchᵉ
thatᵉ forᵉ eachᵉ elementᵉ `bᵉ : B`ᵉ thereᵉ isᵉ aᵉ uniqueᵉ `aᵉ : A`ᵉ equippedᵉ with anᵉ
identificationᵉ `(fᵉ aᵉ) ＝ᵉ b`,ᵉ i.e.,ᵉ contractibleᵉ mapsᵉ areᵉ theᵉ typeᵉ theoreticᵉ
bijections.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-contr-mapᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-contr-mapᵉ fᵉ = (yᵉ : Bᵉ) → is-contrᵉ (fiberᵉ fᵉ yᵉ)
```

## Properties

### Any contractible map is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} (Hᵉ : is-contr-mapᵉ fᵉ)
  where

  map-inv-is-contr-mapᵉ : Bᵉ → Aᵉ
  map-inv-is-contr-mapᵉ yᵉ = pr1ᵉ (centerᵉ (Hᵉ yᵉ))

  is-section-map-inv-is-contr-mapᵉ :
    is-sectionᵉ fᵉ map-inv-is-contr-mapᵉ
  is-section-map-inv-is-contr-mapᵉ yᵉ = pr2ᵉ (centerᵉ (Hᵉ yᵉ))

  is-retraction-map-inv-is-contr-mapᵉ :
    is-retractionᵉ fᵉ map-inv-is-contr-mapᵉ
  is-retraction-map-inv-is-contr-mapᵉ xᵉ =
    apᵉ
      ( pr1ᵉ {Bᵉ = λ zᵉ → (fᵉ zᵉ ＝ᵉ fᵉ xᵉ)})
      ( ( invᵉ
          ( contractionᵉ
            ( Hᵉ (fᵉ xᵉ))
            ( ( map-inv-is-contr-mapᵉ (fᵉ xᵉ)) ,ᵉ
              ( is-section-map-inv-is-contr-mapᵉ (fᵉ xᵉ))))) ∙ᵉ
        ( contractionᵉ (Hᵉ (fᵉ xᵉ)) (xᵉ ,ᵉ reflᵉ)))

  section-is-contr-mapᵉ : sectionᵉ fᵉ
  section-is-contr-mapᵉ =
    ( map-inv-is-contr-mapᵉ ,ᵉ is-section-map-inv-is-contr-mapᵉ)

  retraction-is-contr-mapᵉ : retractionᵉ fᵉ
  retraction-is-contr-mapᵉ =
    ( map-inv-is-contr-mapᵉ ,ᵉ is-retraction-map-inv-is-contr-mapᵉ)

  abstract
    is-equiv-is-contr-mapᵉ : is-equivᵉ fᵉ
    is-equiv-is-contr-mapᵉ =
      is-equiv-is-invertibleᵉ
        ( map-inv-is-contr-mapᵉ)
        ( is-section-map-inv-is-contr-mapᵉ)
        ( is-retraction-map-inv-is-contr-mapᵉ)
```

### Any coherently invertible map is a contractible map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  abstract
    center-fiber-is-coherently-invertibleᵉ :
      is-coherently-invertibleᵉ fᵉ → (yᵉ : Bᵉ) → fiberᵉ fᵉ yᵉ
    pr1ᵉ (center-fiber-is-coherently-invertibleᵉ Hᵉ yᵉ) =
      map-inv-is-coherently-invertibleᵉ Hᵉ yᵉ
    pr2ᵉ (center-fiber-is-coherently-invertibleᵉ Hᵉ yᵉ) =
      is-section-map-inv-is-coherently-invertibleᵉ Hᵉ yᵉ

    contraction-fiber-is-coherently-invertibleᵉ :
      (Hᵉ : is-coherently-invertibleᵉ fᵉ) → (yᵉ : Bᵉ) → (tᵉ : fiberᵉ fᵉ yᵉ) →
      (center-fiber-is-coherently-invertibleᵉ Hᵉ yᵉ) ＝ᵉ tᵉ
    contraction-fiber-is-coherently-invertibleᵉ Hᵉ yᵉ (xᵉ ,ᵉ reflᵉ) =
      eq-Eq-fiberᵉ fᵉ yᵉ
        ( is-retraction-map-inv-is-coherently-invertibleᵉ Hᵉ xᵉ)
        ( ( right-unitᵉ) ∙ᵉ
          ( invᵉ ( coh-is-coherently-invertibleᵉ Hᵉ xᵉ)))

  is-contr-map-is-coherently-invertibleᵉ :
    is-coherently-invertibleᵉ fᵉ → is-contr-mapᵉ fᵉ
  pr1ᵉ (is-contr-map-is-coherently-invertibleᵉ Hᵉ yᵉ) =
    center-fiber-is-coherently-invertibleᵉ Hᵉ yᵉ
  pr2ᵉ (is-contr-map-is-coherently-invertibleᵉ Hᵉ yᵉ) =
    contraction-fiber-is-coherently-invertibleᵉ Hᵉ yᵉ
```

### Any equivalence is a contractible map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  abstract
    is-contr-map-is-equivᵉ : is-equivᵉ fᵉ → is-contr-mapᵉ fᵉ
    is-contr-map-is-equivᵉ =
      is-contr-map-is-coherently-invertibleᵉ ∘ᵉ is-coherently-invertible-is-equivᵉ
```

## See also

-ᵉ Forᵉ theᵉ notionᵉ ofᵉ biinvertibleᵉ mapsᵉ seeᵉ
  [`foundation.equivalences`](foundation.equivalences.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ coherentlyᵉ invertibleᵉ maps,ᵉ alsoᵉ knownᵉ asᵉ half-adjointᵉ
  equivalences,ᵉ seeᵉ
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ path-splitᵉ mapsᵉ seeᵉ
  [`foundation.path-split-maps`](foundation.path-split-maps.md).ᵉ