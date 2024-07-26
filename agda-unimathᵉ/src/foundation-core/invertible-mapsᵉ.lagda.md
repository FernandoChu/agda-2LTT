# Invertible maps

```agda
module foundation-core.invertible-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
```

</details>

## Idea

Anᵉ {{#conceptᵉ "inverse"ᵉ Disambiguation="mapsᵉ ofᵉ types"ᵉ Agda=is-inverseᵉ}} forᵉ aᵉ
mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ aᵉ mapᵉ `gᵉ : Bᵉ → A`ᵉ equippedᵉ with
[homotopies](foundation-core.homotopies.mdᵉ) `fᵉ ∘ᵉ gᵉ ~ᵉ id`ᵉ andᵉ `gᵉ ∘ᵉ fᵉ ~ᵉ id`.ᵉ Suchᵉ
data,ᵉ however,ᵉ isᵉ [structure](foundation.structure.mdᵉ) onᵉ theᵉ mapᵉ `f`,ᵉ andᵉ notᵉ
generallyᵉ aᵉ [property](foundation-core.propositions.md).ᵉ

## Definition

### The predicate that a map `g` is an inverse of a map `f`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-inverseᵉ : (Aᵉ → Bᵉ) → (Bᵉ → Aᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-inverseᵉ fᵉ gᵉ = ((fᵉ ∘ᵉ gᵉ) ~ᵉ idᵉ) ×ᵉ ((gᵉ ∘ᵉ fᵉ) ~ᵉ idᵉ)

  is-section-is-inverseᵉ :
    {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ} → is-inverseᵉ fᵉ gᵉ → fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ
  is-section-is-inverseᵉ = pr1ᵉ

  is-retraction-is-inverseᵉ :
    {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ} → is-inverseᵉ fᵉ gᵉ → gᵉ ∘ᵉ fᵉ ~ᵉ idᵉ
  is-retraction-is-inverseᵉ = pr2ᵉ
```

### The predicate that a map `f` is invertible

```agda
is-invertibleᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-invertibleᵉ {Aᵉ = Aᵉ} {Bᵉ} fᵉ = Σᵉ (Bᵉ → Aᵉ) (is-inverseᵉ fᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} (gᵉ : is-invertibleᵉ fᵉ)
  where

  map-inv-is-invertibleᵉ : Bᵉ → Aᵉ
  map-inv-is-invertibleᵉ = pr1ᵉ gᵉ

  is-inverse-map-inv-is-invertibleᵉ : is-inverseᵉ fᵉ map-inv-is-invertibleᵉ
  is-inverse-map-inv-is-invertibleᵉ = pr2ᵉ gᵉ

  is-section-map-inv-is-invertibleᵉ : fᵉ ∘ᵉ map-inv-is-invertibleᵉ ~ᵉ idᵉ
  is-section-map-inv-is-invertibleᵉ = pr1ᵉ is-inverse-map-inv-is-invertibleᵉ

  is-retraction-map-inv-is-invertibleᵉ : map-inv-is-invertibleᵉ ∘ᵉ fᵉ ~ᵉ idᵉ
  is-retraction-map-inv-is-invertibleᵉ = pr2ᵉ is-inverse-map-inv-is-invertibleᵉ

  section-is-invertibleᵉ : sectionᵉ fᵉ
  pr1ᵉ section-is-invertibleᵉ = map-inv-is-invertibleᵉ
  pr2ᵉ section-is-invertibleᵉ = is-section-map-inv-is-invertibleᵉ

  retraction-is-invertibleᵉ : retractionᵉ fᵉ
  pr1ᵉ retraction-is-invertibleᵉ = map-inv-is-invertibleᵉ
  pr2ᵉ retraction-is-invertibleᵉ = is-retraction-map-inv-is-invertibleᵉ
```

### The type of invertible maps

```agda
invertible-mapᵉ : {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
invertible-mapᵉ Aᵉ Bᵉ = Σᵉ (Aᵉ → Bᵉ) (is-invertibleᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  map-invertible-mapᵉ : invertible-mapᵉ Aᵉ Bᵉ → Aᵉ → Bᵉ
  map-invertible-mapᵉ = pr1ᵉ

  is-invertible-map-invertible-mapᵉ :
    (fᵉ : invertible-mapᵉ Aᵉ Bᵉ) → is-invertibleᵉ (map-invertible-mapᵉ fᵉ)
  is-invertible-map-invertible-mapᵉ = pr2ᵉ

  map-inv-invertible-mapᵉ : invertible-mapᵉ Aᵉ Bᵉ → Bᵉ → Aᵉ
  map-inv-invertible-mapᵉ =
    map-inv-is-invertibleᵉ ∘ᵉ is-invertible-map-invertible-mapᵉ

  is-retraction-map-inv-invertible-mapᵉ :
    (fᵉ : invertible-mapᵉ Aᵉ Bᵉ) →
    map-inv-invertible-mapᵉ fᵉ ∘ᵉ map-invertible-mapᵉ fᵉ ~ᵉ idᵉ
  is-retraction-map-inv-invertible-mapᵉ =
    is-retraction-map-inv-is-invertibleᵉ ∘ᵉ is-invertible-map-invertible-mapᵉ

  is-section-map-inv-invertible-mapᵉ :
    (fᵉ : invertible-mapᵉ Aᵉ Bᵉ) →
    map-invertible-mapᵉ fᵉ ∘ᵉ map-inv-invertible-mapᵉ fᵉ ~ᵉ idᵉ
  is-section-map-inv-invertible-mapᵉ =
    is-section-map-inv-is-invertibleᵉ ∘ᵉ is-invertible-map-invertible-mapᵉ
```

## Properties

### The identity invertible map

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  is-inverse-idᵉ : is-inverseᵉ idᵉ (idᵉ {Aᵉ = Aᵉ})
  pr1ᵉ is-inverse-idᵉ = refl-htpyᵉ
  pr2ᵉ is-inverse-idᵉ = refl-htpyᵉ

  is-invertible-idᵉ : is-invertibleᵉ (idᵉ {Aᵉ = Aᵉ})
  pr1ᵉ is-invertible-idᵉ = idᵉ
  pr2ᵉ is-invertible-idᵉ = is-inverse-idᵉ

  id-invertible-mapᵉ : invertible-mapᵉ Aᵉ Aᵉ
  pr1ᵉ id-invertible-mapᵉ = idᵉ
  pr2ᵉ id-invertible-mapᵉ = is-invertible-idᵉ
```

### The inverse of an invertible map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-inverse-inv-is-inverseᵉ :
    {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ} → is-inverseᵉ fᵉ gᵉ → is-inverseᵉ gᵉ fᵉ
  pr1ᵉ (is-inverse-inv-is-inverseᵉ {fᵉ} {gᵉ} Hᵉ) =
    is-retraction-map-inv-is-invertibleᵉ (gᵉ ,ᵉ Hᵉ)
  pr2ᵉ (is-inverse-inv-is-inverseᵉ {fᵉ} {gᵉ} Hᵉ) =
    is-section-map-inv-is-invertibleᵉ (gᵉ ,ᵉ Hᵉ)

  is-invertible-map-inv-is-invertibleᵉ :
    {fᵉ : Aᵉ → Bᵉ} (gᵉ : is-invertibleᵉ fᵉ) → is-invertibleᵉ (map-inv-is-invertibleᵉ gᵉ)
  pr1ᵉ (is-invertible-map-inv-is-invertibleᵉ {fᵉ} gᵉ) = fᵉ
  pr2ᵉ (is-invertible-map-inv-is-invertibleᵉ {fᵉ} gᵉ) =
    is-inverse-inv-is-inverseᵉ {fᵉ} (is-inverse-map-inv-is-invertibleᵉ gᵉ)

  is-invertible-map-inv-invertible-mapᵉ :
    (fᵉ : invertible-mapᵉ Aᵉ Bᵉ) → is-invertibleᵉ (map-inv-invertible-mapᵉ fᵉ)
  is-invertible-map-inv-invertible-mapᵉ fᵉ =
    is-invertible-map-inv-is-invertibleᵉ (is-invertible-map-invertible-mapᵉ fᵉ)

  inv-invertible-mapᵉ : invertible-mapᵉ Aᵉ Bᵉ → invertible-mapᵉ Bᵉ Aᵉ
  pr1ᵉ (inv-invertible-mapᵉ fᵉ) = map-inv-invertible-mapᵉ fᵉ
  pr2ᵉ (inv-invertible-mapᵉ fᵉ) = is-invertible-map-inv-invertible-mapᵉ fᵉ
```

### The inversion operation on invertible maps is a strict involution

Theᵉ inversionᵉ operationᵉ onᵉ invertibleᵉ mapsᵉ isᵉ aᵉ strictᵉ involution,ᵉ where,ᵉ byᵉ
strictᵉ involution,ᵉ weᵉ meanᵉ thatᵉ `inv-invertible-mapᵉ (inv-invertible-mapᵉ fᵉ) ≐ᵉ f`ᵉ
syntactically.ᵉ Thisᵉ canᵉ beᵉ observedᵉ byᵉ theᵉ factᵉ thatᵉ theᵉ type-checkerᵉ acceptsᵉ
`refl`ᵉ asᵉ proofᵉ ofᵉ thisᵉ equation.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-involution-inv-invertible-mapᵉ :
    {fᵉ : invertible-mapᵉ Aᵉ Bᵉ} → inv-invertible-mapᵉ (inv-invertible-mapᵉ fᵉ) ＝ᵉ fᵉ
  is-involution-inv-invertible-mapᵉ = reflᵉ
```

### Composition of invertible maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ) (Gᵉ : is-invertibleᵉ gᵉ) (Fᵉ : is-invertibleᵉ fᵉ)
  where

  map-inv-is-invertible-compᵉ : Cᵉ → Aᵉ
  map-inv-is-invertible-compᵉ =
    map-inv-is-invertibleᵉ Fᵉ ∘ᵉ map-inv-is-invertibleᵉ Gᵉ

  is-section-map-inv-is-invertible-compᵉ :
    is-sectionᵉ (gᵉ ∘ᵉ fᵉ) map-inv-is-invertible-compᵉ
  is-section-map-inv-is-invertible-compᵉ =
    is-section-map-section-compᵉ gᵉ fᵉ
      ( section-is-invertibleᵉ Fᵉ)
      ( section-is-invertibleᵉ Gᵉ)

  is-retraction-map-inv-is-invertible-compᵉ :
    is-retractionᵉ (gᵉ ∘ᵉ fᵉ) map-inv-is-invertible-compᵉ
  is-retraction-map-inv-is-invertible-compᵉ =
    is-retraction-map-retraction-compᵉ gᵉ fᵉ
      ( retraction-is-invertibleᵉ Gᵉ)
      ( retraction-is-invertibleᵉ Fᵉ)

  is-invertible-compᵉ : is-invertibleᵉ (gᵉ ∘ᵉ fᵉ)
  is-invertible-compᵉ =
    ( map-inv-is-invertible-compᵉ ,ᵉ
      is-section-map-inv-is-invertible-compᵉ ,ᵉ
      is-retraction-map-inv-is-invertible-compᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  is-invertible-map-comp-invertible-mapᵉ :
    (gᵉ : invertible-mapᵉ Bᵉ Cᵉ) (fᵉ : invertible-mapᵉ Aᵉ Bᵉ) →
    is-invertibleᵉ (map-invertible-mapᵉ gᵉ ∘ᵉ map-invertible-mapᵉ fᵉ)
  is-invertible-map-comp-invertible-mapᵉ gᵉ fᵉ =
    is-invertible-compᵉ
      ( map-invertible-mapᵉ gᵉ)
      ( map-invertible-mapᵉ fᵉ)
      ( is-invertible-map-invertible-mapᵉ gᵉ)
      ( is-invertible-map-invertible-mapᵉ fᵉ)

  comp-invertible-mapᵉ :
    invertible-mapᵉ Bᵉ Cᵉ → invertible-mapᵉ Aᵉ Bᵉ → invertible-mapᵉ Aᵉ Cᵉ
  pr1ᵉ (comp-invertible-mapᵉ gᵉ fᵉ) = map-invertible-mapᵉ gᵉ ∘ᵉ map-invertible-mapᵉ fᵉ
  pr2ᵉ (comp-invertible-mapᵉ gᵉ fᵉ) = is-invertible-map-comp-invertible-mapᵉ gᵉ fᵉ
```

### Invertible maps are closed under homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-section-map-inv-is-invertible-htpyᵉ :
    {fᵉ f'ᵉ : Aᵉ → Bᵉ} (Hᵉ : f'ᵉ ~ᵉ fᵉ) (Fᵉ : is-invertibleᵉ fᵉ) →
    is-sectionᵉ f'ᵉ (map-inv-is-invertibleᵉ Fᵉ)
  is-section-map-inv-is-invertible-htpyᵉ Hᵉ (gᵉ ,ᵉ Sᵉ ,ᵉ Rᵉ) = Hᵉ ·rᵉ gᵉ ∙hᵉ Sᵉ

  is-retraction-map-inv-is-invertible-htpyᵉ :
    {fᵉ f'ᵉ : Aᵉ → Bᵉ} (Hᵉ : f'ᵉ ~ᵉ fᵉ) (Fᵉ : is-invertibleᵉ fᵉ) →
    is-retractionᵉ f'ᵉ (map-inv-is-invertibleᵉ Fᵉ)
  is-retraction-map-inv-is-invertible-htpyᵉ Hᵉ (gᵉ ,ᵉ Sᵉ ,ᵉ Rᵉ) = gᵉ ·lᵉ Hᵉ ∙hᵉ Rᵉ

  is-invertible-htpyᵉ :
    {fᵉ f'ᵉ : Aᵉ → Bᵉ} → f'ᵉ ~ᵉ fᵉ → is-invertibleᵉ fᵉ → is-invertibleᵉ f'ᵉ
  is-invertible-htpyᵉ Hᵉ Fᵉ =
    ( map-inv-is-invertibleᵉ Fᵉ ,ᵉ
      is-section-map-inv-is-invertible-htpyᵉ Hᵉ Fᵉ ,ᵉ
      is-retraction-map-inv-is-invertible-htpyᵉ Hᵉ Fᵉ)

  is-invertible-inv-htpyᵉ :
    {fᵉ f'ᵉ : Aᵉ → Bᵉ} → fᵉ ~ᵉ f'ᵉ → is-invertibleᵉ fᵉ → is-invertibleᵉ f'ᵉ
  is-invertible-inv-htpyᵉ Hᵉ = is-invertible-htpyᵉ (inv-htpyᵉ Hᵉ)

  htpy-map-inv-is-invertibleᵉ :
    {fᵉ gᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) (Fᵉ : is-invertibleᵉ fᵉ) (Gᵉ : is-invertibleᵉ gᵉ) →
    map-inv-is-invertibleᵉ Fᵉ ~ᵉ map-inv-is-invertibleᵉ Gᵉ
  htpy-map-inv-is-invertibleᵉ Hᵉ Fᵉ Gᵉ =
    ( ( inv-htpyᵉ (is-retraction-map-inv-is-invertibleᵉ Gᵉ)) ·rᵉ
      ( map-inv-is-invertibleᵉ Fᵉ)) ∙hᵉ
    ( ( map-inv-is-invertibleᵉ Gᵉ) ·lᵉ
      ( ( inv-htpyᵉ Hᵉ ·rᵉ map-inv-is-invertibleᵉ Fᵉ) ∙hᵉ
        ( is-section-map-inv-is-invertibleᵉ Fᵉ)))
```

### Any section of an invertible map is homotopic to its inverse

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : invertible-mapᵉ Aᵉ Bᵉ)
  where

  htpy-map-inv-invertible-map-sectionᵉ :
    (fᵉ : sectionᵉ (map-invertible-mapᵉ eᵉ)) →
    map-inv-invertible-mapᵉ eᵉ ~ᵉ
    map-sectionᵉ (map-invertible-mapᵉ eᵉ) fᵉ
  htpy-map-inv-invertible-map-sectionᵉ (fᵉ ,ᵉ Hᵉ) =
    ( map-inv-invertible-mapᵉ eᵉ ·lᵉ inv-htpyᵉ Hᵉ) ∙hᵉ
    ( is-retraction-map-inv-invertible-mapᵉ eᵉ ·rᵉ fᵉ)
```

### Any retraction of an invertible map is homotopic to its inverse

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : invertible-mapᵉ Aᵉ Bᵉ)
  where

  htpy-map-inv-invertible-map-retractionᵉ :
    (fᵉ : retractionᵉ (map-invertible-mapᵉ eᵉ)) →
    map-inv-invertible-mapᵉ eᵉ ~ᵉ
    map-retractionᵉ (map-invertible-mapᵉ eᵉ) fᵉ
  htpy-map-inv-invertible-map-retractionᵉ (fᵉ ,ᵉ Hᵉ) =
    ( inv-htpyᵉ Hᵉ ·rᵉ map-inv-invertible-mapᵉ eᵉ) ∙hᵉ
    ( fᵉ ·lᵉ is-section-map-inv-invertible-mapᵉ eᵉ)
```

### Invertible maps are injective

Theᵉ constructionᵉ ofᵉ theᵉ converseᵉ mapᵉ ofᵉ theᵉ
[actionᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ)
isᵉ aᵉ rerunᵉ ofᵉ theᵉ proofᵉ thatᵉ mapsᵉ with
[retractions](foundation-core.retractions.mdᵉ) areᵉ
[injective](foundation-core.injective-maps.mdᵉ) (`is-injective-retraction`).ᵉ Weᵉ
repeatᵉ theᵉ proofᵉ to avoidᵉ cyclicᵉ dependencies.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} (Hᵉ : is-invertibleᵉ fᵉ)
  where

  is-injective-is-invertibleᵉ : {xᵉ yᵉ : Aᵉ} → fᵉ xᵉ ＝ᵉ fᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  is-injective-is-invertibleᵉ =
    is-injective-retractionᵉ fᵉ (retraction-is-invertibleᵉ Hᵉ)
```

## See also

-ᵉ Forᵉ theᵉ coherentᵉ notionᵉ ofᵉ invertibleᵉ mapsᵉ seeᵉ
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ biinvertibleᵉ mapsᵉ seeᵉ
  [`foundation.equivalences`](foundation.equivalences.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ mapsᵉ with contractibleᵉ fibersᵉ seeᵉ
  [`foundation.contractible-maps`](foundation.contractible-maps.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ path-splitᵉ mapsᵉ seeᵉ
  [`foundation.path-split-maps`](foundation.path-split-maps.md).ᵉ