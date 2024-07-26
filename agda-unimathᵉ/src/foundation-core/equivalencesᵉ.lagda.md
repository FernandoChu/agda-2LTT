# Equivalences

```agda
module foundation-core.equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.coherently-invertible-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.invertible-mapsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
```

</details>

## Idea

Anᵉ **equivalence**ᵉ isᵉ aᵉ mapᵉ thatᵉ hasᵉ aᵉ [section](foundation-core.sections.mdᵉ)
andᵉ aᵉ (separateᵉ) [retraction](foundation-core.retractions.md).ᵉ Thisᵉ conditionᵉ isᵉ
alsoᵉ calledᵉ beingᵉ **biinvertible**.ᵉ

Theᵉ conditionᵉ ofᵉ biinvertibilityᵉ mayᵉ lookᵉ oddᵉ: Whyᵉ notᵉ sayᵉ thatᵉ anᵉ equivalenceᵉ
isᵉ aᵉ mapᵉ thatᵉ hasᵉ aᵉ [2-sidedᵉ inverse](foundation-core.invertible-maps.md)?ᵉ Theᵉ
reasonᵉ isᵉ thatᵉ theᵉ conditionᵉ ofᵉ invertibilityᵉ isᵉ
[structure](foundation.structure.md),ᵉ whereasᵉ theᵉ conditionᵉ ofᵉ beingᵉ
biinvertibleᵉ isᵉ aᵉ [property](foundation-core.propositions.md).ᵉ Toᵉ quicklyᵉ seeᵉ
thisᵉ: ifᵉ `f`ᵉ isᵉ anᵉ equivalence,ᵉ thenᵉ itᵉ hasᵉ upᵉ to
[homotopy](foundation-core.homotopies.mdᵉ) onlyᵉ oneᵉ section,ᵉ andᵉ itᵉ hasᵉ upᵉ to
homotopyᵉ onlyᵉ oneᵉ retraction.ᵉ

## Definition

### The predicate of being an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-equivᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-equivᵉ fᵉ = sectionᵉ fᵉ ×ᵉ retractionᵉ fᵉ
```

### Components of a proof of equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} (Hᵉ : is-equivᵉ fᵉ)
  where

  section-is-equivᵉ : sectionᵉ fᵉ
  section-is-equivᵉ = pr1ᵉ Hᵉ

  retraction-is-equivᵉ : retractionᵉ fᵉ
  retraction-is-equivᵉ = pr2ᵉ Hᵉ

  map-section-is-equivᵉ : Bᵉ → Aᵉ
  map-section-is-equivᵉ = map-sectionᵉ fᵉ section-is-equivᵉ

  map-retraction-is-equivᵉ : Bᵉ → Aᵉ
  map-retraction-is-equivᵉ = map-retractionᵉ fᵉ retraction-is-equivᵉ

  is-section-map-section-is-equivᵉ : is-sectionᵉ fᵉ map-section-is-equivᵉ
  is-section-map-section-is-equivᵉ = is-section-map-sectionᵉ fᵉ section-is-equivᵉ

  is-retraction-map-retraction-is-equivᵉ :
    is-retractionᵉ fᵉ map-retraction-is-equivᵉ
  is-retraction-map-retraction-is-equivᵉ =
    is-retraction-map-retractionᵉ fᵉ retraction-is-equivᵉ
```

### Equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  equivᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equivᵉ = Σᵉ (Aᵉ → Bᵉ) is-equivᵉ

infix 6 _≃ᵉ_

_≃ᵉ_ : {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
Aᵉ ≃ᵉ Bᵉ = equivᵉ Aᵉ Bᵉ
```

### Components of an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  map-equivᵉ : Aᵉ → Bᵉ
  map-equivᵉ = pr1ᵉ eᵉ

  is-equiv-map-equivᵉ : is-equivᵉ map-equivᵉ
  is-equiv-map-equivᵉ = pr2ᵉ eᵉ

  section-map-equivᵉ : sectionᵉ map-equivᵉ
  section-map-equivᵉ = section-is-equivᵉ is-equiv-map-equivᵉ

  map-section-map-equivᵉ : Bᵉ → Aᵉ
  map-section-map-equivᵉ = map-sectionᵉ map-equivᵉ section-map-equivᵉ

  is-section-map-section-map-equivᵉ :
    is-sectionᵉ map-equivᵉ map-section-map-equivᵉ
  is-section-map-section-map-equivᵉ =
    is-section-map-sectionᵉ map-equivᵉ section-map-equivᵉ

  retraction-map-equivᵉ : retractionᵉ map-equivᵉ
  retraction-map-equivᵉ = retraction-is-equivᵉ is-equiv-map-equivᵉ

  map-retraction-map-equivᵉ : Bᵉ → Aᵉ
  map-retraction-map-equivᵉ = map-retractionᵉ map-equivᵉ retraction-map-equivᵉ

  is-retraction-map-retraction-map-equivᵉ :
    is-retractionᵉ map-equivᵉ map-retraction-map-equivᵉ
  is-retraction-map-retraction-map-equivᵉ =
    is-retraction-map-retractionᵉ map-equivᵉ retraction-map-equivᵉ
```

### The identity equivalence

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-equiv-idᵉ : is-equivᵉ (idᵉ {lᵉ} {Aᵉ})
  pr1ᵉ (pr1ᵉ is-equiv-idᵉ) = idᵉ
  pr2ᵉ (pr1ᵉ is-equiv-idᵉ) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ is-equiv-idᵉ) = idᵉ
  pr2ᵉ (pr2ᵉ is-equiv-idᵉ) = refl-htpyᵉ

  id-equivᵉ : Aᵉ ≃ᵉ Aᵉ
  pr1ᵉ id-equivᵉ = idᵉ
  pr2ᵉ id-equivᵉ = is-equiv-idᵉ
```

## Properties

### A map is invertible if and only if it is an equivalence

**Proof:**ᵉ Itᵉ isᵉ clearᵉ thatᵉ ifᵉ aᵉ mapᵉ isᵉ
[invertible](foundation-core.invertible-maps.md),ᵉ thenᵉ itᵉ isᵉ alsoᵉ biinvertible,ᵉ
andᵉ henceᵉ anᵉ equivalence.ᵉ

Forᵉ theᵉ converse,ᵉ supposeᵉ thatᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ anᵉ equivalenceᵉ with sectionᵉ
`gᵉ : Bᵉ → A`ᵉ equippedᵉ with `Gᵉ : fᵉ ∘ᵉ gᵉ ~ᵉ id`,ᵉ andᵉ retractionᵉ `hᵉ : Bᵉ → A`ᵉ equippedᵉ
with `Hᵉ : hᵉ ∘ᵉ fᵉ ~ᵉ id`.ᵉ Weᵉ claimᵉ thatᵉ theᵉ mapᵉ `gᵉ : Bᵉ → A`ᵉ isᵉ alsoᵉ aᵉ retraction.ᵉ
Toᵉ seeᵉ this,ᵉ weᵉ concatenateᵉ theᵉ followingᵉ homotopiesᵉ

```text
         H⁻¹ᵉ ·rᵉ gᵉ ·rᵉ fᵉ                  hᵉ ·lᵉ Gᵉ ·rᵉ fᵉ           Hᵉ
  gᵉ ∘ᵉ hᵉ --------------->ᵉ hᵉ ∘ᵉ fᵉ ∘ᵉ gᵉ ∘ᵉ fᵉ ------------->ᵉ hᵉ ∘ᵉ fᵉ ----->ᵉ id.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  is-equiv-is-invertible'ᵉ : is-invertibleᵉ fᵉ → is-equivᵉ fᵉ
  is-equiv-is-invertible'ᵉ (gᵉ ,ᵉ Hᵉ ,ᵉ Kᵉ) = ((gᵉ ,ᵉ Hᵉ) ,ᵉ (gᵉ ,ᵉ Kᵉ))

  is-equiv-is-invertibleᵉ :
    (gᵉ : Bᵉ → Aᵉ) (Hᵉ : fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ) (Kᵉ : gᵉ ∘ᵉ fᵉ ~ᵉ idᵉ) → is-equivᵉ fᵉ
  is-equiv-is-invertibleᵉ gᵉ Hᵉ Kᵉ = is-equiv-is-invertible'ᵉ (gᵉ ,ᵉ Hᵉ ,ᵉ Kᵉ)

  is-retraction-map-section-is-equivᵉ :
    (Hᵉ : is-equivᵉ fᵉ) → is-retractionᵉ fᵉ (map-section-is-equivᵉ Hᵉ)
  is-retraction-map-section-is-equivᵉ Hᵉ =
    ( ( inv-htpyᵉ
        ( ( is-retraction-map-retraction-is-equivᵉ Hᵉ) ·rᵉ
          ( map-section-is-equivᵉ Hᵉ ∘ᵉ fᵉ))) ∙hᵉ
      ( map-retraction-is-equivᵉ Hᵉ ·lᵉ is-section-map-section-is-equivᵉ Hᵉ ·rᵉ fᵉ)) ∙hᵉ
    ( is-retraction-map-retraction-is-equivᵉ Hᵉ)

  is-invertible-is-equivᵉ : is-equivᵉ fᵉ → is-invertibleᵉ fᵉ
  pr1ᵉ (is-invertible-is-equivᵉ Hᵉ) = map-section-is-equivᵉ Hᵉ
  pr1ᵉ (pr2ᵉ (is-invertible-is-equivᵉ Hᵉ)) = is-section-map-section-is-equivᵉ Hᵉ
  pr2ᵉ (pr2ᵉ (is-invertible-is-equivᵉ Hᵉ)) = is-retraction-map-section-is-equivᵉ Hᵉ
```

### Coherently invertible maps are equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  is-equiv-is-coherently-invertibleᵉ :
    is-coherently-invertibleᵉ fᵉ → is-equivᵉ fᵉ
  is-equiv-is-coherently-invertibleᵉ Hᵉ =
    is-equiv-is-invertible'ᵉ (is-invertible-is-coherently-invertibleᵉ Hᵉ)

  is-equiv-is-transpose-coherently-invertibleᵉ :
    is-transpose-coherently-invertibleᵉ fᵉ → is-equivᵉ fᵉ
  is-equiv-is-transpose-coherently-invertibleᵉ Hᵉ =
    is-equiv-is-invertible'ᵉ
      ( is-invertible-is-transpose-coherently-invertibleᵉ Hᵉ)
```

Theᵉ followingᵉ mapsᵉ areᵉ notᵉ simpleᵉ constructionsᵉ andᵉ shouldᵉ notᵉ beᵉ computedᵉ with.ᵉ
Therefore,ᵉ weᵉ markᵉ themᵉ asᵉ `abstract`.ᵉ

```agda
  abstract
    is-coherently-invertible-is-equivᵉ :
      is-equivᵉ fᵉ → is-coherently-invertibleᵉ fᵉ
    is-coherently-invertible-is-equivᵉ =
      is-coherently-invertible-is-invertibleᵉ ∘ᵉ is-invertible-is-equivᵉ

  abstract
    is-transpose-coherently-invertible-is-equivᵉ :
      is-equivᵉ fᵉ → is-transpose-coherently-invertibleᵉ fᵉ
    is-transpose-coherently-invertible-is-equivᵉ =
      is-transpose-coherently-invertible-is-invertibleᵉ ∘ᵉ is-invertible-is-equivᵉ
```

### Structure obtained from being coherently invertible

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} (Hᵉ : is-equivᵉ fᵉ)
  where

  map-inv-is-equivᵉ : Bᵉ → Aᵉ
  map-inv-is-equivᵉ = pr1ᵉ (is-invertible-is-equivᵉ Hᵉ)

  is-section-map-inv-is-equivᵉ : is-sectionᵉ fᵉ map-inv-is-equivᵉ
  is-section-map-inv-is-equivᵉ =
    is-section-map-inv-is-coherently-invertible-is-invertibleᵉ
      ( is-invertible-is-equivᵉ Hᵉ)

  is-retraction-map-inv-is-equivᵉ : is-retractionᵉ fᵉ map-inv-is-equivᵉ
  is-retraction-map-inv-is-equivᵉ =
    is-retraction-map-inv-is-coherently-invertible-is-invertibleᵉ
      ( is-invertible-is-equivᵉ Hᵉ)

  coherence-map-inv-is-equivᵉ :
    coherence-is-coherently-invertibleᵉ fᵉ
      ( map-inv-is-equivᵉ)
      ( is-section-map-inv-is-equivᵉ)
      ( is-retraction-map-inv-is-equivᵉ)
  coherence-map-inv-is-equivᵉ =
    coh-is-coherently-invertible-is-invertibleᵉ (is-invertible-is-equivᵉ Hᵉ)

  is-equiv-map-inv-is-equivᵉ : is-equivᵉ map-inv-is-equivᵉ
  is-equiv-map-inv-is-equivᵉ =
    is-equiv-is-invertibleᵉ fᵉ
      ( is-retraction-map-inv-is-equivᵉ)
      ( is-section-map-inv-is-equivᵉ)
```

### The inverse of an equivalence is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  map-inv-equivᵉ : Bᵉ → Aᵉ
  map-inv-equivᵉ = map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)

  is-section-map-inv-equivᵉ : is-sectionᵉ (map-equivᵉ eᵉ) map-inv-equivᵉ
  is-section-map-inv-equivᵉ = is-section-map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)

  is-retraction-map-inv-equivᵉ : is-retractionᵉ (map-equivᵉ eᵉ) map-inv-equivᵉ
  is-retraction-map-inv-equivᵉ =
    is-retraction-map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)

  coherence-map-inv-equivᵉ :
    coherence-is-coherently-invertibleᵉ
      ( map-equivᵉ eᵉ)
      ( map-inv-equivᵉ)
      ( is-section-map-inv-equivᵉ)
      ( is-retraction-map-inv-equivᵉ)
  coherence-map-inv-equivᵉ =
    coherence-map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)

  is-equiv-map-inv-equivᵉ : is-equivᵉ map-inv-equivᵉ
  is-equiv-map-inv-equivᵉ = is-equiv-map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)

  inv-equivᵉ : Bᵉ ≃ᵉ Aᵉ
  pr1ᵉ inv-equivᵉ = map-inv-equivᵉ
  pr2ᵉ inv-equivᵉ = is-equiv-map-inv-equivᵉ
```

### The 3-for-2 property of equivalences

Theᵉ **3-for-2ᵉ property**ᵉ ofᵉ equivalencesᵉ assertsᵉ thatᵉ forᵉ anyᵉ
[commutingᵉ triangle](foundation-core.commuting-triangles-of-maps.mdᵉ) ofᵉ mapsᵉ

```text
       hᵉ
  Aᵉ ------>ᵉ Bᵉ
   \ᵉ       /ᵉ
   f\ᵉ     /gᵉ
     \ᵉ   /ᵉ
      ∨ᵉ ∨ᵉ
       X,ᵉ
```

ifᵉ twoᵉ ofᵉ theᵉ threeᵉ mapsᵉ areᵉ equivalences,ᵉ thenᵉ soᵉ isᵉ theᵉ third.ᵉ

Weᵉ alsoᵉ record specialᵉ casesᵉ ofᵉ theᵉ 3-for-2ᵉ propertyᵉ ofᵉ equivalences,ᵉ where weᵉ
onlyᵉ assumeᵉ mapsᵉ `gᵉ : Bᵉ → X`ᵉ andᵉ `hᵉ : Aᵉ → B`.ᵉ Inᵉ thisᵉ specialᵉ case,ᵉ weᵉ setᵉ
`fᵉ :=ᵉ gᵉ ∘ᵉ h`ᵉ andᵉ theᵉ triangleᵉ commutesᵉ byᵉ `refl-htpy`.ᵉ

[Andréᵉ Joyal](https://en.wikipedia.org/wiki/André_Joyalᵉ) proposedᵉ callingᵉ thisᵉ
propertyᵉ theᵉ 3-for-2ᵉ property,ᵉ despiteᵉ mostᵉ mathematiciansᵉ callingᵉ itᵉ theᵉ
_2-out-of-3ᵉ property_.ᵉ Theᵉ storyᵉ goesᵉ thatᵉ onᵉ theᵉ produceᵉ marketᵉ isᵉ isᵉ commonᵉ to
advertiseᵉ aᵉ discountᵉ asᵉ "3-for-2".ᵉ Ifᵉ youᵉ buyᵉ twoᵉ apples,ᵉ thenᵉ youᵉ getᵉ theᵉ thirdᵉ
forᵉ free.ᵉ Similarly,ᵉ ifᵉ youᵉ proveᵉ thatᵉ twoᵉ mapsᵉ in aᵉ commutingᵉ triangleᵉ areᵉ
equivalences,ᵉ thenᵉ youᵉ getᵉ theᵉ thirdᵉ forᵉ free.ᵉ

#### The left map in a commuting triangle is an equivalence if the other two maps are equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Tᵉ : fᵉ ~ᵉ gᵉ ∘ᵉ hᵉ)
  where

  abstract
    is-equiv-left-map-triangleᵉ : is-equivᵉ hᵉ → is-equivᵉ gᵉ → is-equivᵉ fᵉ
    pr1ᵉ (is-equiv-left-map-triangleᵉ Hᵉ Gᵉ) =
      section-left-map-triangleᵉ fᵉ gᵉ hᵉ Tᵉ
        ( section-is-equivᵉ Hᵉ)
        ( section-is-equivᵉ Gᵉ)
    pr2ᵉ (is-equiv-left-map-triangleᵉ Hᵉ Gᵉ) =
      retraction-left-map-triangleᵉ fᵉ gᵉ hᵉ Tᵉ
        ( retraction-is-equivᵉ Gᵉ)
        ( retraction-is-equivᵉ Hᵉ)
```

#### The right map in a commuting triangle is an equivalence if the other two maps are equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ ∘ᵉ hᵉ)
  where

  abstract
    is-equiv-right-map-triangleᵉ :
      is-equivᵉ fᵉ → is-equivᵉ hᵉ → is-equivᵉ gᵉ
    is-equiv-right-map-triangleᵉ
      ( section-fᵉ ,ᵉ retraction-fᵉ)
      ( (shᵉ ,ᵉ is-section-shᵉ) ,ᵉ retraction-hᵉ) =
        ( pairᵉ
          ( section-right-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ section-fᵉ)
          ( retraction-left-map-triangleᵉ gᵉ fᵉ shᵉ
            ( inv-htpyᵉ
              ( ( Hᵉ ·rᵉ map-sectionᵉ hᵉ (shᵉ ,ᵉ is-section-shᵉ)) ∙hᵉ
                ( gᵉ ·lᵉ is-section-map-sectionᵉ hᵉ (shᵉ ,ᵉ is-section-shᵉ))))
            ( retraction-fᵉ)
            ( hᵉ ,ᵉ is-section-shᵉ)))
```

#### If the left and right maps in a commuting triangle are equivalences, then the top map is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ ∘ᵉ hᵉ)
  where

  section-is-equiv-top-map-triangleᵉ :
    is-equivᵉ gᵉ → is-equivᵉ fᵉ → sectionᵉ hᵉ
  section-is-equiv-top-map-triangleᵉ Gᵉ Fᵉ =
    section-left-map-triangleᵉ hᵉ
      ( map-retraction-is-equivᵉ Gᵉ)
      ( fᵉ)
      ( inv-htpyᵉ
        ( ( map-retractionᵉ gᵉ (retraction-is-equivᵉ Gᵉ) ·lᵉ Hᵉ) ∙hᵉ
          ( is-retraction-map-retractionᵉ gᵉ (retraction-is-equivᵉ Gᵉ) ·rᵉ hᵉ)))
      ( section-is-equivᵉ Fᵉ)
      ( gᵉ ,ᵉ is-retraction-map-retraction-is-equivᵉ Gᵉ)

  map-section-is-equiv-top-map-triangleᵉ :
    is-equivᵉ gᵉ → is-equivᵉ fᵉ → Bᵉ → Aᵉ
  map-section-is-equiv-top-map-triangleᵉ Gᵉ Fᵉ =
    map-sectionᵉ hᵉ (section-is-equiv-top-map-triangleᵉ Gᵉ Fᵉ)

  abstract
    is-equiv-top-map-triangleᵉ :
      is-equivᵉ gᵉ → is-equivᵉ fᵉ → is-equivᵉ hᵉ
    is-equiv-top-map-triangleᵉ
      ( section-gᵉ ,ᵉ (rgᵉ ,ᵉ is-retraction-rgᵉ))
      ( section-fᵉ ,ᵉ retraction-fᵉ) =
      ( pairᵉ
        ( section-left-map-triangleᵉ hᵉ rgᵉ fᵉ
          ( inv-htpyᵉ
            ( ( map-retractionᵉ gᵉ (rgᵉ ,ᵉ is-retraction-rgᵉ) ·lᵉ Hᵉ) ∙hᵉ
              ( is-retraction-map-retractionᵉ gᵉ (rgᵉ ,ᵉ is-retraction-rgᵉ) ·rᵉ hᵉ)))
          ( section-fᵉ)
          ( gᵉ ,ᵉ is-retraction-rgᵉ))
        ( retraction-top-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ retraction-fᵉ))
```

#### Composites of equivalences are equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  where

  abstract
    is-equiv-compᵉ :
      (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) → is-equivᵉ hᵉ → is-equivᵉ gᵉ → is-equivᵉ (gᵉ ∘ᵉ hᵉ)
    pr1ᵉ (is-equiv-compᵉ gᵉ hᵉ (shᵉ ,ᵉ rhᵉ) (sgᵉ ,ᵉ rgᵉ)) = section-compᵉ gᵉ hᵉ shᵉ sgᵉ
    pr2ᵉ (is-equiv-compᵉ gᵉ hᵉ (shᵉ ,ᵉ rhᵉ) (sgᵉ ,ᵉ rgᵉ)) = retraction-compᵉ gᵉ hᵉ rgᵉ rhᵉ

  comp-equivᵉ : Bᵉ ≃ᵉ Xᵉ → Aᵉ ≃ᵉ Bᵉ → Aᵉ ≃ᵉ Xᵉ
  pr1ᵉ (comp-equivᵉ gᵉ hᵉ) = map-equivᵉ gᵉ ∘ᵉ map-equivᵉ hᵉ
  pr2ᵉ (comp-equivᵉ gᵉ hᵉ) = is-equiv-compᵉ (pr1ᵉ gᵉ) (pr1ᵉ hᵉ) (pr2ᵉ hᵉ) (pr2ᵉ gᵉ)

  infixr 15 _∘eᵉ_
  _∘eᵉ_ : Bᵉ ≃ᵉ Xᵉ → Aᵉ ≃ᵉ Bᵉ → Aᵉ ≃ᵉ Xᵉ
  _∘eᵉ_ = comp-equivᵉ
```

#### If a composite and its right factor are equivalences, then so is its left factor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  where

  is-equiv-left-factorᵉ :
    (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) →
    is-equivᵉ (gᵉ ∘ᵉ hᵉ) → is-equivᵉ hᵉ → is-equivᵉ gᵉ
  is-equiv-left-factorᵉ gᵉ hᵉ is-equiv-ghᵉ is-equiv-hᵉ =
      is-equiv-right-map-triangleᵉ (gᵉ ∘ᵉ hᵉ) gᵉ hᵉ refl-htpyᵉ is-equiv-ghᵉ is-equiv-hᵉ
```

#### If a composite and its left factor are equivalences, then so is its right factor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  where

  is-equiv-right-factorᵉ :
    (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) →
    is-equivᵉ gᵉ → is-equivᵉ (gᵉ ∘ᵉ hᵉ) → is-equivᵉ hᵉ
  is-equiv-right-factorᵉ gᵉ hᵉ is-equiv-gᵉ is-equiv-ghᵉ =
    is-equiv-top-map-triangleᵉ (gᵉ ∘ᵉ hᵉ) gᵉ hᵉ refl-htpyᵉ is-equiv-gᵉ is-equiv-ghᵉ
```

### Equivalences are closed under homotopies

Weᵉ showᵉ thatᵉ ifᵉ `fᵉ ~ᵉ g`,ᵉ thenᵉ `f`ᵉ isᵉ anᵉ equivalenceᵉ ifᵉ andᵉ onlyᵉ ifᵉ `g`ᵉ isᵉ anᵉ
equivalence.ᵉ Furthermore,ᵉ weᵉ showᵉ thatᵉ ifᵉ `f`ᵉ andᵉ `g`ᵉ areᵉ homotopicᵉ equivaleces,ᵉ
thenᵉ theirᵉ inversesᵉ areᵉ alsoᵉ homotopic.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-equiv-htpyᵉ :
      {fᵉ : Aᵉ → Bᵉ} (gᵉ : Aᵉ → Bᵉ) → fᵉ ~ᵉ gᵉ → is-equivᵉ gᵉ → is-equivᵉ fᵉ
    pr1ᵉ (pr1ᵉ (is-equiv-htpyᵉ gᵉ Gᵉ ((hᵉ ,ᵉ Hᵉ) ,ᵉ (kᵉ ,ᵉ Kᵉ)))) = hᵉ
    pr2ᵉ (pr1ᵉ (is-equiv-htpyᵉ gᵉ Gᵉ ((hᵉ ,ᵉ Hᵉ) ,ᵉ (kᵉ ,ᵉ Kᵉ)))) = (Gᵉ ·rᵉ hᵉ) ∙hᵉ Hᵉ
    pr1ᵉ (pr2ᵉ (is-equiv-htpyᵉ gᵉ Gᵉ ((hᵉ ,ᵉ Hᵉ) ,ᵉ (kᵉ ,ᵉ Kᵉ)))) = kᵉ
    pr2ᵉ (pr2ᵉ (is-equiv-htpyᵉ gᵉ Gᵉ ((hᵉ ,ᵉ Hᵉ) ,ᵉ (kᵉ ,ᵉ Kᵉ)))) = (kᵉ ·lᵉ Gᵉ) ∙hᵉ Kᵉ

  is-equiv-htpy-equivᵉ : {fᵉ : Aᵉ → Bᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) → fᵉ ~ᵉ map-equivᵉ eᵉ → is-equivᵉ fᵉ
  is-equiv-htpy-equivᵉ eᵉ Hᵉ = is-equiv-htpyᵉ (map-equivᵉ eᵉ) Hᵉ (is-equiv-map-equivᵉ eᵉ)

  abstract
    is-equiv-htpy'ᵉ : (fᵉ : Aᵉ → Bᵉ) {gᵉ : Aᵉ → Bᵉ} → fᵉ ~ᵉ gᵉ → is-equivᵉ fᵉ → is-equivᵉ gᵉ
    is-equiv-htpy'ᵉ fᵉ Hᵉ = is-equiv-htpyᵉ fᵉ (inv-htpyᵉ Hᵉ)

  is-equiv-htpy-equiv'ᵉ : (eᵉ : Aᵉ ≃ᵉ Bᵉ) {gᵉ : Aᵉ → Bᵉ} → map-equivᵉ eᵉ ~ᵉ gᵉ → is-equivᵉ gᵉ
  is-equiv-htpy-equiv'ᵉ eᵉ Hᵉ =
    is-equiv-htpy'ᵉ (map-equivᵉ eᵉ) Hᵉ (is-equiv-map-equivᵉ eᵉ)

  htpy-map-inv-is-equivᵉ :
    {fᵉ gᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) (Fᵉ : is-equivᵉ fᵉ) (Gᵉ : is-equivᵉ gᵉ) →
    map-inv-is-equivᵉ Fᵉ ~ᵉ map-inv-is-equivᵉ Gᵉ
  htpy-map-inv-is-equivᵉ Hᵉ Fᵉ Gᵉ =
    htpy-map-inv-is-invertibleᵉ Hᵉ
      ( is-invertible-is-equivᵉ Fᵉ)
      ( is-invertible-is-equivᵉ Gᵉ)
```

### Any retraction of an equivalence is an equivalence

```agda
abstract
  is-equiv-is-retractionᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ} →
    is-equivᵉ fᵉ → (gᵉ ∘ᵉ fᵉ) ~ᵉ idᵉ → is-equivᵉ gᵉ
  is-equiv-is-retractionᵉ {Aᵉ = Aᵉ} {fᵉ = fᵉ} {gᵉ = gᵉ} is-equiv-fᵉ Hᵉ =
    is-equiv-right-map-triangleᵉ idᵉ gᵉ fᵉ (inv-htpyᵉ Hᵉ) is-equiv-idᵉ is-equiv-fᵉ
```

### Any section of an equivalence is an equivalence

```agda
abstract
  is-equiv-is-sectionᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ} →
    is-equivᵉ fᵉ → fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ → is-equivᵉ gᵉ
  is-equiv-is-sectionᵉ {Bᵉ = Bᵉ} {fᵉ = fᵉ} {gᵉ = gᵉ} is-equiv-fᵉ Hᵉ =
    is-equiv-top-map-triangleᵉ idᵉ fᵉ gᵉ (inv-htpyᵉ Hᵉ) is-equiv-fᵉ is-equiv-idᵉ
```

### If a section of `f` is an equivalence, then `f` is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-equiv-is-equiv-sectionᵉ :
      (sᵉ : sectionᵉ fᵉ) → is-equivᵉ (map-sectionᵉ fᵉ sᵉ) → is-equivᵉ fᵉ
    is-equiv-is-equiv-sectionᵉ (gᵉ ,ᵉ Gᵉ) Sᵉ = is-equiv-is-retractionᵉ Sᵉ Gᵉ
```

### If a retraction of `f` is an equivalence, then `f` is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-equiv-is-equiv-retractionᵉ :
      (rᵉ : retractionᵉ fᵉ) → is-equivᵉ (map-retractionᵉ fᵉ rᵉ) → is-equivᵉ fᵉ
    is-equiv-is-equiv-retractionᵉ (gᵉ ,ᵉ Gᵉ) Rᵉ = is-equiv-is-sectionᵉ Rᵉ Gᵉ
```

### Any section of an equivalence is homotopic to its inverse

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  htpy-map-inv-equiv-sectionᵉ :
    (fᵉ : sectionᵉ (map-equivᵉ eᵉ)) → map-inv-equivᵉ eᵉ ~ᵉ map-sectionᵉ (map-equivᵉ eᵉ) fᵉ
  htpy-map-inv-equiv-sectionᵉ (fᵉ ,ᵉ Hᵉ) =
    (map-inv-equivᵉ eᵉ ·lᵉ inv-htpyᵉ Hᵉ) ∙hᵉ (is-retraction-map-inv-equivᵉ eᵉ ·rᵉ fᵉ)
```

### Any retraction of an equivalence is homotopic to its inverse

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  htpy-map-inv-equiv-retractionᵉ :
    (fᵉ : retractionᵉ (map-equivᵉ eᵉ)) →
    map-inv-equivᵉ eᵉ ~ᵉ map-retractionᵉ (map-equivᵉ eᵉ) fᵉ
  htpy-map-inv-equiv-retractionᵉ (fᵉ ,ᵉ Hᵉ) =
    (inv-htpyᵉ Hᵉ ·rᵉ map-inv-equivᵉ eᵉ) ∙hᵉ (fᵉ ·lᵉ is-section-map-inv-equivᵉ eᵉ)
```

### Equivalences in commuting squares

```agda
is-equiv-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  {fᵉ : Aᵉ → Bᵉ} {gᵉ : Xᵉ → Yᵉ} (iᵉ : Aᵉ ≃ᵉ Xᵉ) (jᵉ : Bᵉ ≃ᵉ Yᵉ)
  (Hᵉ : (map-equivᵉ jᵉ ∘ᵉ fᵉ) ~ᵉ (gᵉ ∘ᵉ map-equivᵉ iᵉ)) → is-equivᵉ gᵉ → is-equivᵉ fᵉ
is-equiv-equivᵉ {fᵉ = fᵉ} {gᵉ} iᵉ jᵉ Hᵉ Kᵉ =
  is-equiv-right-factorᵉ
    ( map-equivᵉ jᵉ)
    ( fᵉ)
    ( is-equiv-map-equivᵉ jᵉ)
    ( is-equiv-left-map-triangleᵉ
      ( map-equivᵉ jᵉ ∘ᵉ fᵉ)
      ( gᵉ)
      ( map-equivᵉ iᵉ)
      ( Hᵉ)
      ( is-equiv-map-equivᵉ iᵉ)
      ( Kᵉ))

is-equiv-equiv'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  {fᵉ : Aᵉ → Bᵉ} {gᵉ : Xᵉ → Yᵉ} (iᵉ : Aᵉ ≃ᵉ Xᵉ) (jᵉ : Bᵉ ≃ᵉ Yᵉ)
  (Hᵉ : (map-equivᵉ jᵉ ∘ᵉ fᵉ) ~ᵉ (gᵉ ∘ᵉ map-equivᵉ iᵉ)) → is-equivᵉ fᵉ → is-equivᵉ gᵉ
is-equiv-equiv'ᵉ {fᵉ = fᵉ} {gᵉ} iᵉ jᵉ Hᵉ Kᵉ =
  is-equiv-left-factorᵉ
    ( gᵉ)
    ( map-equivᵉ iᵉ)
    ( is-equiv-left-map-triangleᵉ
      ( gᵉ ∘ᵉ map-equivᵉ iᵉ)
      ( map-equivᵉ jᵉ)
      ( fᵉ)
      ( inv-htpyᵉ Hᵉ)
      ( Kᵉ)
      ( is-equiv-map-equivᵉ jᵉ))
    ( is-equiv-map-equivᵉ iᵉ)
```

Weᵉ willᵉ assumeᵉ aᵉ commutingᵉ squareᵉ

```text
        hᵉ
    Aᵉ ----->ᵉ Cᵉ
    |        |
  fᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Dᵉ
        iᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Cᵉ → Dᵉ) (hᵉ : Aᵉ → Cᵉ) (iᵉ : Bᵉ → Dᵉ) (Hᵉ : (iᵉ ∘ᵉ fᵉ) ~ᵉ (gᵉ ∘ᵉ hᵉ))
  where

  abstract
    is-equiv-top-is-equiv-left-squareᵉ :
      is-equivᵉ iᵉ → is-equivᵉ fᵉ → is-equivᵉ gᵉ → is-equivᵉ hᵉ
    is-equiv-top-is-equiv-left-squareᵉ Eiᵉ Efᵉ Egᵉ =
      is-equiv-top-map-triangleᵉ (iᵉ ∘ᵉ fᵉ) gᵉ hᵉ Hᵉ Egᵉ (is-equiv-compᵉ iᵉ fᵉ Efᵉ Eiᵉ)

  abstract
    is-equiv-top-is-equiv-bottom-squareᵉ :
      is-equivᵉ fᵉ → is-equivᵉ gᵉ → is-equivᵉ iᵉ → is-equivᵉ hᵉ
    is-equiv-top-is-equiv-bottom-squareᵉ Efᵉ Egᵉ Eiᵉ =
      is-equiv-top-map-triangleᵉ (iᵉ ∘ᵉ fᵉ) gᵉ hᵉ Hᵉ Egᵉ (is-equiv-compᵉ iᵉ fᵉ Efᵉ Eiᵉ)

  abstract
    is-equiv-bottom-is-equiv-top-squareᵉ :
      is-equivᵉ fᵉ → is-equivᵉ gᵉ → is-equivᵉ hᵉ → is-equivᵉ iᵉ
    is-equiv-bottom-is-equiv-top-squareᵉ Efᵉ Egᵉ Ehᵉ =
      is-equiv-left-factorᵉ iᵉ fᵉ
        ( is-equiv-left-map-triangleᵉ (iᵉ ∘ᵉ fᵉ) gᵉ hᵉ Hᵉ Ehᵉ Egᵉ)
        ( Efᵉ)

  abstract
    is-equiv-left-is-equiv-right-squareᵉ :
      is-equivᵉ hᵉ → is-equivᵉ iᵉ → is-equivᵉ gᵉ → is-equivᵉ fᵉ
    is-equiv-left-is-equiv-right-squareᵉ Ehᵉ Eiᵉ Egᵉ =
      is-equiv-right-factorᵉ iᵉ fᵉ Eiᵉ
        ( is-equiv-left-map-triangleᵉ (iᵉ ∘ᵉ fᵉ) gᵉ hᵉ Hᵉ Ehᵉ Egᵉ)

  abstract
    is-equiv-right-is-equiv-left-squareᵉ :
      is-equivᵉ hᵉ → is-equivᵉ iᵉ → is-equivᵉ fᵉ → is-equivᵉ gᵉ
    is-equiv-right-is-equiv-left-squareᵉ Ehᵉ Eiᵉ Efᵉ =
      is-equiv-right-map-triangleᵉ (iᵉ ∘ᵉ fᵉ) gᵉ hᵉ Hᵉ (is-equiv-compᵉ iᵉ fᵉ Efᵉ Eiᵉ) Ehᵉ
```

### Equivalences are embeddings

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-emb-is-equivᵉ :
      {fᵉ : Aᵉ → Bᵉ} → is-equivᵉ fᵉ → (xᵉ yᵉ : Aᵉ) → is-equivᵉ (apᵉ fᵉ {xᵉ} {yᵉ})
    is-emb-is-equivᵉ Hᵉ xᵉ yᵉ =
      is-equiv-is-invertible'ᵉ
        ( is-invertible-ap-is-coherently-invertibleᵉ
          ( is-coherently-invertible-is-equivᵉ Hᵉ))

  equiv-apᵉ :
    (eᵉ : Aᵉ ≃ᵉ Bᵉ) (xᵉ yᵉ : Aᵉ) → (xᵉ ＝ᵉ yᵉ) ≃ᵉ (map-equivᵉ eᵉ xᵉ ＝ᵉ map-equivᵉ eᵉ yᵉ)
  pr1ᵉ (equiv-apᵉ eᵉ xᵉ yᵉ) = apᵉ (map-equivᵉ eᵉ)
  pr2ᵉ (equiv-apᵉ eᵉ xᵉ yᵉ) = is-emb-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) xᵉ yᵉ

  map-inv-equiv-apᵉ :
    (eᵉ : Aᵉ ≃ᵉ Bᵉ) (xᵉ yᵉ : Aᵉ) → map-equivᵉ eᵉ xᵉ ＝ᵉ map-equivᵉ eᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  map-inv-equiv-apᵉ eᵉ xᵉ yᵉ = map-inv-equivᵉ (equiv-apᵉ eᵉ xᵉ yᵉ)
```

## Equivalence reasoning

Equivalencesᵉ canᵉ beᵉ constructedᵉ byᵉ equationalᵉ reasoningᵉ in theᵉ followingᵉ wayᵉ:

```text
equivalence-reasoningᵉ
  Xᵉ ≃ᵉ Yᵉ byᵉ equiv-1ᵉ
    ≃ᵉ Zᵉ byᵉ equiv-2ᵉ
    ≃ᵉ Vᵉ byᵉ equiv-3ᵉ
```

Theᵉ equivalenceᵉ constructedᵉ in thisᵉ wayᵉ isᵉ `equiv-1ᵉ ∘eᵉ (equiv-2ᵉ ∘eᵉ equiv-3)`,ᵉ
i.e.,ᵉ theᵉ equivivalenceᵉ isᵉ associatedᵉ fullyᵉ to theᵉ right.ᵉ

**Note.**ᵉ Inᵉ situationsᵉ where itᵉ isᵉ importantᵉ to haveᵉ preciseᵉ controlᵉ overᵉ anᵉ
equivalenceᵉ orᵉ itsᵉ inverse,ᵉ itᵉ isᵉ oftenᵉ betterᵉ to avoidᵉ makingᵉ useᵉ ofᵉ
equivalenceᵉ reasoning.ᵉ Forᵉ example,ᵉ sinceᵉ manyᵉ ofᵉ theᵉ entriesᵉ provingᵉ thatᵉ aᵉ mapᵉ
isᵉ anᵉ equivalenceᵉ areᵉ markedᵉ asᵉ `abstract`ᵉ in agda-unimath,ᵉ theᵉ inverseᵉ ofᵉ anᵉ
equivalenceᵉ oftenᵉ doesᵉ notᵉ computeᵉ to anyᵉ mapᵉ thatᵉ oneᵉ mightᵉ expectᵉ theᵉ inverseᵉ
to be.ᵉ Ifᵉ inversesᵉ ofᵉ equivalencesᵉ areᵉ usedᵉ in equivalenceᵉ reasoning,ᵉ thisᵉ
resultsᵉ in aᵉ composedᵉ equivalenceᵉ thatᵉ alsoᵉ doesᵉ notᵉ computeᵉ to anyᵉ expectedᵉ
underlyingᵉ map.ᵉ

Evenᵉ ifᵉ aᵉ proofᵉ byᵉ equivalenceᵉ reasoningᵉ isᵉ clearᵉ to theᵉ humanᵉ reader,ᵉ
constructingᵉ equivalencesᵉ byᵉ handᵉ byᵉ constructingᵉ mapsᵉ backᵉ andᵉ forthᵉ andᵉ twoᵉ
homotopiesᵉ witnessingᵉ thatᵉ theyᵉ areᵉ mutualᵉ inversesᵉ isᵉ oftenᵉ theᵉ mostᵉ
straigtforwardᵉ solutionᵉ thatᵉ givesᵉ theᵉ bestᵉ expectedᵉ computationalᵉ behaviorᵉ ofᵉ
theᵉ constructedᵉ equivalence.ᵉ Inᵉ particular,ᵉ ifᵉ theᵉ underlyingᵉ mapᵉ orᵉ itsᵉ inverseᵉ
areᵉ noteworthyᵉ maps,ᵉ itᵉ isᵉ goodᵉ practiceᵉ to defineᵉ themᵉ directlyᵉ ratherᵉ thanᵉ asᵉ
underlyingᵉ mapsᵉ ofᵉ equivalencesᵉ constructedᵉ byᵉ equivalenceᵉ reasoning.ᵉ

```agda
infixl 1 equivalence-reasoningᵉ_
infixl 0 step-equivalence-reasoningᵉ

equivalence-reasoningᵉ_ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) → Xᵉ ≃ᵉ Xᵉ
equivalence-reasoningᵉ Xᵉ = id-equivᵉ

step-equivalence-reasoningᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
  (Xᵉ ≃ᵉ Yᵉ) → (Zᵉ : UUᵉ l3ᵉ) → (Yᵉ ≃ᵉ Zᵉ) → (Xᵉ ≃ᵉ Zᵉ)
step-equivalence-reasoningᵉ eᵉ Zᵉ fᵉ = fᵉ ∘eᵉ eᵉ

syntax step-equivalence-reasoningᵉ eᵉ Zᵉ fᵉ = eᵉ ≃ᵉ Zᵉ byᵉ fᵉ
```

## See also

-ᵉ Forᵉ theᵉ notionᵉ ofᵉ coherentlyᵉ invertibleᵉ maps,ᵉ alsoᵉ knownᵉ asᵉ half-adjointᵉ
  equivalences,ᵉ seeᵉ
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ mapsᵉ with contractibleᵉ fibersᵉ seeᵉ
  [`foundation.contractible-maps`](foundation.contractible-maps.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ path-splitᵉ mapsᵉ seeᵉ
  [`foundation.path-split-maps`](foundation.path-split-maps.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ finitelyᵉ coherentᵉ equivalence,ᵉ seeᵉ
  [`foundation.finitely-coherent-equivalence`)(foundation.finitely-coherent-equivalence.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ finitelyᵉ coherentlyᵉ invertibleᵉ map,ᵉ seeᵉ
  [`foundation.finitely-coherently-invertible-map`)(foundation.finitely-coherently-invertible-map.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ infinitelyᵉ coherentᵉ equivalence,ᵉ seeᵉ
  [`foundation.infinitely-coherent-equivalences`](foundation.infinitely-coherent-equivalences.md).ᵉ

### Table of files about function types, composition, and equivalences

{{#includeᵉ tables/composition.mdᵉ}}