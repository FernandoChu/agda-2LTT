# Sections

```agda
module foundation-core.sectionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Aᵉ **section**ᵉ ofᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ consistsᵉ ofᵉ aᵉ mapᵉ `sᵉ : Bᵉ → A`ᵉ equippedᵉ with aᵉ
homotopyᵉ `fᵉ ∘ᵉ sᵉ ~ᵉ id`.ᵉ Inᵉ otherᵉ words,ᵉ aᵉ sectionᵉ ofᵉ aᵉ mapᵉ `f`ᵉ isᵉ aᵉ rightᵉ inverseᵉ
ofᵉ `f`.ᵉ Forᵉ example,ᵉ everyᵉ dependentᵉ functionᵉ inducesᵉ aᵉ sectionᵉ ofᵉ theᵉ
projectionᵉ map.ᵉ

Noteᵉ thatᵉ unlikeᵉ retractions,ᵉ sectionsᵉ don'tᵉ induceᵉ sectionsᵉ onᵉ identityᵉ types.ᵉ
Aᵉ mapᵉ `f`ᵉ equippedᵉ with aᵉ sectionᵉ suchᵉ thatᵉ allᵉ
[actionsᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ)
`apᵉ fᵉ : (xᵉ ＝ᵉ yᵉ) → (fᵉ xᵉ ＝ᵉ fᵉ y)`ᵉ comeᵉ equippedᵉ with sectionsᵉ isᵉ calledᵉ aᵉ
[pathᵉ split](foundation-core.path-split-maps.mdᵉ) map.ᵉ Theᵉ conditionᵉ ofᵉ beingᵉ
pathᵉ splitᵉ isᵉ equivalentᵉ to beingᵉ anᵉ
[equivalence](foundation-core.equivalences.md).ᵉ

## Definition

### The predicate of being a section of a map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-sectionᵉ : (Bᵉ → Aᵉ) → UUᵉ l2ᵉ
  is-sectionᵉ gᵉ = fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ
```

### The type of sections of a map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  sectionᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  sectionᵉ = Σᵉ (Bᵉ → Aᵉ) (is-sectionᵉ fᵉ)

  map-sectionᵉ : sectionᵉ → Bᵉ → Aᵉ
  map-sectionᵉ = pr1ᵉ

  is-section-map-sectionᵉ : (sᵉ : sectionᵉ) → is-sectionᵉ fᵉ (map-sectionᵉ sᵉ)
  is-section-map-sectionᵉ = pr2ᵉ
```

## Properties

### If `g ∘ h` has a section then `g` has a section

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (sᵉ : sectionᵉ (gᵉ ∘ᵉ hᵉ))
  where

  map-section-left-factorᵉ : Xᵉ → Bᵉ
  map-section-left-factorᵉ = hᵉ ∘ᵉ map-sectionᵉ (gᵉ ∘ᵉ hᵉ) sᵉ

  is-section-map-section-left-factorᵉ : is-sectionᵉ gᵉ map-section-left-factorᵉ
  is-section-map-section-left-factorᵉ = pr2ᵉ sᵉ

  section-left-factorᵉ : sectionᵉ gᵉ
  pr1ᵉ section-left-factorᵉ = map-section-left-factorᵉ
  pr2ᵉ section-left-factorᵉ = is-section-map-section-left-factorᵉ
```

### Composites of sections are sections of composites

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (tᵉ : sectionᵉ hᵉ) (sᵉ : sectionᵉ gᵉ)
  where

  map-section-compᵉ : Xᵉ → Aᵉ
  map-section-compᵉ = map-sectionᵉ hᵉ tᵉ ∘ᵉ map-sectionᵉ gᵉ sᵉ

  is-section-map-section-compᵉ :
    is-sectionᵉ (gᵉ ∘ᵉ hᵉ) map-section-compᵉ
  is-section-map-section-compᵉ =
    ( gᵉ ·lᵉ (is-section-map-sectionᵉ hᵉ tᵉ ·rᵉ map-sectionᵉ gᵉ sᵉ)) ∙hᵉ
    ( is-section-map-sectionᵉ gᵉ sᵉ)

  section-compᵉ : sectionᵉ (gᵉ ∘ᵉ hᵉ)
  pr1ᵉ section-compᵉ = map-section-compᵉ
  pr2ᵉ section-compᵉ = is-section-map-section-compᵉ
```

### In a commuting triangle `g ∘ h ~ f`, any section of `f` induces a section of `g`

Inᵉ aᵉ commutingᵉ triangleᵉ ofᵉ theᵉ formᵉ

```text
       hᵉ
  Aᵉ ------>ᵉ Bᵉ
   \ᵉ       /ᵉ
   f\ᵉ     /gᵉ
     \ᵉ   /ᵉ
      ∨ᵉ ∨ᵉ
       X,ᵉ
```

ifᵉ `sᵉ : Xᵉ → A`ᵉ isᵉ aᵉ sectionᵉ ofᵉ theᵉ mapᵉ `f`ᵉ onᵉ theᵉ left,ᵉ thenᵉ `hᵉ ∘ᵉ s`ᵉ isᵉ aᵉ
sectionᵉ ofᵉ theᵉ mapᵉ `g`ᵉ onᵉ theᵉ right.ᵉ

Noteᵉ: Inᵉ thisᵉ fileᵉ weᵉ areᵉ unableᵉ to useᵉ theᵉ definitionᵉ ofᵉ
[commutingᵉ triangles](foundation-core.commuting-triangles-of-maps.md),ᵉ becauseᵉ
thatᵉ wouldᵉ resultᵉ in aᵉ cyclicᵉ module dependency.ᵉ

Weᵉ stateᵉ twoᵉ versionsᵉ: oneᵉ with aᵉ homotopyᵉ `gᵉ ∘ᵉ hᵉ ~ᵉ f`,ᵉ andᵉ theᵉ otherᵉ with aᵉ
homotopyᵉ `fᵉ ~ᵉ gᵉ ∘ᵉ h`.ᵉ Ourᵉ conventionᵉ forᵉ commutingᵉ trianglesᵉ ofᵉ mapsᵉ isᵉ thatᵉ theᵉ
homotopyᵉ isᵉ specifiedᵉ in theᵉ secondᵉ way,ᵉ i.e.,ᵉ asᵉ `fᵉ ~ᵉ gᵉ ∘ᵉ h`.ᵉ

#### First version, with the commutativity of the triangle opposite to our convention

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (H'ᵉ : gᵉ ∘ᵉ hᵉ ~ᵉ fᵉ) (sᵉ : sectionᵉ fᵉ)
  where

  map-section-right-map-triangle'ᵉ : Xᵉ → Bᵉ
  map-section-right-map-triangle'ᵉ = hᵉ ∘ᵉ map-sectionᵉ fᵉ sᵉ

  is-section-map-section-right-map-triangle'ᵉ :
    is-sectionᵉ gᵉ map-section-right-map-triangle'ᵉ
  is-section-map-section-right-map-triangle'ᵉ =
    (H'ᵉ ·rᵉ map-sectionᵉ fᵉ sᵉ) ∙hᵉ is-section-map-sectionᵉ fᵉ sᵉ

  section-right-map-triangle'ᵉ : sectionᵉ gᵉ
  pr1ᵉ section-right-map-triangle'ᵉ =
    map-section-right-map-triangle'ᵉ
  pr2ᵉ section-right-map-triangle'ᵉ =
    is-section-map-section-right-map-triangle'ᵉ
```

#### Second version, with the commutativity of the triangle accoring to our convention

Weᵉ stateᵉ theᵉ sameᵉ resultᵉ asᵉ theᵉ previousᵉ result,ᵉ onlyᵉ with theᵉ homotopyᵉ
witnessingᵉ theᵉ commutativityᵉ ofᵉ theᵉ triangleᵉ inverted.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ ∘ᵉ hᵉ) (sᵉ : sectionᵉ fᵉ)
  where

  map-section-right-map-triangleᵉ : Xᵉ → Bᵉ
  map-section-right-map-triangleᵉ =
    map-section-right-map-triangle'ᵉ fᵉ gᵉ hᵉ (inv-htpyᵉ Hᵉ) sᵉ

  is-section-map-section-right-map-triangleᵉ :
    is-sectionᵉ gᵉ map-section-right-map-triangleᵉ
  is-section-map-section-right-map-triangleᵉ =
    is-section-map-section-right-map-triangle'ᵉ fᵉ gᵉ hᵉ (inv-htpyᵉ Hᵉ) sᵉ

  section-right-map-triangleᵉ : sectionᵉ gᵉ
  section-right-map-triangleᵉ =
    section-right-map-triangle'ᵉ fᵉ gᵉ hᵉ (inv-htpyᵉ Hᵉ) sᵉ
```

### Composites of sections in commuting triangles are sections

Inᵉ aᵉ commutingᵉ triangleᵉ ofᵉ theᵉ formᵉ

```text
       hᵉ
  Aᵉ ------>ᵉ Bᵉ
   \ᵉ       /ᵉ
   f\ᵉ     /gᵉ
     \ᵉ   /ᵉ
      ∨ᵉ ∨ᵉ
       X,ᵉ
```

ifᵉ `sᵉ : Xᵉ → B`ᵉ isᵉ aᵉ sectionᵉ ofᵉ theᵉ mapᵉ `g`ᵉ onᵉ theᵉ rightᵉ andᵉ `tᵉ : Bᵉ → A`ᵉ isᵉ aᵉ
sectionᵉ ofᵉ theᵉ mapᵉ `h`ᵉ onᵉ top,ᵉ thenᵉ `tᵉ ∘ᵉ s`ᵉ isᵉ aᵉ sectionᵉ ofᵉ theᵉ mapᵉ `f`ᵉ onᵉ theᵉ
left.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ ∘ᵉ hᵉ) (tᵉ : sectionᵉ hᵉ)
  where

  map-section-left-map-triangleᵉ : sectionᵉ gᵉ → Xᵉ → Aᵉ
  map-section-left-map-triangleᵉ sᵉ = map-section-compᵉ gᵉ hᵉ tᵉ sᵉ

  is-section-map-section-left-map-triangleᵉ :
    (sᵉ : sectionᵉ gᵉ) → is-sectionᵉ fᵉ (map-section-left-map-triangleᵉ sᵉ)
  is-section-map-section-left-map-triangleᵉ sᵉ =
    ( Hᵉ ·rᵉ map-section-compᵉ gᵉ hᵉ tᵉ sᵉ) ∙hᵉ
    ( is-section-map-section-compᵉ gᵉ hᵉ tᵉ sᵉ)

  section-left-map-triangleᵉ : sectionᵉ gᵉ → sectionᵉ fᵉ
  pr1ᵉ (section-left-map-triangleᵉ sᵉ) = map-section-left-map-triangleᵉ sᵉ
  pr2ᵉ (section-left-map-triangleᵉ sᵉ) = is-section-map-section-left-map-triangleᵉ sᵉ
```