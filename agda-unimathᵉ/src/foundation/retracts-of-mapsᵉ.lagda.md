# Retracts of maps

```agda
module foundation.retracts-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-prisms-of-mapsᵉ
open import foundation.commuting-triangles-of-morphisms-arrowsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.diagonal-maps-of-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-fibers-of-mapsᵉ
open import foundation.homotopies-morphisms-arrowsᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.constant-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.retracts-of-typesᵉ
open import foundation-core.sectionsᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ saidᵉ to beᵉ aᵉ **retract**ᵉ ofᵉ aᵉ mapᵉ `gᵉ : Xᵉ → Y`ᵉ ifᵉ itᵉ isᵉ aᵉ
retractᵉ in theᵉ arrowᵉ categoryᵉ ofᵉ types.ᵉ Inᵉ otherᵉ words,ᵉ `f`ᵉ isᵉ aᵉ retractᵉ ofᵉ `g`ᵉ
ifᵉ thereᵉ areᵉ [morphismsᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ) `iᵉ : fᵉ → g`ᵉ
andᵉ `rᵉ : gᵉ → f`ᵉ equippedᵉ with aᵉ homotopyᵉ ofᵉ morphismsᵉ ofᵉ arrowsᵉ `rᵉ ∘ᵉ iᵉ ~ᵉ id`.ᵉ

Moreᵉ explicitly,ᵉ itᵉ consistsᵉ ofᵉ [retracts](foundation-core.retractions.mdᵉ) `A`ᵉ
ofᵉ `X`ᵉ andᵉ `B`ᵉ ofᵉ `Y`ᵉ thatᵉ fitᵉ intoᵉ aᵉ commutativeᵉ diagramᵉ

```text
         i₀ᵉ        r₀ᵉ
    Aᵉ ------>ᵉ Xᵉ ------>ᵉ Aᵉ
    |         |         |
  fᵉ |    iᵉ    | gᵉ   rᵉ   | fᵉ
    ∨ᵉ         ∨ᵉ         ∨ᵉ
    Bᵉ ------>ᵉ Yᵉ ------>ᵉ Bᵉ
         i₁ᵉ        r₁ᵉ
```

with coherencesᵉ

```text
  iᵉ : i₁ᵉ ∘ᵉ fᵉ ~ᵉ gᵉ ∘ᵉ i₀ᵉ  andᵉ   rᵉ : r₁ᵉ ∘ᵉ gᵉ ~ᵉ fᵉ ∘ᵉ r₀ᵉ
```

witnessingᵉ thatᵉ theᵉ leftᵉ andᵉ rightᵉ
[squaresᵉ commute](foundation-core.commuting-squares-of-maps.md),ᵉ andᵉ aᵉ higherᵉ
coherenceᵉ

```text
                     rᵉ ·rᵉ i₀ᵉ
       r₁ᵉ ∘ᵉ gᵉ ∘ᵉ i₀ᵉ ---------->ᵉ fᵉ ∘ᵉ r₀ᵉ ∘ᵉ i₀ᵉ
            |                      |
            |                      |
  r₁ᵉ ·lᵉ i⁻¹ᵉ |          Lᵉ           | fᵉ ·lᵉ H₀ᵉ
            |                      |
            ∨ᵉ                      ∨ᵉ
      r₁ᵉ ∘ᵉ i₁ᵉ ∘ᵉ fᵉ --------------->ᵉ fᵉ
                       H₁ᵉ ·rᵉ fᵉ
```

witnessingᵉ thatᵉ theᵉ
[squareᵉ ofᵉ homotopies](foundation.commuting-squares-of-homotopies.mdᵉ) commutes,ᵉ
where `H₀`ᵉ andᵉ `H₁`ᵉ areᵉ theᵉ retractingᵉ homotopiesᵉ ofᵉ `r₀ᵉ ∘ᵉ i₀`ᵉ andᵉ `r₁ᵉ ∘ᵉ i₁`ᵉ
respectively.ᵉ

Thisᵉ coherenceᵉ requirementᵉ arisesᵉ fromᵉ theᵉ implicitᵉ requirementᵉ thatᵉ theᵉ totalᵉ
pastingᵉ ofᵉ theᵉ retractionᵉ squareᵉ shouldᵉ restrictᵉ to theᵉ reflexivityᵉ homotopyᵉ onᵉ
theᵉ squareᵉ

```text
    Aᵉ =========ᵉ Aᵉ
    |           |
  fᵉ | refl-htpyᵉ | fᵉ
    ∨ᵉ           ∨ᵉ
    Bᵉ =========ᵉ B,ᵉ
```

asᵉ weᵉ areᵉ askingᵉ forᵉ theᵉ morphismsᵉ to composeᵉ to theᵉ identityᵉ morphismᵉ ofᵉ
arrows.ᵉ

## Definition

### The predicate of being a retraction of a morphism of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (iᵉ : hom-arrowᵉ fᵉ gᵉ) (rᵉ : hom-arrowᵉ gᵉ fᵉ)
  where

  is-retraction-hom-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-retraction-hom-arrowᵉ = coherence-triangle-hom-arrow'ᵉ fᵉ gᵉ fᵉ id-hom-arrowᵉ rᵉ iᵉ
```

### The type of retractions of a morphism of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (iᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  retraction-hom-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  retraction-hom-arrowᵉ = Σᵉ (hom-arrowᵉ gᵉ fᵉ) (is-retraction-hom-arrowᵉ fᵉ gᵉ iᵉ)

  module _
    (rᵉ : retraction-hom-arrowᵉ)
    where

    hom-retraction-hom-arrowᵉ : hom-arrowᵉ gᵉ fᵉ
    hom-retraction-hom-arrowᵉ = pr1ᵉ rᵉ

    is-retraction-hom-retraction-hom-arrowᵉ :
      is-retraction-hom-arrowᵉ fᵉ gᵉ iᵉ hom-retraction-hom-arrowᵉ
    is-retraction-hom-retraction-hom-arrowᵉ = pr2ᵉ rᵉ
```

### The predicate that a morphism `f` is a retract of a morphism `g`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  where

  retract-mapᵉ : (gᵉ : Xᵉ → Yᵉ) (fᵉ : Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  retract-mapᵉ gᵉ fᵉ = Σᵉ (hom-arrowᵉ fᵉ gᵉ) (retraction-hom-arrowᵉ fᵉ gᵉ)
```

### The higher coherence in the definition of retracts of maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (iᵉ : hom-arrowᵉ fᵉ gᵉ) (rᵉ : hom-arrowᵉ gᵉ fᵉ)
  (Hᵉ : is-retractionᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ iᵉ) (map-domain-hom-arrowᵉ gᵉ fᵉ rᵉ))
  (H'ᵉ :
    is-retractionᵉ
      ( map-codomain-hom-arrowᵉ fᵉ gᵉ iᵉ)
      ( map-codomain-hom-arrowᵉ gᵉ fᵉ rᵉ))
  where

  coherence-retract-mapᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-retract-mapᵉ =
    coherence-htpy-hom-arrowᵉ fᵉ fᵉ (comp-hom-arrowᵉ fᵉ gᵉ fᵉ rᵉ iᵉ) id-hom-arrowᵉ Hᵉ H'ᵉ
```

### The binary relation `f g ↦ f retract-of-map g` asserting that `f` is a retract of the map `g`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  infix 6 _retract-of-mapᵉ_

  _retract-of-mapᵉ_ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  _retract-of-mapᵉ_ = retract-mapᵉ gᵉ fᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (Rᵉ : fᵉ retract-of-mapᵉ gᵉ)
  where

  inclusion-retract-mapᵉ : hom-arrowᵉ fᵉ gᵉ
  inclusion-retract-mapᵉ = pr1ᵉ Rᵉ

  map-domain-inclusion-retract-mapᵉ : Aᵉ → Xᵉ
  map-domain-inclusion-retract-mapᵉ =
    map-domain-hom-arrowᵉ fᵉ gᵉ inclusion-retract-mapᵉ

  map-codomain-inclusion-retract-mapᵉ : Bᵉ → Yᵉ
  map-codomain-inclusion-retract-mapᵉ =
    map-codomain-hom-arrowᵉ fᵉ gᵉ inclusion-retract-mapᵉ

  coh-inclusion-retract-mapᵉ :
    coherence-square-mapsᵉ
      ( map-domain-inclusion-retract-mapᵉ)
      ( fᵉ)
      ( gᵉ)
      ( map-codomain-inclusion-retract-mapᵉ)
  coh-inclusion-retract-mapᵉ =
    coh-hom-arrowᵉ fᵉ gᵉ inclusion-retract-mapᵉ

  retraction-retract-mapᵉ : retraction-hom-arrowᵉ fᵉ gᵉ inclusion-retract-mapᵉ
  retraction-retract-mapᵉ = pr2ᵉ Rᵉ

  hom-retraction-retract-mapᵉ : hom-arrowᵉ gᵉ fᵉ
  hom-retraction-retract-mapᵉ =
    hom-retraction-hom-arrowᵉ fᵉ gᵉ inclusion-retract-mapᵉ retraction-retract-mapᵉ

  map-domain-hom-retraction-retract-mapᵉ : Xᵉ → Aᵉ
  map-domain-hom-retraction-retract-mapᵉ =
    map-domain-hom-arrowᵉ gᵉ fᵉ hom-retraction-retract-mapᵉ

  map-codomain-hom-retraction-retract-mapᵉ : Yᵉ → Bᵉ
  map-codomain-hom-retraction-retract-mapᵉ =
    map-codomain-hom-arrowᵉ gᵉ fᵉ hom-retraction-retract-mapᵉ

  coh-hom-retraction-retract-mapᵉ :
    coherence-square-mapsᵉ
      ( map-domain-hom-retraction-retract-mapᵉ)
      ( gᵉ)
      ( fᵉ)
      ( map-codomain-hom-retraction-retract-mapᵉ)
  coh-hom-retraction-retract-mapᵉ =
    coh-hom-arrowᵉ gᵉ fᵉ hom-retraction-retract-mapᵉ

  is-retraction-hom-retraction-retract-mapᵉ :
    is-retraction-hom-arrowᵉ fᵉ gᵉ inclusion-retract-mapᵉ hom-retraction-retract-mapᵉ
  is-retraction-hom-retraction-retract-mapᵉ =
    is-retraction-hom-retraction-hom-arrowᵉ fᵉ gᵉ
      ( inclusion-retract-mapᵉ)
      ( retraction-retract-mapᵉ)

  is-retraction-map-domain-hom-retraction-retract-mapᵉ :
    is-retractionᵉ
      ( map-domain-inclusion-retract-mapᵉ)
      ( map-domain-hom-retraction-retract-mapᵉ)
  is-retraction-map-domain-hom-retraction-retract-mapᵉ =
    htpy-domain-htpy-hom-arrowᵉ fᵉ fᵉ
      ( comp-hom-arrowᵉ fᵉ gᵉ fᵉ hom-retraction-retract-mapᵉ inclusion-retract-mapᵉ)
      ( id-hom-arrowᵉ)
      ( is-retraction-hom-retraction-retract-mapᵉ)

  retract-domain-retract-mapᵉ :
    Aᵉ retract-ofᵉ Xᵉ
  pr1ᵉ retract-domain-retract-mapᵉ =
    map-domain-inclusion-retract-mapᵉ
  pr1ᵉ (pr2ᵉ retract-domain-retract-mapᵉ) =
    map-domain-hom-retraction-retract-mapᵉ
  pr2ᵉ (pr2ᵉ retract-domain-retract-mapᵉ) =
    is-retraction-map-domain-hom-retraction-retract-mapᵉ

  is-retraction-map-codomain-hom-retraction-retract-mapᵉ :
    is-retractionᵉ
      ( map-codomain-inclusion-retract-mapᵉ)
      ( map-codomain-hom-retraction-retract-mapᵉ)
  is-retraction-map-codomain-hom-retraction-retract-mapᵉ =
    htpy-codomain-htpy-hom-arrowᵉ fᵉ fᵉ
      ( comp-hom-arrowᵉ fᵉ gᵉ fᵉ hom-retraction-retract-mapᵉ inclusion-retract-mapᵉ)
      ( id-hom-arrowᵉ)
      ( is-retraction-hom-retraction-retract-mapᵉ)

  retract-codomain-retract-mapᵉ : Bᵉ retract-ofᵉ Yᵉ
  pr1ᵉ retract-codomain-retract-mapᵉ =
    map-codomain-inclusion-retract-mapᵉ
  pr1ᵉ (pr2ᵉ retract-codomain-retract-mapᵉ) =
    map-codomain-hom-retraction-retract-mapᵉ
  pr2ᵉ (pr2ᵉ retract-codomain-retract-mapᵉ) =
    is-retraction-map-codomain-hom-retraction-retract-mapᵉ

  coh-retract-mapᵉ :
    coherence-retract-mapᵉ fᵉ gᵉ
      ( inclusion-retract-mapᵉ)
      ( hom-retraction-retract-mapᵉ)
      ( is-retraction-map-domain-hom-retraction-retract-mapᵉ)
      ( is-retraction-map-codomain-hom-retraction-retract-mapᵉ)
  coh-retract-mapᵉ =
    coh-htpy-hom-arrowᵉ fᵉ fᵉ
      ( comp-hom-arrowᵉ fᵉ gᵉ fᵉ hom-retraction-retract-mapᵉ inclusion-retract-mapᵉ)
      ( id-hom-arrowᵉ)
      ( is-retraction-hom-retraction-retract-mapᵉ)
```

## Properties

### Retracts of maps with sections have sections

Inᵉ fact,ᵉ weᵉ onlyᵉ needᵉ theᵉ followingᵉ data to showᵉ thisᵉ:

```text
                 r₀ᵉ
            Xᵉ ------>ᵉ Aᵉ
            |         |
          gᵉ |    rᵉ    | fᵉ
            ∨ᵉ         ∨ᵉ
  Bᵉ ------>ᵉ Yᵉ ------>ᵉ B.ᵉ
       i₁ᵉ   H₁ᵉ   r₁ᵉ
```

**Proof:**ᵉ Noteᵉ thatᵉ `f`ᵉ isᵉ theᵉ rightᵉ mapᵉ ofᵉ aᵉ triangleᵉ

```text
            r₀ᵉ
       Xᵉ ------>ᵉ Aᵉ
        \ᵉ       /ᵉ
  r₁ᵉ ∘ᵉ gᵉ \ᵉ     /ᵉ fᵉ
          \ᵉ   /ᵉ
           ∨ᵉ ∨ᵉ
            B.ᵉ
```

Sinceᵉ bothᵉ `r₁`ᵉ andᵉ `g`ᵉ areᵉ assumedᵉ to haveᵉ
[sections](foundation-core.sections.md),ᵉ itᵉ followsᵉ thatᵉ theᵉ compositeᵉ `r₁ᵉ ∘ᵉ g`ᵉ
hasᵉ aᵉ section,ᵉ andᵉ thereforeᵉ `f`ᵉ hasᵉ aᵉ section.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (r₀ᵉ : Xᵉ → Aᵉ) (R₁ᵉ : Bᵉ retract-ofᵉ Yᵉ)
  (rᵉ : coherence-square-mapsᵉ r₀ᵉ gᵉ fᵉ (map-retraction-retractᵉ R₁ᵉ))
  (sᵉ : sectionᵉ gᵉ)
  where

  section-retract-map-section'ᵉ : sectionᵉ fᵉ
  section-retract-map-section'ᵉ =
    section-right-map-triangleᵉ
      ( map-retraction-retractᵉ R₁ᵉ ∘ᵉ gᵉ)
      ( fᵉ)
      ( r₀ᵉ)
      ( rᵉ)
      ( section-compᵉ (map-retraction-retractᵉ R₁ᵉ) gᵉ sᵉ (section-retractᵉ R₁ᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (Rᵉ : fᵉ retract-of-mapᵉ gᵉ)
  where

  section-retract-map-sectionᵉ : sectionᵉ gᵉ → sectionᵉ fᵉ
  section-retract-map-sectionᵉ =
    section-retract-map-section'ᵉ fᵉ gᵉ
      ( map-domain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( retract-codomain-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( coh-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
```

### Retracts of maps with retractions have retractions

Inᵉ fact,ᵉ weᵉ onlyᵉ needᵉ theᵉ followingᵉ data to showᵉ thisᵉ:

```text
         i₀ᵉ   Hᵉ   r₀ᵉ
    Aᵉ ------>ᵉ Xᵉ ------>ᵉ Aᵉ
    |         |
  fᵉ |    iᵉ    | gᵉ
    ∨ᵉ         ∨ᵉ
    Bᵉ ------>ᵉ Y.ᵉ
         i₁ᵉ
```

**Proof:**ᵉ Noteᵉ thatᵉ `f`ᵉ isᵉ theᵉ topᵉ mapᵉ in theᵉ triangleᵉ

```text
            fᵉ
       Aᵉ ------>ᵉ Bᵉ
        \ᵉ       /ᵉ
  gᵉ ∘ᵉ i₀ᵉ \ᵉ     /ᵉ i₁ᵉ
          \ᵉ   /ᵉ
           ∨ᵉ ∨ᵉ
            Y.ᵉ
```

Sinceᵉ bothᵉ `g`ᵉ andᵉ `i₀`ᵉ areᵉ assumedᵉ to haveᵉ retractions,ᵉ itᵉ followsᵉ thatᵉ
`gᵉ ∘ᵉ i₀`ᵉ hasᵉ aᵉ retraction,ᵉ andᵉ henceᵉ thatᵉ `f`ᵉ hasᵉ aᵉ retraction.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (R₀ᵉ : Aᵉ retract-ofᵉ Xᵉ) (i₁ᵉ : Bᵉ → Yᵉ)
  (iᵉ : coherence-square-mapsᵉ (inclusion-retractᵉ R₀ᵉ) fᵉ gᵉ i₁ᵉ)
  (sᵉ : retractionᵉ gᵉ)
  where

  retraction-retract-map-retraction'ᵉ : retractionᵉ fᵉ
  retraction-retract-map-retraction'ᵉ =
    retraction-top-map-triangleᵉ
      ( gᵉ ∘ᵉ inclusion-retractᵉ R₀ᵉ)
      ( i₁ᵉ)
      ( fᵉ)
      ( inv-htpyᵉ iᵉ)
      ( retraction-compᵉ gᵉ (inclusion-retractᵉ R₀ᵉ) sᵉ (retraction-retractᵉ R₀ᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (Rᵉ : fᵉ retract-of-mapᵉ gᵉ)
  where

  retraction-retract-map-retractionᵉ : retractionᵉ gᵉ → retractionᵉ fᵉ
  retraction-retract-map-retractionᵉ =
    retraction-retract-map-retraction'ᵉ fᵉ gᵉ
      ( retract-domain-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( coh-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ)
```

### Equivalences are closed under retracts of maps

Weᵉ mayᵉ observeᵉ thatᵉ theᵉ higherᵉ coherenceᵉ ofᵉ aᵉ retractᵉ ofᵉ mapsᵉ isᵉ notᵉ needed.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (R₀ᵉ : Aᵉ retract-ofᵉ Xᵉ) (R₁ᵉ : Bᵉ retract-ofᵉ Yᵉ)
  (iᵉ : coherence-square-mapsᵉ (inclusion-retractᵉ R₀ᵉ) fᵉ gᵉ (inclusion-retractᵉ R₁ᵉ))
  (rᵉ :
    coherence-square-mapsᵉ
      ( map-retraction-retractᵉ R₀ᵉ)
      ( gᵉ)
      ( fᵉ)
      ( map-retraction-retractᵉ R₁ᵉ))
  (Hᵉ : is-equivᵉ gᵉ)
  where

  is-equiv-retract-map-is-equiv'ᵉ : is-equivᵉ fᵉ
  pr1ᵉ is-equiv-retract-map-is-equiv'ᵉ =
    section-retract-map-section'ᵉ fᵉ gᵉ
      ( map-retraction-retractᵉ R₀ᵉ)
      ( R₁ᵉ)
      ( rᵉ)
      ( section-is-equivᵉ Hᵉ)
  pr2ᵉ is-equiv-retract-map-is-equiv'ᵉ =
    retraction-retract-map-retraction'ᵉ fᵉ gᵉ
      ( R₀ᵉ)
      ( inclusion-retractᵉ R₁ᵉ)
      ( iᵉ)
      ( retraction-is-equivᵉ Hᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (Rᵉ : fᵉ retract-of-mapᵉ gᵉ) (Hᵉ : is-equivᵉ gᵉ)
  where

  section-retract-map-is-equivᵉ : sectionᵉ fᵉ
  section-retract-map-is-equivᵉ =
    section-retract-map-sectionᵉ fᵉ gᵉ Rᵉ (section-is-equivᵉ Hᵉ)

  retraction-retract-map-is-equivᵉ : retractionᵉ fᵉ
  retraction-retract-map-is-equivᵉ =
    retraction-retract-map-retractionᵉ fᵉ gᵉ Rᵉ (retraction-is-equivᵉ Hᵉ)

  is-equiv-retract-map-is-equivᵉ : is-equivᵉ fᵉ
  pr1ᵉ is-equiv-retract-map-is-equivᵉ = section-retract-map-is-equivᵉ
  pr2ᵉ is-equiv-retract-map-is-equivᵉ = retraction-retract-map-is-equivᵉ
```

### If `f` is a retract of `g`, then the fiber inclusions of `f` are retracts of the fiber inclusions of `g`

Considerᵉ aᵉ retractᵉ `fᵉ : Aᵉ → B`ᵉ ofᵉ aᵉ mapᵉ `gᵉ : Xᵉ → Y`,ᵉ asᵉ indicatedᵉ in theᵉ bottomᵉ
rowᵉ ofᵉ squaresᵉ in theᵉ diagramᵉ below.ᵉ

```text
              jᵉ                     sᵉ
  fiberᵉ fᵉ bᵉ ----->ᵉ fiberᵉ gᵉ (i₁ᵉ bᵉ) ----->ᵉ fiberᵉ fᵉ bᵉ
     |                 |                    |
     |       i'ᵉ        |         r'ᵉ         |
     ∨ᵉ                 ∨ᵉ                    ∨ᵉ
     Aᵉ -----ᵉ i₀ᵉ ----->ᵉ Xᵉ -------ᵉ r₀ᵉ ------>ᵉ Aᵉ
     |                 |                    |
   fᵉ |       iᵉ         | gᵉ       rᵉ          | fᵉ
     ∨ᵉ                 ∨ᵉ                    ∨ᵉ
     Bᵉ -------------->ᵉ Yᵉ ----------------->ᵉ Bᵉ
             i₁ᵉ                  r₁ᵉ
```

Thenᵉ weᵉ claimᵉ thatᵉ theᵉ [fiberᵉ inclusion](foundation-core.fibers-of-maps.mdᵉ)
`fiberᵉ fᵉ bᵉ → A`ᵉ isᵉ aᵉ retractᵉ ofᵉ theᵉ fiberᵉ inclusionᵉ `fiberᵉ gᵉ (i'ᵉ xᵉ) → X`.ᵉ

**Proof:**ᵉ Byᵉ
[functorialityᵉ ofᵉ fibersᵉ ofᵉ maps](foundation.functoriality-fibers-of-maps.mdᵉ) weᵉ
obtainᵉ aᵉ commutingᵉ diagramᵉ

```text
              jᵉ                     sᵉ                          ≃ᵉ
  fiberᵉ fᵉ bᵉ ----->ᵉ fiberᵉ gᵉ (i₁ᵉ bᵉ) ----->ᵉ fiberᵉ fᵉ (r₀ᵉ (i₀ᵉ bᵉ)) ----->ᵉ fiberᵉ fᵉ bᵉ
     |                 |                       |                        |
     |       i'ᵉ        |           r'ᵉ          |                        |
     ∨ᵉ                 ∨ᵉ                       ∨ᵉ                        ∨ᵉ
     Aᵉ -------------->ᵉ Xᵉ -------------------->ᵉ Aᵉ --------------------->ᵉ Aᵉ
             i₀ᵉ                    r₀ᵉ                       idᵉ
```

whichᵉ isᵉ homotopicᵉ to theᵉ identityᵉ morphismᵉ ofᵉ arrows.ᵉ Weᵉ thenᵉ finishᵉ offᵉ theᵉ
proofᵉ with theᵉ followingᵉ stepsᵉ:

1.ᵉ Weᵉ reassociateᵉ theᵉ compositionᵉ ofᵉ morphismsᵉ ofᵉ fibers,ᵉ whichᵉ isᵉ associatedᵉ in
   theᵉ aboveᵉ diagramᵉ asᵉ `□ᵉ (□ᵉ □)`.ᵉ
2.ᵉ Thenᵉ weᵉ useᵉ thatᵉ `hom-arrow-fiber`ᵉ preservesᵉ composition.ᵉ
3.ᵉ Next,ᵉ weᵉ applyᵉ theᵉ actionᵉ onᵉ `htpy-hom-arrow`ᵉ ofᵉ `fiber`.ᵉ
4.ᵉ Finally,ᵉ weᵉ useᵉ thatᵉ `hom-arrow-fiber`ᵉ preservesᵉ identityᵉ morphismsᵉ ofᵉ
   arrows.ᵉ

Whileᵉ eachᵉ ofᵉ theseᵉ stepsᵉ areᵉ veryᵉ simpleᵉ to formalize,ᵉ theᵉ operationsᵉ thatᵉ areᵉ
involvedᵉ takeᵉ aᵉ lotᵉ ofᵉ argumentsᵉ andᵉ thereforeᵉ theᵉ codeᵉ isᵉ somewhatᵉ lengthy.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (Rᵉ : fᵉ retract-of-mapᵉ gᵉ) (bᵉ : Bᵉ)
  where

  inclusion-retract-map-inclusion-fiber-retract-mapᵉ :
    hom-arrowᵉ
      ( inclusion-fiberᵉ fᵉ {bᵉ})
      ( inclusion-fiberᵉ gᵉ {map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ})
  inclusion-retract-map-inclusion-fiber-retract-mapᵉ =
    hom-arrow-fiberᵉ fᵉ gᵉ (inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ) bᵉ

  hom-retraction-retract-map-inclusion-fiber-retract-mapᵉ :
    hom-arrowᵉ
      ( inclusion-fiberᵉ gᵉ {map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ})
      ( inclusion-fiberᵉ fᵉ {bᵉ})
  hom-retraction-retract-map-inclusion-fiber-retract-mapᵉ =
    comp-hom-arrowᵉ
      ( inclusion-fiberᵉ gᵉ)
      ( inclusion-fiberᵉ fᵉ)
      ( inclusion-fiberᵉ fᵉ)
      ( tr-hom-arrow-inclusion-fiberᵉ fᵉ
        ( is-retraction-map-codomain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
      ( hom-arrow-fiberᵉ gᵉ fᵉ
        ( hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
        ( map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))

  is-retraction-hom-retraction-retract-map-inclusion-fiber-retract-mapᵉ :
    is-retraction-hom-arrowᵉ
      ( inclusion-fiberᵉ fᵉ)
      ( inclusion-fiberᵉ gᵉ)
      ( inclusion-retract-map-inclusion-fiber-retract-mapᵉ)
      ( hom-retraction-retract-map-inclusion-fiber-retract-mapᵉ)
  is-retraction-hom-retraction-retract-map-inclusion-fiber-retract-mapᵉ =
    concat-htpy-hom-arrowᵉ
      ( inclusion-fiberᵉ fᵉ)
      ( inclusion-fiberᵉ fᵉ)
      ( comp-hom-arrowᵉ
        ( inclusion-fiberᵉ fᵉ)
        ( inclusion-fiberᵉ gᵉ)
        ( inclusion-fiberᵉ fᵉ)
        ( comp-hom-arrowᵉ
          ( inclusion-fiberᵉ gᵉ)
          ( inclusion-fiberᵉ fᵉ)
          ( inclusion-fiberᵉ fᵉ)
          ( tr-hom-arrow-inclusion-fiberᵉ fᵉ
            ( is-retraction-map-codomain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
          ( hom-arrow-fiberᵉ gᵉ fᵉ
            ( hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
            ( map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ)))
        ( inclusion-retract-map-inclusion-fiber-retract-mapᵉ))
      ( comp-hom-arrowᵉ
        ( inclusion-fiberᵉ fᵉ)
        ( inclusion-fiberᵉ fᵉ)
        ( inclusion-fiberᵉ fᵉ)
        ( tr-hom-arrow-inclusion-fiberᵉ fᵉ
          ( is-retraction-map-codomain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
        ( comp-hom-arrowᵉ
          ( inclusion-fiberᵉ fᵉ)
          ( inclusion-fiberᵉ gᵉ)
          ( inclusion-fiberᵉ fᵉ)
          ( hom-arrow-fiberᵉ gᵉ fᵉ
            ( hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
            ( map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
          ( inclusion-retract-map-inclusion-fiber-retract-mapᵉ)))
      ( id-hom-arrowᵉ)
      ( inv-assoc-comp-hom-arrowᵉ
        ( inclusion-fiberᵉ fᵉ)
        ( inclusion-fiberᵉ gᵉ)
        ( inclusion-fiberᵉ fᵉ)
        ( inclusion-fiberᵉ fᵉ)
        ( tr-hom-arrow-inclusion-fiberᵉ fᵉ
          ( is-retraction-map-codomain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
        ( hom-arrow-fiberᵉ gᵉ fᵉ
          ( hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
          ( map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
        ( inclusion-retract-map-inclusion-fiber-retract-mapᵉ))
      ( concat-htpy-hom-arrowᵉ
        ( inclusion-fiberᵉ fᵉ)
        ( inclusion-fiberᵉ fᵉ)
        ( comp-hom-arrowᵉ
          ( inclusion-fiberᵉ fᵉ)
          ( inclusion-fiberᵉ fᵉ)
          ( inclusion-fiberᵉ fᵉ)
          ( tr-hom-arrow-inclusion-fiberᵉ fᵉ
            ( is-retraction-map-codomain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
          ( comp-hom-arrowᵉ
            ( inclusion-fiberᵉ fᵉ)
            ( inclusion-fiberᵉ gᵉ)
            ( inclusion-fiberᵉ fᵉ)
            ( hom-arrow-fiberᵉ gᵉ fᵉ
              ( hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
              ( map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
            ( inclusion-retract-map-inclusion-fiber-retract-mapᵉ)))
        ( comp-hom-arrowᵉ
          ( inclusion-fiberᵉ fᵉ)
          ( inclusion-fiberᵉ fᵉ)
          ( inclusion-fiberᵉ fᵉ)
          ( tr-hom-arrow-inclusion-fiberᵉ fᵉ
            ( is-retraction-map-codomain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
          ( hom-arrow-fiberᵉ fᵉ fᵉ
            ( comp-hom-arrowᵉ fᵉ gᵉ fᵉ
              ( hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
              ( inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ))
            ( bᵉ)))
        ( id-hom-arrowᵉ)
        ( left-whisker-comp-hom-arrowᵉ
          ( inclusion-fiberᵉ fᵉ)
          ( inclusion-fiberᵉ fᵉ)
          ( inclusion-fiberᵉ fᵉ)
          ( tr-hom-arrow-inclusion-fiberᵉ fᵉ
            ( is-retraction-map-codomain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
          ( comp-hom-arrowᵉ
            ( inclusion-fiberᵉ fᵉ)
            ( inclusion-fiberᵉ gᵉ)
            ( inclusion-fiberᵉ fᵉ)
            ( hom-arrow-fiberᵉ gᵉ fᵉ
              ( hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
              ( map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
            ( hom-arrow-fiberᵉ fᵉ gᵉ (inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ) bᵉ))
          ( hom-arrow-fiberᵉ fᵉ fᵉ
            ( comp-hom-arrowᵉ fᵉ gᵉ fᵉ
              ( hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
              ( inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ))
            ( bᵉ))
          ( inv-htpy-hom-arrowᵉ
            ( inclusion-fiberᵉ fᵉ)
            ( inclusion-fiberᵉ fᵉ)
            ( hom-arrow-fiberᵉ fᵉ fᵉ
              ( comp-hom-arrowᵉ fᵉ gᵉ fᵉ
                ( hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
                ( inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ))
              ( bᵉ))
            ( comp-hom-arrowᵉ
              ( inclusion-fiberᵉ fᵉ)
              ( inclusion-fiberᵉ gᵉ)
              ( inclusion-fiberᵉ fᵉ)
              ( hom-arrow-fiberᵉ gᵉ fᵉ
                ( hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
                ( map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
              ( hom-arrow-fiberᵉ fᵉ gᵉ (inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ) bᵉ))
            ( preserves-comp-hom-arrow-fiberᵉ fᵉ gᵉ fᵉ
              ( hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
              ( inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ)
              ( bᵉ))))
        ( concat-htpy-hom-arrowᵉ
          ( inclusion-fiberᵉ fᵉ)
          ( inclusion-fiberᵉ fᵉ)
          ( comp-hom-arrowᵉ
            ( inclusion-fiberᵉ fᵉ)
            ( inclusion-fiberᵉ fᵉ)
            ( inclusion-fiberᵉ fᵉ)
            ( tr-hom-arrow-inclusion-fiberᵉ fᵉ
              ( is-retraction-map-codomain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
            ( hom-arrow-fiberᵉ fᵉ fᵉ
              ( comp-hom-arrowᵉ fᵉ gᵉ fᵉ
                ( hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
                ( inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ))
              ( bᵉ)))
          ( hom-arrow-fiberᵉ fᵉ fᵉ id-hom-arrowᵉ bᵉ)
          ( id-hom-arrowᵉ)
          ( htpy-hom-arrow-fiberᵉ fᵉ fᵉ
            ( comp-hom-arrowᵉ fᵉ gᵉ fᵉ
              ( hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
              ( inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ))
            ( id-hom-arrowᵉ)
            ( is-retraction-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
            ( bᵉ))
          ( preserves-id-hom-arrow-fiberᵉ fᵉ bᵉ)))

  retract-map-inclusion-fiber-retract-mapᵉ :
    retract-mapᵉ
      ( inclusion-fiberᵉ gᵉ {map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ})
      ( inclusion-fiberᵉ fᵉ {bᵉ})
  pr1ᵉ retract-map-inclusion-fiber-retract-mapᵉ =
    inclusion-retract-map-inclusion-fiber-retract-mapᵉ
  pr1ᵉ (pr2ᵉ retract-map-inclusion-fiber-retract-mapᵉ) =
    hom-retraction-retract-map-inclusion-fiber-retract-mapᵉ
  pr2ᵉ (pr2ᵉ retract-map-inclusion-fiber-retract-mapᵉ) =
    is-retraction-hom-retraction-retract-map-inclusion-fiber-retract-mapᵉ
```

### If `f` is a retract of `g`, then the fibers of `f` are retracts of the fibers of `g`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (Rᵉ : fᵉ retract-of-mapᵉ gᵉ) (bᵉ : Bᵉ)
  where

  retract-fiber-retract-mapᵉ :
    retractᵉ
      ( fiberᵉ gᵉ (map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
      ( fiberᵉ fᵉ bᵉ)
  retract-fiber-retract-mapᵉ =
    retract-domain-retract-mapᵉ
      ( inclusion-fiberᵉ fᵉ)
      ( inclusion-fiberᵉ gᵉ)
      ( retract-map-inclusion-fiber-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ)
```

### If `f` is a retract of `g`, then `- ∘ f` is a retract of `- ∘ g`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (Rᵉ : fᵉ retract-of-mapᵉ gᵉ) (Sᵉ : UUᵉ l5ᵉ)
  where

  inclusion-precomp-retract-mapᵉ : hom-arrowᵉ (precompᵉ fᵉ Sᵉ) (precompᵉ gᵉ Sᵉ)
  inclusion-precomp-retract-mapᵉ =
    precomp-hom-arrowᵉ gᵉ fᵉ (hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ) Sᵉ

  hom-retraction-precomp-retract-mapᵉ : hom-arrowᵉ (precompᵉ gᵉ Sᵉ) (precompᵉ fᵉ Sᵉ)
  hom-retraction-precomp-retract-mapᵉ =
    precomp-hom-arrowᵉ fᵉ gᵉ (inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ) Sᵉ

  is-retraction-map-domain-precomp-retract-mapᵉ :
    is-retractionᵉ
      ( map-domain-hom-arrowᵉ
        ( precompᵉ fᵉ Sᵉ)
        ( precompᵉ gᵉ Sᵉ)
        ( inclusion-precomp-retract-mapᵉ))
      ( map-domain-hom-arrowᵉ
        ( precompᵉ gᵉ Sᵉ)
        ( precompᵉ fᵉ Sᵉ)
        ( hom-retraction-precomp-retract-mapᵉ))
  is-retraction-map-domain-precomp-retract-mapᵉ =
    htpy-precompᵉ (is-retraction-map-codomain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ) Sᵉ

  is-retraction-map-codomain-precomp-retract-mapᵉ :
    is-retractionᵉ
      ( map-codomain-hom-arrowᵉ
        ( precompᵉ fᵉ Sᵉ)
        ( precompᵉ gᵉ Sᵉ)
        ( inclusion-precomp-retract-mapᵉ))
      ( map-codomain-hom-arrowᵉ
        ( precompᵉ gᵉ Sᵉ)
        ( precompᵉ fᵉ Sᵉ)
        ( hom-retraction-precomp-retract-mapᵉ))
  is-retraction-map-codomain-precomp-retract-mapᵉ =
    htpy-precompᵉ (is-retraction-map-domain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ) Sᵉ

  coh-retract-precomp-retract-mapᵉ :
    coherence-retract-mapᵉ
      ( precompᵉ fᵉ Sᵉ)
      ( precompᵉ gᵉ Sᵉ)
      ( inclusion-precomp-retract-mapᵉ)
      ( hom-retraction-precomp-retract-mapᵉ)
      ( is-retraction-map-domain-precomp-retract-mapᵉ)
      ( is-retraction-map-codomain-precomp-retract-mapᵉ)
  coh-retract-precomp-retract-mapᵉ =
    ( precomp-vertical-coherence-prism-inv-triangles-mapsᵉ
      ( idᵉ)
      ( map-domain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( map-domain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( idᵉ)
      ( map-codomain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( fᵉ)
      ( gᵉ)
      ( fᵉ)
      ( is-retraction-map-domain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( refl-htpyᵉ)
      ( coh-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( coh-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( is-retraction-map-codomain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( coh-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( Sᵉ)) ∙hᵉ
    ( ap-concat-htpyᵉ
      ( is-retraction-map-codomain-precomp-retract-mapᵉ ·rᵉ precompᵉ fᵉ Sᵉ)
      ( λ xᵉ → apᵉ invᵉ (eq-htpy-refl-htpyᵉ (precompᵉ fᵉ Sᵉ xᵉ))))

  is-retraction-hom-retraction-precomp-retract-mapᵉ :
    is-retraction-hom-arrowᵉ
      ( precompᵉ fᵉ Sᵉ)
      ( precompᵉ gᵉ Sᵉ)
      ( inclusion-precomp-retract-mapᵉ)
      ( hom-retraction-precomp-retract-mapᵉ)
  pr1ᵉ is-retraction-hom-retraction-precomp-retract-mapᵉ =
    is-retraction-map-domain-precomp-retract-mapᵉ
  pr1ᵉ (pr2ᵉ is-retraction-hom-retraction-precomp-retract-mapᵉ) =
    is-retraction-map-codomain-precomp-retract-mapᵉ
  pr2ᵉ (pr2ᵉ is-retraction-hom-retraction-precomp-retract-mapᵉ) =
    coh-retract-precomp-retract-mapᵉ

  retraction-precomp-retract-mapᵉ :
    retraction-hom-arrowᵉ
      ( precompᵉ fᵉ Sᵉ)
      ( precompᵉ gᵉ Sᵉ)
      ( inclusion-precomp-retract-mapᵉ)
  pr1ᵉ retraction-precomp-retract-mapᵉ =
    hom-retraction-precomp-retract-mapᵉ
  pr2ᵉ retraction-precomp-retract-mapᵉ =
    is-retraction-hom-retraction-precomp-retract-mapᵉ

  retract-map-precomp-retract-mapᵉ : (precompᵉ fᵉ Sᵉ) retract-of-mapᵉ (precompᵉ gᵉ Sᵉ)
  pr1ᵉ retract-map-precomp-retract-mapᵉ = inclusion-precomp-retract-mapᵉ
  pr2ᵉ retract-map-precomp-retract-mapᵉ = retraction-precomp-retract-mapᵉ
```

### If `f` is a retract of `g`, then `f ∘ -` is a retract of `g ∘ -`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (Rᵉ : fᵉ retract-of-mapᵉ gᵉ) (Sᵉ : UUᵉ l5ᵉ)
  where

  inclusion-postcomp-retract-mapᵉ : hom-arrowᵉ (postcompᵉ Sᵉ fᵉ) (postcompᵉ Sᵉ gᵉ)
  inclusion-postcomp-retract-mapᵉ =
    postcomp-hom-arrowᵉ fᵉ gᵉ (inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ) Sᵉ

  hom-retraction-postcomp-retract-mapᵉ : hom-arrowᵉ (postcompᵉ Sᵉ gᵉ) (postcompᵉ Sᵉ fᵉ)
  hom-retraction-postcomp-retract-mapᵉ =
    postcomp-hom-arrowᵉ gᵉ fᵉ (hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ) Sᵉ

  is-retraction-map-domain-postcomp-retract-mapᵉ :
    is-retractionᵉ
      ( map-domain-hom-arrowᵉ
        ( postcompᵉ Sᵉ fᵉ)
        ( postcompᵉ Sᵉ gᵉ)
        ( inclusion-postcomp-retract-mapᵉ))
      ( map-domain-hom-arrowᵉ
        ( postcompᵉ Sᵉ gᵉ)
        ( postcompᵉ Sᵉ fᵉ)
        ( hom-retraction-postcomp-retract-mapᵉ))
  is-retraction-map-domain-postcomp-retract-mapᵉ =
    htpy-postcompᵉ Sᵉ (is-retraction-map-domain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)

  is-retraction-map-codomain-postcomp-retract-mapᵉ :
    is-retractionᵉ
      ( map-codomain-hom-arrowᵉ
        ( postcompᵉ Sᵉ fᵉ)
        ( postcompᵉ Sᵉ gᵉ)
        ( inclusion-postcomp-retract-mapᵉ))
      ( map-codomain-hom-arrowᵉ
        ( postcompᵉ Sᵉ gᵉ)
        ( postcompᵉ Sᵉ fᵉ)
        ( hom-retraction-postcomp-retract-mapᵉ))
  is-retraction-map-codomain-postcomp-retract-mapᵉ =
    htpy-postcompᵉ Sᵉ
      ( is-retraction-map-codomain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)

  coh-retract-postcomp-retract-mapᵉ :
    coherence-retract-mapᵉ
      ( postcompᵉ Sᵉ fᵉ)
      ( postcompᵉ Sᵉ gᵉ)
      ( inclusion-postcomp-retract-mapᵉ)
      ( hom-retraction-postcomp-retract-mapᵉ)
      ( is-retraction-map-domain-postcomp-retract-mapᵉ)
      ( is-retraction-map-codomain-postcomp-retract-mapᵉ)
  coh-retract-postcomp-retract-mapᵉ =
    ( postcomp-vertical-coherence-prism-inv-triangles-mapsᵉ
      ( idᵉ)
      ( map-domain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( map-domain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( idᵉ)
      ( map-codomain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( fᵉ)
      ( gᵉ)
      ( fᵉ)
      ( is-retraction-map-domain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( refl-htpyᵉ)
      ( coh-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( coh-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( is-retraction-map-codomain-hom-retraction-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( coh-retract-mapᵉ fᵉ gᵉ Rᵉ)
      ( Sᵉ)) ∙hᵉ
    ( ap-concat-htpyᵉ
      ( is-retraction-map-codomain-postcomp-retract-mapᵉ ·rᵉ postcompᵉ Sᵉ fᵉ)
      ( eq-htpy-refl-htpyᵉ ∘ᵉ postcompᵉ Sᵉ fᵉ))

  is-retraction-hom-retraction-postcomp-retract-mapᵉ :
    is-retraction-hom-arrowᵉ
      ( postcompᵉ Sᵉ fᵉ)
      ( postcompᵉ Sᵉ gᵉ)
      ( inclusion-postcomp-retract-mapᵉ)
      ( hom-retraction-postcomp-retract-mapᵉ)
  pr1ᵉ is-retraction-hom-retraction-postcomp-retract-mapᵉ =
    is-retraction-map-domain-postcomp-retract-mapᵉ
  pr1ᵉ (pr2ᵉ is-retraction-hom-retraction-postcomp-retract-mapᵉ) =
    is-retraction-map-codomain-postcomp-retract-mapᵉ
  pr2ᵉ (pr2ᵉ is-retraction-hom-retraction-postcomp-retract-mapᵉ) =
    coh-retract-postcomp-retract-mapᵉ

  retraction-postcomp-retract-mapᵉ :
    retraction-hom-arrowᵉ
      ( postcompᵉ Sᵉ fᵉ)
      ( postcompᵉ Sᵉ gᵉ)
      ( inclusion-postcomp-retract-mapᵉ)
  pr1ᵉ retraction-postcomp-retract-mapᵉ =
    hom-retraction-postcomp-retract-mapᵉ
  pr2ᵉ retraction-postcomp-retract-mapᵉ =
    is-retraction-hom-retraction-postcomp-retract-mapᵉ

  retract-map-postcomp-retract-mapᵉ :
    (postcompᵉ Sᵉ fᵉ) retract-of-mapᵉ (postcompᵉ Sᵉ gᵉ)
  pr1ᵉ retract-map-postcomp-retract-mapᵉ = inclusion-postcomp-retract-mapᵉ
  pr2ᵉ retract-map-postcomp-retract-mapᵉ = retraction-postcomp-retract-mapᵉ
```

### If `A` is a retract of `B` and `S` is a retract of `T` then `diagonal-exponential A S` is a retract of `diagonal-exponential B T`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Sᵉ : UUᵉ l3ᵉ} {Tᵉ : UUᵉ l4ᵉ}
  (Rᵉ : Aᵉ retract-ofᵉ Bᵉ) (Qᵉ : Sᵉ retract-ofᵉ Tᵉ)
  where

  inclusion-diagonal-exponential-retractᵉ :
    hom-arrowᵉ (diagonal-exponentialᵉ Aᵉ Sᵉ) (diagonal-exponentialᵉ Bᵉ Tᵉ)
  inclusion-diagonal-exponential-retractᵉ =
    ( inclusion-retractᵉ Rᵉ ,ᵉ
      precompᵉ (map-retraction-retractᵉ Qᵉ) Bᵉ ∘ᵉ postcompᵉ Sᵉ (inclusion-retractᵉ Rᵉ) ,ᵉ
      refl-htpyᵉ)

  hom-retraction-diagonal-exponential-retractᵉ :
    hom-arrowᵉ (diagonal-exponentialᵉ Bᵉ Tᵉ) (diagonal-exponentialᵉ Aᵉ Sᵉ)
  hom-retraction-diagonal-exponential-retractᵉ =
    ( map-retraction-retractᵉ Rᵉ ,ᵉ
      postcompᵉ Sᵉ (map-retraction-retractᵉ Rᵉ) ∘ᵉ precompᵉ (inclusion-retractᵉ Qᵉ) Bᵉ ,ᵉ
      refl-htpyᵉ)

  coh-retract-map-diagonal-exponential-retractᵉ :
    coherence-retract-mapᵉ
      ( diagonal-exponentialᵉ Aᵉ Sᵉ)
      ( diagonal-exponentialᵉ Bᵉ Tᵉ)
      ( inclusion-diagonal-exponential-retractᵉ)
      ( hom-retraction-diagonal-exponential-retractᵉ)
      ( is-retraction-map-retraction-retractᵉ Rᵉ)
      ( horizontal-concat-htpyᵉ
        ( htpy-postcompᵉ Sᵉ (is-retraction-map-retraction-retractᵉ Rᵉ))
        ( htpy-precompᵉ (is-retraction-map-retraction-retractᵉ Qᵉ) Aᵉ))
  coh-retract-map-diagonal-exponential-retractᵉ xᵉ =
    ( compute-eq-htpy-ap-diagonal-exponentialᵉ Sᵉ
      ( map-retraction-retractᵉ Rᵉ (inclusion-retractᵉ Rᵉ xᵉ))
      ( xᵉ)
      ( is-retraction-map-retraction-retractᵉ Rᵉ xᵉ)) ∙ᵉ
    ( apᵉ
      ( λ pᵉ →
        ( apᵉ (λ fᵉ aᵉ → map-retraction-retractᵉ Rᵉ (inclusion-retractᵉ Rᵉ (fᵉ aᵉ))) pᵉ) ∙ᵉ
        ( eq-htpyᵉ (λ _ → is-retraction-map-retraction-retractᵉ Rᵉ xᵉ)))
      ( invᵉ
        ( ( apᵉ
            ( eq-htpyᵉ)
            ( eq-htpyᵉ (ap-constᵉ xᵉ ·rᵉ is-retraction-map-retraction-retractᵉ Qᵉ))) ∙ᵉ
          ( eq-htpy-refl-htpyᵉ (diagonal-exponentialᵉ Aᵉ Sᵉ xᵉ))))) ∙ᵉ
      ( invᵉ right-unitᵉ)

  is-retraction-hom-retraction-diagonal-exponential-retractᵉ :
    is-retraction-hom-arrowᵉ
      ( diagonal-exponentialᵉ Aᵉ Sᵉ)
      ( diagonal-exponentialᵉ Bᵉ Tᵉ)
      ( inclusion-diagonal-exponential-retractᵉ)
      ( hom-retraction-diagonal-exponential-retractᵉ)
  is-retraction-hom-retraction-diagonal-exponential-retractᵉ =
    ( ( is-retraction-map-retraction-retractᵉ Rᵉ) ,ᵉ
      ( horizontal-concat-htpyᵉ
        ( htpy-postcompᵉ Sᵉ (is-retraction-map-retraction-retractᵉ Rᵉ))
        ( htpy-precompᵉ (is-retraction-map-retraction-retractᵉ Qᵉ) Aᵉ)) ,ᵉ
      ( coh-retract-map-diagonal-exponential-retractᵉ))

  retract-map-diagonal-exponential-retractᵉ :
    (diagonal-exponentialᵉ Aᵉ Sᵉ) retract-of-mapᵉ (diagonal-exponentialᵉ Bᵉ Tᵉ)
  retract-map-diagonal-exponential-retractᵉ =
    ( inclusion-diagonal-exponential-retractᵉ ,ᵉ
      hom-retraction-diagonal-exponential-retractᵉ ,ᵉ
      is-retraction-hom-retraction-diagonal-exponential-retractᵉ)
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ UF13ᵉ}}

## External links

-ᵉ [Retractsᵉ in arrowᵉ categories](https://ncatlab.org/nlab/show/retract#in_arrow_categoriesᵉ)
  atᵉ $n$Labᵉ

Aᵉ wikidataᵉ identifierᵉ wasᵉ notᵉ availableᵉ forᵉ thisᵉ concept.ᵉ