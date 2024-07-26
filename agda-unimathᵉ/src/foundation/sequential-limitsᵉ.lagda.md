# Sequential limits

```agda
module foundation.sequential-limitsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cones-over-inverse-sequential-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.inverse-sequential-diagramsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universal-property-sequential-limitsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-homotopiesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Givenᵉ anᵉ
[inverseᵉ sequentialᵉ diagramᵉ ofᵉ types](foundation.inverse-sequential-diagrams.mdᵉ)

```text
               fₙᵉ                     f₁ᵉ      f₀ᵉ
  ⋯ᵉ --->ᵉ Aₙ₊₁ᵉ --->ᵉ Aₙᵉ --->ᵉ ⋯ᵉ --->ᵉ A₂ᵉ --->ᵉ A₁ᵉ --->ᵉ A₀ᵉ
```

weᵉ canᵉ formᵉ theᵉ **standardᵉ sequentialᵉ limit**ᵉ `limₙᵉ Aₙ`ᵉ satisfyingᵉ
[theᵉ universalᵉ propertyᵉ ofᵉ theᵉ sequentialᵉ limit](foundation.universal-property-sequential-limits.mdᵉ)
ofᵉ `Aₙ`ᵉ thusᵉ completingᵉ theᵉ diagramᵉ

```text
                           fₙᵉ                     f₁ᵉ      f₀ᵉ
  limₙᵉ Aₙᵉ --->ᵉ ⋯ᵉ --->ᵉ Aₙ₊₁ᵉ --->ᵉ Aₙᵉ --->ᵉ ⋯ᵉ --->ᵉ A₂ᵉ --->ᵉ A₁ᵉ --->ᵉ A₀.ᵉ
```

Theᵉ standardᵉ sequentialᵉ limitᵉ consistsᵉ ofᵉ "pointsᵉ atᵉ infinity",ᵉ whichᵉ canᵉ beᵉ
recordedᵉ asᵉ [sequences](foundation.dependent-sequences.mdᵉ) ofᵉ termsᵉ whoseᵉ imagesᵉ
underᵉ `f`ᵉ agreeᵉ:

```text
  ⋯ᵉ  ↦ᵉ   xₙ₊₁ᵉ  ↦ᵉ   xₙᵉ  ↦ᵉ   ⋯ᵉ  ↦ᵉ   x₂ᵉ  ↦ᵉ   x₁ᵉ  ↦ᵉ   x₀ᵉ
          ⫙ᵉ        ⫙ᵉ              ⫙ᵉ       ⫙ᵉ       ⫙ᵉ
  ⋯ᵉ --->ᵉ Aₙ₊₁ᵉ --->ᵉ Aₙᵉ --->ᵉ ⋯ᵉ --->ᵉ A₂ᵉ --->ᵉ A₁ᵉ --->ᵉ A₀.ᵉ
```

## Definitions

### The standard sequential limit

```agda
module _
  {lᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ lᵉ)
  where

  standard-sequential-limitᵉ : UUᵉ lᵉ
  standard-sequential-limitᵉ =
    Σᵉ ( (nᵉ : ℕᵉ) → family-inverse-sequential-diagramᵉ Aᵉ nᵉ)
      ( λ aᵉ → (nᵉ : ℕᵉ) → aᵉ nᵉ ＝ᵉ map-inverse-sequential-diagramᵉ Aᵉ nᵉ (aᵉ (succ-ℕᵉ nᵉ)))

module _
  {lᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ lᵉ)
  where

  sequence-standard-sequential-limitᵉ :
    standard-sequential-limitᵉ Aᵉ → (nᵉ : ℕᵉ) →
    family-inverse-sequential-diagramᵉ Aᵉ nᵉ
  sequence-standard-sequential-limitᵉ = pr1ᵉ

  coherence-standard-sequential-limitᵉ :
    (xᵉ : standard-sequential-limitᵉ Aᵉ) (nᵉ : ℕᵉ) →
    sequence-standard-sequential-limitᵉ xᵉ nᵉ ＝ᵉ
    map-inverse-sequential-diagramᵉ Aᵉ nᵉ
      ( sequence-standard-sequential-limitᵉ xᵉ (succ-ℕᵉ nᵉ))
  coherence-standard-sequential-limitᵉ = pr2ᵉ
```

### The cone at the standard sequential limit

```agda
module _
  {lᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ lᵉ)
  where

  cone-standard-sequential-limitᵉ :
    cone-inverse-sequential-diagramᵉ Aᵉ (standard-sequential-limitᵉ Aᵉ)
  pr1ᵉ cone-standard-sequential-limitᵉ nᵉ xᵉ =
    sequence-standard-sequential-limitᵉ Aᵉ xᵉ nᵉ
  pr2ᵉ cone-standard-sequential-limitᵉ nᵉ xᵉ =
    coherence-standard-sequential-limitᵉ Aᵉ xᵉ nᵉ
```

### The gap map into the standard sequential limit

Theᵉ **gapᵉ map**ᵉ ofᵉ aᵉ
[coneᵉ overᵉ anᵉ inverseᵉ sequentialᵉ diagram](foundation.cones-over-inverse-sequential-diagrams.mdᵉ)
isᵉ theᵉ mapᵉ fromᵉ theᵉ domainᵉ ofᵉ theᵉ coneᵉ intoᵉ theᵉ standardᵉ sequentialᵉ limit.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ) {Xᵉ : UUᵉ l2ᵉ}
  where

  gap-inverse-sequential-diagramᵉ :
    cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ → Xᵉ → standard-sequential-limitᵉ Aᵉ
  pr1ᵉ (gap-inverse-sequential-diagramᵉ cᵉ xᵉ) nᵉ =
    map-cone-inverse-sequential-diagramᵉ Aᵉ cᵉ nᵉ xᵉ
  pr2ᵉ (gap-inverse-sequential-diagramᵉ cᵉ xᵉ) nᵉ =
    coherence-cone-inverse-sequential-diagramᵉ Aᵉ cᵉ nᵉ xᵉ
```

### The property of being a sequential limit

Theᵉ [proposition](foundation-core.propositions.mdᵉ) `is-sequential-limit`ᵉ isᵉ theᵉ
assertionᵉ thatᵉ theᵉ gapᵉ mapᵉ isᵉ anᵉ [equivalence](foundation-core.equivalences.md).ᵉ
Noteᵉ thatᵉ thisᵉ propositionᵉ isᵉ [small](foundation-core.small-types.md),ᵉ whereasᵉ
[theᵉ universalᵉ property](foundation.universal-property-sequential-limits.mdᵉ) isᵉ
aᵉ largeᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ) {Xᵉ : UUᵉ l2ᵉ}
  where

  is-sequential-limitᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-sequential-limitᵉ cᵉ = is-equivᵉ (gap-inverse-sequential-diagramᵉ Aᵉ cᵉ)

  is-property-is-sequential-limitᵉ :
    (cᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ) → is-propᵉ (is-sequential-limitᵉ cᵉ)
  is-property-is-sequential-limitᵉ cᵉ =
    is-property-is-equivᵉ (gap-inverse-sequential-diagramᵉ Aᵉ cᵉ)

  is-sequential-limit-Propᵉ :
    (cᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (is-sequential-limit-Propᵉ cᵉ) = is-sequential-limitᵉ cᵉ
  pr2ᵉ (is-sequential-limit-Propᵉ cᵉ) = is-property-is-sequential-limitᵉ cᵉ
```

## Properties

### Characterization of equality in the standard sequential limit

```agda
module _
  {lᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ lᵉ)
  where

  coherence-Eq-standard-sequential-limitᵉ :
    (sᵉ tᵉ : standard-sequential-limitᵉ Aᵉ)
    (Hᵉ :
      sequence-standard-sequential-limitᵉ Aᵉ sᵉ ~ᵉ
      sequence-standard-sequential-limitᵉ Aᵉ tᵉ) → UUᵉ lᵉ
  coherence-Eq-standard-sequential-limitᵉ sᵉ tᵉ Hᵉ =
    coherence-square-homotopiesᵉ
      ( Hᵉ)
      ( coherence-standard-sequential-limitᵉ Aᵉ sᵉ)
      ( coherence-standard-sequential-limitᵉ Aᵉ tᵉ)
      ( λ nᵉ → apᵉ (map-inverse-sequential-diagramᵉ Aᵉ nᵉ) (Hᵉ (succ-ℕᵉ nᵉ)))

  Eq-standard-sequential-limitᵉ : (sᵉ tᵉ : standard-sequential-limitᵉ Aᵉ) → UUᵉ lᵉ
  Eq-standard-sequential-limitᵉ sᵉ tᵉ =
    Σᵉ ( sequence-standard-sequential-limitᵉ Aᵉ sᵉ ~ᵉ
        sequence-standard-sequential-limitᵉ Aᵉ tᵉ)
      ( coherence-Eq-standard-sequential-limitᵉ sᵉ tᵉ)

  refl-Eq-standard-sequential-limitᵉ :
    (sᵉ : standard-sequential-limitᵉ Aᵉ) → Eq-standard-sequential-limitᵉ sᵉ sᵉ
  pr1ᵉ (refl-Eq-standard-sequential-limitᵉ sᵉ) = refl-htpyᵉ
  pr2ᵉ (refl-Eq-standard-sequential-limitᵉ sᵉ) = right-unit-htpyᵉ

  Eq-eq-standard-sequential-limitᵉ :
    (sᵉ tᵉ : standard-sequential-limitᵉ Aᵉ) →
    sᵉ ＝ᵉ tᵉ → Eq-standard-sequential-limitᵉ sᵉ tᵉ
  Eq-eq-standard-sequential-limitᵉ sᵉ .sᵉ reflᵉ =
    refl-Eq-standard-sequential-limitᵉ sᵉ

  is-torsorial-Eq-standard-sequential-limitᵉ :
    (sᵉ : standard-sequential-limitᵉ Aᵉ) →
    is-torsorialᵉ (Eq-standard-sequential-limitᵉ sᵉ)
  is-torsorial-Eq-standard-sequential-limitᵉ sᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (pr1ᵉ sᵉ))
      ( pr1ᵉ sᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-Eq-Πᵉ (λ nᵉ → is-torsorial-Idᵉ (pr2ᵉ sᵉ nᵉ ∙ᵉ reflᵉ)))

  is-equiv-Eq-eq-standard-sequential-limitᵉ :
    (sᵉ tᵉ : standard-sequential-limitᵉ Aᵉ) →
    is-equivᵉ (Eq-eq-standard-sequential-limitᵉ sᵉ tᵉ)
  is-equiv-Eq-eq-standard-sequential-limitᵉ sᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-Eq-standard-sequential-limitᵉ sᵉ)
      ( Eq-eq-standard-sequential-limitᵉ sᵉ)

  extensionality-standard-sequential-limitᵉ :
    (sᵉ tᵉ : standard-sequential-limitᵉ Aᵉ) →
    (sᵉ ＝ᵉ tᵉ) ≃ᵉ Eq-standard-sequential-limitᵉ sᵉ tᵉ
  pr1ᵉ (extensionality-standard-sequential-limitᵉ sᵉ tᵉ) =
    Eq-eq-standard-sequential-limitᵉ sᵉ tᵉ
  pr2ᵉ (extensionality-standard-sequential-limitᵉ sᵉ tᵉ) =
    is-equiv-Eq-eq-standard-sequential-limitᵉ sᵉ tᵉ

  eq-Eq-standard-sequential-limitᵉ :
    (sᵉ tᵉ : standard-sequential-limitᵉ Aᵉ) →
    Eq-standard-sequential-limitᵉ sᵉ tᵉ → sᵉ ＝ᵉ tᵉ
  eq-Eq-standard-sequential-limitᵉ sᵉ tᵉ =
    map-inv-equivᵉ (extensionality-standard-sequential-limitᵉ sᵉ tᵉ)
```

### The standard sequential limit satisfies the universal property of a sequential limit

```agda
module _
  {l1ᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ)
  where

  cone-map-standard-sequential-limitᵉ :
    {lᵉ : Level} {Yᵉ : UUᵉ lᵉ} →
    (Yᵉ → standard-sequential-limitᵉ Aᵉ) → cone-inverse-sequential-diagramᵉ Aᵉ Yᵉ
  cone-map-standard-sequential-limitᵉ {Yᵉ = Yᵉ} =
    cone-map-inverse-sequential-diagramᵉ Aᵉ {Yᵉ = Yᵉ}
      ( cone-standard-sequential-limitᵉ Aᵉ)

  is-retraction-gap-inverse-sequential-diagramᵉ :
    {lᵉ : Level} {Yᵉ : UUᵉ lᵉ} →
    is-retractionᵉ
      ( cone-map-standard-sequential-limitᵉ {Yᵉ = Yᵉ})
      ( gap-inverse-sequential-diagramᵉ Aᵉ)
  is-retraction-gap-inverse-sequential-diagramᵉ = refl-htpyᵉ

  is-section-gap-inverse-sequential-diagramᵉ :
    {lᵉ : Level} {Yᵉ : UUᵉ lᵉ} →
    is-sectionᵉ
      ( cone-map-standard-sequential-limitᵉ {Yᵉ = Yᵉ})
      ( gap-inverse-sequential-diagramᵉ Aᵉ)
  is-section-gap-inverse-sequential-diagramᵉ = refl-htpyᵉ

  up-standard-sequential-limitᵉ :
    universal-property-sequential-limitᵉ Aᵉ (cone-standard-sequential-limitᵉ Aᵉ)
  pr1ᵉ (pr1ᵉ (up-standard-sequential-limitᵉ Xᵉ)) =
    gap-inverse-sequential-diagramᵉ Aᵉ
  pr2ᵉ (pr1ᵉ (up-standard-sequential-limitᵉ Xᵉ)) =
    is-section-gap-inverse-sequential-diagramᵉ
  pr1ᵉ (pr2ᵉ (up-standard-sequential-limitᵉ Xᵉ)) =
    gap-inverse-sequential-diagramᵉ Aᵉ
  pr2ᵉ (pr2ᵉ (up-standard-sequential-limitᵉ Xᵉ)) =
    is-retraction-gap-inverse-sequential-diagramᵉ
```

### A cone over an inverse sequential diagram is equal to the value of `cone-map-inverse-sequential-diagram` at its own gap map

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ) {Xᵉ : UUᵉ l2ᵉ}
  (cᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  htpy-cone-up-sequential-limit-standard-sequential-limitᵉ :
    htpy-cone-inverse-sequential-diagramᵉ Aᵉ
      ( cone-map-inverse-sequential-diagramᵉ Aᵉ
        ( cone-standard-sequential-limitᵉ Aᵉ)
        ( gap-inverse-sequential-diagramᵉ Aᵉ cᵉ))
      ( cᵉ)
  pr1ᵉ htpy-cone-up-sequential-limit-standard-sequential-limitᵉ nᵉ = refl-htpyᵉ
  pr2ᵉ htpy-cone-up-sequential-limit-standard-sequential-limitᵉ nᵉ =
    right-unit-htpyᵉ
```

### A cone satisfies the universal property of the sequential limit if and only if the gap map is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ) {Xᵉ : UUᵉ l2ᵉ}
  (cᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  is-sequential-limit-universal-property-sequential-limitᵉ :
    universal-property-sequential-limitᵉ Aᵉ cᵉ → is-sequential-limitᵉ Aᵉ cᵉ
  is-sequential-limit-universal-property-sequential-limitᵉ =
    is-equiv-universal-property-sequential-limit-universal-property-sequential-limitᵉ
      ( cone-standard-sequential-limitᵉ Aᵉ)
      ( cᵉ)
      ( gap-inverse-sequential-diagramᵉ Aᵉ cᵉ)
      ( htpy-cone-up-sequential-limit-standard-sequential-limitᵉ Aᵉ cᵉ)
      ( up-standard-sequential-limitᵉ Aᵉ)

  universal-property-is-sequential-limitᵉ :
    is-sequential-limitᵉ Aᵉ cᵉ → universal-property-sequential-limitᵉ Aᵉ cᵉ
  universal-property-is-sequential-limitᵉ is-lim-cᵉ =
    universal-property-sequential-limit-universal-property-sequential-limit-is-equivᵉ
      ( cone-standard-sequential-limitᵉ Aᵉ)
      ( cᵉ)
      ( gap-inverse-sequential-diagramᵉ Aᵉ cᵉ)
      ( htpy-cone-up-sequential-limit-standard-sequential-limitᵉ Aᵉ cᵉ)
      ( is-lim-cᵉ)
      ( up-standard-sequential-limitᵉ Aᵉ)
```

## Table of files about sequential limits

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ sequentialᵉ limitsᵉ asᵉ aᵉ generalᵉ
concept.ᵉ

{{#includeᵉ tables/sequential-limits.mdᵉ}}