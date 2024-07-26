# The universal property of the family of fibers of maps

```agda
module foundation.universal-property-family-of-fibers-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.diagonal-maps-of-typesᵉ
open import foundation.families-of-equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.constant-mapsᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.precomposition-dependent-functionsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ

open import orthogonal-factorization-systems.extensions-double-lifts-families-of-elementsᵉ
open import orthogonal-factorization-systems.lifts-families-of-elementsᵉ
```

</details>

## Idea

Anyᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ inducesᵉ aᵉ typeᵉ familyᵉ `fiberᵉ fᵉ : Bᵉ → 𝒰`ᵉ ofᵉ
[fibers](foundation-core.fibers-of-maps.mdᵉ) ofᵉ `f`.ᵉ Byᵉ
[precomposing](foundation.precomposition-type-families.mdᵉ) with `f`,ᵉ weᵉ obtainᵉ
theᵉ typeᵉ familyᵉ `(fiberᵉ fᵉ) ∘ᵉ fᵉ : Aᵉ → 𝒰`,ᵉ whichᵉ alwaysᵉ hasᵉ aᵉ sectionᵉ givenᵉ byᵉ

```text
  λ aᵉ → (aᵉ ,ᵉ reflᵉ) : (aᵉ : Aᵉ) → fiberᵉ fᵉ (fᵉ a).ᵉ
```

Weᵉ canᵉ uniquelyᵉ characterizeᵉ theᵉ familyᵉ ofᵉ fibersᵉ `fiberᵉ fᵉ : Bᵉ → 𝒰`ᵉ asᵉ theᵉ
initialᵉ typeᵉ familyᵉ equippedᵉ with suchᵉ aᵉ section.ᵉ Explicitly,ᵉ theᵉ
{{#conceptᵉ "universalᵉ propertyᵉ ofᵉ theᵉ familyᵉ ofᵉ fibers"ᵉ Disambiguation="maps"ᵉ Agda=universal-property-family-of-fibersᵉ}}
`fiberᵉ fᵉ : Bᵉ → 𝒰`ᵉ ofᵉ aᵉ mapᵉ `f`ᵉ isᵉ thatᵉ theᵉ precompositionᵉ operationᵉ

```text
  ((bᵉ : Bᵉ) → fiberᵉ fᵉ bᵉ → Xᵉ bᵉ) → ((aᵉ : Aᵉ) → Xᵉ (fᵉ aᵉ))
```

isᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) forᵉ anyᵉ typeᵉ familyᵉ
`Xᵉ : Bᵉ → 𝒰`.ᵉ Noteᵉ thatᵉ forᵉ anyᵉ typeᵉ familyᵉ `X`ᵉ overᵉ `B`ᵉ andᵉ anyᵉ mapᵉ `fᵉ : Aᵉ → B`,ᵉ
theᵉ typeᵉ ofᵉ
[lifts](orthogonal-factorization-systems.lifts-families-of-elements.mdᵉ) ofᵉ `f`ᵉ
to `X`ᵉ isᵉ preciselyᵉ theᵉ typeᵉ ofᵉ sectionsᵉ

```text
  (aᵉ : Aᵉ) → Xᵉ (fᵉ a).ᵉ
```

Theᵉ familyᵉ ofᵉ fibersᵉ ofᵉ `f`ᵉ isᵉ thereforeᵉ theᵉ initialᵉ typeᵉ familyᵉ overᵉ `B`ᵉ
equippedᵉ with aᵉ liftᵉ ofᵉ `f`.ᵉ

Thisᵉ universalᵉ propertyᵉ isᵉ especiallyᵉ usefulᵉ whenᵉ `A`ᵉ orᵉ `B`ᵉ enjoyᵉ mappingᵉ outᵉ
universalᵉ properties.ᵉ Thisᵉ letsᵉ usᵉ characterizeᵉ theᵉ sectionsᵉ `(aᵉ : Aᵉ) → Xᵉ (fᵉ a)`ᵉ
in termsᵉ ofᵉ theᵉ mappingᵉ outᵉ propertiesᵉ ofᵉ `A`ᵉ andᵉ theᵉ descentᵉ data ofᵉ `B`.ᵉ

**Note:**ᵉ Weᵉ disambiguateᵉ betweenᵉ theᵉ _universalᵉ propertyᵉ ofᵉ theᵉ familyᵉ ofᵉ
fibersᵉ ofᵉ aᵉ mapᵉ_ andᵉ theᵉ _universalᵉ propertyᵉ ofᵉ theᵉ fiberᵉ ofᵉ aᵉ mapᵉ_ atᵉ aᵉ pointᵉ
in theᵉ codomain.ᵉ Theᵉ universalᵉ propertyᵉ ofᵉ theᵉ familyᵉ ofᵉ fibersᵉ ofᵉ aᵉ mapᵉ isᵉ asᵉ
describedᵉ above,ᵉ whileᵉ theᵉ universalᵉ propertyᵉ ofᵉ theᵉ fiberᵉ `fiberᵉ fᵉ b`ᵉ ofᵉ aᵉ mapᵉ
`f`ᵉ atᵉ `b`ᵉ isᵉ aᵉ specialᵉ caseᵉ ofᵉ theᵉ universalᵉ propertyᵉ ofᵉ pullbacks.ᵉ

## Definitions

### The dependent universal property of the family of fibers of a map

Considerᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ aᵉ typeᵉ familyᵉ `Fᵉ : Bᵉ → 𝒰`ᵉ equippedᵉ with aᵉ liftᵉ
`δᵉ : (aᵉ : Aᵉ) → Fᵉ (fᵉ a)`ᵉ ofᵉ `f`ᵉ to `F`.ᵉ Thenᵉ thereᵉ isᵉ anᵉ evaluationᵉ mapᵉ

```text
  ((bᵉ : Bᵉ) (zᵉ : Fᵉ bᵉ) → Xᵉ bᵉ zᵉ) → ((aᵉ : Aᵉ) → Xᵉ (fᵉ aᵉ) (δᵉ aᵉ))
```

forᵉ anyᵉ binaryᵉ typeᵉ familyᵉ `Xᵉ : (bᵉ : Bᵉ) → Fᵉ bᵉ → 𝒰`.ᵉ Thisᵉ evaluationᵉ mapᵉ takesᵉ aᵉ
binaryᵉ familyᵉ ofᵉ elementsᵉ ofᵉ `X`ᵉ to aᵉ
[doubleᵉ lift](orthogonal-factorization-systems.double-lifts-families-of-elements.mdᵉ)
ofᵉ `f`ᵉ andᵉ `δ`.ᵉ Theᵉ
{{#conceptᵉ "dependentᵉ universalᵉ propertyᵉ ofᵉ theᵉ familyᵉ ofᵉ fibersᵉ ofᵉ aᵉ map"ᵉ Agda=dependent-universal-property-family-of-fibersᵉ}}
`f`ᵉ assertsᵉ thatᵉ thisᵉ evaluationᵉ mapᵉ isᵉ anᵉ equivalence.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  dependent-universal-property-family-of-fibersᵉ :
    {fᵉ : Aᵉ → Bᵉ} (Fᵉ : Bᵉ → UUᵉ l3ᵉ) (δᵉ : lift-family-of-elementsᵉ Fᵉ fᵉ) → UUωᵉ
  dependent-universal-property-family-of-fibersᵉ Fᵉ δᵉ =
    {lᵉ : Level} (Xᵉ : (bᵉ : Bᵉ) → Fᵉ bᵉ → UUᵉ lᵉ) →
    is-equivᵉ (ev-double-lift-family-of-elementsᵉ {Bᵉ = Fᵉ} {Xᵉ} δᵉ)
```

### The universal property of the family of fibers of a map

Considerᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ aᵉ typeᵉ familyᵉ `Fᵉ : Bᵉ → 𝒰`ᵉ equippedᵉ with aᵉ liftᵉ
`δᵉ : (aᵉ : Aᵉ) → Fᵉ (fᵉ a)`ᵉ ofᵉ `f`ᵉ to `F`.ᵉ Thenᵉ thereᵉ isᵉ anᵉ evaluationᵉ mapᵉ

```text
  ((bᵉ : Bᵉ) → Fᵉ bᵉ → Xᵉ bᵉ) → ((aᵉ : Aᵉ) → Xᵉ (fᵉ aᵉ))
```

forᵉ anyᵉ binaryᵉ typeᵉ familyᵉ `Xᵉ : Bᵉ → 𝒰`.ᵉ Thisᵉ evaluationᵉ mapᵉ takesᵉ aᵉ binaryᵉ
familyᵉ ofᵉ elementsᵉ ofᵉ `X`ᵉ to aᵉ doubleᵉ liftᵉ ofᵉ `f`ᵉ andᵉ `δ`.ᵉ Theᵉ universalᵉ
propertyᵉ ofᵉ theᵉ familyᵉ ofᵉ fibersᵉ ofᵉ `f`ᵉ assertsᵉ thatᵉ thisᵉ evaluationᵉ mapᵉ isᵉ anᵉ
equivalence.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  universal-property-family-of-fibersᵉ :
    {fᵉ : Aᵉ → Bᵉ} (Fᵉ : Bᵉ → UUᵉ l3ᵉ) (δᵉ : lift-family-of-elementsᵉ Fᵉ fᵉ) → UUωᵉ
  universal-property-family-of-fibersᵉ Fᵉ δᵉ =
    {lᵉ : Level} (Xᵉ : Bᵉ → UUᵉ lᵉ) →
    is-equivᵉ (ev-double-lift-family-of-elementsᵉ {Bᵉ = Fᵉ} {λ bᵉ _ → Xᵉ bᵉ} δᵉ)
```

### The lift of any map to its family of fibers

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  lift-family-of-elements-fiberᵉ : lift-family-of-elementsᵉ (fiberᵉ fᵉ) fᵉ
  pr1ᵉ (lift-family-of-elements-fiberᵉ aᵉ) = aᵉ
  pr2ᵉ (lift-family-of-elements-fiberᵉ aᵉ) = reflᵉ
```

## Properties

### The family of fibers of a map satisfies the dependent universal property of the family of fibers of a map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  module _
    {l3ᵉ : Level} (Cᵉ : (yᵉ : Bᵉ) (zᵉ : fiberᵉ fᵉ yᵉ) → UUᵉ l3ᵉ)
    where

    ev-lift-family-of-elements-fiberᵉ :
      ((yᵉ : Bᵉ) (zᵉ : fiberᵉ fᵉ yᵉ) → Cᵉ yᵉ zᵉ) → ((xᵉ : Aᵉ) → Cᵉ (fᵉ xᵉ) (xᵉ ,ᵉ reflᵉ))
    ev-lift-family-of-elements-fiberᵉ =
      ev-double-lift-family-of-elementsᵉ (lift-family-of-elements-fiberᵉ fᵉ)

    extend-lift-family-of-elements-fiberᵉ :
      ((xᵉ : Aᵉ) → Cᵉ (fᵉ xᵉ) (xᵉ ,ᵉ reflᵉ)) → ((yᵉ : Bᵉ) (zᵉ : fiberᵉ fᵉ yᵉ) → Cᵉ yᵉ zᵉ)
    extend-lift-family-of-elements-fiberᵉ hᵉ .(fᵉ xᵉ) (xᵉ ,ᵉ reflᵉ) = hᵉ xᵉ

    is-section-extend-lift-family-of-elements-fiberᵉ :
      is-sectionᵉ
        ( ev-lift-family-of-elements-fiberᵉ)
        ( extend-lift-family-of-elements-fiberᵉ)
    is-section-extend-lift-family-of-elements-fiberᵉ hᵉ = reflᵉ

    is-retraction-extend-lift-family-of-elements-fiber'ᵉ :
      (hᵉ : (yᵉ : Bᵉ) (zᵉ : fiberᵉ fᵉ yᵉ) → Cᵉ yᵉ zᵉ) (yᵉ : Bᵉ) →
      extend-lift-family-of-elements-fiberᵉ
        ( ev-lift-family-of-elements-fiberᵉ hᵉ)
        ( yᵉ) ~ᵉ
      hᵉ yᵉ
    is-retraction-extend-lift-family-of-elements-fiber'ᵉ hᵉ .(fᵉ zᵉ) (zᵉ ,ᵉ reflᵉ) =
      reflᵉ

    is-retraction-extend-lift-family-of-elements-fiberᵉ :
      is-retractionᵉ
        ( ev-lift-family-of-elements-fiberᵉ)
        ( extend-lift-family-of-elements-fiberᵉ)
    is-retraction-extend-lift-family-of-elements-fiberᵉ hᵉ =
      eq-htpyᵉ (eq-htpyᵉ ∘ᵉ is-retraction-extend-lift-family-of-elements-fiber'ᵉ hᵉ)

    is-equiv-extend-lift-family-of-elements-fiberᵉ :
      is-equivᵉ extend-lift-family-of-elements-fiberᵉ
    is-equiv-extend-lift-family-of-elements-fiberᵉ =
      is-equiv-is-invertibleᵉ
        ( ev-lift-family-of-elements-fiberᵉ)
        ( is-retraction-extend-lift-family-of-elements-fiberᵉ)
        ( is-section-extend-lift-family-of-elements-fiberᵉ)

    inv-equiv-dependent-universal-property-family-of-fibersᵉ :
      ((xᵉ : Aᵉ) → Cᵉ (fᵉ xᵉ) (xᵉ ,ᵉ reflᵉ)) ≃ᵉ ((yᵉ : Bᵉ) (zᵉ : fiberᵉ fᵉ yᵉ) → Cᵉ yᵉ zᵉ)
    pr1ᵉ inv-equiv-dependent-universal-property-family-of-fibersᵉ =
      extend-lift-family-of-elements-fiberᵉ
    pr2ᵉ inv-equiv-dependent-universal-property-family-of-fibersᵉ =
      is-equiv-extend-lift-family-of-elements-fiberᵉ

  dependent-universal-property-family-of-fibers-fiberᵉ :
    dependent-universal-property-family-of-fibersᵉ
      ( fiberᵉ fᵉ)
      ( lift-family-of-elements-fiberᵉ fᵉ)
  dependent-universal-property-family-of-fibers-fiberᵉ Cᵉ =
    is-equiv-is-invertibleᵉ
      ( extend-lift-family-of-elements-fiberᵉ Cᵉ)
      ( is-section-extend-lift-family-of-elements-fiberᵉ Cᵉ)
      ( is-retraction-extend-lift-family-of-elements-fiberᵉ Cᵉ)

  equiv-dependent-universal-property-family-of-fibersᵉ :
    {l3ᵉ : Level} (Cᵉ : (yᵉ : Bᵉ) (zᵉ : fiberᵉ fᵉ yᵉ) → UUᵉ l3ᵉ) →
    ((yᵉ : Bᵉ) (zᵉ : fiberᵉ fᵉ yᵉ) → Cᵉ yᵉ zᵉ) ≃ᵉ
    ((xᵉ : Aᵉ) → Cᵉ (fᵉ xᵉ) (xᵉ ,ᵉ reflᵉ))
  pr1ᵉ (equiv-dependent-universal-property-family-of-fibersᵉ Cᵉ) =
    ev-lift-family-of-elements-fiberᵉ Cᵉ
  pr2ᵉ (equiv-dependent-universal-property-family-of-fibersᵉ Cᵉ) =
    dependent-universal-property-family-of-fibers-fiberᵉ Cᵉ
```

### The family of fibers of a map satisfies the universal property of the family of fibers of a map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  universal-property-family-of-fibers-fiberᵉ :
    universal-property-family-of-fibersᵉ
      ( fiberᵉ fᵉ)
      ( lift-family-of-elements-fiberᵉ fᵉ)
  universal-property-family-of-fibers-fiberᵉ Cᵉ =
    dependent-universal-property-family-of-fibers-fiberᵉ fᵉ (λ yᵉ _ → Cᵉ yᵉ)

  equiv-universal-property-family-of-fibersᵉ :
    {l3ᵉ : Level} (Cᵉ : Bᵉ → UUᵉ l3ᵉ) →
    ((yᵉ : Bᵉ) → fiberᵉ fᵉ yᵉ → Cᵉ yᵉ) ≃ᵉ lift-family-of-elementsᵉ Cᵉ fᵉ
  equiv-universal-property-family-of-fibersᵉ Cᵉ =
    equiv-dependent-universal-property-family-of-fibersᵉ fᵉ (λ yᵉ _ → Cᵉ yᵉ)
```

### The inverse equivalence of the universal property of the family of fibers of a map

Theᵉ inverseᵉ ofᵉ theᵉ equivalenceᵉ `equiv-universal-property-family-of-fibers`ᵉ hasᵉ aᵉ
reasonablyᵉ niceᵉ definition,ᵉ soᵉ weᵉ alsoᵉ record itᵉ here.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Cᵉ : Bᵉ → UUᵉ l3ᵉ)
  where

  inv-equiv-universal-property-family-of-fibersᵉ :
    (lift-family-of-elementsᵉ Cᵉ fᵉ) ≃ᵉ ((yᵉ : Bᵉ) → fiberᵉ fᵉ yᵉ → Cᵉ yᵉ)
  inv-equiv-universal-property-family-of-fibersᵉ =
    inv-equiv-dependent-universal-property-family-of-fibersᵉ fᵉ (λ yᵉ _ → Cᵉ yᵉ)
```

### If a type family equipped with a lift of a map satisfies the universal property of the family of fibers, then it satisfies a unique extension property

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  {Fᵉ : Bᵉ → UUᵉ l3ᵉ} {δᵉ : (aᵉ : Aᵉ) → Fᵉ (fᵉ aᵉ)}
  (uᵉ : universal-property-family-of-fibersᵉ Fᵉ δᵉ)
  (Gᵉ : Bᵉ → UUᵉ l4ᵉ) (γᵉ : (aᵉ : Aᵉ) → Gᵉ (fᵉ aᵉ))
  where

  abstract
    uniqueness-extension-universal-property-family-of-fibersᵉ :
      is-contrᵉ
        ( extension-double-lift-family-of-elementsᵉ (λ yᵉ (ᵉ_ : Fᵉ yᵉ) → Gᵉ yᵉ) δᵉ γᵉ)
    uniqueness-extension-universal-property-family-of-fibersᵉ =
      is-contr-equivᵉ
        ( fiberᵉ (ev-double-lift-family-of-elementsᵉ δᵉ) γᵉ)
        ( equiv-totᵉ (λ hᵉ → equiv-eq-htpyᵉ))
        ( is-contr-map-is-equivᵉ (uᵉ Gᵉ) γᵉ)

  abstract
    extension-universal-property-family-of-fibersᵉ :
      extension-double-lift-family-of-elementsᵉ (λ yᵉ (ᵉ_ : Fᵉ yᵉ) → Gᵉ yᵉ) δᵉ γᵉ
    extension-universal-property-family-of-fibersᵉ =
      centerᵉ uniqueness-extension-universal-property-family-of-fibersᵉ

  fiberwise-map-universal-property-family-of-fibersᵉ :
    (bᵉ : Bᵉ) → Fᵉ bᵉ → Gᵉ bᵉ
  fiberwise-map-universal-property-family-of-fibersᵉ =
    family-of-elements-extension-double-lift-family-of-elementsᵉ
      extension-universal-property-family-of-fibersᵉ

  is-extension-fiberwise-map-universal-property-family-of-fibersᵉ :
    is-extension-double-lift-family-of-elementsᵉ
      ( λ yᵉ _ → Gᵉ yᵉ)
      ( δᵉ)
      ( γᵉ)
      ( fiberwise-map-universal-property-family-of-fibersᵉ)
  is-extension-fiberwise-map-universal-property-family-of-fibersᵉ =
    is-extension-extension-double-lift-family-of-elementsᵉ
      extension-universal-property-family-of-fibersᵉ
```

### The family of fibers of a map is uniquely unique

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Fᵉ : Bᵉ → UUᵉ l3ᵉ)
  (δᵉ : (aᵉ : Aᵉ) → Fᵉ (fᵉ aᵉ)) (uᵉ : universal-property-family-of-fibersᵉ Fᵉ δᵉ)
  (Gᵉ : Bᵉ → UUᵉ l4ᵉ) (γᵉ : (aᵉ : Aᵉ) → Gᵉ (fᵉ aᵉ))
  (vᵉ : universal-property-family-of-fibersᵉ Gᵉ γᵉ)
  where

  is-retraction-extension-universal-property-family-of-fibersᵉ :
    comp-extension-double-lift-family-of-elementsᵉ
      ( extension-universal-property-family-of-fibersᵉ vᵉ Fᵉ δᵉ)
      ( extension-universal-property-family-of-fibersᵉ uᵉ Gᵉ γᵉ) ＝ᵉ
    id-extension-double-lift-family-of-elementsᵉ δᵉ
  is-retraction-extension-universal-property-family-of-fibersᵉ =
    eq-is-contrᵉ
      ( uniqueness-extension-universal-property-family-of-fibersᵉ uᵉ Fᵉ δᵉ)

  is-section-extension-universal-property-family-of-fibersᵉ :
    comp-extension-double-lift-family-of-elementsᵉ
      ( extension-universal-property-family-of-fibersᵉ uᵉ Gᵉ γᵉ)
      ( extension-universal-property-family-of-fibersᵉ vᵉ Fᵉ δᵉ) ＝ᵉ
    id-extension-double-lift-family-of-elementsᵉ γᵉ
  is-section-extension-universal-property-family-of-fibersᵉ =
    eq-is-contrᵉ
      ( uniqueness-extension-universal-property-family-of-fibersᵉ vᵉ Gᵉ γᵉ)

  is-retraction-fiberwise-map-universal-property-family-of-fibersᵉ :
    (bᵉ : Bᵉ) →
    is-retractionᵉ
      ( fiberwise-map-universal-property-family-of-fibersᵉ uᵉ Gᵉ γᵉ bᵉ)
      ( fiberwise-map-universal-property-family-of-fibersᵉ vᵉ Fᵉ δᵉ bᵉ)
  is-retraction-fiberwise-map-universal-property-family-of-fibersᵉ bᵉ =
    htpy-eqᵉ
      ( htpy-eqᵉ
        ( apᵉ
          ( pr1ᵉ)
          ( is-retraction-extension-universal-property-family-of-fibersᵉ))
        ( bᵉ))

  is-section-fiberwise-map-universal-property-family-of-fibersᵉ :
    (bᵉ : Bᵉ) →
    is-sectionᵉ
      ( fiberwise-map-universal-property-family-of-fibersᵉ uᵉ Gᵉ γᵉ bᵉ)
      ( fiberwise-map-universal-property-family-of-fibersᵉ vᵉ Fᵉ δᵉ bᵉ)
  is-section-fiberwise-map-universal-property-family-of-fibersᵉ bᵉ =
    htpy-eqᵉ
      ( htpy-eqᵉ
        ( apᵉ
          ( pr1ᵉ)
          ( is-section-extension-universal-property-family-of-fibersᵉ))
        ( bᵉ))

  is-fiberwise-equiv-fiberwise-map-universal-property-family-of-fibersᵉ :
    is-fiberwise-equivᵉ (fiberwise-map-universal-property-family-of-fibersᵉ uᵉ Gᵉ γᵉ)
  is-fiberwise-equiv-fiberwise-map-universal-property-family-of-fibersᵉ bᵉ =
    is-equiv-is-invertibleᵉ
      ( family-of-elements-extension-double-lift-family-of-elementsᵉ
        ( extension-universal-property-family-of-fibersᵉ vᵉ Fᵉ δᵉ)
        ( bᵉ))
      ( is-section-fiberwise-map-universal-property-family-of-fibersᵉ bᵉ)
      ( is-retraction-fiberwise-map-universal-property-family-of-fibersᵉ bᵉ)

  uniquely-unique-family-of-fibersᵉ :
    is-contrᵉ
      ( Σᵉ ( fiberwise-equivᵉ Fᵉ Gᵉ)
          ( λ hᵉ →
            ev-double-lift-family-of-elementsᵉ δᵉ (map-fiberwise-equivᵉ hᵉ) ~ᵉ γᵉ))
  uniquely-unique-family-of-fibersᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( uniqueness-extension-universal-property-family-of-fibersᵉ uᵉ Gᵉ γᵉ)
      ( is-property-is-fiberwise-equivᵉ)
      ( fiberwise-map-universal-property-family-of-fibersᵉ uᵉ Gᵉ γᵉ)
      ( is-extension-fiberwise-map-universal-property-family-of-fibersᵉ uᵉ Gᵉ γᵉ)
      ( is-fiberwise-equiv-fiberwise-map-universal-property-family-of-fibersᵉ)

  extension-by-fiberwise-equiv-universal-property-family-of-fibersᵉ :
    Σᵉ ( fiberwise-equivᵉ Fᵉ Gᵉ)
      ( λ hᵉ → ev-double-lift-family-of-elementsᵉ δᵉ (map-fiberwise-equivᵉ hᵉ) ~ᵉ γᵉ)
  extension-by-fiberwise-equiv-universal-property-family-of-fibersᵉ =
    centerᵉ uniquely-unique-family-of-fibersᵉ

  fiberwise-equiv-universal-property-of-fibersᵉ :
    fiberwise-equivᵉ Fᵉ Gᵉ
  fiberwise-equiv-universal-property-of-fibersᵉ =
    pr1ᵉ extension-by-fiberwise-equiv-universal-property-family-of-fibersᵉ

  is-extension-fiberwise-equiv-universal-property-of-fibersᵉ :
    is-extension-double-lift-family-of-elementsᵉ
      ( λ yᵉ _ → Gᵉ yᵉ)
      ( δᵉ)
      ( γᵉ)
      ( map-fiberwise-equivᵉ
        ( fiberwise-equiv-universal-property-of-fibersᵉ))
  is-extension-fiberwise-equiv-universal-property-of-fibersᵉ =
    pr2ᵉ extension-by-fiberwise-equiv-universal-property-family-of-fibersᵉ
```

### A type family `C` over `B` satisfies the universal property of the family of fibers of a map `f : A → B` if and only if the constant map `C b → (fiber f b → C b)` is an equivalence for every `b : B`

Inᵉ otherᵉ words,ᵉ theᵉ dependentᵉ typeᵉ `C`ᵉ isᵉ
`f`-[local](orthogonal-factorization-systems.local-types.mdᵉ) ifᵉ itsᵉ fiberᵉ overᵉ
`b`ᵉ isᵉ `fiberᵉ fᵉ b`-[null](orthogonal-factorization-systems.null-types.mdᵉ) forᵉ
everyᵉ `bᵉ : B`.ᵉ

Thisᵉ conditionᵉ simplifies,ᵉ forᵉ example,ᵉ theᵉ proofᵉ thatᵉ
[connectedᵉ maps](foundation.connected-maps.mdᵉ) satisfyᵉ aᵉ dependentᵉ universalᵉ
property.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} {Cᵉ : Bᵉ → UUᵉ l3ᵉ}
  where

  is-equiv-precomp-Π-fiber-conditionᵉ :
    ((bᵉ : Bᵉ) → is-equivᵉ (diagonal-exponentialᵉ (Cᵉ bᵉ) (fiberᵉ fᵉ bᵉ))) →
    is-equivᵉ (precomp-Πᵉ fᵉ Cᵉ)
  is-equiv-precomp-Π-fiber-conditionᵉ Hᵉ =
    is-equiv-compᵉ
      ( ev-lift-family-of-elements-fiberᵉ fᵉ (λ bᵉ _ → Cᵉ bᵉ))
      ( map-Πᵉ (λ bᵉ → diagonal-exponentialᵉ (Cᵉ bᵉ) (fiberᵉ fᵉ bᵉ)))
      ( is-equiv-map-Π-is-fiberwise-equivᵉ Hᵉ)
      ( universal-property-family-of-fibers-fiberᵉ fᵉ Cᵉ)
```