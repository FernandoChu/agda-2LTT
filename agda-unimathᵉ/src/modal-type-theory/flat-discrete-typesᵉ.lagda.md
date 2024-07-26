# Flat discrete types

```agda
{-# OPTIONSᵉ --cohesionᵉ --flat-splitᵉ #-}

module modal-type-theory.flat-discrete-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import modal-type-theory.flat-modalityᵉ
```

</details>

## Idea

Aᵉ crispᵉ typeᵉ isᵉ saidᵉ to beᵉ **(flatᵉ) discrete**ᵉ ifᵉ itᵉ isᵉ
[flat](modal-type-theory.flat-modality.mdᵉ) modal,ᵉ i.e.ᵉ ifᵉ theᵉ flatᵉ counitᵉ atᵉ
thatᵉ typeᵉ isᵉ anᵉ [equivalence](foundation-core.equivalences.md).ᵉ

## Definition

```agda
is-flat-discreteᵉ : {@♭ᵉ lᵉ : Level} (@♭ᵉ Aᵉ : UUᵉ lᵉ) → UUᵉ lᵉ
is-flat-discreteᵉ {lᵉ} Aᵉ = is-equivᵉ (counit-flatᵉ {lᵉ} {Aᵉ})
```

## Properties

### Being flat is a property

```agda
is-property-is-flat-discreteᵉ :
  {@♭ᵉ lᵉ : Level} (@♭ᵉ Aᵉ : UUᵉ lᵉ) → is-propᵉ (is-flat-discreteᵉ Aᵉ)
is-property-is-flat-discreteᵉ {lᵉ} Aᵉ = is-property-is-equivᵉ (counit-flatᵉ {lᵉ} {Aᵉ})

is-flat-discrete-Propᵉ : {@♭ᵉ lᵉ : Level} (@♭ᵉ Aᵉ : UUᵉ lᵉ) → Propᵉ lᵉ
is-flat-discrete-Propᵉ {lᵉ} Aᵉ = is-equiv-Propᵉ (counit-flatᵉ {lᵉ} {Aᵉ})
```

### The empty type is flat

```agda
map-is-flat-discrete-emptyᵉ : emptyᵉ → ♭ᵉ emptyᵉ
map-is-flat-discrete-emptyᵉ ()

is-section-map-is-flat-discrete-emptyᵉ :
  (counit-flatᵉ ∘ᵉ map-is-flat-discrete-emptyᵉ) ~ᵉ idᵉ
is-section-map-is-flat-discrete-emptyᵉ ()

is-retraction-map-is-flat-discrete-emptyᵉ :
  (map-is-flat-discrete-emptyᵉ ∘ᵉ counit-flatᵉ) ~ᵉ idᵉ
is-retraction-map-is-flat-discrete-emptyᵉ (cons-flatᵉ ())

is-flat-discrete-emptyᵉ : is-flat-discreteᵉ emptyᵉ
is-flat-discrete-emptyᵉ =
  is-equiv-is-invertibleᵉ
    ( map-is-flat-discrete-emptyᵉ)
    ( is-section-map-is-flat-discrete-emptyᵉ)
    ( is-retraction-map-is-flat-discrete-emptyᵉ)
```

### The unit type is flat

```agda
map-is-flat-discrete-unitᵉ : unitᵉ → ♭ᵉ unitᵉ
map-is-flat-discrete-unitᵉ starᵉ = cons-flatᵉ starᵉ

is-section-map-is-flat-discrete-unitᵉ :
  counit-flatᵉ ∘ᵉ map-is-flat-discrete-unitᵉ ~ᵉ idᵉ
is-section-map-is-flat-discrete-unitᵉ _ = reflᵉ

is-retraction-map-is-flat-discrete-unitᵉ :
  map-is-flat-discrete-unitᵉ ∘ᵉ counit-flatᵉ ~ᵉ idᵉ
is-retraction-map-is-flat-discrete-unitᵉ (cons-flatᵉ _) = reflᵉ

is-flat-discrete-unitᵉ : is-flat-discreteᵉ unitᵉ
is-flat-discrete-unitᵉ =
  is-equiv-is-invertibleᵉ
    ( map-is-flat-discrete-unitᵉ)
    ( is-section-map-is-flat-discrete-unitᵉ)
    ( is-retraction-map-is-flat-discrete-unitᵉ)
```

## See also

-ᵉ [Sharpᵉ codiscreteᵉ types](modal-type-theory.sharp-codiscrete-types.mdᵉ) forᵉ theᵉ
  dualᵉ notion.ᵉ