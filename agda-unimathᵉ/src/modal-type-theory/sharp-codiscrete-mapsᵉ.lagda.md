# Sharp codiscrete maps

```agda
{-# OPTIONSᵉ --cohesionᵉ --flat-splitᵉ #-}

module modal-type-theory.sharp-codiscrete-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.fibers-of-mapsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import modal-type-theory.sharp-codiscrete-typesᵉ
```

</details>

## Idea

Aᵉ mapᵉ isᵉ saidᵉ to beᵉ **(sharpᵉ) codiscrete**ᵉ ifᵉ itsᵉ
[fibers](foundation-core.fibers-of-maps.mdᵉ) areᵉ
[(sharpᵉ) codiscrete](modal-type-theory.sharp-codiscrete-types.md).ᵉ

## Definition

```agda
is-sharp-codiscrete-mapᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-sharp-codiscrete-mapᵉ fᵉ = is-sharp-codiscrete-familyᵉ (fiberᵉ fᵉ)
```

## Properties

### Being codiscrete is a property

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-sharp-codiscrete-map-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-sharp-codiscrete-map-Propᵉ = is-sharp-codiscrete-family-Propᵉ (fiberᵉ fᵉ)

  is-prop-is-sharp-codiscrete-mapᵉ : is-propᵉ (is-sharp-codiscrete-mapᵉ fᵉ)
  is-prop-is-sharp-codiscrete-mapᵉ =
    is-prop-type-Propᵉ is-sharp-codiscrete-map-Propᵉ
```