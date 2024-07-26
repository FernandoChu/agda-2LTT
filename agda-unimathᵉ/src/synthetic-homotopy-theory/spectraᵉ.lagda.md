# Spectra

```agda
module synthetic-homotopy-theory.spectraᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-equivalencesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.loop-spacesᵉ
open import synthetic-homotopy-theory.prespectraᵉ
open import synthetic-homotopy-theory.suspensions-of-pointed-typesᵉ
open import synthetic-homotopy-theory.suspensions-of-typesᵉ
```

</details>

## Idea

Aᵉ **spectrum**ᵉ isᵉ aᵉ [sequence](foundation.sequences.mdᵉ) ofᵉ
[pointedᵉ types](structured-types.pointed-types.mdᵉ) `A`ᵉ equippedᵉ with anᵉ
equivalenceᵉ

```text
  Aₙᵉ ≃∗ᵉ ΩAₙ₊₁ᵉ
```

forᵉ eachᵉ `nᵉ : ℕ`.ᵉ

## Definition

### The predicate on prespectra of being a spectrum

```agda
is-spectrum-Propᵉ : {lᵉ : Level} → Prespectrumᵉ lᵉ → Propᵉ lᵉ
is-spectrum-Propᵉ Aᵉ =
  Π-Propᵉ ℕᵉ
    ( λ nᵉ →
      is-pointed-equiv-Propᵉ (pointed-adjoint-structure-map-Prespectrumᵉ Aᵉ nᵉ))

is-spectrumᵉ : {lᵉ : Level} → Prespectrumᵉ lᵉ → UUᵉ lᵉ
is-spectrumᵉ = type-Propᵉ ∘ᵉ is-spectrum-Propᵉ

is-prop-is-spectrumᵉ : {lᵉ : Level} (Aᵉ : Prespectrumᵉ lᵉ) → is-propᵉ (is-spectrumᵉ Aᵉ)
is-prop-is-spectrumᵉ = is-prop-type-Propᵉ ∘ᵉ is-spectrum-Propᵉ
```

### The type of spectra

```agda
Spectrumᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Spectrumᵉ lᵉ = Σᵉ (Prespectrumᵉ lᵉ) (is-spectrumᵉ)

module _
  {lᵉ : Level} (Aᵉ : Spectrumᵉ lᵉ)
  where

  prespectrum-Spectrumᵉ : Prespectrumᵉ lᵉ
  prespectrum-Spectrumᵉ = pr1ᵉ Aᵉ

  pointed-type-Spectrumᵉ : ℕᵉ → Pointed-Typeᵉ lᵉ
  pointed-type-Spectrumᵉ = pointed-type-Prespectrumᵉ prespectrum-Spectrumᵉ

  type-Spectrumᵉ : ℕᵉ → UUᵉ lᵉ
  type-Spectrumᵉ = type-Prespectrumᵉ prespectrum-Spectrumᵉ

  point-Spectrumᵉ : (nᵉ : ℕᵉ) → type-Spectrumᵉ nᵉ
  point-Spectrumᵉ = point-Prespectrumᵉ prespectrum-Spectrumᵉ

  pointed-adjoint-structure-map-Spectrumᵉ :
    (nᵉ : ℕᵉ) → pointed-type-Spectrumᵉ nᵉ →∗ᵉ Ωᵉ (pointed-type-Spectrumᵉ (succ-ℕᵉ nᵉ))
  pointed-adjoint-structure-map-Spectrumᵉ =
    pointed-adjoint-structure-map-Prespectrumᵉ prespectrum-Spectrumᵉ

  adjoint-structure-map-Spectrumᵉ :
    (nᵉ : ℕᵉ) → type-Spectrumᵉ nᵉ → type-Ωᵉ (pointed-type-Spectrumᵉ (succ-ℕᵉ nᵉ))
  adjoint-structure-map-Spectrumᵉ =
    adjoint-structure-map-Prespectrumᵉ prespectrum-Spectrumᵉ

  preserves-point-adjoint-structure-map-Spectrumᵉ :
    (nᵉ : ℕᵉ) →
    adjoint-structure-map-Prespectrumᵉ (pr1ᵉ Aᵉ) nᵉ (point-Prespectrumᵉ (pr1ᵉ Aᵉ) nᵉ) ＝ᵉ
    refl-Ωᵉ (pointed-type-Prespectrumᵉ (pr1ᵉ Aᵉ) (succ-ℕᵉ nᵉ))
  preserves-point-adjoint-structure-map-Spectrumᵉ =
    preserves-point-adjoint-structure-map-Prespectrumᵉ prespectrum-Spectrumᵉ

  is-equiv-pointed-adjoint-structure-map-Spectrumᵉ :
    (nᵉ : ℕᵉ) → is-pointed-equivᵉ (pointed-adjoint-structure-map-Spectrumᵉ nᵉ)
  is-equiv-pointed-adjoint-structure-map-Spectrumᵉ = pr2ᵉ Aᵉ

  structure-equiv-Spectrumᵉ :
    (nᵉ : ℕᵉ) → type-Spectrumᵉ nᵉ ≃ᵉ type-Ωᵉ (pointed-type-Spectrumᵉ (succ-ℕᵉ nᵉ))
  pr1ᵉ (structure-equiv-Spectrumᵉ nᵉ) = adjoint-structure-map-Spectrumᵉ nᵉ
  pr2ᵉ (structure-equiv-Spectrumᵉ nᵉ) =
    is-equiv-pointed-adjoint-structure-map-Spectrumᵉ nᵉ

  pointed-structure-equiv-Spectrumᵉ :
    (nᵉ : ℕᵉ) → pointed-type-Spectrumᵉ nᵉ ≃∗ᵉ Ωᵉ (pointed-type-Spectrumᵉ (succ-ℕᵉ nᵉ))
  pr1ᵉ (pointed-structure-equiv-Spectrumᵉ nᵉ) = structure-equiv-Spectrumᵉ nᵉ
  pr2ᵉ (pointed-structure-equiv-Spectrumᵉ nᵉ) =
    preserves-point-adjoint-structure-map-Spectrumᵉ nᵉ
```

### The structure maps of a spectrum

```agda
module _
  {lᵉ : Level} (Aᵉ : Spectrumᵉ lᵉ) (nᵉ : ℕᵉ)
  where

  pointed-structure-map-Spectrumᵉ :
    suspension-Pointed-Typeᵉ (pointed-type-Spectrumᵉ Aᵉ nᵉ) →∗ᵉ
    pointed-type-Spectrumᵉ Aᵉ (succ-ℕᵉ nᵉ)
  pointed-structure-map-Spectrumᵉ =
    pointed-structure-map-Prespectrumᵉ (prespectrum-Spectrumᵉ Aᵉ) nᵉ

  structure-map-Spectrumᵉ :
    suspensionᵉ (type-Spectrumᵉ Aᵉ nᵉ) → type-Spectrumᵉ Aᵉ (succ-ℕᵉ nᵉ)
  structure-map-Spectrumᵉ = map-pointed-mapᵉ pointed-structure-map-Spectrumᵉ

  preserves-point-structure-map-Spectrumᵉ :
    structure-map-Spectrumᵉ north-suspensionᵉ ＝ᵉ point-Spectrumᵉ Aᵉ (succ-ℕᵉ nᵉ)
  preserves-point-structure-map-Spectrumᵉ =
    preserves-point-pointed-mapᵉ pointed-structure-map-Spectrumᵉ
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ May99ᵉ}}