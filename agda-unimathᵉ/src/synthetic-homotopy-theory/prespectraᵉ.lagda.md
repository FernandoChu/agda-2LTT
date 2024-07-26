# Prespectra

```agda
module synthetic-homotopy-theory.prespectraᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.loop-spacesᵉ
open import synthetic-homotopy-theory.suspensions-of-pointed-typesᵉ
open import synthetic-homotopy-theory.suspensions-of-typesᵉ
open import synthetic-homotopy-theory.universal-property-suspensions-of-pointed-typesᵉ
```

</details>

## Idea

Aᵉ **prespectrum**ᵉ isᵉ aᵉ [sequence](foundation.sequences.mdᵉ) ofᵉ
[pointedᵉ types](structured-types.pointed-types.mdᵉ) `Aₙ`ᵉ
[equipped](foundation.structure.mdᵉ) with
[pointedᵉ maps](structured-types.pointed-maps.mdᵉ)

```text
  εᵉ : Aₙᵉ →∗ᵉ ΩAₙ₊₁ᵉ
```

forᵉ eachᵉ `nᵉ : ℕ`,ᵉ calledᵉ theᵉ **adjointᵉ structureᵉ maps**ᵉ ofᵉ theᵉ prespectrum.ᵉ

Byᵉ theᵉ
[loop-suspensionᵉ adjunction](synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.md),ᵉ
specifyingᵉ structureᵉ mapsᵉ `Aₙᵉ →∗ᵉ Ωᵉ Aₙ₊₁`ᵉ isᵉ
[equivalent](foundation-core.equivalences.mdᵉ) to specifyingᵉ theirᵉ adjointᵉ mapsᵉ

```text
  ΣAₙᵉ → Aₙ₊₁.ᵉ
```

## Definition

```agda
Prespectrumᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Prespectrumᵉ lᵉ =
  Σᵉ (ℕᵉ → Pointed-Typeᵉ lᵉ) (λ Aᵉ → (nᵉ : ℕᵉ) → Aᵉ nᵉ →∗ᵉ Ωᵉ (Aᵉ (succ-ℕᵉ nᵉ)))

module _
  {lᵉ : Level} (Aᵉ : Prespectrumᵉ lᵉ) (nᵉ : ℕᵉ)
  where

  pointed-type-Prespectrumᵉ : Pointed-Typeᵉ lᵉ
  pointed-type-Prespectrumᵉ = pr1ᵉ Aᵉ nᵉ

  type-Prespectrumᵉ : UUᵉ lᵉ
  type-Prespectrumᵉ = type-Pointed-Typeᵉ pointed-type-Prespectrumᵉ

  point-Prespectrumᵉ : type-Prespectrumᵉ
  point-Prespectrumᵉ = point-Pointed-Typeᵉ pointed-type-Prespectrumᵉ

module _
  {lᵉ : Level} (Aᵉ : Prespectrumᵉ lᵉ) (nᵉ : ℕᵉ)
  where

  pointed-adjoint-structure-map-Prespectrumᵉ :
    pointed-type-Prespectrumᵉ Aᵉ nᵉ →∗ᵉ Ωᵉ (pointed-type-Prespectrumᵉ Aᵉ (succ-ℕᵉ nᵉ))
  pointed-adjoint-structure-map-Prespectrumᵉ = pr2ᵉ Aᵉ nᵉ

  adjoint-structure-map-Prespectrumᵉ :
    type-Prespectrumᵉ Aᵉ nᵉ → type-Ωᵉ (pointed-type-Prespectrumᵉ Aᵉ (succ-ℕᵉ nᵉ))
  adjoint-structure-map-Prespectrumᵉ =
    map-pointed-mapᵉ pointed-adjoint-structure-map-Prespectrumᵉ

  preserves-point-adjoint-structure-map-Prespectrumᵉ :
    adjoint-structure-map-Prespectrumᵉ (point-Prespectrumᵉ Aᵉ nᵉ) ＝ᵉ
    refl-Ωᵉ (pointed-type-Prespectrumᵉ Aᵉ (succ-ℕᵉ nᵉ))
  preserves-point-adjoint-structure-map-Prespectrumᵉ =
    preserves-point-pointed-mapᵉ pointed-adjoint-structure-map-Prespectrumᵉ
```

### The structure maps of a prespectrum

```agda
module _
  {lᵉ : Level} (Aᵉ : Prespectrumᵉ lᵉ) (nᵉ : ℕᵉ)
  where

  pointed-structure-map-Prespectrumᵉ :
    suspension-Pointed-Typeᵉ (pointed-type-Prespectrumᵉ Aᵉ nᵉ) →∗ᵉ
    pointed-type-Prespectrumᵉ Aᵉ (succ-ℕᵉ nᵉ)
  pointed-structure-map-Prespectrumᵉ =
    inv-transpose-suspension-loop-adjunctionᵉ
      ( pointed-type-Prespectrumᵉ Aᵉ nᵉ)
      ( pointed-type-Prespectrumᵉ Aᵉ (succ-ℕᵉ nᵉ))
      ( pointed-adjoint-structure-map-Prespectrumᵉ Aᵉ nᵉ)

  structure-map-Prespectrumᵉ :
    suspensionᵉ (type-Prespectrumᵉ Aᵉ nᵉ) → type-Prespectrumᵉ Aᵉ (succ-ℕᵉ nᵉ)
  structure-map-Prespectrumᵉ = map-pointed-mapᵉ pointed-structure-map-Prespectrumᵉ

  preserves-point-structure-map-Prespectrumᵉ :
    structure-map-Prespectrumᵉ north-suspensionᵉ ＝ᵉ point-Prespectrumᵉ Aᵉ (succ-ℕᵉ nᵉ)
  preserves-point-structure-map-Prespectrumᵉ =
    preserves-point-pointed-mapᵉ pointed-structure-map-Prespectrumᵉ
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ May99ᵉ}}