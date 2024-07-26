# Suspension prespectra

```agda
module synthetic-homotopy-theory.suspension-prespectraᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.iterated-suspensions-of-pointed-typesᵉ
open import synthetic-homotopy-theory.loop-spacesᵉ
open import synthetic-homotopy-theory.prespectraᵉ
open import synthetic-homotopy-theory.suspensions-of-pointed-typesᵉ
open import synthetic-homotopy-theory.universal-property-suspensions-of-pointed-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ [pointedᵉ type](structured-types.pointed-types.mdᵉ) `A`,ᵉ theᵉ
[sequence](foundation.sequences.mdᵉ) ofᵉ
[iteratedᵉ suspensions](synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.mdᵉ)
ofᵉ `A`ᵉ

```text
  Aᵉ   Σ¹Aᵉ   Σ²Aᵉ   Σ³Aᵉ   ...
```

definesᵉ aᵉ [prespectrum](synthetic-homotopy-theory.prespectra.mdᵉ) `Σ^∞A`ᵉ thatᵉ weᵉ
callᵉ theᵉ **suspensionᵉ prespectrum**ᵉ ofᵉ `A`.ᵉ Itsᵉ structureᵉ mapᵉ isᵉ definedᵉ
degreewiseᵉ byᵉ theᵉ identityᵉ

```text
  Σⁿ⁺¹Aᵉ = Σⁿ⁺¹Aᵉ   ↝ᵉ   ΣⁿAᵉ →∗ᵉ ΩΣⁿ⁺¹Aᵉ
```

**Note:**ᵉ Evenᵉ thoughᵉ theᵉ suspensionᵉ prespectrumᵉ isᵉ definedᵉ degreewiseᵉ byᵉ theᵉ
adjointᵉ to theᵉ identityᵉ map,ᵉ itᵉ isᵉ notᵉ in generalᵉ aᵉ
[spectrum](synthetic-homotopy-theory.spectra.md),ᵉ asᵉ theᵉ transposingᵉ mapᵉ ofᵉ theᵉ
[loop-suspensionᵉ adjunction](synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.mdᵉ)
doesᵉ notᵉ generallyᵉ sendᵉ [equivalences](foundation-core.equivalences.mdᵉ) to
equivalences.ᵉ

## Definition

```agda
pointed-structure-map-suspension-Prespectrumᵉ :
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ) (nᵉ : ℕᵉ) →
  suspension-Pointed-Typeᵉ (iterated-suspension-Pointed-Typeᵉ nᵉ Aᵉ) →∗ᵉ
  iterated-suspension-Pointed-Typeᵉ (succ-ℕᵉ nᵉ) Aᵉ
pointed-structure-map-suspension-Prespectrumᵉ Aᵉ nᵉ = id-pointed-mapᵉ

pointed-adjoint-structure-map-suspension-Prespectrumᵉ :
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ) (nᵉ : ℕᵉ) →
  iterated-suspension-Pointed-Typeᵉ nᵉ Aᵉ →∗ᵉ
  Ωᵉ (iterated-suspension-Pointed-Typeᵉ (succ-ℕᵉ nᵉ) Aᵉ)
pointed-adjoint-structure-map-suspension-Prespectrumᵉ Aᵉ nᵉ =
  transpose-suspension-loop-adjunctionᵉ
    ( iterated-suspension-Pointed-Typeᵉ nᵉ Aᵉ)
    ( iterated-suspension-Pointed-Typeᵉ (succ-ℕᵉ nᵉ) Aᵉ)
    ( pointed-structure-map-suspension-Prespectrumᵉ Aᵉ nᵉ)

suspension-Prespectrumᵉ : {lᵉ : Level} → Pointed-Typeᵉ lᵉ → Prespectrumᵉ lᵉ
pr1ᵉ (suspension-Prespectrumᵉ Aᵉ) nᵉ = iterated-suspension-Pointed-Typeᵉ nᵉ Aᵉ
pr2ᵉ (suspension-Prespectrumᵉ Aᵉ) =
  pointed-adjoint-structure-map-suspension-Prespectrumᵉ Aᵉ
```