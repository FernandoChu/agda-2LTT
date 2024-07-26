# The sphere prespectrum

```agda
module synthetic-homotopy-theory.sphere-prespectrumᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.prespectraᵉ
open import synthetic-homotopy-theory.suspension-prespectraᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ [spheres](synthetic-homotopy-theory.spheres.mdᵉ) `Sⁿ`ᵉ defineᵉ aᵉ
[prespectrum](synthetic-homotopy-theory.prespectra.mdᵉ)

```text
  Sⁿᵉ →∗ᵉ ΩSⁿ⁺¹ᵉ
```

whichᵉ weᵉ callᵉ theᵉ **sphereᵉ prespectrum**.ᵉ

**Note:**ᵉ Evenᵉ thoughᵉ theᵉ sphereᵉ prespectrumᵉ isᵉ definedᵉ degreewiseᵉ byᵉ theᵉ
adjointᵉ to theᵉ identityᵉ map,ᵉ itᵉ isᵉ notᵉ in generalᵉ aᵉ
[spectrum](synthetic-homotopy-theory.spectra.md),ᵉ asᵉ theᵉ transposingᵉ mapᵉ ofᵉ theᵉ
[loop-suspensionᵉ adjunction](synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.mdᵉ)
doesᵉ notᵉ generallyᵉ sendᵉ [equivalences](foundation-core.equivalences.mdᵉ) to
equivalences.ᵉ

## Definition

### The sphere prespectrum

```agda
sphere-Prespectrumᵉ : Prespectrumᵉ lzero
sphere-Prespectrumᵉ = suspension-Prespectrumᵉ (Finᵉ 2 ,ᵉ zero-Finᵉ 1ᵉ)
```