# Conjugation of loops

```agda
module synthetic-homotopy-theory.conjugation-loopsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ

open import synthetic-homotopy-theory.loop-spacesᵉ
```

</details>

## Idea

Forᵉ anyᵉ [identification](foundation.identity-types.mdᵉ) `pᵉ : xᵉ ＝ᵉ y`ᵉ in aᵉ typeᵉ
`A`ᵉ thereᵉ isᵉ anᵉ **conjugationᵉ action**ᵉ `Ωᵉ (Aᵉ ,ᵉ xᵉ) →∗ᵉ Ωᵉ (Aᵉ ,ᵉ y)`ᵉ onᵉ
[loopᵉ spaces](synthetic-homotopy-theory.loop-spaces.md),ᵉ whichᵉ isᵉ theᵉ
[pointedᵉ map](structured-types.pointed-maps.mdᵉ) givenᵉ byᵉ `ωᵉ ↦ᵉ p⁻¹ωp`.ᵉ

## Definition

### The standard definition of conjugation on loop spaces

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  map-conjugation-Ωᵉ : {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → type-Ωᵉ (Aᵉ ,ᵉ xᵉ) → type-Ωᵉ (Aᵉ ,ᵉ yᵉ)
  map-conjugation-Ωᵉ pᵉ ωᵉ = invᵉ pᵉ ∙ᵉ (ωᵉ ∙ᵉ pᵉ)

  preserves-point-conjugation-Ωᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → map-conjugation-Ωᵉ pᵉ reflᵉ ＝ᵉ reflᵉ
  preserves-point-conjugation-Ωᵉ pᵉ = left-invᵉ pᵉ

  conjugation-Ωᵉ : {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → Ωᵉ (Aᵉ ,ᵉ xᵉ) →∗ᵉ Ωᵉ (Aᵉ ,ᵉ yᵉ)
  pr1ᵉ (conjugation-Ωᵉ pᵉ) = map-conjugation-Ωᵉ pᵉ
  pr2ᵉ (conjugation-Ωᵉ pᵉ) = preserves-point-conjugation-Ωᵉ pᵉ
```

### A second definition of conjugation on loop spaces

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  conjugation-Ω'ᵉ : {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → Ωᵉ (Aᵉ ,ᵉ xᵉ) →∗ᵉ Ωᵉ (Aᵉ ,ᵉ yᵉ)
  conjugation-Ω'ᵉ reflᵉ = id-pointed-mapᵉ

  map-conjugation-Ω'ᵉ : {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → type-Ωᵉ (Aᵉ ,ᵉ xᵉ) → type-Ωᵉ (Aᵉ ,ᵉ yᵉ)
  map-conjugation-Ω'ᵉ pᵉ = map-pointed-mapᵉ (conjugation-Ω'ᵉ pᵉ)

  preserves-point-conjugation-Ω'ᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → map-conjugation-Ω'ᵉ pᵉ reflᵉ ＝ᵉ reflᵉ
  preserves-point-conjugation-Ω'ᵉ pᵉ =
    preserves-point-pointed-mapᵉ (conjugation-Ω'ᵉ pᵉ)
```

## Properties

### The two definitions of conjugation on loop spaces are pointed homotopic

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  htpy-compute-conjugation-Ωᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → map-conjugation-Ωᵉ pᵉ ~ᵉ map-conjugation-Ω'ᵉ pᵉ
  htpy-compute-conjugation-Ωᵉ reflᵉ ωᵉ = right-unitᵉ

  coherence-point-compute-conjugation-Ωᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( conjugation-Ωᵉ pᵉ)
      ( conjugation-Ω'ᵉ pᵉ)
      ( htpy-compute-conjugation-Ωᵉ pᵉ)
  coherence-point-compute-conjugation-Ωᵉ reflᵉ = reflᵉ

  compute-conjugation-Ωᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → conjugation-Ωᵉ pᵉ ~∗ᵉ conjugation-Ω'ᵉ pᵉ
  pr1ᵉ (compute-conjugation-Ωᵉ pᵉ) = htpy-compute-conjugation-Ωᵉ pᵉ
  pr2ᵉ (compute-conjugation-Ωᵉ pᵉ) = coherence-point-compute-conjugation-Ωᵉ pᵉ
```