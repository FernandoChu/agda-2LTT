# Conjugation of pointed types

```agda
module structured-types.conjugation-pointed-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.conjugation-loopsᵉ
open import synthetic-homotopy-theory.functoriality-loop-spacesᵉ
open import synthetic-homotopy-theory.loop-spacesᵉ
```

</details>

## Idea

Conjugationᵉ onᵉ aᵉ [pointedᵉ type](structured-types.pointed-types.mdᵉ) `(B,b)`ᵉ isᵉ
definedᵉ asᵉ aᵉ familyᵉ ofᵉ [pointedᵉ maps](structured-types.pointed-maps.mdᵉ)
`conjᵉ uᵉ pᵉ : (B,bᵉ) →∗ᵉ (B,u)`ᵉ indexedᵉ byᵉ `uᵉ : B`ᵉ andᵉ `pᵉ : bᵉ ＝ᵉ u`,ᵉ suchᵉ thatᵉ
`conjᵉ bᵉ ω`ᵉ actsᵉ onᵉ theᵉ [loopᵉ space](synthetic-homotopy-theory.loop-spaces.mdᵉ)
`Ωᵉ (Bᵉ ,ᵉ b)`ᵉ byᵉ conjugation,ᵉ i.e.,ᵉ itᵉ mapsᵉ aᵉ loopᵉ `αᵉ : bᵉ ＝ᵉ b`ᵉ to theᵉ loopᵉ
`ω⁻¹αω`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Bᵉ : Pointed-Typeᵉ lᵉ)
  where

  map-conjugation-Pointed-Typeᵉ :
    {uᵉ : type-Pointed-Typeᵉ Bᵉ} (pᵉ : point-Pointed-Typeᵉ Bᵉ ＝ᵉ uᵉ) →
    type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Bᵉ
  map-conjugation-Pointed-Typeᵉ reflᵉ = idᵉ

  preserves-point-conjugation-Pointed-Typeᵉ :
    {uᵉ : type-Pointed-Typeᵉ Bᵉ} (pᵉ : point-Pointed-Typeᵉ Bᵉ ＝ᵉ uᵉ) →
    map-conjugation-Pointed-Typeᵉ pᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ uᵉ
  preserves-point-conjugation-Pointed-Typeᵉ reflᵉ = reflᵉ

  conjugation-Pointed-Typeᵉ :
    {uᵉ : type-Pointed-Typeᵉ Bᵉ} (pᵉ : point-Pointed-Typeᵉ Bᵉ ＝ᵉ uᵉ) →
    Bᵉ →∗ᵉ (type-Pointed-Typeᵉ Bᵉ ,ᵉ uᵉ)
  pr1ᵉ (conjugation-Pointed-Typeᵉ pᵉ) = map-conjugation-Pointed-Typeᵉ pᵉ
  pr2ᵉ (conjugation-Pointed-Typeᵉ pᵉ) = preserves-point-conjugation-Pointed-Typeᵉ pᵉ
```

## Properties

### The conjugation map on a pointed type acts on loop spaces by conjugation

```agda
module _
  {lᵉ : Level} {Bᵉ : Pointed-Typeᵉ lᵉ}
  where

  action-on-loops-conjugation-Pointed-Typeᵉ :
    {uᵉ : type-Pointed-Typeᵉ Bᵉ} (pᵉ : point-Pointed-Typeᵉ Bᵉ ＝ᵉ uᵉ) →
    Ωᵉ Bᵉ →∗ᵉ Ωᵉ (type-Pointed-Typeᵉ Bᵉ ,ᵉ uᵉ)
  action-on-loops-conjugation-Pointed-Typeᵉ pᵉ =
    pointed-map-Ωᵉ (conjugation-Pointed-Typeᵉ Bᵉ pᵉ)

  map-action-on-loops-conjugation-Pointed-Typeᵉ :
    {uᵉ : type-Pointed-Typeᵉ Bᵉ} (pᵉ : point-Pointed-Typeᵉ Bᵉ ＝ᵉ uᵉ) →
    type-Ωᵉ Bᵉ → type-Ωᵉ (type-Pointed-Typeᵉ Bᵉ ,ᵉ uᵉ)
  map-action-on-loops-conjugation-Pointed-Typeᵉ pᵉ =
    map-pointed-mapᵉ
      ( action-on-loops-conjugation-Pointed-Typeᵉ pᵉ)

  preserves-point-action-on-loops-conjugation-Pointed-Typeᵉ :
    {uᵉ : type-Pointed-Typeᵉ Bᵉ} (pᵉ : point-Pointed-Typeᵉ Bᵉ ＝ᵉ uᵉ) →
    map-action-on-loops-conjugation-Pointed-Typeᵉ pᵉ reflᵉ ＝ᵉ reflᵉ
  preserves-point-action-on-loops-conjugation-Pointed-Typeᵉ pᵉ =
    preserves-point-pointed-mapᵉ
      ( action-on-loops-conjugation-Pointed-Typeᵉ pᵉ)

  compute-action-on-loops-conjugation-Pointed-Type'ᵉ :
    {uᵉ : type-Pointed-Typeᵉ Bᵉ} (pᵉ : point-Pointed-Typeᵉ Bᵉ ＝ᵉ uᵉ) →
    conjugation-Ω'ᵉ pᵉ ~∗ᵉ action-on-loops-conjugation-Pointed-Typeᵉ pᵉ
  pr1ᵉ (compute-action-on-loops-conjugation-Pointed-Type'ᵉ reflᵉ) ωᵉ = invᵉ (ap-idᵉ ωᵉ)
  pr2ᵉ (compute-action-on-loops-conjugation-Pointed-Type'ᵉ reflᵉ) = reflᵉ

  compute-action-on-loops-conjugation-Pointed-Typeᵉ :
    {uᵉ : type-Pointed-Typeᵉ Bᵉ} (pᵉ : point-Pointed-Typeᵉ Bᵉ ＝ᵉ uᵉ) →
    conjugation-Ωᵉ pᵉ ~∗ᵉ action-on-loops-conjugation-Pointed-Typeᵉ pᵉ
  compute-action-on-loops-conjugation-Pointed-Typeᵉ pᵉ =
    concat-pointed-htpyᵉ
      ( compute-conjugation-Ωᵉ pᵉ)
      ( compute-action-on-loops-conjugation-Pointed-Type'ᵉ pᵉ)

  htpy-compute-action-on-loops-conjugation-Pointed-Typeᵉ :
    {uᵉ : type-Pointed-Typeᵉ Bᵉ} (pᵉ : point-Pointed-Typeᵉ Bᵉ ＝ᵉ uᵉ) →
    map-conjugation-Ωᵉ pᵉ ~ᵉ map-action-on-loops-conjugation-Pointed-Typeᵉ pᵉ
  htpy-compute-action-on-loops-conjugation-Pointed-Typeᵉ pᵉ =
    pr1ᵉ (compute-action-on-loops-conjugation-Pointed-Typeᵉ pᵉ)
```