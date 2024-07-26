# Double loop spaces

```agda
module synthetic-homotopy-theory.double-loop-spacesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.path-algebraᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import structured-types.pointed-equivalencesᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.functoriality-loop-spacesᵉ
open import synthetic-homotopy-theory.iterated-loop-spacesᵉ
open import synthetic-homotopy-theory.loop-spacesᵉ
```

</details>

## Idea

Theᵉ **doubleᵉ loopᵉ space**ᵉ ofᵉ aᵉ [pointedᵉ type](structured-types.pointed-types.mdᵉ)
`A`ᵉ isᵉ theᵉ [loopᵉ space](synthetic-homotopy-theory.loop-spaces.mdᵉ) ofᵉ theᵉ loopᵉ
spaceᵉ ofᵉ `A`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level}
  where

  Ω²ᵉ : Pointed-Typeᵉ lᵉ → Pointed-Typeᵉ lᵉ
  Ω²ᵉ Aᵉ = iterated-loop-spaceᵉ 2 Aᵉ

  type-Ω²ᵉ : {Aᵉ : UUᵉ lᵉ} (aᵉ : Aᵉ) → UUᵉ lᵉ
  type-Ω²ᵉ aᵉ = reflᵉ {xᵉ = aᵉ} ＝ᵉ reflᵉ {xᵉ = aᵉ}

  refl-Ω²ᵉ : {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} → type-Ω²ᵉ aᵉ
  refl-Ω²ᵉ = reflᵉ
```

### Vertical and horizontal concatenation operations on double loop

spaces.ᵉ

```agda
vertical-concat-Ω²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} → type-Ω²ᵉ aᵉ → type-Ω²ᵉ aᵉ → type-Ω²ᵉ aᵉ
vertical-concat-Ω²ᵉ αᵉ βᵉ = vertical-concat-Id²ᵉ αᵉ βᵉ

horizontal-concat-Ω²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} → type-Ω²ᵉ aᵉ → type-Ω²ᵉ aᵉ → type-Ω²ᵉ aᵉ
horizontal-concat-Ω²ᵉ αᵉ βᵉ = horizontal-concat-Id²ᵉ αᵉ βᵉ
```

### Unit laws horizontal, vertical concatenation, and whiskering

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  left-unit-law-vertical-concat-Ω²ᵉ :
    {aᵉ : Aᵉ} {αᵉ : type-Ω²ᵉ aᵉ} → vertical-concat-Ω²ᵉ refl-Ω²ᵉ αᵉ ＝ᵉ αᵉ
  left-unit-law-vertical-concat-Ω²ᵉ = left-unitᵉ

  right-unit-law-vertical-concat-Ω²ᵉ :
    {aᵉ : Aᵉ} {αᵉ : type-Ω²ᵉ aᵉ} → vertical-concat-Ω²ᵉ αᵉ refl-Ω²ᵉ ＝ᵉ αᵉ
  right-unit-law-vertical-concat-Ω²ᵉ = right-unitᵉ

  left-unit-law-horizontal-concat-Ω²ᵉ :
    {aᵉ : Aᵉ} {αᵉ : type-Ω²ᵉ aᵉ} →
    horizontal-concat-Ω²ᵉ refl-Ω²ᵉ αᵉ ＝ᵉ αᵉ
  left-unit-law-horizontal-concat-Ω²ᵉ {αᵉ = αᵉ} =
    compute-left-refl-horizontal-concat-Id²ᵉ αᵉ ∙ᵉ ap-idᵉ αᵉ

  naturality-right-unitᵉ :
    {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ qᵉ) →
    coherence-square-identificationsᵉ
      ( right-unitᵉ)
      ( right-whisker-concatᵉ αᵉ reflᵉ)
      ( αᵉ)
      ( right-unitᵉ)
  naturality-right-unitᵉ {pᵉ = reflᵉ} reflᵉ = reflᵉ

  naturality-right-unit-Ω²ᵉ :
    {xᵉ : Aᵉ} (αᵉ : type-Ω²ᵉ xᵉ) → right-whisker-concatᵉ αᵉ reflᵉ ＝ᵉ αᵉ
  naturality-right-unit-Ω²ᵉ αᵉ = invᵉ right-unitᵉ ∙ᵉ naturality-right-unitᵉ αᵉ

  right-unit-law-horizontal-concat-Ω²ᵉ :
    {aᵉ : Aᵉ} {αᵉ : type-Ω²ᵉ aᵉ} → horizontal-concat-Ω²ᵉ αᵉ refl-Ω²ᵉ ＝ᵉ αᵉ
  right-unit-law-horizontal-concat-Ω²ᵉ {αᵉ = αᵉ} =
    compute-right-refl-horizontal-concat-Id²ᵉ αᵉ ∙ᵉ naturality-right-unit-Ω²ᵉ αᵉ

  left-unit-law-left-whisker-Ω²ᵉ :
    {aᵉ : Aᵉ} (αᵉ : type-Ω²ᵉ aᵉ) → left-whisker-concatᵉ (refl-Ωᵉ (Aᵉ ,ᵉ aᵉ)) αᵉ ＝ᵉ αᵉ
  left-unit-law-left-whisker-Ω²ᵉ αᵉ =
    left-unit-law-left-whisker-concatᵉ αᵉ

  right-unit-law-right-whisker-Ω²ᵉ :
    {aᵉ : Aᵉ} (αᵉ : type-Ω²ᵉ aᵉ) → right-whisker-concatᵉ αᵉ (refl-Ωᵉ (Aᵉ ,ᵉ aᵉ)) ＝ᵉ αᵉ
  right-unit-law-right-whisker-Ω²ᵉ αᵉ =
    invᵉ (right-unit-law-right-whisker-concatᵉ αᵉ ∙ᵉ right-unitᵉ)
```

### The interchange law for double loop spaces

```agda
interchange-Ω²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (αᵉ βᵉ γᵉ δᵉ : type-Ω²ᵉ aᵉ) →
  Idᵉ
    ( horizontal-concat-Ω²ᵉ (vertical-concat-Ω²ᵉ αᵉ βᵉ) (vertical-concat-Ω²ᵉ γᵉ δᵉ))
    ( vertical-concat-Ω²ᵉ (horizontal-concat-Ω²ᵉ αᵉ γᵉ) (horizontal-concat-Ω²ᵉ βᵉ δᵉ))
interchange-Ω²ᵉ = interchange-Id²ᵉ
```

## Properties

### The loop space of a pointed type is equivalent to a double loop space

```agda
module _
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ) {xᵉ : type-Pointed-Typeᵉ Aᵉ}
  (pᵉ : point-Pointed-Typeᵉ Aᵉ ＝ᵉ xᵉ)
  where

  pointed-equiv-2-loop-pointed-identityᵉ :
    Ωᵉ (point-Pointed-Typeᵉ Aᵉ ＝ᵉ xᵉ ,ᵉ pᵉ) ≃∗ᵉ Ω²ᵉ Aᵉ
  pointed-equiv-2-loop-pointed-identityᵉ =
    pointed-equiv-Ω-pointed-equivᵉ (pointed-equiv-loop-pointed-identityᵉ Aᵉ pᵉ)
```