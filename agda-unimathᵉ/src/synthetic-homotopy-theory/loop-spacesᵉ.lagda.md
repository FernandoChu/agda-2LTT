# Loop spaces

```agda
module synthetic-homotopy-theory.loop-spacesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.h-spacesᵉ
open import structured-types.magmasᵉ
open import structured-types.pointed-equivalencesᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.wild-quasigroupsᵉ
```

</details>

## Idea

Theᵉ **loopᵉ space**ᵉ ofᵉ aᵉ [pointedᵉ type](structured-types.pointed-types.mdᵉ) `A`ᵉ isᵉ
theᵉ pointedᵉ typeᵉ ofᵉ self-[identifications](foundation-core.identity-types.mdᵉ) ofᵉ
theᵉ baseᵉ pointᵉ ofᵉ `A`.ᵉ Theᵉ loopᵉ spaceᵉ comesᵉ equippedᵉ with aᵉ group-likeᵉ structureᵉ
inducedᵉ byᵉ theᵉ groupoidal-likeᵉ structureᵉ onᵉ identifications.ᵉ

## Table of files directly related to loop spaces

{{#includeᵉ tables/loop-spaces-concepts.mdᵉ}}

## Definitions

### The loop space of a pointed type

```agda
module _
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ)
  where

  type-Ωᵉ : UUᵉ lᵉ
  type-Ωᵉ = Idᵉ (point-Pointed-Typeᵉ Aᵉ) (point-Pointed-Typeᵉ Aᵉ)

  refl-Ωᵉ : type-Ωᵉ
  refl-Ωᵉ = reflᵉ

  Ωᵉ : Pointed-Typeᵉ lᵉ
  Ωᵉ = pairᵉ type-Ωᵉ refl-Ωᵉ
```

### The magma of loops on a pointed space

```agda
module _
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ)
  where

  mul-Ωᵉ : type-Ωᵉ Aᵉ → type-Ωᵉ Aᵉ → type-Ωᵉ Aᵉ
  mul-Ωᵉ xᵉ yᵉ = xᵉ ∙ᵉ yᵉ

  Ω-Magmaᵉ : Magmaᵉ lᵉ
  pr1ᵉ Ω-Magmaᵉ = type-Ωᵉ Aᵉ
  pr2ᵉ Ω-Magmaᵉ = mul-Ωᵉ
```

### The H-space of loops on a pointed space

```agda
module _
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ)
  where

  left-unit-law-mul-Ωᵉ : (xᵉ : type-Ωᵉ Aᵉ) → mul-Ωᵉ Aᵉ (refl-Ωᵉ Aᵉ) xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Ωᵉ xᵉ = left-unitᵉ

  right-unit-law-mul-Ωᵉ : (xᵉ : type-Ωᵉ Aᵉ) → mul-Ωᵉ Aᵉ xᵉ (refl-Ωᵉ Aᵉ) ＝ᵉ xᵉ
  right-unit-law-mul-Ωᵉ xᵉ = right-unitᵉ

  coherence-unit-laws-mul-Ωᵉ :
    left-unit-law-mul-Ωᵉ reflᵉ ＝ᵉ right-unit-law-mul-Ωᵉ reflᵉ
  coherence-unit-laws-mul-Ωᵉ = reflᵉ

  Ω-H-Spaceᵉ : H-Spaceᵉ lᵉ
  pr1ᵉ Ω-H-Spaceᵉ = Ωᵉ Aᵉ
  pr1ᵉ (pr2ᵉ Ω-H-Spaceᵉ) = mul-Ωᵉ Aᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ Ω-H-Spaceᵉ)) = left-unit-law-mul-Ωᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Ω-H-Spaceᵉ))) = right-unit-law-mul-Ωᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Ω-H-Spaceᵉ))) = coherence-unit-laws-mul-Ωᵉ
```

### The wild quasigroup of loops on a pointed space

```agda
module _
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ)
  where

  inv-Ωᵉ : type-Ωᵉ Aᵉ → type-Ωᵉ Aᵉ
  inv-Ωᵉ = invᵉ

  left-inverse-law-mul-Ωᵉ :
    (xᵉ : type-Ωᵉ Aᵉ) → Idᵉ (mul-Ωᵉ Aᵉ (inv-Ωᵉ xᵉ) xᵉ) (refl-Ωᵉ Aᵉ)
  left-inverse-law-mul-Ωᵉ xᵉ = left-invᵉ xᵉ

  right-inverse-law-mul-Ωᵉ :
    (xᵉ : type-Ωᵉ Aᵉ) → Idᵉ (mul-Ωᵉ Aᵉ xᵉ (inv-Ωᵉ xᵉ)) (refl-Ωᵉ Aᵉ)
  right-inverse-law-mul-Ωᵉ xᵉ = right-invᵉ xᵉ

  Ω-Wild-Quasigroupᵉ : Wild-Quasigroupᵉ lᵉ
  pr1ᵉ Ω-Wild-Quasigroupᵉ = Ω-Magmaᵉ Aᵉ
  pr2ᵉ Ω-Wild-Quasigroupᵉ = is-binary-equiv-concatᵉ
```

### Associativity of concatenation on loop spaces

```agda
module _
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ)
  where

  associative-mul-Ωᵉ :
    (xᵉ yᵉ zᵉ : type-Ωᵉ Aᵉ) →
    Idᵉ (mul-Ωᵉ Aᵉ (mul-Ωᵉ Aᵉ xᵉ yᵉ) zᵉ) (mul-Ωᵉ Aᵉ xᵉ (mul-Ωᵉ Aᵉ yᵉ zᵉ))
  associative-mul-Ωᵉ xᵉ yᵉ zᵉ = assocᵉ xᵉ yᵉ zᵉ
```

Weᵉ computeᵉ transportᵉ ofᵉ `type-Ω`.ᵉ

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ : Aᵉ}
  where

  equiv-tr-Ωᵉ : Idᵉ xᵉ yᵉ → Ωᵉ (pairᵉ Aᵉ xᵉ) ≃∗ᵉ Ωᵉ (pairᵉ Aᵉ yᵉ)
  equiv-tr-Ωᵉ reflᵉ = pairᵉ id-equivᵉ reflᵉ

  equiv-tr-type-Ωᵉ : Idᵉ xᵉ yᵉ → type-Ωᵉ (pairᵉ Aᵉ xᵉ) ≃ᵉ type-Ωᵉ (pairᵉ Aᵉ yᵉ)
  equiv-tr-type-Ωᵉ pᵉ =
    equiv-pointed-equivᵉ (equiv-tr-Ωᵉ pᵉ)

  tr-type-Ωᵉ : Idᵉ xᵉ yᵉ → type-Ωᵉ (pairᵉ Aᵉ xᵉ) → type-Ωᵉ (pairᵉ Aᵉ yᵉ)
  tr-type-Ωᵉ pᵉ = map-equivᵉ (equiv-tr-type-Ωᵉ pᵉ)

  is-equiv-tr-type-Ωᵉ : (pᵉ : Idᵉ xᵉ yᵉ) → is-equivᵉ (tr-type-Ωᵉ pᵉ)
  is-equiv-tr-type-Ωᵉ pᵉ = is-equiv-map-equivᵉ (equiv-tr-type-Ωᵉ pᵉ)

  preserves-refl-tr-Ωᵉ : (pᵉ : Idᵉ xᵉ yᵉ) → Idᵉ (tr-type-Ωᵉ pᵉ reflᵉ) reflᵉ
  preserves-refl-tr-Ωᵉ reflᵉ = reflᵉ

  preserves-mul-tr-Ωᵉ :
    (pᵉ : Idᵉ xᵉ yᵉ) (uᵉ vᵉ : type-Ωᵉ (pairᵉ Aᵉ xᵉ)) →
    Idᵉ
      ( tr-type-Ωᵉ pᵉ (mul-Ωᵉ (pairᵉ Aᵉ xᵉ) uᵉ vᵉ))
      ( mul-Ωᵉ (pairᵉ Aᵉ yᵉ) (tr-type-Ωᵉ pᵉ uᵉ) (tr-type-Ωᵉ pᵉ vᵉ))
  preserves-mul-tr-Ωᵉ reflᵉ uᵉ vᵉ = reflᵉ

  preserves-inv-tr-Ωᵉ :
    (pᵉ : Idᵉ xᵉ yᵉ) (uᵉ : type-Ωᵉ (pairᵉ Aᵉ xᵉ)) →
    Idᵉ
      ( tr-type-Ωᵉ pᵉ (inv-Ωᵉ (pairᵉ Aᵉ xᵉ) uᵉ))
      ( inv-Ωᵉ (pairᵉ Aᵉ yᵉ) (tr-type-Ωᵉ pᵉ uᵉ))
  preserves-inv-tr-Ωᵉ reflᵉ uᵉ = reflᵉ

  eq-tr-type-Ωᵉ :
    (pᵉ : Idᵉ xᵉ yᵉ) (qᵉ : type-Ωᵉ (pairᵉ Aᵉ xᵉ)) →
    Idᵉ (tr-type-Ωᵉ pᵉ qᵉ) (invᵉ pᵉ ∙ᵉ (qᵉ ∙ᵉ pᵉ))
  eq-tr-type-Ωᵉ reflᵉ qᵉ = invᵉ right-unitᵉ
```

## Properties

### Every pointed identity type is equivalent to a loop space

```agda
module _
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ) {xᵉ : type-Pointed-Typeᵉ Aᵉ}
  (pᵉ : point-Pointed-Typeᵉ Aᵉ ＝ᵉ xᵉ)
  where

  pointed-equiv-loop-pointed-identityᵉ :
    ( pairᵉ (point-Pointed-Typeᵉ Aᵉ ＝ᵉ xᵉ) pᵉ) ≃∗ᵉ Ωᵉ Aᵉ
  pr1ᵉ pointed-equiv-loop-pointed-identityᵉ =
    equiv-concat'ᵉ (point-Pointed-Typeᵉ Aᵉ) (invᵉ pᵉ)
  pr2ᵉ pointed-equiv-loop-pointed-identityᵉ =
    right-invᵉ pᵉ
```