# Scalar multiplication of vectors on rings

```agda
module linear-algebra.scalar-multiplication-vectors-on-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.endomorphism-rings-abelian-groupsᵉ
open import group-theory.homomorphisms-abelian-groupsᵉ

open import linear-algebra.vectorsᵉ
open import linear-algebra.vectors-on-ringsᵉ

open import ring-theory.homomorphisms-ringsᵉ
open import ring-theory.modules-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Definition

### Scalar multiplication of vectors on rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  scalar-mul-vec-Ringᵉ : {nᵉ : ℕᵉ} (rᵉ : type-Ringᵉ Rᵉ) → vec-Ringᵉ Rᵉ nᵉ → vec-Ringᵉ Rᵉ nᵉ
  scalar-mul-vec-Ringᵉ rᵉ empty-vecᵉ = empty-vecᵉ
  scalar-mul-vec-Ringᵉ rᵉ (xᵉ ∷ᵉ vᵉ) = mul-Ringᵉ Rᵉ rᵉ xᵉ ∷ᵉ scalar-mul-vec-Ringᵉ rᵉ vᵉ

  associative-scalar-mul-vec-Ringᵉ :
    {nᵉ : ℕᵉ} (rᵉ sᵉ : type-Ringᵉ Rᵉ) (vᵉ : vec-Ringᵉ Rᵉ nᵉ) →
    scalar-mul-vec-Ringᵉ (mul-Ringᵉ Rᵉ rᵉ sᵉ) vᵉ ＝ᵉ
    scalar-mul-vec-Ringᵉ rᵉ (scalar-mul-vec-Ringᵉ sᵉ vᵉ)
  associative-scalar-mul-vec-Ringᵉ rᵉ sᵉ empty-vecᵉ = reflᵉ
  associative-scalar-mul-vec-Ringᵉ rᵉ sᵉ (xᵉ ∷ᵉ vᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( associative-mul-Ringᵉ Rᵉ rᵉ sᵉ xᵉ)
      ( associative-scalar-mul-vec-Ringᵉ rᵉ sᵉ vᵉ)

  unit-law-scalar-mul-vec-Ringᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vec-Ringᵉ Rᵉ nᵉ) → scalar-mul-vec-Ringᵉ (one-Ringᵉ Rᵉ) vᵉ ＝ᵉ vᵉ
  unit-law-scalar-mul-vec-Ringᵉ empty-vecᵉ = reflᵉ
  unit-law-scalar-mul-vec-Ringᵉ (xᵉ ∷ᵉ vᵉ) =
    ap-binaryᵉ _∷ᵉ_ (left-unit-law-mul-Ringᵉ Rᵉ xᵉ) (unit-law-scalar-mul-vec-Ringᵉ vᵉ)

  left-distributive-scalar-mul-add-vec-Ringᵉ :
    {nᵉ : ℕᵉ} (rᵉ : type-Ringᵉ Rᵉ) (v1ᵉ v2ᵉ : vec-Ringᵉ Rᵉ nᵉ) →
    scalar-mul-vec-Ringᵉ rᵉ (add-vec-Ringᵉ Rᵉ v1ᵉ v2ᵉ) ＝ᵉ
    add-vec-Ringᵉ Rᵉ (scalar-mul-vec-Ringᵉ rᵉ v1ᵉ) (scalar-mul-vec-Ringᵉ rᵉ v2ᵉ)
  left-distributive-scalar-mul-add-vec-Ringᵉ rᵉ empty-vecᵉ empty-vecᵉ = reflᵉ
  left-distributive-scalar-mul-add-vec-Ringᵉ rᵉ (xᵉ ∷ᵉ v1ᵉ) (yᵉ ∷ᵉ v2ᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( left-distributive-mul-add-Ringᵉ Rᵉ rᵉ xᵉ yᵉ)
      ( left-distributive-scalar-mul-add-vec-Ringᵉ rᵉ v1ᵉ v2ᵉ)

  right-distributive-scalar-mul-add-vec-Ringᵉ :
    {nᵉ : ℕᵉ} (rᵉ sᵉ : type-Ringᵉ Rᵉ) (vᵉ : vec-Ringᵉ Rᵉ nᵉ) →
    scalar-mul-vec-Ringᵉ (add-Ringᵉ Rᵉ rᵉ sᵉ) vᵉ ＝ᵉ
    add-vec-Ringᵉ Rᵉ (scalar-mul-vec-Ringᵉ rᵉ vᵉ) (scalar-mul-vec-Ringᵉ sᵉ vᵉ)
  right-distributive-scalar-mul-add-vec-Ringᵉ rᵉ sᵉ empty-vecᵉ = reflᵉ
  right-distributive-scalar-mul-add-vec-Ringᵉ rᵉ sᵉ (xᵉ ∷ᵉ vᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( right-distributive-mul-add-Ringᵉ Rᵉ rᵉ sᵉ xᵉ)
      ( right-distributive-scalar-mul-add-vec-Ringᵉ rᵉ sᵉ vᵉ)
```

## Properties

### Scalar multiplication defines an `Ab`-endomorphism of `vec-Ring`s, and this mapping is a ring homomorphism `R → End(vec R n)`

```agda
  scalar-mul-vec-Ring-endomorphismᵉ :
    (nᵉ : ℕᵉ) (rᵉ : type-Ringᵉ Rᵉ) → hom-Abᵉ (vec-Ring-Abᵉ Rᵉ nᵉ) (vec-Ring-Abᵉ Rᵉ nᵉ)
  pr1ᵉ (scalar-mul-vec-Ring-endomorphismᵉ nᵉ rᵉ) = scalar-mul-vec-Ringᵉ rᵉ
  pr2ᵉ (scalar-mul-vec-Ring-endomorphismᵉ nᵉ rᵉ) {xᵉ} {yᵉ} =
    left-distributive-scalar-mul-add-vec-Ringᵉ rᵉ xᵉ yᵉ

  scalar-mul-hom-Ringᵉ :
    (nᵉ : ℕᵉ) → hom-Ringᵉ Rᵉ (endomorphism-ring-Abᵉ (vec-Ring-Abᵉ Rᵉ nᵉ))
  pr1ᵉ (pr1ᵉ (scalar-mul-hom-Ringᵉ nᵉ)) = scalar-mul-vec-Ring-endomorphismᵉ nᵉ
  pr2ᵉ (pr1ᵉ (scalar-mul-hom-Ringᵉ nᵉ)) {k1ᵉ} {k2ᵉ} =
    eq-htpy-hom-Abᵉ
      ( vec-Ring-Abᵉ Rᵉ nᵉ)
      ( vec-Ring-Abᵉ Rᵉ nᵉ)
      ( right-distributive-scalar-mul-add-vec-Ringᵉ k1ᵉ k2ᵉ)
  pr1ᵉ (pr2ᵉ (scalar-mul-hom-Ringᵉ nᵉ)) {k1ᵉ} {k2ᵉ} =
    eq-htpy-hom-Abᵉ
      ( vec-Ring-Abᵉ Rᵉ nᵉ)
      ( vec-Ring-Abᵉ Rᵉ nᵉ)
      ( associative-scalar-mul-vec-Ringᵉ k1ᵉ k2ᵉ)
  pr2ᵉ (pr2ᵉ (scalar-mul-hom-Ringᵉ nᵉ)) =
    eq-htpy-hom-Abᵉ
      ( vec-Ring-Abᵉ Rᵉ nᵉ)
      ( vec-Ring-Abᵉ Rᵉ nᵉ)
      ( unit-law-scalar-mul-vec-Ringᵉ)

  vec-left-module-Ringᵉ : (nᵉ : ℕᵉ) → left-module-Ringᵉ lᵉ Rᵉ
  vec-left-module-Ringᵉ nᵉ = vec-Ring-Abᵉ Rᵉ nᵉ ,ᵉ scalar-mul-hom-Ringᵉ nᵉ
```