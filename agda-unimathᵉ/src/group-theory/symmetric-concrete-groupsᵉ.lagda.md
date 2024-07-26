# Symmetric concrete groups

```agda
module group-theory.symmetric-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.universe-levelsᵉ

open import group-theory.automorphism-groupsᵉ
open import group-theory.concrete-groupsᵉ
```

</details>

## Idea

Theᵉ **symmetricᵉ concreteᵉ group**ᵉ ofᵉ aᵉ [set](foundation-core.sets.mdᵉ) `X`ᵉ isᵉ theᵉ
[connectedᵉ component](foundation.connected-components-universes.mdᵉ) ofᵉ theᵉ
universeᵉ ofᵉ setsᵉ atᵉ `X`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Aᵉ : Setᵉ lᵉ)
  where

  classifying-type-symmetric-Concrete-Groupᵉ : UUᵉ (lsuc lᵉ)
  classifying-type-symmetric-Concrete-Groupᵉ =
    classifying-type-Automorphism-Groupᵉ (Set-1-Typeᵉ lᵉ) Aᵉ

  shape-symmetric-Concrete-Groupᵉ : classifying-type-symmetric-Concrete-Groupᵉ
  shape-symmetric-Concrete-Groupᵉ = shape-Automorphism-Groupᵉ (Set-1-Typeᵉ lᵉ) Aᵉ

  symmetric-Concrete-Groupᵉ : Concrete-Groupᵉ (lsuc lᵉ)
  symmetric-Concrete-Groupᵉ = Automorphism-Groupᵉ (Set-1-Typeᵉ lᵉ) Aᵉ
```

## Properties

### Characterizing equality of the classifying type of the symmetric concrete groups

```agda
module _
  {lᵉ : Level} (Aᵉ : Setᵉ lᵉ)
  where

  equiv-classifying-type-symmetric-Concrete-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-symmetric-Concrete-Groupᵉ Aᵉ) → UUᵉ lᵉ
  equiv-classifying-type-symmetric-Concrete-Groupᵉ Xᵉ Yᵉ =
    equiv-Setᵉ (pr1ᵉ Xᵉ) (pr1ᵉ Yᵉ)

  type-symmetric-Concrete-Groupᵉ : UUᵉ lᵉ
  type-symmetric-Concrete-Groupᵉ =
    equiv-classifying-type-symmetric-Concrete-Groupᵉ
      ( shape-symmetric-Concrete-Groupᵉ Aᵉ)
      ( shape-symmetric-Concrete-Groupᵉ Aᵉ)

  extensionality-classifying-type-symmetric-Concrete-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-symmetric-Concrete-Groupᵉ Aᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-classifying-type-symmetric-Concrete-Groupᵉ Xᵉ Yᵉ
  extensionality-classifying-type-symmetric-Concrete-Groupᵉ Xᵉ =
    extensionality-type-subtypeᵉ
      ( λ Yᵉ → mere-eq-Propᵉ Yᵉ Aᵉ)
      ( pr2ᵉ Xᵉ)
      ( id-equivᵉ)
      ( extensionality-Setᵉ (pr1ᵉ Xᵉ))

  equiv-eq-classifying-type-symmetric-Concrete-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-symmetric-Concrete-Groupᵉ Aᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) → equiv-classifying-type-symmetric-Concrete-Groupᵉ Xᵉ Yᵉ
  equiv-eq-classifying-type-symmetric-Concrete-Groupᵉ Xᵉ Yᵉ =
    map-equivᵉ (extensionality-classifying-type-symmetric-Concrete-Groupᵉ Xᵉ Yᵉ)

  refl-equiv-eq-classifying-type-symmetric-Concrete-Groupᵉ :
    (Xᵉ : classifying-type-symmetric-Concrete-Groupᵉ Aᵉ) →
    equiv-eq-classifying-type-symmetric-Concrete-Groupᵉ Xᵉ Xᵉ reflᵉ ＝ᵉ id-equivᵉ
  refl-equiv-eq-classifying-type-symmetric-Concrete-Groupᵉ Xᵉ = reflᵉ

  preserves-mul-equiv-eq-classifying-type-symmetric-Concrete-Groupᵉ :
    (Xᵉ Yᵉ Zᵉ : classifying-type-symmetric-Concrete-Groupᵉ Aᵉ)
    (qᵉ : Yᵉ ＝ᵉ Zᵉ) (pᵉ : Xᵉ ＝ᵉ Yᵉ) →
    equiv-eq-classifying-type-symmetric-Concrete-Groupᵉ Xᵉ Zᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ
    ( ( equiv-eq-classifying-type-symmetric-Concrete-Groupᵉ Yᵉ Zᵉ qᵉ) ∘eᵉ
      ( equiv-eq-classifying-type-symmetric-Concrete-Groupᵉ Xᵉ Yᵉ pᵉ))
  preserves-mul-equiv-eq-classifying-type-symmetric-Concrete-Groupᵉ
    Xᵉ .Xᵉ Zᵉ qᵉ reflᵉ =
    invᵉ
      ( right-unit-law-equivᵉ
        ( equiv-eq-classifying-type-symmetric-Concrete-Groupᵉ Xᵉ Zᵉ qᵉ))
```

### Equivalent sets have isomorphic symmetric concrete groups

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#737](https://github.com/UniMath/agda-unimath/issues/737ᵉ)