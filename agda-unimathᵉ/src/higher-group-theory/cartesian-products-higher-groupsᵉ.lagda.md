# Cartesian products of higher groups

```agda
module higher-group-theory.cartesian-products-higher-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-groupsᵉ

open import structured-types.pointed-cartesian-product-typesᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.loop-spacesᵉ
```

</details>

## Idea

Theᵉ **cartesianᵉ product**ᵉ ofᵉ
[higherᵉ groups](higher-group-theory.higher-groups.mdᵉ) isᵉ alsoᵉ aᵉ higherᵉ group.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Hᵉ : ∞-Groupᵉ l2ᵉ)
  where

  product-∞-Groupᵉ : ∞-Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ product-∞-Groupᵉ =
    product-Pointed-Typeᵉ
      ( classifying-pointed-type-∞-Groupᵉ Gᵉ)
      ( classifying-pointed-type-∞-Groupᵉ Hᵉ)
  pr2ᵉ product-∞-Groupᵉ =
    is-0-connected-productᵉ
      ( classifying-type-∞-Groupᵉ Gᵉ)
      ( classifying-type-∞-Groupᵉ Hᵉ)
      ( is-0-connected-classifying-type-∞-Groupᵉ Gᵉ)
      ( is-0-connected-classifying-type-∞-Groupᵉ Hᵉ)

  classifying-pointed-type-product-∞-Groupᵉ : Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  classifying-pointed-type-product-∞-Groupᵉ = pr1ᵉ product-∞-Groupᵉ

  classifying-type-product-∞-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  classifying-type-product-∞-Groupᵉ =
    type-Pointed-Typeᵉ classifying-pointed-type-product-∞-Groupᵉ

  shape-product-∞-Groupᵉ : classifying-type-product-∞-Groupᵉ
  shape-product-∞-Groupᵉ =
    point-Pointed-Typeᵉ classifying-pointed-type-product-∞-Groupᵉ

  is-0-connected-classifying-type-product-∞-Groupᵉ :
    is-0-connectedᵉ classifying-type-product-∞-Groupᵉ
  is-0-connected-classifying-type-product-∞-Groupᵉ = pr2ᵉ product-∞-Groupᵉ

  mere-eq-classifying-type-product-∞-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-product-∞-Groupᵉ) → mere-eqᵉ Xᵉ Yᵉ
  mere-eq-classifying-type-product-∞-Groupᵉ =
    mere-eq-is-0-connectedᵉ
      is-0-connected-classifying-type-product-∞-Groupᵉ

  elim-prop-classifying-type-product-∞-Groupᵉ :
    {l2ᵉ : Level} (Pᵉ : classifying-type-product-∞-Groupᵉ → Propᵉ l2ᵉ) →
    type-Propᵉ (Pᵉ shape-product-∞-Groupᵉ) →
    ((Xᵉ : classifying-type-product-∞-Groupᵉ) → type-Propᵉ (Pᵉ Xᵉ))
  elim-prop-classifying-type-product-∞-Groupᵉ =
    apply-dependent-universal-property-is-0-connectedᵉ
      shape-product-∞-Groupᵉ
      is-0-connected-classifying-type-product-∞-Groupᵉ

  type-product-∞-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-product-∞-Groupᵉ = type-Ωᵉ classifying-pointed-type-product-∞-Groupᵉ

  unit-product-∞-Groupᵉ : type-product-∞-Groupᵉ
  unit-product-∞-Groupᵉ = refl-Ωᵉ classifying-pointed-type-product-∞-Groupᵉ

  mul-product-∞-Groupᵉ : (xᵉ yᵉ : type-product-∞-Groupᵉ) → type-product-∞-Groupᵉ
  mul-product-∞-Groupᵉ = mul-Ωᵉ classifying-pointed-type-product-∞-Groupᵉ

  assoc-mul-product-∞-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-product-∞-Groupᵉ) →
    Idᵉ
      ( mul-product-∞-Groupᵉ (mul-product-∞-Groupᵉ xᵉ yᵉ) zᵉ)
      ( mul-product-∞-Groupᵉ xᵉ (mul-product-∞-Groupᵉ yᵉ zᵉ))
  assoc-mul-product-∞-Groupᵉ =
    associative-mul-Ωᵉ classifying-pointed-type-product-∞-Groupᵉ

  left-unit-law-mul-product-∞-Groupᵉ :
    (xᵉ : type-product-∞-Groupᵉ) →
    Idᵉ (mul-product-∞-Groupᵉ unit-product-∞-Groupᵉ xᵉ) xᵉ
  left-unit-law-mul-product-∞-Groupᵉ =
    left-unit-law-mul-Ωᵉ classifying-pointed-type-product-∞-Groupᵉ

  right-unit-law-mul-product-∞-Groupᵉ :
    (yᵉ : type-product-∞-Groupᵉ) →
    Idᵉ (mul-product-∞-Groupᵉ yᵉ unit-product-∞-Groupᵉ) yᵉ
  right-unit-law-mul-product-∞-Groupᵉ =
    right-unit-law-mul-Ωᵉ classifying-pointed-type-product-∞-Groupᵉ

  coherence-unit-laws-mul-product-∞-Groupᵉ :
    Idᵉ
      ( left-unit-law-mul-product-∞-Groupᵉ unit-product-∞-Groupᵉ)
      ( right-unit-law-mul-product-∞-Groupᵉ unit-product-∞-Groupᵉ)
  coherence-unit-laws-mul-product-∞-Groupᵉ = reflᵉ

  inv-product-∞-Groupᵉ : type-product-∞-Groupᵉ → type-product-∞-Groupᵉ
  inv-product-∞-Groupᵉ = inv-Ωᵉ classifying-pointed-type-product-∞-Groupᵉ

  left-inverse-law-mul-product-∞-Groupᵉ :
    (xᵉ : type-product-∞-Groupᵉ) →
    Idᵉ (mul-product-∞-Groupᵉ (inv-product-∞-Groupᵉ xᵉ) xᵉ) unit-product-∞-Groupᵉ
  left-inverse-law-mul-product-∞-Groupᵉ =
    left-inverse-law-mul-Ωᵉ classifying-pointed-type-product-∞-Groupᵉ

  right-inverse-law-mul-product-∞-Groupᵉ :
    (xᵉ : type-product-∞-Groupᵉ) →
    Idᵉ (mul-product-∞-Groupᵉ xᵉ (inv-product-∞-Groupᵉ xᵉ)) unit-product-∞-Groupᵉ
  right-inverse-law-mul-product-∞-Groupᵉ =
    right-inverse-law-mul-Ωᵉ classifying-pointed-type-product-∞-Groupᵉ
```

## Properties

### The underlying type of a product of higher groups is the product of their underlying types

```agda
  equiv-type-∞-Group-product-∞-Groupᵉ :
    type-product-∞-Groupᵉ ≃ᵉ
    ( type-∞-Groupᵉ Gᵉ ×ᵉ type-∞-Groupᵉ Hᵉ)
  equiv-type-∞-Group-product-∞-Groupᵉ =
    equiv-pair-eqᵉ shape-product-∞-Groupᵉ shape-product-∞-Groupᵉ
```