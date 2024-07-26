# Pointed cartesian product types

```agda
module structured-types.pointed-cartesian-product-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Givenᵉ twoᵉ pointedᵉ typesᵉ `aᵉ : A`ᵉ andᵉ `bᵉ : B`,ᵉ theirᵉ cartesianᵉ productᵉ isᵉ againᵉ
canonicallyᵉ pointedᵉ atᵉ `(aᵉ ,ᵉ bᵉ) : Aᵉ ×ᵉ B`.ᵉ Weᵉ callᵉ thisᵉ theᵉ **pointedᵉ cartesianᵉ
product**ᵉ orᵉ **pointedᵉ product**ᵉ ofᵉ theᵉ twoᵉ pointedᵉ types.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  where

  product-Pointed-Typeᵉ :
    (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ) → Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (product-Pointed-Typeᵉ (Aᵉ ,ᵉ aᵉ) (Bᵉ ,ᵉ bᵉ)) = Aᵉ ×ᵉ Bᵉ
  pr2ᵉ (product-Pointed-Typeᵉ (Aᵉ ,ᵉ aᵉ) (Bᵉ ,ᵉ bᵉ)) = aᵉ ,ᵉ bᵉ

  infixr 15 _×∗ᵉ_
  _×∗ᵉ_ = product-Pointed-Typeᵉ
```

## Properties

### The pointed projections from the pointed product `A ×∗ B` onto `A` and `B`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ)
  where

  map-pr1-product-Pointed-Typeᵉ :
    type-Pointed-Typeᵉ (Aᵉ ×∗ᵉ Bᵉ) → type-Pointed-Typeᵉ Aᵉ
  map-pr1-product-Pointed-Typeᵉ = pr1ᵉ

  pr1-product-Pointed-Typeᵉ : (Aᵉ ×∗ᵉ Bᵉ) →∗ᵉ Aᵉ
  pr1ᵉ pr1-product-Pointed-Typeᵉ = map-pr1-product-Pointed-Typeᵉ
  pr2ᵉ pr1-product-Pointed-Typeᵉ = reflᵉ

  map-pr2-product-Pointed-Typeᵉ :
    type-Pointed-Typeᵉ (Aᵉ ×∗ᵉ Bᵉ) → type-Pointed-Typeᵉ Bᵉ
  map-pr2-product-Pointed-Typeᵉ = pr2ᵉ

  pr2-product-Pointed-Typeᵉ : (Aᵉ ×∗ᵉ Bᵉ) →∗ᵉ Bᵉ
  pr1ᵉ pr2-product-Pointed-Typeᵉ = map-pr2-product-Pointed-Typeᵉ
  pr2ᵉ pr2-product-Pointed-Typeᵉ = reflᵉ
```

### The pointed product `A ×∗ B` comes equipped with pointed inclusion of `A` and `B`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ)
  where

  map-inl-product-Pointed-Typeᵉ :
    type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ (Aᵉ ×∗ᵉ Bᵉ)
  pr1ᵉ (map-inl-product-Pointed-Typeᵉ xᵉ) = xᵉ
  pr2ᵉ (map-inl-product-Pointed-Typeᵉ xᵉ) = point-Pointed-Typeᵉ Bᵉ

  inl-product-Pointed-Typeᵉ : Aᵉ →∗ᵉ (Aᵉ ×∗ᵉ Bᵉ)
  pr1ᵉ inl-product-Pointed-Typeᵉ = map-inl-product-Pointed-Typeᵉ
  pr2ᵉ inl-product-Pointed-Typeᵉ = reflᵉ

  map-inr-product-Pointed-Typeᵉ :
    type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ (Aᵉ ×∗ᵉ Bᵉ)
  pr1ᵉ (map-inr-product-Pointed-Typeᵉ yᵉ) = point-Pointed-Typeᵉ Aᵉ
  pr2ᵉ (map-inr-product-Pointed-Typeᵉ yᵉ) = yᵉ

  inr-product-Pointed-Typeᵉ : Bᵉ →∗ᵉ (Aᵉ ×∗ᵉ Bᵉ)
  pr1ᵉ inr-product-Pointed-Typeᵉ = map-inr-product-Pointed-Typeᵉ
  pr2ᵉ inr-product-Pointed-Typeᵉ = reflᵉ
```

### The pointed inclusions into `A ×∗ B` are sections to the pointed projections

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ)
  where

  is-section-map-inl-product-Pointed-Typeᵉ :
    (map-pr1-product-Pointed-Typeᵉ Aᵉ Bᵉ ∘ᵉ map-inl-product-Pointed-Typeᵉ Aᵉ Bᵉ) ~ᵉ idᵉ
  is-section-map-inl-product-Pointed-Typeᵉ = refl-htpyᵉ

  is-section-map-inr-product-Pointed-Typeᵉ :
    (map-pr2-product-Pointed-Typeᵉ Aᵉ Bᵉ ∘ᵉ map-inr-product-Pointed-Typeᵉ Aᵉ Bᵉ) ~ᵉ idᵉ
  is-section-map-inr-product-Pointed-Typeᵉ = refl-htpyᵉ
```

### The pointed gap map for the pointed product

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  where

  map-gap-product-Pointed-Typeᵉ :
    {l3ᵉ : Level} {Sᵉ : Pointed-Typeᵉ l3ᵉ}
    (fᵉ : Sᵉ →∗ᵉ Aᵉ) (gᵉ : Sᵉ →∗ᵉ Bᵉ) →
    type-Pointed-Typeᵉ Sᵉ → type-Pointed-Typeᵉ (Aᵉ ×∗ᵉ Bᵉ)
  pr1ᵉ (map-gap-product-Pointed-Typeᵉ fᵉ gᵉ xᵉ) = map-pointed-mapᵉ fᵉ xᵉ
  pr2ᵉ (map-gap-product-Pointed-Typeᵉ fᵉ gᵉ xᵉ) = map-pointed-mapᵉ gᵉ xᵉ

  gap-product-Pointed-Typeᵉ :
    {l3ᵉ : Level} {Sᵉ : Pointed-Typeᵉ l3ᵉ}
    (fᵉ : Sᵉ →∗ᵉ Aᵉ) (gᵉ : Sᵉ →∗ᵉ Bᵉ) → Sᵉ →∗ᵉ (Aᵉ ×∗ᵉ Bᵉ)
  pr1ᵉ (gap-product-Pointed-Typeᵉ fᵉ gᵉ) =
    map-gap-product-Pointed-Typeᵉ fᵉ gᵉ
  pr2ᵉ (gap-product-Pointed-Typeᵉ fᵉ gᵉ) =
    eq-pairᵉ
      ( preserves-point-pointed-mapᵉ fᵉ)
      ( preserves-point-pointed-mapᵉ gᵉ)
```