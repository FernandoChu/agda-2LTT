# Invertible elements in rings

```agda
module ring-theory.invertible-elements-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.invertible-elements-monoidsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Idea

**Invertibleᵉ elements**ᵉ in aᵉ [ring](ring-theory.rings.mdᵉ) areᵉ elementsᵉ thatᵉ haveᵉ
aᵉ two-sidedᵉ multiplicativeᵉ inverse.ᵉ Suchᵉ elementsᵉ areᵉ alsoᵉ calledᵉ theᵉ
**(multiplicativeᵉ) units**ᵉ ofᵉ theᵉ ring.ᵉ

Theᵉ [set](foundation.sets.mdᵉ) ofᵉ unitsᵉ ofᵉ anyᵉ ringᵉ formsᵉ aᵉ
[group](group-theory.groups.md),ᵉ calledᵉ theᵉ
[groupᵉ ofᵉ units](ring-theory.groups-of-units-rings.md).ᵉ Theᵉ groupᵉ ofᵉ unitsᵉ ofᵉ aᵉ
ringᵉ isᵉ constructedᵉ in
[`ring-theory.groups-of-units-rings`](ring-theory.groups-of-units-rings.md).ᵉ

## Definitions

### Left invertible elements of rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-left-inverse-element-Ringᵉ : (xᵉ yᵉ : type-Ringᵉ Rᵉ) → UUᵉ lᵉ
  is-left-inverse-element-Ringᵉ =
    is-left-inverse-element-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  is-left-invertible-element-Ringᵉ : type-Ringᵉ Rᵉ → UUᵉ lᵉ
  is-left-invertible-element-Ringᵉ =
    is-left-invertible-element-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) {xᵉ : type-Ringᵉ Rᵉ}
  where

  retraction-is-left-invertible-element-Ringᵉ :
    is-left-invertible-element-Ringᵉ Rᵉ xᵉ → type-Ringᵉ Rᵉ
  retraction-is-left-invertible-element-Ringᵉ =
    retraction-is-left-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-left-inverse-retraction-is-left-invertible-element-Ringᵉ :
    (Hᵉ : is-left-invertible-element-Ringᵉ Rᵉ xᵉ) →
    is-left-inverse-element-Ringᵉ Rᵉ xᵉ
      ( retraction-is-left-invertible-element-Ringᵉ Hᵉ)
  is-left-inverse-retraction-is-left-invertible-element-Ringᵉ =
    is-left-inverse-retraction-is-left-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
```

### Right invertible elements of rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-right-inverse-element-Ringᵉ : (xᵉ yᵉ : type-Ringᵉ Rᵉ) → UUᵉ lᵉ
  is-right-inverse-element-Ringᵉ =
    is-right-inverse-element-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  is-right-invertible-element-Ringᵉ : type-Ringᵉ Rᵉ → UUᵉ lᵉ
  is-right-invertible-element-Ringᵉ =
    is-right-invertible-element-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) {xᵉ : type-Ringᵉ Rᵉ}
  where

  section-is-right-invertible-element-Ringᵉ :
    is-right-invertible-element-Ringᵉ Rᵉ xᵉ → type-Ringᵉ Rᵉ
  section-is-right-invertible-element-Ringᵉ =
    section-is-right-invertible-element-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  is-right-inverse-section-is-right-invertible-element-Ringᵉ :
    (Hᵉ : is-right-invertible-element-Ringᵉ Rᵉ xᵉ) →
    is-right-inverse-element-Ringᵉ Rᵉ xᵉ
      ( section-is-right-invertible-element-Ringᵉ Hᵉ)
  is-right-inverse-section-is-right-invertible-element-Ringᵉ =
    is-right-inverse-section-is-right-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
```

### Invertible elements of rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (xᵉ : type-Ringᵉ Rᵉ)
  where

  is-inverse-element-Ringᵉ : type-Ringᵉ Rᵉ → UUᵉ lᵉ
  is-inverse-element-Ringᵉ =
    is-inverse-element-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ) xᵉ

  is-invertible-element-Ringᵉ : UUᵉ lᵉ
  is-invertible-element-Ringᵉ =
    is-invertible-element-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ) xᵉ

module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) {xᵉ : type-Ringᵉ Rᵉ}
  where

  inv-is-invertible-element-Ringᵉ :
    is-invertible-element-Ringᵉ Rᵉ xᵉ → type-Ringᵉ Rᵉ
  inv-is-invertible-element-Ringᵉ =
    inv-is-invertible-element-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  is-right-inverse-inv-is-invertible-element-Ringᵉ :
    (Hᵉ : is-invertible-element-Ringᵉ Rᵉ xᵉ) →
    is-right-inverse-element-Ringᵉ Rᵉ xᵉ (inv-is-invertible-element-Ringᵉ Hᵉ)
  is-right-inverse-inv-is-invertible-element-Ringᵉ =
    is-right-inverse-inv-is-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-left-inverse-inv-is-invertible-element-Ringᵉ :
    (Hᵉ : is-invertible-element-Ringᵉ Rᵉ xᵉ) →
    is-left-inverse-element-Ringᵉ Rᵉ xᵉ (inv-is-invertible-element-Ringᵉ Hᵉ)
  is-left-inverse-inv-is-invertible-element-Ringᵉ =
    is-left-inverse-inv-is-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
```

## Properties

### Being an invertible element is a property

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-prop-is-invertible-element-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → is-propᵉ (is-invertible-element-Ringᵉ Rᵉ xᵉ)
  is-prop-is-invertible-element-Ringᵉ =
    is-prop-is-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-invertible-element-prop-Ringᵉ : type-Ringᵉ Rᵉ → Propᵉ lᵉ
  is-invertible-element-prop-Ringᵉ =
    is-invertible-element-prop-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
```

### Inverses are left/right inverses

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-left-invertible-is-invertible-element-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) →
    is-invertible-element-Ringᵉ Rᵉ xᵉ → is-left-invertible-element-Ringᵉ Rᵉ xᵉ
  is-left-invertible-is-invertible-element-Ringᵉ =
    is-left-invertible-is-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-right-invertible-is-invertible-element-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) →
    is-invertible-element-Ringᵉ Rᵉ xᵉ → is-right-invertible-element-Ringᵉ Rᵉ xᵉ
  is-right-invertible-is-invertible-element-Ringᵉ =
    is-right-invertible-is-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
```

### The inverse invertible element

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-right-invertible-left-inverse-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) (Hᵉ : is-left-invertible-element-Ringᵉ Rᵉ xᵉ) →
    is-right-invertible-element-Ringᵉ Rᵉ
      ( retraction-is-left-invertible-element-Ringᵉ Rᵉ Hᵉ)
  is-right-invertible-left-inverse-Ringᵉ =
    is-right-invertible-left-inverse-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-left-invertible-right-inverse-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) (Hᵉ : is-right-invertible-element-Ringᵉ Rᵉ xᵉ) →
    is-left-invertible-element-Ringᵉ Rᵉ
      ( section-is-right-invertible-element-Ringᵉ Rᵉ Hᵉ)
  is-left-invertible-right-inverse-Ringᵉ =
    is-left-invertible-right-inverse-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-invertible-element-inverse-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) (Hᵉ : is-invertible-element-Ringᵉ Rᵉ xᵉ) →
    is-invertible-element-Ringᵉ Rᵉ
      ( inv-is-invertible-element-Ringᵉ Rᵉ Hᵉ)
  is-invertible-element-inverse-Ringᵉ =
    is-invertible-element-inverse-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
```

### Any invertible element of a monoid has a contractible type of right inverses

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-contr-is-right-invertible-element-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → is-invertible-element-Ringᵉ Rᵉ xᵉ →
    is-contrᵉ (is-right-invertible-element-Ringᵉ Rᵉ xᵉ)
  is-contr-is-right-invertible-element-Ringᵉ =
    is-contr-is-right-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
```

### Any invertible element of a monoid has a contractible type of left inverses

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-contr-is-left-invertible-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → is-invertible-element-Ringᵉ Rᵉ xᵉ →
    is-contrᵉ (is-left-invertible-element-Ringᵉ Rᵉ xᵉ)
  is-contr-is-left-invertible-Ringᵉ =
    is-contr-is-left-invertible-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
```

### The unit of a monoid is invertible

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-left-invertible-element-one-Ringᵉ :
    is-left-invertible-element-Ringᵉ Rᵉ (one-Ringᵉ Rᵉ)
  is-left-invertible-element-one-Ringᵉ =
    is-left-invertible-element-unit-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-right-invertible-element-one-Ringᵉ :
    is-right-invertible-element-Ringᵉ Rᵉ (one-Ringᵉ Rᵉ)
  is-right-invertible-element-one-Ringᵉ =
    is-right-invertible-element-unit-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-invertible-element-one-Ringᵉ :
    is-invertible-element-Ringᵉ Rᵉ (one-Ringᵉ Rᵉ)
  is-invertible-element-one-Ringᵉ =
    is-invertible-element-unit-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
```

### Invertible elements are closed under multiplication

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-left-invertible-element-mul-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    is-left-invertible-element-Ringᵉ Rᵉ xᵉ →
    is-left-invertible-element-Ringᵉ Rᵉ yᵉ →
    is-left-invertible-element-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)
  is-left-invertible-element-mul-Ringᵉ =
    is-left-invertible-element-mul-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-right-invertible-element-mul-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    is-right-invertible-element-Ringᵉ Rᵉ xᵉ →
    is-right-invertible-element-Ringᵉ Rᵉ yᵉ →
    is-right-invertible-element-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)
  is-right-invertible-element-mul-Ringᵉ =
    is-right-invertible-element-mul-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-invertible-element-mul-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    is-invertible-element-Ringᵉ Rᵉ xᵉ →
    is-invertible-element-Ringᵉ Rᵉ yᵉ →
    is-invertible-element-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)
  is-invertible-element-mul-Ringᵉ =
    is-invertible-element-mul-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
```

### Invertible elements are closed under negatives

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-invertible-element-neg-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) →
    is-invertible-element-Ringᵉ Rᵉ xᵉ →
    is-invertible-element-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ)
  is-invertible-element-neg-Ringᵉ xᵉ =
    map-Σᵉ _
      ( neg-Ringᵉ Rᵉ)
      ( λ yᵉ →
        map-productᵉ
          ( mul-neg-Ringᵉ Rᵉ xᵉ yᵉ ∙ᵉ_)
          ( mul-neg-Ringᵉ Rᵉ yᵉ xᵉ ∙ᵉ_))

  is-invertible-element-neg-Ring'ᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) →
    is-invertible-element-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ) →
    is-invertible-element-Ringᵉ Rᵉ xᵉ
  is-invertible-element-neg-Ring'ᵉ xᵉ Hᵉ =
    trᵉ
      ( is-invertible-element-Ringᵉ Rᵉ)
      ( neg-neg-Ringᵉ Rᵉ xᵉ)
      ( is-invertible-element-neg-Ringᵉ (neg-Ringᵉ Rᵉ xᵉ) Hᵉ)
```

### The inverse of an invertible element is invertible

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-invertible-element-inv-is-invertible-element-Ringᵉ :
    {xᵉ : type-Ringᵉ Rᵉ} (Hᵉ : is-invertible-element-Ringᵉ Rᵉ xᵉ) →
    is-invertible-element-Ringᵉ Rᵉ (inv-is-invertible-element-Ringᵉ Rᵉ Hᵉ)
  is-invertible-element-inv-is-invertible-element-Ringᵉ =
    is-invertible-element-inv-is-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
```

### An element is invertible if and only if multiplying by it is an equivalence

#### An element `x` is invertible if and only if `z ↦ xz` is an equivalence

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) {xᵉ : type-Ringᵉ Rᵉ}
  where

  inv-is-invertible-element-is-equiv-mul-Ringᵉ :
    is-equivᵉ (mul-Ringᵉ Rᵉ xᵉ) → type-Ringᵉ Rᵉ
  inv-is-invertible-element-is-equiv-mul-Ringᵉ =
    inv-is-invertible-element-is-equiv-mul-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Ringᵉ :
    (Hᵉ : is-equivᵉ (mul-Ringᵉ Rᵉ xᵉ)) →
    mul-Ringᵉ Rᵉ xᵉ (inv-is-invertible-element-is-equiv-mul-Ringᵉ Hᵉ) ＝ᵉ
    one-Ringᵉ Rᵉ
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Ringᵉ =
    is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Ringᵉ :
    (Hᵉ : is-equivᵉ (mul-Ringᵉ Rᵉ xᵉ)) →
    mul-Ringᵉ Rᵉ (inv-is-invertible-element-is-equiv-mul-Ringᵉ Hᵉ) xᵉ ＝ᵉ
    one-Ringᵉ Rᵉ
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Ringᵉ =
    is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-invertible-element-is-equiv-mul-Ringᵉ :
    is-equivᵉ (mul-Ringᵉ Rᵉ xᵉ) → is-invertible-element-Ringᵉ Rᵉ xᵉ
  is-invertible-element-is-equiv-mul-Ringᵉ =
    is-invertible-element-is-equiv-mul-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  left-div-is-invertible-element-Ringᵉ :
    is-invertible-element-Ringᵉ Rᵉ xᵉ → type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ
  left-div-is-invertible-element-Ringᵉ =
    left-div-is-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-section-left-div-is-invertible-element-Ringᵉ :
    (Hᵉ : is-invertible-element-Ringᵉ Rᵉ xᵉ) →
    mul-Ringᵉ Rᵉ xᵉ ∘ᵉ left-div-is-invertible-element-Ringᵉ Hᵉ ~ᵉ idᵉ
  is-section-left-div-is-invertible-element-Ringᵉ =
    is-section-left-div-is-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-retraction-left-div-is-invertible-element-Ringᵉ :
    (Hᵉ : is-invertible-element-Ringᵉ Rᵉ xᵉ) →
    left-div-is-invertible-element-Ringᵉ Hᵉ ∘ᵉ mul-Ringᵉ Rᵉ xᵉ ~ᵉ idᵉ
  is-retraction-left-div-is-invertible-element-Ringᵉ =
    is-retraction-left-div-is-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-equiv-mul-is-invertible-element-Ringᵉ :
    is-invertible-element-Ringᵉ Rᵉ xᵉ → is-equivᵉ (mul-Ringᵉ Rᵉ xᵉ)
  is-equiv-mul-is-invertible-element-Ringᵉ =
    is-equiv-mul-is-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
```

#### An element `x` is invertible if and only if `z ↦ zx` is an equivalence

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) {xᵉ : type-Ringᵉ Rᵉ}
  where

  inv-is-invertible-element-is-equiv-mul-Ring'ᵉ :
    is-equivᵉ (mul-Ring'ᵉ Rᵉ xᵉ) → type-Ringᵉ Rᵉ
  inv-is-invertible-element-is-equiv-mul-Ring'ᵉ =
    inv-is-invertible-element-is-equiv-mul-Monoid'ᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Ring'ᵉ :
    (Hᵉ : is-equivᵉ (mul-Ring'ᵉ Rᵉ xᵉ)) →
    mul-Ringᵉ Rᵉ (inv-is-invertible-element-is-equiv-mul-Ring'ᵉ Hᵉ) xᵉ ＝ᵉ
    one-Ringᵉ Rᵉ
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Ring'ᵉ =
    is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid'ᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Ring'ᵉ :
    (Hᵉ : is-equivᵉ (mul-Ring'ᵉ Rᵉ xᵉ)) →
    mul-Ringᵉ Rᵉ xᵉ (inv-is-invertible-element-is-equiv-mul-Ring'ᵉ Hᵉ) ＝ᵉ
    one-Ringᵉ Rᵉ
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Ring'ᵉ =
    is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid'ᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-invertible-element-is-equiv-mul-Ring'ᵉ :
    is-equivᵉ (mul-Ring'ᵉ Rᵉ xᵉ) → is-invertible-element-Ringᵉ Rᵉ xᵉ
  is-invertible-element-is-equiv-mul-Ring'ᵉ =
    is-invertible-element-is-equiv-mul-Monoid'ᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  right-div-is-invertible-element-Ringᵉ :
    is-invertible-element-Ringᵉ Rᵉ xᵉ → type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ
  right-div-is-invertible-element-Ringᵉ =
    right-div-is-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-section-right-div-is-invertible-element-Ringᵉ :
    (Hᵉ : is-invertible-element-Ringᵉ Rᵉ xᵉ) →
    mul-Ring'ᵉ Rᵉ xᵉ ∘ᵉ right-div-is-invertible-element-Ringᵉ Hᵉ ~ᵉ idᵉ
  is-section-right-div-is-invertible-element-Ringᵉ =
    is-section-right-div-is-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-retraction-right-div-is-invertible-element-Ringᵉ :
    (Hᵉ : is-invertible-element-Ringᵉ Rᵉ xᵉ) →
    right-div-is-invertible-element-Ringᵉ Hᵉ ∘ᵉ mul-Ring'ᵉ Rᵉ xᵉ ~ᵉ idᵉ
  is-retraction-right-div-is-invertible-element-Ringᵉ =
    is-retraction-right-div-is-invertible-element-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)

  is-equiv-mul-is-invertible-element-Ring'ᵉ :
    is-invertible-element-Ringᵉ Rᵉ xᵉ → is-equivᵉ (mul-Ring'ᵉ Rᵉ xᵉ)
  is-equiv-mul-is-invertible-element-Ring'ᵉ =
    is-equiv-mul-is-invertible-element-Monoid'ᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
```

## See also

-ᵉ Theᵉ groupᵉ ofᵉ multiplicativeᵉ unitsᵉ ofᵉ aᵉ ringᵉ isᵉ definedᵉ in
  [`ring-theory.groups-of-units-rings`](ring-theory.groups-of-units-rings.md).ᵉ