# Invertible elements in monoids

```agda
module group-theory.invertible-elements-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.monoidsᵉ
```

</details>

## Idea

Anᵉ elementᵉ `xᵉ : M`ᵉ in aᵉ [monoid](group-theory.monoids.mdᵉ) `M`ᵉ isᵉ saidᵉ to beᵉ
**leftᵉ invertible**ᵉ ifᵉ thereᵉ isᵉ anᵉ elementᵉ `yᵉ : M`ᵉ suchᵉ thatᵉ `yxᵉ ＝ᵉ e`,ᵉ andᵉ itᵉ
isᵉ saidᵉ to beᵉ **rightᵉ invertible**ᵉ ifᵉ thereᵉ isᵉ anᵉ elementᵉ `yᵉ : M`ᵉ suchᵉ thatᵉ
`xyᵉ ＝ᵉ e`.ᵉ Theᵉ elementᵉ `x`ᵉ isᵉ saidᵉ to beᵉ **invertible**ᵉ ifᵉ itᵉ hasᵉ aᵉ **two-sidedᵉ
inverse**,ᵉ i.e.,ᵉ ifᵉ ifᵉ thereᵉ isᵉ anᵉ elementᵉ `yᵉ : M`ᵉ suchᵉ thatᵉ `xyᵉ = e`ᵉ andᵉ
`yxᵉ = e`.ᵉ Leftᵉ inversesᵉ ofᵉ elementsᵉ areᵉ alsoᵉ calledᵉ **retractions**ᵉ andᵉ rightᵉ
inversesᵉ areᵉ alsoᵉ calledᵉ **sections**.ᵉ

## Definitions

### Right invertible elements

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ) (xᵉ : type-Monoidᵉ Mᵉ)
  where

  is-right-inverse-element-Monoidᵉ : type-Monoidᵉ Mᵉ → UUᵉ lᵉ
  is-right-inverse-element-Monoidᵉ yᵉ = mul-Monoidᵉ Mᵉ xᵉ yᵉ ＝ᵉ unit-Monoidᵉ Mᵉ

  is-right-invertible-element-Monoidᵉ : UUᵉ lᵉ
  is-right-invertible-element-Monoidᵉ =
    Σᵉ (type-Monoidᵉ Mᵉ) is-right-inverse-element-Monoidᵉ

module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ) {xᵉ : type-Monoidᵉ Mᵉ}
  where

  section-is-right-invertible-element-Monoidᵉ :
    is-right-invertible-element-Monoidᵉ Mᵉ xᵉ → type-Monoidᵉ Mᵉ
  section-is-right-invertible-element-Monoidᵉ = pr1ᵉ

  is-right-inverse-section-is-right-invertible-element-Monoidᵉ :
    (Hᵉ : is-right-invertible-element-Monoidᵉ Mᵉ xᵉ) →
    is-right-inverse-element-Monoidᵉ Mᵉ xᵉ
      ( section-is-right-invertible-element-Monoidᵉ Hᵉ)
  is-right-inverse-section-is-right-invertible-element-Monoidᵉ = pr2ᵉ
```

### Left invertible elements

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ) (xᵉ : type-Monoidᵉ Mᵉ)
  where

  is-left-inverse-element-Monoidᵉ : type-Monoidᵉ Mᵉ → UUᵉ lᵉ
  is-left-inverse-element-Monoidᵉ yᵉ = mul-Monoidᵉ Mᵉ yᵉ xᵉ ＝ᵉ unit-Monoidᵉ Mᵉ

  is-left-invertible-element-Monoidᵉ : UUᵉ lᵉ
  is-left-invertible-element-Monoidᵉ =
    Σᵉ (type-Monoidᵉ Mᵉ) is-left-inverse-element-Monoidᵉ

module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ) {xᵉ : type-Monoidᵉ Mᵉ}
  where

  retraction-is-left-invertible-element-Monoidᵉ :
    is-left-invertible-element-Monoidᵉ Mᵉ xᵉ → type-Monoidᵉ Mᵉ
  retraction-is-left-invertible-element-Monoidᵉ = pr1ᵉ

  is-left-inverse-retraction-is-left-invertible-element-Monoidᵉ :
    (Hᵉ : is-left-invertible-element-Monoidᵉ Mᵉ xᵉ) →
    is-left-inverse-element-Monoidᵉ Mᵉ xᵉ
      ( retraction-is-left-invertible-element-Monoidᵉ Hᵉ)
  is-left-inverse-retraction-is-left-invertible-element-Monoidᵉ = pr2ᵉ
```

### Invertible elements

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ) (xᵉ : type-Monoidᵉ Mᵉ)
  where

  is-inverse-element-Monoidᵉ : type-Monoidᵉ Mᵉ → UUᵉ lᵉ
  is-inverse-element-Monoidᵉ yᵉ =
    is-right-inverse-element-Monoidᵉ Mᵉ xᵉ yᵉ ×ᵉ
    is-left-inverse-element-Monoidᵉ Mᵉ xᵉ yᵉ

  is-invertible-element-Monoidᵉ : UUᵉ lᵉ
  is-invertible-element-Monoidᵉ =
    Σᵉ (type-Monoidᵉ Mᵉ) is-inverse-element-Monoidᵉ

module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ) {xᵉ : type-Monoidᵉ Mᵉ}
  where

  inv-is-invertible-element-Monoidᵉ :
    is-invertible-element-Monoidᵉ Mᵉ xᵉ → type-Monoidᵉ Mᵉ
  inv-is-invertible-element-Monoidᵉ = pr1ᵉ

  is-right-inverse-inv-is-invertible-element-Monoidᵉ :
    (Hᵉ : is-invertible-element-Monoidᵉ Mᵉ xᵉ) →
    is-right-inverse-element-Monoidᵉ Mᵉ xᵉ (inv-is-invertible-element-Monoidᵉ Hᵉ)
  is-right-inverse-inv-is-invertible-element-Monoidᵉ Hᵉ = pr1ᵉ (pr2ᵉ Hᵉ)

  is-left-inverse-inv-is-invertible-element-Monoidᵉ :
    (Hᵉ : is-invertible-element-Monoidᵉ Mᵉ xᵉ) →
    is-left-inverse-element-Monoidᵉ Mᵉ xᵉ (inv-is-invertible-element-Monoidᵉ Hᵉ)
  is-left-inverse-inv-is-invertible-element-Monoidᵉ Hᵉ = pr2ᵉ (pr2ᵉ Hᵉ)
```

## Properties

### Being an invertible element is a property

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  all-elements-equal-is-invertible-element-Monoidᵉ :
    (xᵉ : type-Monoidᵉ Mᵉ) → all-elements-equalᵉ (is-invertible-element-Monoidᵉ Mᵉ xᵉ)
  all-elements-equal-is-invertible-element-Monoidᵉ xᵉ (yᵉ ,ᵉ pᵉ ,ᵉ qᵉ) (y'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) =
    eq-type-subtypeᵉ
      ( λ zᵉ →
        product-Propᵉ
          ( Id-Propᵉ (set-Monoidᵉ Mᵉ) (mul-Monoidᵉ Mᵉ xᵉ zᵉ) (unit-Monoidᵉ Mᵉ))
          ( Id-Propᵉ (set-Monoidᵉ Mᵉ) (mul-Monoidᵉ Mᵉ zᵉ xᵉ) (unit-Monoidᵉ Mᵉ)))
      ( ( invᵉ (left-unit-law-mul-Monoidᵉ Mᵉ yᵉ)) ∙ᵉ
        ( invᵉ (apᵉ (λ zᵉ → mul-Monoidᵉ Mᵉ zᵉ yᵉ) q'ᵉ)) ∙ᵉ
        ( associative-mul-Monoidᵉ Mᵉ y'ᵉ xᵉ yᵉ) ∙ᵉ
        ( apᵉ (mul-Monoidᵉ Mᵉ y'ᵉ) pᵉ) ∙ᵉ
        ( right-unit-law-mul-Monoidᵉ Mᵉ y'ᵉ))

  is-prop-is-invertible-element-Monoidᵉ :
    (xᵉ : type-Monoidᵉ Mᵉ) → is-propᵉ (is-invertible-element-Monoidᵉ Mᵉ xᵉ)
  is-prop-is-invertible-element-Monoidᵉ xᵉ =
    is-prop-all-elements-equalᵉ
      ( all-elements-equal-is-invertible-element-Monoidᵉ xᵉ)

  is-invertible-element-prop-Monoidᵉ : type-Monoidᵉ Mᵉ → Propᵉ lᵉ
  pr1ᵉ (is-invertible-element-prop-Monoidᵉ xᵉ) =
    is-invertible-element-Monoidᵉ Mᵉ xᵉ
  pr2ᵉ (is-invertible-element-prop-Monoidᵉ xᵉ) =
    is-prop-is-invertible-element-Monoidᵉ xᵉ
```

### Inverses are left/right inverses

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  is-left-invertible-is-invertible-element-Monoidᵉ :
    (xᵉ : type-Monoidᵉ Mᵉ) →
    is-invertible-element-Monoidᵉ Mᵉ xᵉ → is-left-invertible-element-Monoidᵉ Mᵉ xᵉ
  pr1ᵉ (is-left-invertible-is-invertible-element-Monoidᵉ xᵉ is-invertible-xᵉ) =
    pr1ᵉ is-invertible-xᵉ
  pr2ᵉ (is-left-invertible-is-invertible-element-Monoidᵉ xᵉ is-invertible-xᵉ) =
    pr2ᵉ (pr2ᵉ is-invertible-xᵉ)

  is-right-invertible-is-invertible-element-Monoidᵉ :
    (xᵉ : type-Monoidᵉ Mᵉ) →
    is-invertible-element-Monoidᵉ Mᵉ xᵉ → is-right-invertible-element-Monoidᵉ Mᵉ xᵉ
  pr1ᵉ (is-right-invertible-is-invertible-element-Monoidᵉ xᵉ is-invertible-xᵉ) =
    pr1ᵉ is-invertible-xᵉ
  pr2ᵉ (is-right-invertible-is-invertible-element-Monoidᵉ xᵉ is-invertible-xᵉ) =
    pr1ᵉ (pr2ᵉ is-invertible-xᵉ)
```

### The inverse invertible element

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  is-right-invertible-left-inverse-Monoidᵉ :
    (xᵉ : type-Monoidᵉ Mᵉ) (lxᵉ : is-left-invertible-element-Monoidᵉ Mᵉ xᵉ) →
    is-right-invertible-element-Monoidᵉ Mᵉ (pr1ᵉ lxᵉ)
  pr1ᵉ (is-right-invertible-left-inverse-Monoidᵉ xᵉ lxᵉ) = xᵉ
  pr2ᵉ (is-right-invertible-left-inverse-Monoidᵉ xᵉ lxᵉ) = pr2ᵉ lxᵉ

  is-left-invertible-right-inverse-Monoidᵉ :
    (xᵉ : type-Monoidᵉ Mᵉ) (rxᵉ : is-right-invertible-element-Monoidᵉ Mᵉ xᵉ) →
    is-left-invertible-element-Monoidᵉ Mᵉ (pr1ᵉ rxᵉ)
  pr1ᵉ (is-left-invertible-right-inverse-Monoidᵉ xᵉ rxᵉ) = xᵉ
  pr2ᵉ (is-left-invertible-right-inverse-Monoidᵉ xᵉ rxᵉ) = pr2ᵉ rxᵉ

  is-invertible-element-inverse-Monoidᵉ :
    (xᵉ : type-Monoidᵉ Mᵉ) (x'ᵉ : is-invertible-element-Monoidᵉ Mᵉ xᵉ) →
    is-invertible-element-Monoidᵉ Mᵉ (pr1ᵉ x'ᵉ)
  pr1ᵉ (is-invertible-element-inverse-Monoidᵉ xᵉ x'ᵉ) = xᵉ
  pr1ᵉ (pr2ᵉ (is-invertible-element-inverse-Monoidᵉ xᵉ x'ᵉ)) = pr2ᵉ (pr2ᵉ x'ᵉ)
  pr2ᵉ (pr2ᵉ (is-invertible-element-inverse-Monoidᵉ xᵉ x'ᵉ)) = pr1ᵉ (pr2ᵉ x'ᵉ)
```

### Any invertible element of a monoid has a contractible type of right inverses

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  is-contr-is-right-invertible-element-Monoidᵉ :
    (xᵉ : type-Monoidᵉ Mᵉ) → is-invertible-element-Monoidᵉ Mᵉ xᵉ →
    is-contrᵉ (is-right-invertible-element-Monoidᵉ Mᵉ xᵉ)
  pr1ᵉ (pr1ᵉ (is-contr-is-right-invertible-element-Monoidᵉ xᵉ (yᵉ ,ᵉ pᵉ ,ᵉ qᵉ))) = yᵉ
  pr2ᵉ (pr1ᵉ (is-contr-is-right-invertible-element-Monoidᵉ xᵉ (yᵉ ,ᵉ pᵉ ,ᵉ qᵉ))) = pᵉ
  pr2ᵉ (is-contr-is-right-invertible-element-Monoidᵉ xᵉ (yᵉ ,ᵉ pᵉ ,ᵉ qᵉ)) (y'ᵉ ,ᵉ q'ᵉ) =
    eq-type-subtypeᵉ
      ( λ uᵉ → Id-Propᵉ (set-Monoidᵉ Mᵉ) (mul-Monoidᵉ Mᵉ xᵉ uᵉ) (unit-Monoidᵉ Mᵉ))
      ( ( invᵉ (right-unit-law-mul-Monoidᵉ Mᵉ yᵉ)) ∙ᵉ
        ( apᵉ (mul-Monoidᵉ Mᵉ yᵉ) (invᵉ q'ᵉ)) ∙ᵉ
        ( invᵉ (associative-mul-Monoidᵉ Mᵉ yᵉ xᵉ y'ᵉ)) ∙ᵉ
        ( apᵉ (mul-Monoid'ᵉ Mᵉ y'ᵉ) qᵉ) ∙ᵉ
        ( left-unit-law-mul-Monoidᵉ Mᵉ y'ᵉ))
```

### Any invertible element of a monoid has a contractible type of left inverses

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  is-contr-is-left-invertible-Monoidᵉ :
    (xᵉ : type-Monoidᵉ Mᵉ) → is-invertible-element-Monoidᵉ Mᵉ xᵉ →
    is-contrᵉ (is-left-invertible-element-Monoidᵉ Mᵉ xᵉ)
  pr1ᵉ (pr1ᵉ (is-contr-is-left-invertible-Monoidᵉ xᵉ (yᵉ ,ᵉ pᵉ ,ᵉ qᵉ))) = yᵉ
  pr2ᵉ (pr1ᵉ (is-contr-is-left-invertible-Monoidᵉ xᵉ (yᵉ ,ᵉ pᵉ ,ᵉ qᵉ))) = qᵉ
  pr2ᵉ (is-contr-is-left-invertible-Monoidᵉ xᵉ (yᵉ ,ᵉ pᵉ ,ᵉ qᵉ)) (y'ᵉ ,ᵉ p'ᵉ) =
    eq-type-subtypeᵉ
      ( λ uᵉ → Id-Propᵉ (set-Monoidᵉ Mᵉ) (mul-Monoidᵉ Mᵉ uᵉ xᵉ) (unit-Monoidᵉ Mᵉ))
      ( ( invᵉ (left-unit-law-mul-Monoidᵉ Mᵉ yᵉ)) ∙ᵉ
        ( apᵉ (mul-Monoid'ᵉ Mᵉ yᵉ) (invᵉ p'ᵉ)) ∙ᵉ
        ( associative-mul-Monoidᵉ Mᵉ y'ᵉ xᵉ yᵉ) ∙ᵉ
        ( apᵉ (mul-Monoidᵉ Mᵉ y'ᵉ) pᵉ) ∙ᵉ
        ( right-unit-law-mul-Monoidᵉ Mᵉ y'ᵉ))
```

### The unit of a monoid is invertible

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  is-left-invertible-element-unit-Monoidᵉ :
    is-left-invertible-element-Monoidᵉ Mᵉ (unit-Monoidᵉ Mᵉ)
  pr1ᵉ is-left-invertible-element-unit-Monoidᵉ = unit-Monoidᵉ Mᵉ
  pr2ᵉ is-left-invertible-element-unit-Monoidᵉ =
    left-unit-law-mul-Monoidᵉ Mᵉ (unit-Monoidᵉ Mᵉ)

  is-right-invertible-element-unit-Monoidᵉ :
    is-right-invertible-element-Monoidᵉ Mᵉ (unit-Monoidᵉ Mᵉ)
  pr1ᵉ is-right-invertible-element-unit-Monoidᵉ = unit-Monoidᵉ Mᵉ
  pr2ᵉ is-right-invertible-element-unit-Monoidᵉ =
    left-unit-law-mul-Monoidᵉ Mᵉ (unit-Monoidᵉ Mᵉ)

  is-invertible-element-unit-Monoidᵉ :
    is-invertible-element-Monoidᵉ Mᵉ (unit-Monoidᵉ Mᵉ)
  pr1ᵉ is-invertible-element-unit-Monoidᵉ =
    unit-Monoidᵉ Mᵉ
  pr1ᵉ (pr2ᵉ is-invertible-element-unit-Monoidᵉ) =
    left-unit-law-mul-Monoidᵉ Mᵉ (unit-Monoidᵉ Mᵉ)
  pr2ᵉ (pr2ᵉ is-invertible-element-unit-Monoidᵉ) =
    left-unit-law-mul-Monoidᵉ Mᵉ (unit-Monoidᵉ Mᵉ)
```

### Invertible elements are closed under multiplication

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  is-left-invertible-element-mul-Monoidᵉ :
    (xᵉ yᵉ : type-Monoidᵉ Mᵉ) →
    is-left-invertible-element-Monoidᵉ Mᵉ xᵉ →
    is-left-invertible-element-Monoidᵉ Mᵉ yᵉ →
    is-left-invertible-element-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ)
  pr1ᵉ (is-left-invertible-element-mul-Monoidᵉ xᵉ yᵉ (lxᵉ ,ᵉ Hᵉ) (lyᵉ ,ᵉ Iᵉ)) =
    mul-Monoidᵉ Mᵉ lyᵉ lxᵉ
  pr2ᵉ (is-left-invertible-element-mul-Monoidᵉ xᵉ yᵉ (lxᵉ ,ᵉ Hᵉ) (lyᵉ ,ᵉ Iᵉ)) =
    ( associative-mul-Monoidᵉ Mᵉ lyᵉ lxᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ)) ∙ᵉ
    ( apᵉ
      ( mul-Monoidᵉ Mᵉ lyᵉ)
      ( ( invᵉ (associative-mul-Monoidᵉ Mᵉ lxᵉ xᵉ yᵉ)) ∙ᵉ
        ( apᵉ (λ zᵉ → mul-Monoidᵉ Mᵉ zᵉ yᵉ) Hᵉ) ∙ᵉ
        ( left-unit-law-mul-Monoidᵉ Mᵉ yᵉ))) ∙ᵉ
    ( Iᵉ)

  is-right-invertible-element-mul-Monoidᵉ :
    (xᵉ yᵉ : type-Monoidᵉ Mᵉ) →
    is-right-invertible-element-Monoidᵉ Mᵉ xᵉ →
    is-right-invertible-element-Monoidᵉ Mᵉ yᵉ →
    is-right-invertible-element-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ)
  pr1ᵉ (is-right-invertible-element-mul-Monoidᵉ xᵉ yᵉ (rxᵉ ,ᵉ Hᵉ) (ryᵉ ,ᵉ Iᵉ)) =
    mul-Monoidᵉ Mᵉ ryᵉ rxᵉ
  pr2ᵉ (is-right-invertible-element-mul-Monoidᵉ xᵉ yᵉ (rxᵉ ,ᵉ Hᵉ) (ryᵉ ,ᵉ Iᵉ)) =
    ( associative-mul-Monoidᵉ Mᵉ xᵉ yᵉ (mul-Monoidᵉ Mᵉ ryᵉ rxᵉ)) ∙ᵉ
    ( apᵉ
      ( mul-Monoidᵉ Mᵉ xᵉ)
      ( ( invᵉ (associative-mul-Monoidᵉ Mᵉ yᵉ ryᵉ rxᵉ)) ∙ᵉ
        ( apᵉ (λ zᵉ → mul-Monoidᵉ Mᵉ zᵉ rxᵉ) Iᵉ) ∙ᵉ
        ( left-unit-law-mul-Monoidᵉ Mᵉ rxᵉ))) ∙ᵉ
    ( Hᵉ)

  is-invertible-element-mul-Monoidᵉ :
    (xᵉ yᵉ : type-Monoidᵉ Mᵉ) →
    is-invertible-element-Monoidᵉ Mᵉ xᵉ →
    is-invertible-element-Monoidᵉ Mᵉ yᵉ →
    is-invertible-element-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ)
  pr1ᵉ (is-invertible-element-mul-Monoidᵉ xᵉ yᵉ (x'ᵉ ,ᵉ Lxᵉ ,ᵉ Rxᵉ) (y'ᵉ ,ᵉ Lyᵉ ,ᵉ Ryᵉ)) =
    mul-Monoidᵉ Mᵉ y'ᵉ x'ᵉ
  pr1ᵉ (pr2ᵉ (is-invertible-element-mul-Monoidᵉ xᵉ yᵉ Hᵉ Kᵉ)) =
    pr2ᵉ
      ( is-right-invertible-element-mul-Monoidᵉ xᵉ yᵉ
        ( is-right-invertible-is-invertible-element-Monoidᵉ Mᵉ xᵉ Hᵉ)
        ( is-right-invertible-is-invertible-element-Monoidᵉ Mᵉ yᵉ Kᵉ))
  pr2ᵉ (pr2ᵉ (is-invertible-element-mul-Monoidᵉ xᵉ yᵉ Hᵉ Kᵉ)) =
    pr2ᵉ
      ( is-left-invertible-element-mul-Monoidᵉ xᵉ yᵉ
        ( is-left-invertible-is-invertible-element-Monoidᵉ Mᵉ xᵉ Hᵉ)
        ( is-left-invertible-is-invertible-element-Monoidᵉ Mᵉ yᵉ Kᵉ))
```

### The inverse of an invertible element is invertible

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  is-invertible-element-inv-is-invertible-element-Monoidᵉ :
    {xᵉ : type-Monoidᵉ Mᵉ} (Hᵉ : is-invertible-element-Monoidᵉ Mᵉ xᵉ) →
    is-invertible-element-Monoidᵉ Mᵉ (inv-is-invertible-element-Monoidᵉ Mᵉ Hᵉ)
  pr1ᵉ (is-invertible-element-inv-is-invertible-element-Monoidᵉ {xᵉ} Hᵉ) = xᵉ
  pr1ᵉ (pr2ᵉ (is-invertible-element-inv-is-invertible-element-Monoidᵉ Hᵉ)) =
    is-left-inverse-inv-is-invertible-element-Monoidᵉ Mᵉ Hᵉ
  pr2ᵉ (pr2ᵉ (is-invertible-element-inv-is-invertible-element-Monoidᵉ Hᵉ)) =
    is-right-inverse-inv-is-invertible-element-Monoidᵉ Mᵉ Hᵉ
```

### An element is invertible if and only if multiplying by it is an equivalence

**Proof:**ᵉ Supposeᵉ thatᵉ theᵉ mapᵉ `zᵉ ↦ᵉ xz`ᵉ isᵉ anᵉ equivalence.ᵉ Thenᵉ thereᵉ isᵉ aᵉ
uniqueᵉ elementᵉ `y`ᵉ suchᵉ thatᵉ `xyᵉ ＝ᵉ 1`.ᵉ Thusᵉ weᵉ haveᵉ aᵉ rightᵉ inverseᵉ ofᵉ `x`.ᵉ Toᵉ
seeᵉ thatᵉ `y`ᵉ isᵉ alsoᵉ aᵉ leftᵉ inverseᵉ ofᵉ `x`,ᵉ noteᵉ thatᵉ theᵉ mapᵉ `zᵉ ↦ᵉ xz`ᵉ isᵉ
injectiveᵉ byᵉ theᵉ assumptionᵉ thatᵉ itᵉ isᵉ anᵉ equivalence.ᵉ Thereforeᵉ itᵉ sufficesᵉ to
showᵉ thatᵉ `x(yxᵉ) ＝ᵉ x1`.ᵉ Thisᵉ followsᵉ fromᵉ theᵉ followingᵉ calculationᵉ:

```text
  x(yxᵉ) ＝ᵉ (xy)xᵉ ＝ᵉ 1xᵉ ＝ᵉ xᵉ ＝ᵉ x1.ᵉ
```

Thisᵉ completesᵉ theᵉ proofᵉ thatᵉ ifᵉ `zᵉ ↦ᵉ xz`ᵉ isᵉ anᵉ equivalence,ᵉ thenᵉ `x`ᵉ isᵉ
invertible.ᵉ Theᵉ converseᵉ isᵉ straightfoward.ᵉ

Inᵉ theᵉ followingᵉ codeᵉ weᵉ giveᵉ theᵉ aboveᵉ proof,ᵉ asᵉ wellᵉ asᵉ theᵉ analogousᵉ proofᵉ
thatᵉ `x`ᵉ isᵉ invertibleᵉ ifᵉ `zᵉ ↦ᵉ zx`ᵉ isᵉ anᵉ equivalence,ᵉ andᵉ theᵉ converseᵉ ofᵉ bothᵉ
statements.ᵉ

#### An element `x` is invertible if and only if `z ↦ xz` is an equivalence

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ) {xᵉ : type-Monoidᵉ Mᵉ}
  where

  inv-is-invertible-element-is-equiv-mul-Monoidᵉ :
    is-equivᵉ (mul-Monoidᵉ Mᵉ xᵉ) → type-Monoidᵉ Mᵉ
  inv-is-invertible-element-is-equiv-mul-Monoidᵉ Hᵉ =
    map-inv-is-equivᵉ Hᵉ (unit-Monoidᵉ Mᵉ)

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoidᵉ :
    (Hᵉ : is-equivᵉ (mul-Monoidᵉ Mᵉ xᵉ)) →
    mul-Monoidᵉ Mᵉ xᵉ (inv-is-invertible-element-is-equiv-mul-Monoidᵉ Hᵉ) ＝ᵉ
    unit-Monoidᵉ Mᵉ
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoidᵉ Hᵉ =
    is-section-map-inv-is-equivᵉ Hᵉ (unit-Monoidᵉ Mᵉ)

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoidᵉ :
    (Hᵉ : is-equivᵉ (mul-Monoidᵉ Mᵉ xᵉ)) →
    mul-Monoidᵉ Mᵉ (inv-is-invertible-element-is-equiv-mul-Monoidᵉ Hᵉ) xᵉ ＝ᵉ
    unit-Monoidᵉ Mᵉ
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoidᵉ Hᵉ =
    is-injective-is-equivᵉ Hᵉ
      ( ( invᵉ (associative-mul-Monoidᵉ Mᵉ _ _ _)) ∙ᵉ
        ( apᵉ
          ( mul-Monoid'ᵉ Mᵉ xᵉ)
          ( is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoidᵉ Hᵉ)) ∙ᵉ
        ( left-unit-law-mul-Monoidᵉ Mᵉ xᵉ) ∙ᵉ
        ( invᵉ (right-unit-law-mul-Monoidᵉ Mᵉ xᵉ)))

  is-invertible-element-is-equiv-mul-Monoidᵉ :
    is-equivᵉ (mul-Monoidᵉ Mᵉ xᵉ) → is-invertible-element-Monoidᵉ Mᵉ xᵉ
  pr1ᵉ (is-invertible-element-is-equiv-mul-Monoidᵉ Hᵉ) =
    inv-is-invertible-element-is-equiv-mul-Monoidᵉ Hᵉ
  pr1ᵉ (pr2ᵉ (is-invertible-element-is-equiv-mul-Monoidᵉ Hᵉ)) =
    is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoidᵉ Hᵉ
  pr2ᵉ (pr2ᵉ (is-invertible-element-is-equiv-mul-Monoidᵉ Hᵉ)) =
    is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoidᵉ Hᵉ

  left-div-is-invertible-element-Monoidᵉ :
    is-invertible-element-Monoidᵉ Mᵉ xᵉ → type-Monoidᵉ Mᵉ → type-Monoidᵉ Mᵉ
  left-div-is-invertible-element-Monoidᵉ Hᵉ =
    mul-Monoidᵉ Mᵉ (inv-is-invertible-element-Monoidᵉ Mᵉ Hᵉ)

  is-section-left-div-is-invertible-element-Monoidᵉ :
    (Hᵉ : is-invertible-element-Monoidᵉ Mᵉ xᵉ) →
    mul-Monoidᵉ Mᵉ xᵉ ∘ᵉ left-div-is-invertible-element-Monoidᵉ Hᵉ ~ᵉ idᵉ
  is-section-left-div-is-invertible-element-Monoidᵉ Hᵉ yᵉ =
    ( invᵉ (associative-mul-Monoidᵉ Mᵉ _ _ _)) ∙ᵉ
    ( apᵉ
      ( mul-Monoid'ᵉ Mᵉ yᵉ)
      ( is-right-inverse-inv-is-invertible-element-Monoidᵉ Mᵉ Hᵉ)) ∙ᵉ
    ( left-unit-law-mul-Monoidᵉ Mᵉ yᵉ)

  is-retraction-left-div-is-invertible-element-Monoidᵉ :
    (Hᵉ : is-invertible-element-Monoidᵉ Mᵉ xᵉ) →
    left-div-is-invertible-element-Monoidᵉ Hᵉ ∘ᵉ mul-Monoidᵉ Mᵉ xᵉ ~ᵉ idᵉ
  is-retraction-left-div-is-invertible-element-Monoidᵉ Hᵉ yᵉ =
    ( invᵉ (associative-mul-Monoidᵉ Mᵉ _ _ _)) ∙ᵉ
    ( apᵉ
      ( mul-Monoid'ᵉ Mᵉ yᵉ)
      ( is-left-inverse-inv-is-invertible-element-Monoidᵉ Mᵉ Hᵉ)) ∙ᵉ
    ( left-unit-law-mul-Monoidᵉ Mᵉ yᵉ)

  is-equiv-mul-is-invertible-element-Monoidᵉ :
    is-invertible-element-Monoidᵉ Mᵉ xᵉ → is-equivᵉ (mul-Monoidᵉ Mᵉ xᵉ)
  is-equiv-mul-is-invertible-element-Monoidᵉ Hᵉ =
    is-equiv-is-invertibleᵉ
      ( left-div-is-invertible-element-Monoidᵉ Hᵉ)
      ( is-section-left-div-is-invertible-element-Monoidᵉ Hᵉ)
      ( is-retraction-left-div-is-invertible-element-Monoidᵉ Hᵉ)
```

#### An element `x` is invertible if and only if `z ↦ zx` is an equivalence

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ) {xᵉ : type-Monoidᵉ Mᵉ}
  where

  inv-is-invertible-element-is-equiv-mul-Monoid'ᵉ :
    is-equivᵉ (mul-Monoid'ᵉ Mᵉ xᵉ) → type-Monoidᵉ Mᵉ
  inv-is-invertible-element-is-equiv-mul-Monoid'ᵉ Hᵉ =
    map-inv-is-equivᵉ Hᵉ (unit-Monoidᵉ Mᵉ)

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid'ᵉ :
    (Hᵉ : is-equivᵉ (mul-Monoid'ᵉ Mᵉ xᵉ)) →
    mul-Monoidᵉ Mᵉ (inv-is-invertible-element-is-equiv-mul-Monoid'ᵉ Hᵉ) xᵉ ＝ᵉ
    unit-Monoidᵉ Mᵉ
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid'ᵉ Hᵉ =
    is-section-map-inv-is-equivᵉ Hᵉ (unit-Monoidᵉ Mᵉ)

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid'ᵉ :
    (Hᵉ : is-equivᵉ (mul-Monoid'ᵉ Mᵉ xᵉ)) →
    mul-Monoidᵉ Mᵉ xᵉ (inv-is-invertible-element-is-equiv-mul-Monoid'ᵉ Hᵉ) ＝ᵉ
    unit-Monoidᵉ Mᵉ
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid'ᵉ Hᵉ =
    is-injective-is-equivᵉ Hᵉ
      ( ( associative-mul-Monoidᵉ Mᵉ _ _ _) ∙ᵉ
        ( apᵉ
          ( mul-Monoidᵉ Mᵉ xᵉ)
          ( is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid'ᵉ Hᵉ)) ∙ᵉ
        ( right-unit-law-mul-Monoidᵉ Mᵉ xᵉ) ∙ᵉ
        ( invᵉ (left-unit-law-mul-Monoidᵉ Mᵉ xᵉ)))

  is-invertible-element-is-equiv-mul-Monoid'ᵉ :
    is-equivᵉ (mul-Monoid'ᵉ Mᵉ xᵉ) → is-invertible-element-Monoidᵉ Mᵉ xᵉ
  pr1ᵉ (is-invertible-element-is-equiv-mul-Monoid'ᵉ Hᵉ) =
    inv-is-invertible-element-is-equiv-mul-Monoid'ᵉ Hᵉ
  pr1ᵉ (pr2ᵉ (is-invertible-element-is-equiv-mul-Monoid'ᵉ Hᵉ)) =
    is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid'ᵉ Hᵉ
  pr2ᵉ (pr2ᵉ (is-invertible-element-is-equiv-mul-Monoid'ᵉ Hᵉ)) =
    is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid'ᵉ Hᵉ

  right-div-is-invertible-element-Monoidᵉ :
    is-invertible-element-Monoidᵉ Mᵉ xᵉ → type-Monoidᵉ Mᵉ → type-Monoidᵉ Mᵉ
  right-div-is-invertible-element-Monoidᵉ Hᵉ =
    mul-Monoid'ᵉ Mᵉ (inv-is-invertible-element-Monoidᵉ Mᵉ Hᵉ)

  is-section-right-div-is-invertible-element-Monoidᵉ :
    (Hᵉ : is-invertible-element-Monoidᵉ Mᵉ xᵉ) →
    mul-Monoid'ᵉ Mᵉ xᵉ ∘ᵉ right-div-is-invertible-element-Monoidᵉ Hᵉ ~ᵉ idᵉ
  is-section-right-div-is-invertible-element-Monoidᵉ Hᵉ yᵉ =
    ( associative-mul-Monoidᵉ Mᵉ _ _ _) ∙ᵉ
    ( apᵉ
      ( mul-Monoidᵉ Mᵉ yᵉ)
      ( is-left-inverse-inv-is-invertible-element-Monoidᵉ Mᵉ Hᵉ)) ∙ᵉ
    ( right-unit-law-mul-Monoidᵉ Mᵉ yᵉ)

  is-retraction-right-div-is-invertible-element-Monoidᵉ :
    (Hᵉ : is-invertible-element-Monoidᵉ Mᵉ xᵉ) →
    right-div-is-invertible-element-Monoidᵉ Hᵉ ∘ᵉ mul-Monoid'ᵉ Mᵉ xᵉ ~ᵉ idᵉ
  is-retraction-right-div-is-invertible-element-Monoidᵉ Hᵉ yᵉ =
    ( associative-mul-Monoidᵉ Mᵉ _ _ _) ∙ᵉ
    ( apᵉ
      ( mul-Monoidᵉ Mᵉ yᵉ)
      ( is-right-inverse-inv-is-invertible-element-Monoidᵉ Mᵉ Hᵉ)) ∙ᵉ
    ( right-unit-law-mul-Monoidᵉ Mᵉ yᵉ)

  is-equiv-mul-is-invertible-element-Monoid'ᵉ :
    is-invertible-element-Monoidᵉ Mᵉ xᵉ → is-equivᵉ (mul-Monoid'ᵉ Mᵉ xᵉ)
  is-equiv-mul-is-invertible-element-Monoid'ᵉ Hᵉ =
    is-equiv-is-invertibleᵉ
      ( right-div-is-invertible-element-Monoidᵉ Hᵉ)
      ( is-section-right-div-is-invertible-element-Monoidᵉ Hᵉ)
      ( is-retraction-right-div-is-invertible-element-Monoidᵉ Hᵉ)
```

## See also

-ᵉ Theᵉ coreᵉ ofᵉ aᵉ monoidᵉ isᵉ definedᵉ in
  [`group-theory.cores-monoids`](group-theory.cores-monoids.md).ᵉ