# Invertible elements in commutative rings

```agda
module commutative-algebra.invertible-elements-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.invertible-elements-ringsᵉ
```

</details>

## Idea

Anᵉ elementᵉ ofᵉ aᵉ [commutativeᵉ ring](commutative-algebra.commutative-rings.mdᵉ)
`A`isᵉ saidᵉ to beᵉ **invertible**ᵉ ifᵉ itᵉ hasᵉ aᵉ two-sidedᵉ inverse.ᵉ However,ᵉ sinceᵉ
multiplicationᵉ in commutativeᵉ ringsᵉ isᵉ commutative,ᵉ anyᵉ elementᵉ isᵉ alreadyᵉ
invertibleᵉ asᵉ soonᵉ asᵉ itᵉ hasᵉ eitherᵉ aᵉ leftᵉ orᵉ aᵉ rightᵉ inverse.ᵉ Theᵉ invertibleᵉ
elementsᵉ ofᵉ aᵉ commutativeᵉ ringᵉ `A`ᵉ areᵉ alsoᵉ calledᵉ theᵉ **(multiplicativeᵉ)
units**ᵉ ofᵉ `A`.ᵉ

Theᵉ [abelianᵉ group](group-theory.abelian-groups.mdᵉ) ofᵉ multiplicativeᵉ unitsᵉ isᵉ
constructedᵉ in
[`commutative-algebra.groups-of-units-commutative-rings`](commutative-algebra.groups-of-units-commutative-rings.md).ᵉ

## Definitions

### Left invertible elements of commutative rings

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  is-left-inverse-element-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ) → UUᵉ lᵉ
  is-left-inverse-element-Commutative-Ringᵉ =
    is-left-inverse-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-left-invertible-element-Commutative-Ringᵉ : type-Commutative-Ringᵉ Aᵉ → UUᵉ lᵉ
  is-left-invertible-element-Commutative-Ringᵉ =
    is-left-invertible-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) {xᵉ : type-Commutative-Ringᵉ Aᵉ}
  where

  retraction-is-left-invertible-element-Commutative-Ringᵉ :
    is-left-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ → type-Commutative-Ringᵉ Aᵉ
  retraction-is-left-invertible-element-Commutative-Ringᵉ =
    retraction-is-left-invertible-element-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)

  is-left-inverse-retraction-is-left-invertible-element-Commutative-Ringᵉ :
    (Hᵉ : is-left-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ) →
    is-left-inverse-element-Commutative-Ringᵉ Aᵉ xᵉ
      ( retraction-is-left-invertible-element-Commutative-Ringᵉ Hᵉ)
  is-left-inverse-retraction-is-left-invertible-element-Commutative-Ringᵉ =
    is-left-inverse-retraction-is-left-invertible-element-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
```

### Aight invertible elements of commutative rings

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  is-right-inverse-element-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ) → UUᵉ lᵉ
  is-right-inverse-element-Commutative-Ringᵉ =
    is-right-inverse-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-right-invertible-element-Commutative-Ringᵉ : type-Commutative-Ringᵉ Aᵉ → UUᵉ lᵉ
  is-right-invertible-element-Commutative-Ringᵉ =
    is-right-invertible-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) {xᵉ : type-Commutative-Ringᵉ Aᵉ}
  where

  section-is-right-invertible-element-Commutative-Ringᵉ :
    is-right-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ → type-Commutative-Ringᵉ Aᵉ
  section-is-right-invertible-element-Commutative-Ringᵉ =
    section-is-right-invertible-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-right-inverse-section-is-right-invertible-element-Commutative-Ringᵉ :
    (Hᵉ : is-right-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ) →
    is-right-inverse-element-Commutative-Ringᵉ Aᵉ xᵉ
      ( section-is-right-invertible-element-Commutative-Ringᵉ Hᵉ)
  is-right-inverse-section-is-right-invertible-element-Commutative-Ringᵉ =
    is-right-inverse-section-is-right-invertible-element-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
```

### Invertible elements of commutative rings

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ)
  where

  is-inverse-element-Commutative-Ringᵉ : type-Commutative-Ringᵉ Aᵉ → UUᵉ lᵉ
  is-inverse-element-Commutative-Ringᵉ =
    is-inverse-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) xᵉ

  is-invertible-element-Commutative-Ringᵉ : UUᵉ lᵉ
  is-invertible-element-Commutative-Ringᵉ =
    is-invertible-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) xᵉ

module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) {xᵉ : type-Commutative-Ringᵉ Aᵉ}
  where

  inv-is-invertible-element-Commutative-Ringᵉ :
    is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ → type-Commutative-Ringᵉ Aᵉ
  inv-is-invertible-element-Commutative-Ringᵉ =
    inv-is-invertible-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-right-inverse-inv-is-invertible-element-Commutative-Ringᵉ :
    (Hᵉ : is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ) →
    is-right-inverse-element-Commutative-Ringᵉ Aᵉ xᵉ
      ( inv-is-invertible-element-Commutative-Ringᵉ Hᵉ)
  is-right-inverse-inv-is-invertible-element-Commutative-Ringᵉ =
    is-right-inverse-inv-is-invertible-element-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)

  is-left-inverse-inv-is-invertible-element-Commutative-Ringᵉ :
    (Hᵉ : is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ) →
    is-left-inverse-element-Commutative-Ringᵉ Aᵉ xᵉ
      ( inv-is-invertible-element-Commutative-Ringᵉ Hᵉ)
  is-left-inverse-inv-is-invertible-element-Commutative-Ringᵉ =
    is-left-inverse-inv-is-invertible-element-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)

  is-invertible-is-left-invertible-element-Commutative-Ringᵉ :
    is-left-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ →
    is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ
  pr1ᵉ (is-invertible-is-left-invertible-element-Commutative-Ringᵉ Hᵉ) =
    retraction-is-left-invertible-element-Commutative-Ringᵉ Aᵉ Hᵉ
  pr1ᵉ (pr2ᵉ (is-invertible-is-left-invertible-element-Commutative-Ringᵉ Hᵉ)) =
    commutative-mul-Commutative-Ringᵉ Aᵉ _ _ ∙ᵉ
    is-left-inverse-retraction-is-left-invertible-element-Commutative-Ringᵉ Aᵉ Hᵉ
  pr2ᵉ (pr2ᵉ (is-invertible-is-left-invertible-element-Commutative-Ringᵉ Hᵉ)) =
    is-left-inverse-retraction-is-left-invertible-element-Commutative-Ringᵉ Aᵉ Hᵉ

  is-invertible-is-right-invertible-element-Commutative-Ringᵉ :
    is-right-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ →
    is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ
  pr1ᵉ (is-invertible-is-right-invertible-element-Commutative-Ringᵉ Hᵉ) =
    section-is-right-invertible-element-Commutative-Ringᵉ Aᵉ Hᵉ
  pr1ᵉ (pr2ᵉ (is-invertible-is-right-invertible-element-Commutative-Ringᵉ Hᵉ)) =
    is-right-inverse-section-is-right-invertible-element-Commutative-Ringᵉ Aᵉ Hᵉ
  pr2ᵉ (pr2ᵉ (is-invertible-is-right-invertible-element-Commutative-Ringᵉ Hᵉ)) =
    commutative-mul-Commutative-Ringᵉ Aᵉ _ _ ∙ᵉ
    is-right-inverse-section-is-right-invertible-element-Commutative-Ringᵉ Aᵉ Hᵉ
```

## Properties

### Being an invertible element is a property

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  is-prop-is-invertible-element-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    is-propᵉ (is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ)
  is-prop-is-invertible-element-Commutative-Ringᵉ =
    is-prop-is-invertible-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-invertible-element-prop-Commutative-Ringᵉ : type-Commutative-Ringᵉ Aᵉ → Propᵉ lᵉ
  is-invertible-element-prop-Commutative-Ringᵉ =
    is-invertible-element-prop-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Inverses are left/right inverses

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  is-left-invertible-is-invertible-element-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ →
    is-left-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ
  is-left-invertible-is-invertible-element-Commutative-Ringᵉ =
    is-left-invertible-is-invertible-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-right-invertible-is-invertible-element-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ →
    is-right-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ
  is-right-invertible-is-invertible-element-Commutative-Ringᵉ =
    is-right-invertible-is-invertible-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### The inverse invertible element

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  is-right-invertible-left-inverse-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ Aᵉ)
    (Hᵉ : is-left-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ) →
    is-right-invertible-element-Commutative-Ringᵉ Aᵉ
      ( retraction-is-left-invertible-element-Commutative-Ringᵉ Aᵉ Hᵉ)
  is-right-invertible-left-inverse-Commutative-Ringᵉ =
    is-right-invertible-left-inverse-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-left-invertible-right-inverse-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ Aᵉ)
    (Hᵉ : is-right-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ) →
    is-left-invertible-element-Commutative-Ringᵉ Aᵉ
      ( section-is-right-invertible-element-Commutative-Ringᵉ Aᵉ Hᵉ)
  is-left-invertible-right-inverse-Commutative-Ringᵉ =
    is-left-invertible-right-inverse-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-invertible-element-inverse-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ Aᵉ)
    (Hᵉ : is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ) →
    is-invertible-element-Commutative-Ringᵉ Aᵉ
      ( inv-is-invertible-element-Commutative-Ringᵉ Aᵉ Hᵉ)
  is-invertible-element-inverse-Commutative-Ringᵉ =
    is-invertible-element-inverse-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Any invertible element of a monoid has a contractible type of right inverses

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  is-contr-is-right-invertible-element-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ Aᵉ) → is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ →
    is-contrᵉ (is-right-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ)
  is-contr-is-right-invertible-element-Commutative-Ringᵉ =
    is-contr-is-right-invertible-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Any invertible element of a monoid has a contractible type of left inverses

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  is-contr-is-left-invertible-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ Aᵉ) → is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ →
    is-contrᵉ (is-left-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ)
  is-contr-is-left-invertible-Commutative-Ringᵉ =
    is-contr-is-left-invertible-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### The unit of a monoid is invertible

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  is-left-invertible-element-one-Commutative-Ringᵉ :
    is-left-invertible-element-Commutative-Ringᵉ Aᵉ (one-Commutative-Ringᵉ Aᵉ)
  is-left-invertible-element-one-Commutative-Ringᵉ =
    is-left-invertible-element-one-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-right-invertible-element-one-Commutative-Ringᵉ :
    is-right-invertible-element-Commutative-Ringᵉ Aᵉ (one-Commutative-Ringᵉ Aᵉ)
  is-right-invertible-element-one-Commutative-Ringᵉ =
    is-right-invertible-element-one-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-invertible-element-one-Commutative-Ringᵉ :
    is-invertible-element-Commutative-Ringᵉ Aᵉ (one-Commutative-Ringᵉ Aᵉ)
  is-invertible-element-one-Commutative-Ringᵉ =
    is-invertible-element-one-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Invertible elements are closed under multiplication

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  is-left-invertible-element-mul-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ) →
    is-left-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ →
    is-left-invertible-element-Commutative-Ringᵉ Aᵉ yᵉ →
    is-left-invertible-element-Commutative-Ringᵉ Aᵉ (mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ)
  is-left-invertible-element-mul-Commutative-Ringᵉ =
    is-left-invertible-element-mul-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-right-invertible-element-mul-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ) →
    is-right-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ →
    is-right-invertible-element-Commutative-Ringᵉ Aᵉ yᵉ →
    is-right-invertible-element-Commutative-Ringᵉ Aᵉ (mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ)
  is-right-invertible-element-mul-Commutative-Ringᵉ =
    is-right-invertible-element-mul-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-invertible-element-mul-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ) →
    is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ →
    is-invertible-element-Commutative-Ringᵉ Aᵉ yᵉ →
    is-invertible-element-Commutative-Ringᵉ Aᵉ (mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ)
  is-invertible-element-mul-Commutative-Ringᵉ =
    is-invertible-element-mul-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### The inverse of an invertible element is invertible

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  is-invertible-element-inv-is-invertible-element-Commutative-Ringᵉ :
    {xᵉ : type-Commutative-Ringᵉ Aᵉ}
    (Hᵉ : is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ) →
    is-invertible-element-Commutative-Ringᵉ Aᵉ
      ( inv-is-invertible-element-Commutative-Ringᵉ Aᵉ Hᵉ)
  is-invertible-element-inv-is-invertible-element-Commutative-Ringᵉ =
    is-invertible-element-inv-is-invertible-element-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
```

## See also

-ᵉ Theᵉ groupᵉ ofᵉ multiplicativeᵉ unitsᵉ ofᵉ aᵉ commutativeᵉ ringᵉ isᵉ definedᵉ in
  [`commutative-algebra.groups-of-units-commutative-rings`](commutative-algebra.groups-of-units-commutative-rings.md).ᵉ