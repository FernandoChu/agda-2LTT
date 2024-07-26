# Decidable propositions

```agda
module foundation-core.decidable-propositionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-negationᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "decidableᵉ proposition"ᵉ Agda=is-decidable-Propᵉ}} isᵉ aᵉ
[proposition](foundation-core.propositions.mdᵉ) thatᵉ hasᵉ aᵉ
[decidable](foundation.decidable-types.mdᵉ) underlyingᵉ type.ᵉ

## Definition

### The subtype of decidable propositions

```agda
is-decidable-propᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
is-decidable-propᵉ Aᵉ = is-propᵉ Aᵉ ×ᵉ is-decidableᵉ Aᵉ

is-prop-is-decidableᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-propᵉ Aᵉ → is-propᵉ (is-decidableᵉ Aᵉ)
is-prop-is-decidableᵉ is-prop-Aᵉ =
  is-prop-coproductᵉ intro-double-negationᵉ is-prop-Aᵉ is-prop-negᵉ

is-decidable-Propᵉ :
  {lᵉ : Level} → Propᵉ lᵉ → Propᵉ lᵉ
pr1ᵉ (is-decidable-Propᵉ Pᵉ) = is-decidableᵉ (type-Propᵉ Pᵉ)
pr2ᵉ (is-decidable-Propᵉ Pᵉ) = is-prop-is-decidableᵉ (is-prop-type-Propᵉ Pᵉ)

is-prop-is-decidable-propᵉ :
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-propᵉ (is-decidable-propᵉ Xᵉ)
is-prop-is-decidable-propᵉ Xᵉ =
  is-prop-has-elementᵉ
    ( λ Hᵉ →
      is-prop-productᵉ
        ( is-prop-is-propᵉ Xᵉ)
        ( is-prop-is-decidableᵉ (pr1ᵉ Hᵉ)))

is-decidable-prop-Propᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → Propᵉ lᵉ
pr1ᵉ (is-decidable-prop-Propᵉ Aᵉ) = is-decidable-propᵉ Aᵉ
pr2ᵉ (is-decidable-prop-Propᵉ Aᵉ) = is-prop-is-decidable-propᵉ Aᵉ
```

### Decidable propositions

```agda
Decidable-Propᵉ :
  (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Decidable-Propᵉ lᵉ = type-subtypeᵉ is-decidable-prop-Propᵉ

module _
  {lᵉ : Level} (Pᵉ : Decidable-Propᵉ lᵉ)
  where

  prop-Decidable-Propᵉ : Propᵉ lᵉ
  prop-Decidable-Propᵉ = totᵉ (λ xᵉ → pr1ᵉ) Pᵉ

  type-Decidable-Propᵉ : UUᵉ lᵉ
  type-Decidable-Propᵉ = type-Propᵉ prop-Decidable-Propᵉ

  abstract
    is-prop-type-Decidable-Propᵉ : is-propᵉ type-Decidable-Propᵉ
    is-prop-type-Decidable-Propᵉ = is-prop-type-Propᵉ prop-Decidable-Propᵉ

  is-decidable-Decidable-Propᵉ : is-decidableᵉ type-Decidable-Propᵉ
  is-decidable-Decidable-Propᵉ = pr2ᵉ (pr2ᵉ Pᵉ)

  is-decidable-prop-type-Decidable-Propᵉ : is-decidable-propᵉ type-Decidable-Propᵉ
  is-decidable-prop-type-Decidable-Propᵉ = pr2ᵉ Pᵉ

  is-decidable-prop-Decidable-Propᵉ : Propᵉ lᵉ
  pr1ᵉ is-decidable-prop-Decidable-Propᵉ = is-decidableᵉ type-Decidable-Propᵉ
  pr2ᵉ is-decidable-prop-Decidable-Propᵉ =
    is-prop-is-decidableᵉ is-prop-type-Decidable-Propᵉ
```

### The empty type is a decidable proposition

```agda
is-decidable-prop-emptyᵉ : is-decidable-propᵉ emptyᵉ
pr1ᵉ is-decidable-prop-emptyᵉ = is-prop-emptyᵉ
pr2ᵉ is-decidable-prop-emptyᵉ = inrᵉ idᵉ

empty-Decidable-Propᵉ : Decidable-Propᵉ lzero
pr1ᵉ empty-Decidable-Propᵉ = emptyᵉ
pr2ᵉ empty-Decidable-Propᵉ = is-decidable-prop-emptyᵉ
```

### The unit type is a decidable proposition

```agda
is-decidable-prop-unitᵉ : is-decidable-propᵉ unitᵉ
pr1ᵉ is-decidable-prop-unitᵉ = is-prop-unitᵉ
pr2ᵉ is-decidable-prop-unitᵉ = inlᵉ starᵉ

unit-Decidable-Propᵉ : Decidable-Propᵉ lzero
pr1ᵉ unit-Decidable-Propᵉ = unitᵉ
pr2ᵉ unit-Decidable-Propᵉ = is-decidable-prop-unitᵉ
```

### The product of two decidable propositions is a decidable proposition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Decidable-Propᵉ l1ᵉ) (Qᵉ : Decidable-Propᵉ l2ᵉ)
  where

  type-product-Decidable-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-product-Decidable-Propᵉ =
    type-product-Propᵉ (prop-Decidable-Propᵉ Pᵉ) (prop-Decidable-Propᵉ Qᵉ)

  is-prop-product-Decidable-Propᵉ : is-propᵉ type-product-Decidable-Propᵉ
  is-prop-product-Decidable-Propᵉ =
    is-prop-product-Propᵉ (prop-Decidable-Propᵉ Pᵉ) (prop-Decidable-Propᵉ Qᵉ)

  is-decidable-product-Decidable-Propᵉ : is-decidableᵉ type-product-Decidable-Propᵉ
  is-decidable-product-Decidable-Propᵉ =
    is-decidable-productᵉ
      ( is-decidable-Decidable-Propᵉ Pᵉ)
      ( is-decidable-Decidable-Propᵉ Qᵉ)

  is-decidable-prop-product-Decidable-Propᵉ :
    is-decidable-propᵉ type-product-Decidable-Propᵉ
  pr1ᵉ is-decidable-prop-product-Decidable-Propᵉ = is-prop-product-Decidable-Propᵉ
  pr2ᵉ is-decidable-prop-product-Decidable-Propᵉ =
    is-decidable-product-Decidable-Propᵉ

  product-Decidable-Propᵉ : Decidable-Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ product-Decidable-Propᵉ = type-product-Decidable-Propᵉ
  pr2ᵉ product-Decidable-Propᵉ = is-decidable-prop-product-Decidable-Propᵉ
```

### Decidability of a propositional truncation

```agda
abstract
  is-prop-is-decidable-trunc-Propᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → is-propᵉ (is-decidableᵉ (type-trunc-Propᵉ Aᵉ))
  is-prop-is-decidable-trunc-Propᵉ Aᵉ =
    is-prop-is-decidableᵉ is-prop-type-trunc-Propᵉ

is-decidable-trunc-Propᵉ : {lᵉ : Level} → UUᵉ lᵉ → Propᵉ lᵉ
pr1ᵉ (is-decidable-trunc-Propᵉ Aᵉ) = is-decidableᵉ (type-trunc-Propᵉ Aᵉ)
pr2ᵉ (is-decidable-trunc-Propᵉ Aᵉ) = is-prop-is-decidable-trunc-Propᵉ Aᵉ

is-decidable-trunc-Prop-is-merely-decidableᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
  is-merely-decidableᵉ Aᵉ → is-decidableᵉ (type-trunc-Propᵉ Aᵉ)
is-decidable-trunc-Prop-is-merely-decidableᵉ Aᵉ =
  map-universal-property-trunc-Propᵉ
    ( is-decidable-trunc-Propᵉ Aᵉ)
    ( fᵉ)
  where
  fᵉ : is-decidableᵉ Aᵉ → type-Propᵉ (is-decidable-trunc-Propᵉ Aᵉ)
  fᵉ (inlᵉ aᵉ) = inlᵉ (unit-trunc-Propᵉ aᵉ)
  fᵉ (inrᵉ fᵉ) = inrᵉ (map-universal-property-trunc-Propᵉ empty-Propᵉ fᵉ)

is-merely-decidable-is-decidable-trunc-Propᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
  is-decidableᵉ (type-trunc-Propᵉ Aᵉ) → is-merely-decidableᵉ Aᵉ
is-merely-decidable-is-decidable-trunc-Propᵉ Aᵉ (inlᵉ xᵉ) =
  apply-universal-property-trunc-Propᵉ xᵉ
    ( is-merely-decidable-Propᵉ Aᵉ)
    ( unit-trunc-Propᵉ ∘ᵉ inlᵉ)
is-merely-decidable-is-decidable-trunc-Propᵉ Aᵉ (inrᵉ fᵉ) =
  unit-trunc-Propᵉ (inrᵉ (fᵉ ∘ᵉ unit-trunc-Propᵉ))
```