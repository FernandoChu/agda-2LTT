# Products of left ideals of rings

```agda
module ring-theory.products-left-ideals-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.left-ideals-generated-by-subsets-ringsᵉ
open import ring-theory.left-ideals-ringsᵉ
open import ring-theory.poset-of-left-ideals-ringsᵉ
open import ring-theory.products-subsets-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.subsets-ringsᵉ
```

</details>

## Idea

Theᵉ **product**ᵉ ofᵉ twoᵉ [leftᵉ ideals](ring-theory.left-ideals-rings.mdᵉ) `I`ᵉ andᵉ
`J`ᵉ in aᵉ [ring](ring-theory.rings.mdᵉ) isᵉ theᵉ leftᵉ idealᵉ
[generatedᵉ by](ring-theory.left-ideals-generated-by-subsets-rings.mdᵉ) allᵉ
productsᵉ ofᵉ elementsᵉ in `I`ᵉ andᵉ `J`.ᵉ

## Definition

### The universal property of the product of two left ideals in a ring

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  (Iᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : left-ideal-Ringᵉ l3ᵉ Rᵉ)
  where

  contains-product-left-ideal-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : left-ideal-Ringᵉ l4ᵉ Rᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  contains-product-left-ideal-Ringᵉ Kᵉ =
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    is-in-left-ideal-Ringᵉ Rᵉ Iᵉ xᵉ → is-in-left-ideal-Ringᵉ Rᵉ Jᵉ yᵉ →
    is-in-left-ideal-Ringᵉ Rᵉ Kᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)

  is-product-left-ideal-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : left-ideal-Ringᵉ l4ᵉ Rᵉ) →
    contains-product-left-ideal-Ringᵉ Kᵉ → UUωᵉ
  is-product-left-ideal-Ringᵉ Kᵉ Hᵉ =
    {l5ᵉ : Level} (Lᵉ : left-ideal-Ringᵉ l5ᵉ Rᵉ) →
    contains-product-left-ideal-Ringᵉ Lᵉ → leq-left-ideal-Ringᵉ Rᵉ Kᵉ Lᵉ
```

### The product of two left ideals in a ring

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  (Iᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : left-ideal-Ringᵉ l3ᵉ Rᵉ)
  where

  generating-subset-product-left-ideal-Ringᵉ : subset-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Rᵉ
  generating-subset-product-left-ideal-Ringᵉ =
    product-subset-Ringᵉ Rᵉ
      ( subset-left-ideal-Ringᵉ Rᵉ Iᵉ)
      ( subset-left-ideal-Ringᵉ Rᵉ Jᵉ)

  product-left-ideal-Ringᵉ : left-ideal-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Rᵉ
  product-left-ideal-Ringᵉ =
    left-ideal-subset-Ringᵉ Rᵉ generating-subset-product-left-ideal-Ringᵉ

  subset-product-left-ideal-Ringᵉ : subset-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Rᵉ
  subset-product-left-ideal-Ringᵉ =
    subset-left-ideal-Ringᵉ Rᵉ product-left-ideal-Ringᵉ

  is-in-product-left-ideal-Ringᵉ : type-Ringᵉ Rᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-in-product-left-ideal-Ringᵉ =
    is-in-left-ideal-Ringᵉ Rᵉ product-left-ideal-Ringᵉ

  contains-product-product-left-ideal-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    is-in-left-ideal-Ringᵉ Rᵉ Iᵉ xᵉ → is-in-left-ideal-Ringᵉ Rᵉ Jᵉ yᵉ →
    is-in-product-left-ideal-Ringᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)
  contains-product-product-left-ideal-Ringᵉ xᵉ yᵉ Hᵉ Kᵉ =
    contains-subset-left-ideal-subset-Ringᵉ Rᵉ
      ( generating-subset-product-left-ideal-Ringᵉ)
      ( mul-Ringᵉ Rᵉ xᵉ yᵉ)
      ( unit-trunc-Propᵉ ((xᵉ ,ᵉ Hᵉ) ,ᵉ (yᵉ ,ᵉ Kᵉ) ,ᵉ reflᵉ))

  is-product-product-left-ideal-Ringᵉ :
    is-product-left-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ
      ( product-left-ideal-Ringᵉ)
      ( contains-product-product-left-ideal-Ringᵉ)
  is-product-product-left-ideal-Ringᵉ Kᵉ Hᵉ =
    is-left-ideal-generated-by-subset-left-ideal-subset-Ringᵉ Rᵉ
      ( generating-subset-product-left-ideal-Ringᵉ)
      ( Kᵉ)
      ( λ xᵉ pᵉ →
        apply-universal-property-trunc-Propᵉ pᵉ
          ( subset-left-ideal-Ringᵉ Rᵉ Kᵉ xᵉ)
          ( λ ((rᵉ ,ᵉ pᵉ) ,ᵉ ((sᵉ ,ᵉ qᵉ) ,ᵉ zᵉ)) →
            is-closed-under-eq-left-ideal-Ringᵉ Rᵉ Kᵉ (Hᵉ rᵉ sᵉ pᵉ qᵉ) (invᵉ zᵉ)))
```

## Properties

### The product of left ideals preserves inequality of left ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Aᵉ : Ringᵉ l1ᵉ)
  (Iᵉ : left-ideal-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : left-ideal-Ringᵉ l3ᵉ Aᵉ)
  (Kᵉ : left-ideal-Ringᵉ l4ᵉ Aᵉ)
  (Lᵉ : left-ideal-Ringᵉ l5ᵉ Aᵉ)
  where

  preserves-leq-product-left-ideal-Ringᵉ :
    leq-left-ideal-Ringᵉ Aᵉ Iᵉ Jᵉ →
    leq-left-ideal-Ringᵉ Aᵉ Kᵉ Lᵉ →
    leq-left-ideal-Ringᵉ Aᵉ
      ( product-left-ideal-Ringᵉ Aᵉ Iᵉ Kᵉ)
      ( product-left-ideal-Ringᵉ Aᵉ Jᵉ Lᵉ)
  preserves-leq-product-left-ideal-Ringᵉ pᵉ qᵉ =
    is-product-product-left-ideal-Ringᵉ Aᵉ Iᵉ Kᵉ
      ( product-left-ideal-Ringᵉ Aᵉ Jᵉ Lᵉ)
      ( λ xᵉ yᵉ uᵉ vᵉ →
        contains-product-product-left-ideal-Ringᵉ Aᵉ Jᵉ Lᵉ _ _
          ( pᵉ xᵉ uᵉ)
          ( qᵉ yᵉ vᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Ringᵉ l1ᵉ)
  (Iᵉ : left-ideal-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : left-ideal-Ringᵉ l3ᵉ Aᵉ)
  (Kᵉ : left-ideal-Ringᵉ l4ᵉ Aᵉ)
  where

  preserves-leq-left-product-left-ideal-Ringᵉ :
    leq-left-ideal-Ringᵉ Aᵉ Iᵉ Jᵉ →
    leq-left-ideal-Ringᵉ Aᵉ
      ( product-left-ideal-Ringᵉ Aᵉ Iᵉ Kᵉ)
      ( product-left-ideal-Ringᵉ Aᵉ Jᵉ Kᵉ)
  preserves-leq-left-product-left-ideal-Ringᵉ pᵉ =
    preserves-leq-product-left-ideal-Ringᵉ Aᵉ Iᵉ Jᵉ Kᵉ Kᵉ pᵉ
      ( refl-leq-left-ideal-Ringᵉ Aᵉ Kᵉ)

  preserves-leq-right-product-left-ideal-Ringᵉ :
    leq-left-ideal-Ringᵉ Aᵉ Jᵉ Kᵉ →
    leq-left-ideal-Ringᵉ Aᵉ
      ( product-left-ideal-Ringᵉ Aᵉ Iᵉ Jᵉ)
      ( product-left-ideal-Ringᵉ Aᵉ Iᵉ Kᵉ)
  preserves-leq-right-product-left-ideal-Ringᵉ =
    preserves-leq-product-left-ideal-Ringᵉ Aᵉ Iᵉ Iᵉ Jᵉ Kᵉ
      ( refl-leq-left-ideal-Ringᵉ Aᵉ Iᵉ)
```