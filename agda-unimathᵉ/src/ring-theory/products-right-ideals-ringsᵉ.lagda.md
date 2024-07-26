# Products of right ideals of rings

```agda
module ring-theory.products-right-ideals-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.poset-of-right-ideals-ringsᵉ
open import ring-theory.products-subsets-ringsᵉ
open import ring-theory.right-ideals-generated-by-subsets-ringsᵉ
open import ring-theory.right-ideals-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.subsets-ringsᵉ
```

</details>

## Idea

Theᵉ **product**ᵉ ofᵉ twoᵉ [rightᵉ ideals](ring-theory.right-ideals-rings.mdᵉ) `I`ᵉ andᵉ
`J`ᵉ in aᵉ [ring](ring-theory.rings.mdᵉ) isᵉ theᵉ rightᵉ idealᵉ
[generatedᵉ by](ring-theory.right-ideals-generated-by-subsets-rings.mdᵉ) allᵉ
productsᵉ ofᵉ elementsᵉ in `I`ᵉ andᵉ `J`.ᵉ

## Definition

### The universal property of the product of two right ideals in a ring

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  (Iᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : right-ideal-Ringᵉ l3ᵉ Rᵉ)
  where

  contains-product-right-ideal-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : right-ideal-Ringᵉ l4ᵉ Rᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  contains-product-right-ideal-Ringᵉ Kᵉ =
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    is-in-right-ideal-Ringᵉ Rᵉ Iᵉ xᵉ → is-in-right-ideal-Ringᵉ Rᵉ Jᵉ yᵉ →
    is-in-right-ideal-Ringᵉ Rᵉ Kᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)

  is-product-right-ideal-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : right-ideal-Ringᵉ l4ᵉ Rᵉ) →
    contains-product-right-ideal-Ringᵉ Kᵉ → UUωᵉ
  is-product-right-ideal-Ringᵉ Kᵉ Hᵉ =
    {l5ᵉ : Level} (Lᵉ : right-ideal-Ringᵉ l5ᵉ Rᵉ) →
    contains-product-right-ideal-Ringᵉ Lᵉ → leq-right-ideal-Ringᵉ Rᵉ Kᵉ Lᵉ
```

### The product of two right ideals in a ring

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  (Iᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : right-ideal-Ringᵉ l3ᵉ Rᵉ)
  where

  generating-subset-product-right-ideal-Ringᵉ : subset-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Rᵉ
  generating-subset-product-right-ideal-Ringᵉ =
    product-subset-Ringᵉ Rᵉ
      ( subset-right-ideal-Ringᵉ Rᵉ Iᵉ)
      ( subset-right-ideal-Ringᵉ Rᵉ Jᵉ)

  product-right-ideal-Ringᵉ : right-ideal-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Rᵉ
  product-right-ideal-Ringᵉ =
    right-ideal-subset-Ringᵉ Rᵉ generating-subset-product-right-ideal-Ringᵉ

  subset-product-right-ideal-Ringᵉ : subset-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Rᵉ
  subset-product-right-ideal-Ringᵉ =
    subset-right-ideal-Ringᵉ Rᵉ product-right-ideal-Ringᵉ

  is-in-product-right-ideal-Ringᵉ : type-Ringᵉ Rᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-in-product-right-ideal-Ringᵉ =
    is-in-right-ideal-Ringᵉ Rᵉ product-right-ideal-Ringᵉ

  contains-product-product-right-ideal-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    is-in-right-ideal-Ringᵉ Rᵉ Iᵉ xᵉ → is-in-right-ideal-Ringᵉ Rᵉ Jᵉ yᵉ →
    is-in-product-right-ideal-Ringᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)
  contains-product-product-right-ideal-Ringᵉ xᵉ yᵉ Hᵉ Kᵉ =
    contains-subset-right-ideal-subset-Ringᵉ Rᵉ
      ( generating-subset-product-right-ideal-Ringᵉ)
      ( mul-Ringᵉ Rᵉ xᵉ yᵉ)
      ( unit-trunc-Propᵉ ((xᵉ ,ᵉ Hᵉ) ,ᵉ (yᵉ ,ᵉ Kᵉ) ,ᵉ reflᵉ))

  is-product-product-right-ideal-Ringᵉ :
    is-product-right-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ
      ( product-right-ideal-Ringᵉ)
      ( contains-product-product-right-ideal-Ringᵉ)
  is-product-product-right-ideal-Ringᵉ Kᵉ Hᵉ =
    is-right-ideal-generated-by-subset-right-ideal-subset-Ringᵉ Rᵉ
      ( generating-subset-product-right-ideal-Ringᵉ)
      ( Kᵉ)
      ( λ xᵉ pᵉ →
        apply-universal-property-trunc-Propᵉ pᵉ
          ( subset-right-ideal-Ringᵉ Rᵉ Kᵉ xᵉ)
          ( λ ((rᵉ ,ᵉ pᵉ) ,ᵉ ((sᵉ ,ᵉ qᵉ) ,ᵉ zᵉ)) →
            is-closed-under-eq-right-ideal-Ringᵉ Rᵉ Kᵉ (Hᵉ rᵉ sᵉ pᵉ qᵉ) (invᵉ zᵉ)))
```

## Properties

### The product of right ideals preserves inequality of right ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Aᵉ : Ringᵉ l1ᵉ)
  (Iᵉ : right-ideal-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : right-ideal-Ringᵉ l3ᵉ Aᵉ)
  (Kᵉ : right-ideal-Ringᵉ l4ᵉ Aᵉ)
  (Lᵉ : right-ideal-Ringᵉ l5ᵉ Aᵉ)
  where

  preserves-leq-product-right-ideal-Ringᵉ :
    leq-right-ideal-Ringᵉ Aᵉ Iᵉ Jᵉ →
    leq-right-ideal-Ringᵉ Aᵉ Kᵉ Lᵉ →
    leq-right-ideal-Ringᵉ Aᵉ
      ( product-right-ideal-Ringᵉ Aᵉ Iᵉ Kᵉ)
      ( product-right-ideal-Ringᵉ Aᵉ Jᵉ Lᵉ)
  preserves-leq-product-right-ideal-Ringᵉ pᵉ qᵉ =
    is-product-product-right-ideal-Ringᵉ Aᵉ Iᵉ Kᵉ
      ( product-right-ideal-Ringᵉ Aᵉ Jᵉ Lᵉ)
      ( λ xᵉ yᵉ uᵉ vᵉ →
        contains-product-product-right-ideal-Ringᵉ Aᵉ Jᵉ Lᵉ _ _
          ( pᵉ xᵉ uᵉ)
          ( qᵉ yᵉ vᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Ringᵉ l1ᵉ)
  (Iᵉ : right-ideal-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : right-ideal-Ringᵉ l3ᵉ Aᵉ)
  (Kᵉ : right-ideal-Ringᵉ l4ᵉ Aᵉ)
  where

  preserves-leq-left-product-right-ideal-Ringᵉ :
    leq-right-ideal-Ringᵉ Aᵉ Iᵉ Jᵉ →
    leq-right-ideal-Ringᵉ Aᵉ
      ( product-right-ideal-Ringᵉ Aᵉ Iᵉ Kᵉ)
      ( product-right-ideal-Ringᵉ Aᵉ Jᵉ Kᵉ)
  preserves-leq-left-product-right-ideal-Ringᵉ pᵉ =
    preserves-leq-product-right-ideal-Ringᵉ Aᵉ Iᵉ Jᵉ Kᵉ Kᵉ pᵉ
      ( refl-leq-right-ideal-Ringᵉ Aᵉ Kᵉ)

  preserves-leq-right-product-right-ideal-Ringᵉ :
    leq-right-ideal-Ringᵉ Aᵉ Jᵉ Kᵉ →
    leq-right-ideal-Ringᵉ Aᵉ
      ( product-right-ideal-Ringᵉ Aᵉ Iᵉ Jᵉ)
      ( product-right-ideal-Ringᵉ Aᵉ Iᵉ Kᵉ)
  preserves-leq-right-product-right-ideal-Ringᵉ =
    preserves-leq-product-right-ideal-Ringᵉ Aᵉ Iᵉ Iᵉ Jᵉ Kᵉ
      ( refl-leq-right-ideal-Ringᵉ Aᵉ Iᵉ)
```