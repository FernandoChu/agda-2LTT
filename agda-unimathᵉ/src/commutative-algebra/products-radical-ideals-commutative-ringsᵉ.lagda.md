# Products of radical ideals of a commutative ring

```agda
module commutative-algebra.products-radical-ideals-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.ideals-commutative-ringsᵉ
open import commutative-algebra.poset-of-radical-ideals-commutative-ringsᵉ
open import commutative-algebra.powers-of-elements-commutative-ringsᵉ
open import commutative-algebra.products-ideals-commutative-ringsᵉ
open import commutative-algebra.radical-ideals-commutative-ringsᵉ
open import commutative-algebra.radicals-of-ideals-commutative-ringsᵉ
open import commutative-algebra.subsets-commutative-ringsᵉ

open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **product**ᵉ ofᵉ twoᵉ
[radicalᵉ ideals](commutative-algebra.radical-ideals-commutative-rings.mdᵉ) `I`ᵉ
andᵉ `J`ᵉ isᵉ theᵉ
[radical](commutative-algebra.radicals-of-ideals-commutative-rings.mdᵉ) ofᵉ theᵉ
[product](commutative-algebra.products-ideals-commutative-rings.mdᵉ) ofᵉ `I`ᵉ andᵉ
`J`.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ productᵉ ofᵉ twoᵉ radicalᵉ idealsᵉ `I`ᵉ andᵉ `J`ᵉ isᵉ theᵉ leastᵉ
radicalᵉ idealᵉ thatᵉ containsᵉ theᵉ productsᵉ ofᵉ elementsᵉ in `I`ᵉ andᵉ in `J`.ᵉ

## Definitions

### The universal property of the product of two radical ideals in a commutative ring

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  contains-product-radical-ideal-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : radical-ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  contains-product-radical-ideal-Commutative-Ringᵉ Kᵉ =
    contains-product-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Kᵉ)

  is-product-radical-ideal-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : radical-ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) →
    contains-product-radical-ideal-Commutative-Ringᵉ Kᵉ → UUωᵉ
  is-product-radical-ideal-Commutative-Ringᵉ Kᵉ Hᵉ =
    {l5ᵉ : Level} (Lᵉ : radical-ideal-Commutative-Ringᵉ l5ᵉ Aᵉ) →
    contains-product-radical-ideal-Commutative-Ringᵉ Lᵉ →
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ Kᵉ Lᵉ
```

### The product of two radical ideals in a commutative ring

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  generating-subset-product-radical-ideal-Commutative-Ringᵉ :
    subset-Commutative-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Aᵉ
  generating-subset-product-radical-ideal-Commutative-Ringᵉ =
    generating-subset-product-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)

  product-radical-ideal-Commutative-Ringᵉ :
    radical-ideal-Commutative-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Aᵉ
  product-radical-ideal-Commutative-Ringᵉ =
    radical-of-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))

  ideal-product-radical-ideal-Commutative-Ringᵉ :
    ideal-Commutative-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Aᵉ
  ideal-product-radical-ideal-Commutative-Ringᵉ =
    ideal-radical-ideal-Commutative-Ringᵉ Aᵉ
      product-radical-ideal-Commutative-Ringᵉ

  is-in-product-radical-ideal-Commutative-Ringᵉ :
    type-Commutative-Ringᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-in-product-radical-ideal-Commutative-Ringᵉ =
    is-in-radical-ideal-Commutative-Ringᵉ Aᵉ
      product-radical-ideal-Commutative-Ringᵉ

  contains-product-product-radical-ideal-Commutative-Ringᵉ :
    contains-product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ
      product-radical-ideal-Commutative-Ringᵉ
  contains-product-product-radical-ideal-Commutative-Ringᵉ xᵉ yᵉ Hᵉ Kᵉ =
    contains-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ)
      ( contains-product-product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
        ( xᵉ)
        ( yᵉ)
        ( Hᵉ)
        ( Kᵉ))

  is-product-product-radical-ideal-Commutative-Ringᵉ :
    is-product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ
      product-radical-ideal-Commutative-Ringᵉ
      contains-product-product-radical-ideal-Commutative-Ringᵉ
  is-product-product-radical-ideal-Commutative-Ringᵉ Kᵉ Hᵉ =
    is-radical-of-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( Kᵉ)
      ( is-product-product-ideal-Commutative-Ringᵉ Aᵉ
          ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
          ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Kᵉ)
          ( Hᵉ))
```

## Properties

### Radical laws for products of ideals

#### `√ (I · √ J) ＝ √ IJ`

Forᵉ theᵉ forwardᵉ inclusion,ᵉ assumeᵉ thatᵉ `xᵉ ∈ᵉ I`ᵉ andᵉ `yᵉ ∈ᵉ √ᵉ J`.ᵉ Thenᵉ thereᵉ existsᵉ
anᵉ `n`ᵉ suchᵉ thatᵉ `yⁿᵉ ∈ᵉ J`.ᵉ Itᵉ followsᵉ thatᵉ

```text
  (xy)ⁿ⁺¹ᵉ ＝ᵉ xⁿ⁺¹yⁿ⁺¹ᵉ = (xxⁿ)(yⁿyᵉ) ＝ᵉ (xyⁿ)(xⁿyᵉ) ∈ᵉ IJ,ᵉ
```

andᵉ henceᵉ `xyᵉ ∈ᵉ √ᵉ IJ`.ᵉ Theᵉ backwardsᵉ inclusionᵉ isᵉ clear,ᵉ sinceᵉ `Jᵉ ⊆ᵉ √ᵉ J`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  forward-inclusion-right-radical-law-product-radical-ideal-Commutative-Ringᵉ :
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( product-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ
        ( product-ideal-Commutative-Ringᵉ Aᵉ
          ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( Jᵉ)))
  forward-inclusion-right-radical-law-product-radical-ideal-Commutative-Ringᵉ =
    is-product-product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ
        ( product-ideal-Commutative-Ringᵉ Aᵉ
          ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( Jᵉ)))
      ( λ xᵉ yᵉ Hᵉ Kᵉ →
        apply-universal-property-trunc-Propᵉ Kᵉ
          ( subset-radical-of-ideal-Commutative-Ringᵉ Aᵉ
            ( product-ideal-Commutative-Ringᵉ Aᵉ
              ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
              ( Jᵉ))
            ( mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ))
          ( λ (nᵉ ,ᵉ pᵉ) →
            intro-existsᵉ
              ( succ-ℕᵉ nᵉ)
              ( is-closed-under-eq-ideal-Commutative-Ring'ᵉ Aᵉ
                ( product-ideal-Commutative-Ringᵉ Aᵉ
                  ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
                  ( Jᵉ))
                ( is-closed-under-right-multiplication-ideal-Commutative-Ringᵉ Aᵉ
                  ( product-ideal-Commutative-Ringᵉ Aᵉ
                    ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
                    ( Jᵉ))
                  ( mul-Commutative-Ringᵉ Aᵉ xᵉ (power-Commutative-Ringᵉ Aᵉ nᵉ yᵉ))
                  ( mul-Commutative-Ringᵉ Aᵉ (power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ) yᵉ)
                  ( contains-product-product-ideal-Commutative-Ringᵉ Aᵉ
                    ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
                    ( Jᵉ)
                    ( xᵉ)
                    ( power-Commutative-Ringᵉ Aᵉ nᵉ yᵉ)
                    ( Hᵉ)
                    ( pᵉ)))
                ( ( distributive-power-mul-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ) xᵉ yᵉ) ∙ᵉ
                  ( ( ap-mul-Commutative-Ringᵉ Aᵉ
                      ( power-succ-Commutative-Ring'ᵉ Aᵉ nᵉ xᵉ)
                      ( power-succ-Commutative-Ringᵉ Aᵉ nᵉ yᵉ)) ∙ᵉ
                    ( interchange-mul-mul-Commutative-Ringᵉ Aᵉ xᵉ
                      ( power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)
                      ( power-Commutative-Ringᵉ Aᵉ nᵉ yᵉ)
                      ( yᵉ)))))))

  backward-inclusion-right-radical-law-product-radical-ideal-Commutative-Ringᵉ :
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ
        ( product-ideal-Commutative-Ringᵉ Aᵉ
          ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( Jᵉ)))
      ( product-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
  backward-inclusion-right-radical-law-product-radical-ideal-Commutative-Ringᵉ =
    is-radical-of-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( Jᵉ))
      ( product-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( is-product-product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( Jᵉ)
        ( ideal-product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
          ( radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
        ( λ xᵉ yᵉ pᵉ qᵉ →
          contains-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
            ( product-ideal-Commutative-Ringᵉ Aᵉ
              ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
              ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
            ( mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ)
            ( contains-product-product-ideal-Commutative-Ringᵉ Aᵉ
              ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
              ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
              ( xᵉ)
              ( yᵉ)
              ( pᵉ)
              ( contains-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ yᵉ qᵉ))))

  right-radical-law-product-radical-ideal-Commutative-Ringᵉ :
    product-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( Iᵉ)
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ) ＝ᵉ
    radical-of-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( Jᵉ))
  right-radical-law-product-radical-ideal-Commutative-Ringᵉ =
    antisymmetric-leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( product-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ
        ( product-ideal-Commutative-Ringᵉ Aᵉ
          ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( Jᵉ)))
      ( forward-inclusion-right-radical-law-product-radical-ideal-Commutative-Ringᵉ)
      ( backward-inclusion-right-radical-law-product-radical-ideal-Commutative-Ringᵉ)
```