# Products of ideals of commutative rings

```agda
module commutative-algebra.products-ideals-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.ideals-commutative-ringsᵉ
open import commutative-algebra.ideals-generated-by-subsets-commutative-ringsᵉ
open import commutative-algebra.poset-of-ideals-commutative-ringsᵉ
open import commutative-algebra.products-subsets-commutative-ringsᵉ
open import commutative-algebra.subsets-commutative-ringsᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import lists.listsᵉ

open import ring-theory.products-ideals-ringsᵉ
```

</details>

## Idea

Theᵉ **product**ᵉ ofᵉ twoᵉ [ideals](commutative-algebra.ideals-commutative-rings.mdᵉ)
`I`ᵉ andᵉ `J`ᵉ in aᵉ [commutativeᵉ ring](commutative-algebra.commutative-rings.mdᵉ) isᵉ
theᵉ idealᵉ generatedᵉ allᵉ productsᵉ ofᵉ elementsᵉ in `I`ᵉ andᵉ `J`.ᵉ

## Definition

### The universal property of the product of two ideals in a commutative ring

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : ideal-Commutative-Ringᵉ l3ᵉ Rᵉ)
  where

  contains-product-ideal-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : ideal-Commutative-Ringᵉ l4ᵉ Rᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  contains-product-ideal-Commutative-Ringᵉ =
    contains-product-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ Jᵉ

  is-product-ideal-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : ideal-Commutative-Ringᵉ l4ᵉ Rᵉ) →
    contains-product-ideal-Commutative-Ringᵉ Kᵉ → UUωᵉ
  is-product-ideal-Commutative-Ringᵉ =
    is-product-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ Jᵉ
```

### The product of two ideals in a commutative ring

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) (Jᵉ : ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  generating-subset-product-ideal-Commutative-Ringᵉ :
    subset-Commutative-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Aᵉ
  generating-subset-product-ideal-Commutative-Ringᵉ =
    generating-subset-product-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ Jᵉ

  product-ideal-Commutative-Ringᵉ : ideal-Commutative-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Aᵉ
  product-ideal-Commutative-Ringᵉ =
    product-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ Jᵉ

  subset-product-ideal-Commutative-Ringᵉ :
    subset-Commutative-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Aᵉ
  subset-product-ideal-Commutative-Ringᵉ =
    subset-ideal-Commutative-Ringᵉ Aᵉ product-ideal-Commutative-Ringᵉ

  is-in-product-ideal-Commutative-Ringᵉ :
    type-Commutative-Ringᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-in-product-ideal-Commutative-Ringᵉ =
    is-in-ideal-Commutative-Ringᵉ Aᵉ product-ideal-Commutative-Ringᵉ

  is-closed-under-eq-product-ideal-Commutative-Ringᵉ :
    {xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ} → is-in-product-ideal-Commutative-Ringᵉ xᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-product-ideal-Commutative-Ringᵉ yᵉ
  is-closed-under-eq-product-ideal-Commutative-Ringᵉ =
    is-closed-under-eq-ideal-Commutative-Ringᵉ Aᵉ product-ideal-Commutative-Ringᵉ

  is-closed-under-eq-product-ideal-Commutative-Ring'ᵉ :
    {xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ} → is-in-product-ideal-Commutative-Ringᵉ yᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-product-ideal-Commutative-Ringᵉ xᵉ
  is-closed-under-eq-product-ideal-Commutative-Ring'ᵉ =
    is-closed-under-eq-ideal-Commutative-Ring'ᵉ Aᵉ product-ideal-Commutative-Ringᵉ

  contains-product-product-ideal-Commutative-Ringᵉ :
    contains-product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ product-ideal-Commutative-Ringᵉ
  contains-product-product-ideal-Commutative-Ringᵉ =
    contains-product-product-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ Jᵉ

  is-product-product-ideal-Commutative-Ringᵉ :
    is-product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ
      product-ideal-Commutative-Ringᵉ
      contains-product-product-ideal-Commutative-Ringᵉ
  is-product-product-ideal-Commutative-Ringᵉ =
    is-product-product-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ Jᵉ
```

## Properties

### The product of ideals preserves inequality of ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  (Kᵉ : ideal-Commutative-Ringᵉ l4ᵉ Aᵉ)
  (Lᵉ : ideal-Commutative-Ringᵉ l5ᵉ Aᵉ)
  where

  preserves-order-product-ideal-Commutative-Ringᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ →
    leq-ideal-Commutative-Ringᵉ Aᵉ Kᵉ Lᵉ →
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Kᵉ)
      ( product-ideal-Commutative-Ringᵉ Aᵉ Jᵉ Lᵉ)
  preserves-order-product-ideal-Commutative-Ringᵉ pᵉ qᵉ =
    is-product-product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Kᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ Jᵉ Lᵉ)
      ( λ xᵉ yᵉ uᵉ vᵉ →
        contains-product-product-ideal-Commutative-Ringᵉ Aᵉ Jᵉ Lᵉ _ _
          ( pᵉ xᵉ uᵉ)
          ( qᵉ yᵉ vᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  (Kᵉ : ideal-Commutative-Ringᵉ l4ᵉ Aᵉ)
  where

  preserves-order-left-product-ideal-Commutative-Ringᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ →
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Kᵉ)
      ( product-ideal-Commutative-Ringᵉ Aᵉ Jᵉ Kᵉ)
  preserves-order-left-product-ideal-Commutative-Ringᵉ pᵉ =
    preserves-order-product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ Kᵉ Kᵉ pᵉ
      ( refl-leq-ideal-Commutative-Ringᵉ Aᵉ Kᵉ)

  preserves-order-right-product-ideal-Commutative-Ringᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ Jᵉ Kᵉ →
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
      ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Kᵉ)
  preserves-order-right-product-ideal-Commutative-Ringᵉ =
    preserves-order-product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Iᵉ Jᵉ Kᵉ
      ( refl-leq-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
```

### The ideal generated by a product of two subsets is the product of the ideals generated by the two subsets

Inᵉ otherᵉ words,ᵉ weᵉ willᵉ showᵉ thatᵉ `(S)(Tᵉ) = (ST)`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Sᵉ : subset-Commutative-Ringᵉ l2ᵉ Aᵉ) (Tᵉ : subset-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  abstract
    forward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ :
      leq-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-subset-Commutative-Ringᵉ Aᵉ
          ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ))
        ( product-ideal-Commutative-Ringᵉ Aᵉ
          ( ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ)
          ( ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ))
    forward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ =
      is-ideal-generated-by-subset-ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
        ( product-ideal-Commutative-Ringᵉ Aᵉ
          ( ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ)
          ( ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ))
        ( λ xᵉ Hᵉ →
          apply-universal-property-trunc-Propᵉ Hᵉ
            ( subset-product-ideal-Commutative-Ringᵉ Aᵉ
              ( ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ)
              ( ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ)
              ( xᵉ))
            ( λ where
              ( sᵉ ,ᵉ tᵉ ,ᵉ reflᵉ) →
                contains-product-product-ideal-Commutative-Ringᵉ Aᵉ
                  ( ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ)
                  ( ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ)
                  ( pr1ᵉ sᵉ)
                  ( pr1ᵉ tᵉ)
                  ( contains-subset-ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ
                    ( pr1ᵉ sᵉ)
                    ( pr2ᵉ sᵉ))
                  ( contains-subset-ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ
                    ( pr1ᵉ tᵉ)
                    ( pr2ᵉ tᵉ))))

  left-backward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ :
    {xᵉ sᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ} →
    is-in-subset-Commutative-Ringᵉ Aᵉ Sᵉ sᵉ →
    (lᵉ : formal-combination-subset-Commutative-Ringᵉ Aᵉ Tᵉ) →
    is-in-ideal-subset-Commutative-Ringᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
      ( mul-Commutative-Ringᵉ Aᵉ
        ( mul-Commutative-Ringᵉ Aᵉ (mul-Commutative-Ringᵉ Aᵉ xᵉ sᵉ) yᵉ)
        ( ev-formal-combination-subset-Commutative-Ringᵉ Aᵉ Tᵉ lᵉ))
  left-backward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ
    Hᵉ nilᵉ =
    is-closed-under-eq-ideal-subset-Commutative-Ring'ᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
      ( contains-zero-ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ))
      ( right-zero-law-mul-Commutative-Ringᵉ Aᵉ _)
  left-backward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ
    {xᵉ} {sᵉ} {yᵉ} Hsᵉ
    ( consᵉ (uᵉ ,ᵉ (tᵉ ,ᵉ Htᵉ) ,ᵉ vᵉ) lᵉ) =
    is-closed-under-eq-ideal-subset-Commutative-Ring'ᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
      ( is-closed-under-addition-ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
        ( is-closed-under-eq-ideal-subset-Commutative-Ring'ᵉ Aᵉ
          ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
          ( is-closed-under-right-multiplication-ideal-Commutative-Ringᵉ Aᵉ
            ( ideal-subset-Commutative-Ringᵉ Aᵉ
              ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ))
            ( _)
            ( _)
            ( is-closed-under-left-multiplication-ideal-Commutative-Ringᵉ Aᵉ
              ( ideal-subset-Commutative-Ringᵉ Aᵉ
                ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ))
              ( mul-Commutative-Ringᵉ Aᵉ xᵉ uᵉ)
              ( mul-Commutative-Ringᵉ Aᵉ sᵉ tᵉ)
              ( contains-subset-ideal-subset-Commutative-Ringᵉ Aᵉ
                ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
                ( mul-Commutative-Ringᵉ Aᵉ sᵉ tᵉ)
                ( unit-trunc-Propᵉ (((sᵉ ,ᵉ Hsᵉ) ,ᵉ (tᵉ ,ᵉ Htᵉ) ,ᵉ reflᵉ))))))
          ( ( interchange-mul-mul-Commutative-Ringᵉ Aᵉ _ _ _ _) ∙ᵉ
            ( apᵉ
              ( mul-Commutative-Ring'ᵉ Aᵉ _)
              ( interchange-mul-mul-Commutative-Ringᵉ Aᵉ _ _ _ _))))
        ( left-backward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ
          Hsᵉ lᵉ))
      ( left-distributive-mul-add-Commutative-Ringᵉ Aᵉ _ _ _)

  right-backward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ :
    {uᵉ tᵉ vᵉ : type-Commutative-Ringᵉ Aᵉ} →
    is-in-subset-Commutative-Ringᵉ Aᵉ Tᵉ tᵉ →
    (kᵉ : formal-combination-subset-Commutative-Ringᵉ Aᵉ Sᵉ) →
    is-in-ideal-subset-Commutative-Ringᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
      ( mul-Commutative-Ringᵉ Aᵉ
        ( ev-formal-combination-subset-Commutative-Ringᵉ Aᵉ Sᵉ kᵉ)
        ( mul-Commutative-Ringᵉ Aᵉ (mul-Commutative-Ringᵉ Aᵉ uᵉ tᵉ) vᵉ))
  right-backward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ
    Htᵉ nilᵉ =
    is-closed-under-eq-ideal-subset-Commutative-Ring'ᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
      ( contains-zero-ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ))
      ( left-zero-law-mul-Commutative-Ringᵉ Aᵉ _)
  right-backward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ
    {uᵉ} {tᵉ} {vᵉ} Htᵉ
    ( consᵉ (xᵉ ,ᵉ (sᵉ ,ᵉ Hsᵉ) ,ᵉ yᵉ) kᵉ) =
    is-closed-under-eq-ideal-subset-Commutative-Ring'ᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
      ( is-closed-under-addition-ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
        ( is-closed-under-eq-ideal-subset-Commutative-Ring'ᵉ Aᵉ
          ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
          ( is-closed-under-right-multiplication-ideal-Commutative-Ringᵉ Aᵉ
            ( ideal-subset-Commutative-Ringᵉ Aᵉ
              ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ))
            ( _)
            ( _)
            ( is-closed-under-left-multiplication-ideal-Commutative-Ringᵉ Aᵉ
              ( ideal-subset-Commutative-Ringᵉ Aᵉ
                ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ))
              ( mul-Commutative-Ringᵉ Aᵉ xᵉ uᵉ)
              ( mul-Commutative-Ringᵉ Aᵉ sᵉ tᵉ)
              ( contains-subset-ideal-subset-Commutative-Ringᵉ Aᵉ
                ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
                ( mul-Commutative-Ringᵉ Aᵉ sᵉ tᵉ)
                ( unit-trunc-Propᵉ (((sᵉ ,ᵉ Hsᵉ) ,ᵉ (tᵉ ,ᵉ Htᵉ) ,ᵉ reflᵉ))))))
          ( ( interchange-mul-mul-Commutative-Ringᵉ Aᵉ _ _ _ _) ∙ᵉ
            ( apᵉ
              ( mul-Commutative-Ring'ᵉ Aᵉ _)
              ( interchange-mul-mul-Commutative-Ringᵉ Aᵉ _ _ _ _))))
        ( right-backward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ
          Htᵉ kᵉ))
      ( right-distributive-mul-add-Commutative-Ringᵉ Aᵉ _ _ _)

  backward-inclusion-preserves-product-ideal-subset-Commutative-Ring'ᵉ :
    ( sᵉ tᵉ : type-Commutative-Ringᵉ Aᵉ)
    ( kᵉ : subset-ideal-subset-Commutative-Ring'ᵉ Aᵉ Sᵉ sᵉ)
    ( lᵉ : subset-ideal-subset-Commutative-Ring'ᵉ Aᵉ Tᵉ tᵉ) →
    is-in-ideal-subset-Commutative-Ringᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
      ( mul-Commutative-Ringᵉ Aᵉ sᵉ tᵉ)
  backward-inclusion-preserves-product-ideal-subset-Commutative-Ring'ᵉ ._ tᵉ
    ( nilᵉ ,ᵉ reflᵉ) lᵉ =
    is-closed-under-eq-ideal-subset-Commutative-Ring'ᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
      ( contains-zero-ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ))
      ( left-zero-law-mul-Commutative-Ringᵉ Aᵉ tᵉ)
  backward-inclusion-preserves-product-ideal-subset-Commutative-Ring'ᵉ ._ ._
    ( consᵉ xᵉ kᵉ ,ᵉ reflᵉ) (nilᵉ ,ᵉ reflᵉ) =
    is-closed-under-eq-ideal-subset-Commutative-Ring'ᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
      ( contains-zero-ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ))
      ( right-zero-law-mul-Commutative-Ringᵉ Aᵉ _)
  backward-inclusion-preserves-product-ideal-subset-Commutative-Ring'ᵉ ._ ._
    ( consᵉ (xᵉ ,ᵉ (sᵉ ,ᵉ Hsᵉ) ,ᵉ yᵉ) kᵉ ,ᵉ reflᵉ) (consᵉ (uᵉ ,ᵉ (tᵉ ,ᵉ Htᵉ) ,ᵉ vᵉ) lᵉ ,ᵉ reflᵉ) =
    is-closed-under-eq-ideal-subset-Commutative-Ring'ᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
      ( is-closed-under-addition-ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
        ( is-closed-under-addition-ideal-subset-Commutative-Ringᵉ Aᵉ
          ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
          ( is-closed-under-eq-ideal-subset-Commutative-Ring'ᵉ Aᵉ
            ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
            ( is-closed-under-right-multiplication-ideal-Commutative-Ringᵉ Aᵉ
              ( ideal-subset-Commutative-Ringᵉ Aᵉ
                ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ))
              ( _)
              ( _)
              ( is-closed-under-left-multiplication-ideal-Commutative-Ringᵉ Aᵉ
                ( ideal-subset-Commutative-Ringᵉ Aᵉ
                  ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ))
                ( mul-Commutative-Ringᵉ Aᵉ xᵉ uᵉ)
                ( mul-Commutative-Ringᵉ Aᵉ sᵉ tᵉ)
                ( contains-subset-ideal-subset-Commutative-Ringᵉ Aᵉ
                  ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
                  ( mul-Commutative-Ringᵉ Aᵉ sᵉ tᵉ)
                  ( unit-trunc-Propᵉ (((sᵉ ,ᵉ Hsᵉ) ,ᵉ (tᵉ ,ᵉ Htᵉ) ,ᵉ reflᵉ))))))
            ( ( interchange-mul-mul-Commutative-Ringᵉ Aᵉ _ _ _ _) ∙ᵉ
              ( apᵉ
                ( mul-Commutative-Ring'ᵉ Aᵉ _)
                ( interchange-mul-mul-Commutative-Ringᵉ Aᵉ _ _ _ _))))
          ( left-backward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ
            Hsᵉ lᵉ))
        ( is-closed-under-addition-ideal-subset-Commutative-Ringᵉ Aᵉ
          ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
          ( right-backward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ
            Htᵉ kᵉ)
          ( backward-inclusion-preserves-product-ideal-subset-Commutative-Ring'ᵉ
            ( _)
            ( _)
            ( kᵉ ,ᵉ reflᵉ)
            ( lᵉ ,ᵉ reflᵉ))))
      ( bidistributive-mul-add-Commutative-Ringᵉ Aᵉ _ _ _ _)

  backward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ)
        ( ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ))
      ( ideal-subset-Commutative-Ringᵉ Aᵉ (product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ))
  backward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ =
    is-product-product-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ)
      ( ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ)
      ( ideal-subset-Commutative-Ringᵉ Aᵉ (product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ))
      ( λ sᵉ tᵉ pᵉ qᵉ →
        apply-twice-universal-property-trunc-Propᵉ pᵉ qᵉ
          ( subset-ideal-subset-Commutative-Ringᵉ Aᵉ
            ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
            ( mul-Commutative-Ringᵉ Aᵉ sᵉ tᵉ))
          ( backward-inclusion-preserves-product-ideal-subset-Commutative-Ring'ᵉ
            sᵉ tᵉ))

  preserves-product-ideal-subset-Commutative-Ringᵉ :
    ideal-subset-Commutative-Ringᵉ Aᵉ (product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ) ＝ᵉ
    product-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ)
      ( ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ)
  preserves-product-ideal-subset-Commutative-Ringᵉ =
    eq-has-same-elements-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-subset-Commutative-Ringᵉ Aᵉ (product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ))
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ)
        ( ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ))
      ( λ xᵉ →
        forward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ xᵉ ,ᵉ
        backward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ xᵉ)
```

### `(SI) ＝ (S)I`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Sᵉ : subset-Commutative-Ringᵉ l2ᵉ Aᵉ) (Iᵉ : ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  forward-inclusion-left-preserves-product-ideal-subset-Commutative-Ringᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)))
      ( product-ideal-Commutative-Ringᵉ Aᵉ (ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ) Iᵉ)
  forward-inclusion-left-preserves-product-ideal-subset-Commutative-Ringᵉ =
    transitive-leq-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)))
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ)
        ( ideal-subset-Commutative-Ringᵉ Aᵉ (subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)))
      ( product-ideal-Commutative-Ringᵉ Aᵉ (ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ) Iᵉ)
      ( preserves-order-right-product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ)
        ( ideal-subset-Commutative-Ringᵉ Aᵉ (subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ))
        ( Iᵉ)
        ( forward-inclusion-idempotent-ideal-subset-Commutative-Ringᵉ Aᵉ Iᵉ))
      ( forward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ
        ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ))

  backward-inclusion-left-preserves-product-ideal-subset-Commutative-Ringᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ (ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ) Iᵉ)
      ( ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)))
  backward-inclusion-left-preserves-product-ideal-subset-Commutative-Ringᵉ =
    transitive-leq-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ (ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ) Iᵉ)
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ)
        ( ideal-subset-Commutative-Ringᵉ Aᵉ (subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)))
      ( ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)))
      ( backward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ
        ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ))
      ( preserves-order-right-product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ)
        ( Iᵉ)
        ( ideal-subset-Commutative-Ringᵉ Aᵉ (subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ))
        ( backward-inclusion-idempotent-ideal-subset-Commutative-Ringᵉ Aᵉ Iᵉ))

  left-preserves-product-ideal-subset-Commutative-Ringᵉ :
    ideal-subset-Commutative-Ringᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ
        ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)) ＝ᵉ
    product-ideal-Commutative-Ringᵉ Aᵉ (ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ) Iᵉ
  left-preserves-product-ideal-subset-Commutative-Ringᵉ =
    eq-has-same-elements-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)))
      ( product-ideal-Commutative-Ringᵉ Aᵉ (ideal-subset-Commutative-Ringᵉ Aᵉ Sᵉ) Iᵉ)
      ( λ xᵉ →
        forward-inclusion-left-preserves-product-ideal-subset-Commutative-Ringᵉ
          xᵉ ,ᵉ
        backward-inclusion-left-preserves-product-ideal-subset-Commutative-Ringᵉ
          xᵉ)
```

### `(IT) ＝ I(T)`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) (Tᵉ : subset-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  forward-inclusion-right-preserves-product-ideal-subset-Commutative-Ringᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( Tᵉ)))
      ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ))
  forward-inclusion-right-preserves-product-ideal-subset-Commutative-Ringᵉ =
    transitive-leq-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( Tᵉ)))
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-subset-Commutative-Ringᵉ Aᵉ (subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ))
        ( ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ))
      ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ))
      ( preserves-order-left-product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-subset-Commutative-Ringᵉ Aᵉ (subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ))
        ( Iᵉ)
        ( ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ)
        ( forward-inclusion-idempotent-ideal-subset-Commutative-Ringᵉ Aᵉ Iᵉ))
      ( forward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ Aᵉ
        ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( Tᵉ))

  backward-inclusion-right-preserves-product-ideal-subset-Commutative-Ringᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ))
      ( ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( Tᵉ)))
  backward-inclusion-right-preserves-product-ideal-subset-Commutative-Ringᵉ =
    transitive-leq-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ))
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-subset-Commutative-Ringᵉ Aᵉ (subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ))
        ( ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ))
      ( ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( Tᵉ)))
      ( backward-inclusion-preserves-product-ideal-subset-Commutative-Ringᵉ Aᵉ
        ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( Tᵉ))
      ( preserves-order-left-product-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( ideal-subset-Commutative-Ringᵉ Aᵉ (subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ))
        ( ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ)
        ( backward-inclusion-idempotent-ideal-subset-Commutative-Ringᵉ Aᵉ Iᵉ))

  right-preserves-product-ideal-subset-Commutative-Ringᵉ :
    ideal-subset-Commutative-Ringᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ
        ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( Tᵉ)) ＝ᵉ
    product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ)
  right-preserves-product-ideal-subset-Commutative-Ringᵉ =
    eq-has-same-elements-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( Tᵉ)))
      ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (ideal-subset-Commutative-Ringᵉ Aᵉ Tᵉ))
      ( λ xᵉ →
        forward-inclusion-right-preserves-product-ideal-subset-Commutative-Ringᵉ
          xᵉ ,ᵉ
        backward-inclusion-right-preserves-product-ideal-subset-Commutative-Ringᵉ
          xᵉ)
```

### The product of ideals is assiciative

Givenᵉ threeᵉ idealsᵉ `I`,ᵉ `J`,ᵉ andᵉ `K`,ᵉ weᵉ haveᵉ thatᵉ

```text
  (IJ)Kᵉ ＝ᵉ ((generating-subset-product-ideal-Commutative-Ringᵉ Iᵉ J)Kᵉ)
        ＝ᵉ (I(generating-subset-product-ideal-Commutative-Ringᵉ Jᵉ Kᵉ))
        ＝ᵉ I(JK).ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  (Kᵉ : ideal-Commutative-Ringᵉ l4ᵉ Aᵉ)
  where

  forward-inclusion-associative-product-ideal-Commutative-Ringᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
        ( Kᵉ))
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( product-ideal-Commutative-Ringᵉ Aᵉ Jᵉ Kᵉ))
  forward-inclusion-associative-product-ideal-Commutative-Ringᵉ xᵉ Hᵉ =
    forward-inclusion-right-preserves-product-ideal-subset-Commutative-Ringᵉ Aᵉ Iᵉ
      ( generating-subset-product-ideal-Commutative-Ringᵉ Aᵉ Jᵉ Kᵉ)
      ( xᵉ)
      ( preserves-order-ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ
          ( product-subset-Commutative-Ringᵉ Aᵉ
            ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
            ( subset-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Kᵉ))
        ( product-subset-Commutative-Ringᵉ Aᵉ
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( product-subset-Commutative-Ringᵉ Aᵉ
            ( subset-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
            ( subset-ideal-Commutative-Ringᵉ Aᵉ Kᵉ)))
        ( forward-inclusion-associative-product-subset-Commutative-Ringᵉ Aᵉ
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Kᵉ))
        ( xᵉ)
        ( backward-inclusion-left-preserves-product-ideal-subset-Commutative-Ringᵉ
          ( Aᵉ)
          ( generating-subset-product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
          ( Kᵉ)
          ( xᵉ)
          ( Hᵉ)))

  backward-inclusion-associative-product-ideal-Commutative-Ringᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
        ( product-ideal-Commutative-Ringᵉ Aᵉ Jᵉ Kᵉ))
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
        ( Kᵉ))
  backward-inclusion-associative-product-ideal-Commutative-Ringᵉ xᵉ Hᵉ =
    forward-inclusion-left-preserves-product-ideal-subset-Commutative-Ringᵉ Aᵉ
      ( generating-subset-product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
      ( Kᵉ)
      ( xᵉ)
      ( preserves-order-ideal-subset-Commutative-Ringᵉ Aᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( product-subset-Commutative-Ringᵉ Aᵉ
            ( subset-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
            ( subset-ideal-Commutative-Ringᵉ Aᵉ Kᵉ)))
        ( product-subset-Commutative-Ringᵉ Aᵉ
          ( product-subset-Commutative-Ringᵉ Aᵉ
            ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
            ( subset-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Kᵉ))
        ( backward-inclusion-associative-product-subset-Commutative-Ringᵉ Aᵉ
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Kᵉ))
        ( xᵉ)
        ( backward-inclusion-right-preserves-product-ideal-subset-Commutative-Ringᵉ
          ( Aᵉ)
          ( Iᵉ)
          ( generating-subset-product-ideal-Commutative-Ringᵉ Aᵉ Jᵉ Kᵉ)
          ( xᵉ)
          ( Hᵉ)))

  associative-product-ideal-Commutative-Ringᵉ :
    product-ideal-Commutative-Ringᵉ Aᵉ (product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ) Kᵉ ＝ᵉ
    product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (product-ideal-Commutative-Ringᵉ Aᵉ Jᵉ Kᵉ)
  associative-product-ideal-Commutative-Ringᵉ =
    eq-has-same-elements-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
        ( Kᵉ))
      ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
        ( product-ideal-Commutative-Ringᵉ Aᵉ Jᵉ Kᵉ))
      ( λ xᵉ →
        forward-inclusion-associative-product-ideal-Commutative-Ringᵉ xᵉ ,ᵉ
        backward-inclusion-associative-product-ideal-Commutative-Ringᵉ xᵉ)
```