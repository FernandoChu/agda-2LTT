# Products of subsets of rings

```agda
module ring-theory.products-subsets-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.subtypesᵉ
open import foundation.unions-subtypesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.ringsᵉ
open import ring-theory.subsets-ringsᵉ
```

</details>

## Idea

Theᵉ **product**ᵉ ofᵉ twoᵉ [subsets](ring-theory.subsets-rings.mdᵉ) `S`ᵉ andᵉ `T`ᵉ ofᵉ aᵉ
[ring](ring-theory.rings.mdᵉ) `R`ᵉ consistsᵉ ofᵉ elementsᵉ ofᵉ theᵉ formᵉ `st`ᵉ where
`sᵉ ∈ᵉ S`ᵉ andᵉ `tᵉ ∈ᵉ T`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Ringᵉ l1ᵉ)
  (Sᵉ : subset-Ringᵉ l2ᵉ Aᵉ) (Tᵉ : subset-Ringᵉ l3ᵉ Aᵉ)
  where

  product-subset-Ringᵉ : subset-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Aᵉ
  product-subset-Ringᵉ xᵉ =
    trunc-Propᵉ
      ( Σᵉ ( type-subtypeᵉ Sᵉ)
          ( λ sᵉ →
            Σᵉ ( type-subtypeᵉ Tᵉ)
              ( λ tᵉ → xᵉ ＝ᵉ mul-Ringᵉ Aᵉ (pr1ᵉ sᵉ) (pr1ᵉ tᵉ))))
```

## Properties

### Products distribute over unions of families of subsets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Ringᵉ l1ᵉ) (Sᵉ : subset-Ringᵉ l2ᵉ Aᵉ)
  {Iᵉ : UUᵉ l3ᵉ} (Tᵉ : Iᵉ → subset-Ringᵉ l4ᵉ Aᵉ)
  where

  abstract
    forward-inclusion-distributive-product-union-family-of-subsets-Ringᵉ :
      product-subset-Ringᵉ Aᵉ Sᵉ (union-family-of-subtypesᵉ Tᵉ) ⊆ᵉ
      union-family-of-subtypesᵉ (λ iᵉ → product-subset-Ringᵉ Aᵉ Sᵉ (Tᵉ iᵉ))
    forward-inclusion-distributive-product-union-family-of-subsets-Ringᵉ xᵉ pᵉ =
      apply-universal-property-trunc-Propᵉ pᵉ
        ( union-family-of-subtypesᵉ (λ iᵉ → product-subset-Ringᵉ Aᵉ Sᵉ (Tᵉ iᵉ)) xᵉ)
        ( λ where
          ( ( sᵉ ,ᵉ Hsᵉ) ,ᵉ (tᵉ ,ᵉ Htᵉ) ,ᵉ reflᵉ) →
            apply-universal-property-trunc-Propᵉ Htᵉ
              ( union-family-of-subtypesᵉ
                ( λ iᵉ → product-subset-Ringᵉ Aᵉ Sᵉ (Tᵉ iᵉ))
                ( xᵉ))
              ( λ (iᵉ ,ᵉ Ht'ᵉ) →
                unit-trunc-Propᵉ
                  ( iᵉ ,ᵉ unit-trunc-Propᵉ ((sᵉ ,ᵉ Hsᵉ) ,ᵉ (tᵉ ,ᵉ Ht'ᵉ) ,ᵉ reflᵉ))))

  abstract
    backward-inclusion-distributive-product-union-family-of-subsets-Ringᵉ :
      union-family-of-subtypesᵉ (λ iᵉ → product-subset-Ringᵉ Aᵉ Sᵉ (Tᵉ iᵉ)) ⊆ᵉ
      product-subset-Ringᵉ Aᵉ Sᵉ (union-family-of-subtypesᵉ Tᵉ)
    backward-inclusion-distributive-product-union-family-of-subsets-Ringᵉ xᵉ pᵉ =
      apply-universal-property-trunc-Propᵉ pᵉ
        ( product-subset-Ringᵉ Aᵉ Sᵉ (union-family-of-subtypesᵉ Tᵉ) xᵉ)
        ( λ (iᵉ ,ᵉ uᵉ) →
          apply-universal-property-trunc-Propᵉ uᵉ
            ( product-subset-Ringᵉ Aᵉ Sᵉ (union-family-of-subtypesᵉ Tᵉ) xᵉ)
            ( λ where
              ( ( sᵉ ,ᵉ Hsᵉ) ,ᵉ (tᵉ ,ᵉ Htᵉ) ,ᵉ reflᵉ) →
                unit-trunc-Propᵉ
                  ( (sᵉ ,ᵉ Hsᵉ) ,ᵉ (tᵉ ,ᵉ unit-trunc-Propᵉ (iᵉ ,ᵉ Htᵉ)) ,ᵉ reflᵉ)))

  distributive-product-union-family-of-subsets-Ringᵉ :
    product-subset-Ringᵉ Aᵉ Sᵉ (union-family-of-subtypesᵉ Tᵉ) ＝ᵉ
    union-family-of-subtypesᵉ (λ iᵉ → product-subset-Ringᵉ Aᵉ Sᵉ (Tᵉ iᵉ))
  distributive-product-union-family-of-subsets-Ringᵉ =
    antisymmetric-leq-subtypeᵉ
      ( product-subset-Ringᵉ Aᵉ Sᵉ (union-family-of-subtypesᵉ Tᵉ))
      ( union-family-of-subtypesᵉ (λ iᵉ → product-subset-Ringᵉ Aᵉ Sᵉ (Tᵉ iᵉ)))
      ( forward-inclusion-distributive-product-union-family-of-subsets-Ringᵉ)
      ( backward-inclusion-distributive-product-union-family-of-subsets-Ringᵉ)
```

### The product of subsets of commutative rings is associative

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Ringᵉ l1ᵉ)
  (Rᵉ : subset-Ringᵉ l2ᵉ Aᵉ)
  (Sᵉ : subset-Ringᵉ l3ᵉ Aᵉ)
  (Tᵉ : subset-Ringᵉ l4ᵉ Aᵉ)
  where

  abstract
    forward-inclusion-associative-product-subset-Ringᵉ :
      ( product-subset-Ringᵉ Aᵉ
        ( product-subset-Ringᵉ Aᵉ Rᵉ Sᵉ)
        ( Tᵉ)) ⊆ᵉ
      ( product-subset-Ringᵉ Aᵉ
        ( Rᵉ)
        ( product-subset-Ringᵉ Aᵉ Sᵉ Tᵉ))
    forward-inclusion-associative-product-subset-Ringᵉ xᵉ Hᵉ =
      apply-universal-property-trunc-Propᵉ Hᵉ
        ( product-subset-Ringᵉ Aᵉ Rᵉ
          ( product-subset-Ringᵉ Aᵉ Sᵉ Tᵉ)
          ( xᵉ))
        ( λ where
          ( ( uᵉ ,ᵉ Kᵉ) ,ᵉ (tᵉ ,ᵉ Htᵉ) ,ᵉ reflᵉ) →
            apply-universal-property-trunc-Propᵉ Kᵉ
              ( product-subset-Ringᵉ Aᵉ Rᵉ
                ( product-subset-Ringᵉ Aᵉ Sᵉ Tᵉ)
                ( _))
              ( λ where
                ( ( rᵉ ,ᵉ Hrᵉ) ,ᵉ (sᵉ ,ᵉ Hsᵉ) ,ᵉ reflᵉ) →
                  unit-trunc-Propᵉ
                    ( ( rᵉ ,ᵉ Hrᵉ) ,ᵉ
                      ( ( mul-Ringᵉ Aᵉ sᵉ tᵉ) ,ᵉ
                        ( unit-trunc-Propᵉ ((sᵉ ,ᵉ Hsᵉ) ,ᵉ (tᵉ ,ᵉ Htᵉ) ,ᵉ reflᵉ))) ,ᵉ
                      ( associative-mul-Ringᵉ Aᵉ rᵉ sᵉ tᵉ))))

  abstract
    backward-inclusion-associative-product-subset-Ringᵉ :
      ( product-subset-Ringᵉ Aᵉ
        ( Rᵉ)
        ( product-subset-Ringᵉ Aᵉ Sᵉ Tᵉ)) ⊆ᵉ
      ( product-subset-Ringᵉ Aᵉ
        ( product-subset-Ringᵉ Aᵉ Rᵉ Sᵉ)
        ( Tᵉ))
    backward-inclusion-associative-product-subset-Ringᵉ xᵉ Hᵉ =
      apply-universal-property-trunc-Propᵉ Hᵉ
        ( product-subset-Ringᵉ Aᵉ
          ( product-subset-Ringᵉ Aᵉ Rᵉ Sᵉ)
          ( Tᵉ)
          ( xᵉ))
        ( λ where
          ( ( rᵉ ,ᵉ Hrᵉ) ,ᵉ (vᵉ ,ᵉ Kᵉ) ,ᵉ reflᵉ) →
            apply-universal-property-trunc-Propᵉ Kᵉ
              ( product-subset-Ringᵉ Aᵉ
                ( product-subset-Ringᵉ Aᵉ Rᵉ Sᵉ)
                ( Tᵉ)
                ( _))
              ( λ where
                ( ( sᵉ ,ᵉ Hsᵉ) ,ᵉ (tᵉ ,ᵉ Htᵉ) ,ᵉ reflᵉ) →
                  unit-trunc-Propᵉ
                    ( ( ( mul-Ringᵉ Aᵉ rᵉ sᵉ) ,ᵉ
                        ( unit-trunc-Propᵉ ((rᵉ ,ᵉ Hrᵉ) ,ᵉ (sᵉ ,ᵉ Hsᵉ) ,ᵉ reflᵉ))) ,ᵉ
                      ( tᵉ ,ᵉ Htᵉ) ,ᵉ
                      ( invᵉ (associative-mul-Ringᵉ Aᵉ rᵉ sᵉ tᵉ)))))

  associative-product-subset-Ringᵉ :
    product-subset-Ringᵉ Aᵉ
      ( product-subset-Ringᵉ Aᵉ Rᵉ Sᵉ)
      ( Tᵉ) ＝ᵉ
    product-subset-Ringᵉ Aᵉ
      ( Rᵉ)
      ( product-subset-Ringᵉ Aᵉ Sᵉ Tᵉ)
  associative-product-subset-Ringᵉ =
    eq-has-same-elements-subtypeᵉ
      ( product-subset-Ringᵉ Aᵉ
        ( product-subset-Ringᵉ Aᵉ Rᵉ Sᵉ)
        ( Tᵉ))
      ( product-subset-Ringᵉ Aᵉ
        ( Rᵉ)
        ( product-subset-Ringᵉ Aᵉ Sᵉ Tᵉ))
      ( λ xᵉ →
        forward-inclusion-associative-product-subset-Ringᵉ xᵉ ,ᵉ
        backward-inclusion-associative-product-subset-Ringᵉ xᵉ)
```