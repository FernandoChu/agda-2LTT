# Cartesian products of concrete groups

```agda
module group-theory.cartesian-products-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.1-typesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.groupsᵉ

open import higher-group-theory.cartesian-products-higher-groupsᵉ
open import higher-group-theory.higher-groupsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Theᵉ cartesianᵉ productᵉ ofᵉ twoᵉ concreteᵉ groupsᵉ isᵉ definedᵉ asᵉ theᵉ cartesianᵉ productᵉ
ofᵉ theirᵉ underlyingᵉ `∞-group`ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Rᵉ : Concrete-Groupᵉ l2ᵉ)
  where

  product-Concrete-Groupᵉ : Concrete-Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ product-Concrete-Groupᵉ =
    product-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( ∞-group-Concrete-Groupᵉ Rᵉ)
  pr2ᵉ product-Concrete-Groupᵉ =
    is-set-equivᵉ
      ( type-∞-Groupᵉ (pr1ᵉ Gᵉ) ×ᵉ
        type-∞-Groupᵉ (pr1ᵉ Rᵉ))
      ( equiv-type-∞-Group-product-∞-Groupᵉ
          ( ∞-group-Concrete-Groupᵉ Gᵉ)
          ( ∞-group-Concrete-Groupᵉ Rᵉ))
      ( is-set-productᵉ
          ( is-set-type-Concrete-Groupᵉ Gᵉ)
          ( is-set-type-Concrete-Groupᵉ Rᵉ))

  ∞-group-product-Concrete-Groupᵉ : ∞-Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  ∞-group-product-Concrete-Groupᵉ = pr1ᵉ product-Concrete-Groupᵉ

  classifying-pointed-type-product-Concrete-Groupᵉ : Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  classifying-pointed-type-product-Concrete-Groupᵉ =
    classifying-pointed-type-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  classifying-type-product-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  classifying-type-product-Concrete-Groupᵉ =
    classifying-type-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  shape-product-Concrete-Groupᵉ : classifying-type-product-Concrete-Groupᵉ
  shape-product-Concrete-Groupᵉ =
    shape-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  is-0-connected-classifying-type-product-Concrete-Groupᵉ :
    is-0-connectedᵉ classifying-type-product-Concrete-Groupᵉ
  is-0-connected-classifying-type-product-Concrete-Groupᵉ =
    is-0-connected-classifying-type-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  mere-eq-classifying-type-product-Concrete-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-product-Concrete-Groupᵉ) → mere-eqᵉ Xᵉ Yᵉ
  mere-eq-classifying-type-product-Concrete-Groupᵉ =
    mere-eq-classifying-type-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  elim-prop-classifying-type-product-Concrete-Groupᵉ :
    {l2ᵉ : Level} (Pᵉ : classifying-type-product-Concrete-Groupᵉ → Propᵉ l2ᵉ) →
    type-Propᵉ (Pᵉ shape-product-Concrete-Groupᵉ) →
    ((Xᵉ : classifying-type-product-Concrete-Groupᵉ) → type-Propᵉ (Pᵉ Xᵉ))
  elim-prop-classifying-type-product-Concrete-Groupᵉ =
    elim-prop-classifying-type-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  type-product-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-product-Concrete-Groupᵉ = type-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  is-set-type-product-Concrete-Groupᵉ : is-setᵉ type-product-Concrete-Groupᵉ
  is-set-type-product-Concrete-Groupᵉ = pr2ᵉ product-Concrete-Groupᵉ

  set-product-Concrete-Groupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-product-Concrete-Groupᵉ =
    pairᵉ type-product-Concrete-Groupᵉ is-set-type-product-Concrete-Groupᵉ

  abstract
    is-1-type-classifying-type-product-Concrete-Groupᵉ :
      is-truncᵉ one-𝕋ᵉ classifying-type-product-Concrete-Groupᵉ
    is-1-type-classifying-type-product-Concrete-Groupᵉ Xᵉ Yᵉ =
      apply-universal-property-trunc-Propᵉ
        ( mere-eq-classifying-type-product-Concrete-Groupᵉ
            shape-product-Concrete-Groupᵉ
            Xᵉ)
        ( is-set-Propᵉ (Idᵉ Xᵉ Yᵉ))
        ( λ where
          reflᵉ →
            apply-universal-property-trunc-Propᵉ
              ( mere-eq-classifying-type-product-Concrete-Groupᵉ
                  shape-product-Concrete-Groupᵉ
                  Yᵉ)
              ( is-set-Propᵉ (Idᵉ shape-product-Concrete-Groupᵉ Yᵉ))
              ( λ where reflᵉ → is-set-type-product-Concrete-Groupᵉ))

  classifying-1-type-product-Concrete-Groupᵉ : Truncated-Typeᵉ (l1ᵉ ⊔ l2ᵉ) one-𝕋ᵉ
  classifying-1-type-product-Concrete-Groupᵉ =
    pairᵉ
      classifying-type-product-Concrete-Groupᵉ
      is-1-type-classifying-type-product-Concrete-Groupᵉ

  Id-product-BG-Setᵉ :
    (Xᵉ Yᵉ : classifying-type-product-Concrete-Groupᵉ) → Setᵉ (l1ᵉ ⊔ l2ᵉ)
  Id-product-BG-Setᵉ Xᵉ Yᵉ = Id-Setᵉ classifying-1-type-product-Concrete-Groupᵉ Xᵉ Yᵉ

  unit-product-Concrete-Groupᵉ : type-product-Concrete-Groupᵉ
  unit-product-Concrete-Groupᵉ = unit-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  mul-product-Concrete-Groupᵉ :
    (xᵉ yᵉ : type-product-Concrete-Groupᵉ) → type-product-Concrete-Groupᵉ
  mul-product-Concrete-Groupᵉ = mul-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  mul-product-Concrete-Group'ᵉ :
    (xᵉ yᵉ : type-product-Concrete-Groupᵉ) → type-product-Concrete-Groupᵉ
  mul-product-Concrete-Group'ᵉ xᵉ yᵉ = mul-product-Concrete-Groupᵉ yᵉ xᵉ

  associative-mul-product-Concrete-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-product-Concrete-Groupᵉ) →
    Idᵉ
      (mul-product-Concrete-Groupᵉ (mul-product-Concrete-Groupᵉ xᵉ yᵉ) zᵉ)
      (mul-product-Concrete-Groupᵉ xᵉ (mul-product-Concrete-Groupᵉ yᵉ zᵉ))
  associative-mul-product-Concrete-Groupᵉ =
    associative-mul-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  left-unit-law-mul-product-Concrete-Groupᵉ :
    (xᵉ : type-product-Concrete-Groupᵉ) →
    Idᵉ (mul-product-Concrete-Groupᵉ unit-product-Concrete-Groupᵉ xᵉ) xᵉ
  left-unit-law-mul-product-Concrete-Groupᵉ =
    left-unit-law-mul-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  right-unit-law-mul-product-Concrete-Groupᵉ :
    (yᵉ : type-product-Concrete-Groupᵉ) →
    Idᵉ (mul-product-Concrete-Groupᵉ yᵉ unit-product-Concrete-Groupᵉ) yᵉ
  right-unit-law-mul-product-Concrete-Groupᵉ =
    right-unit-law-mul-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  coherence-unit-laws-mul-product-Concrete-Groupᵉ :
    Idᵉ
      ( left-unit-law-mul-product-Concrete-Groupᵉ unit-product-Concrete-Groupᵉ)
      ( right-unit-law-mul-product-Concrete-Groupᵉ unit-product-Concrete-Groupᵉ)
  coherence-unit-laws-mul-product-Concrete-Groupᵉ =
    coherence-unit-laws-mul-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  inv-product-Concrete-Groupᵉ :
    type-product-Concrete-Groupᵉ → type-product-Concrete-Groupᵉ
  inv-product-Concrete-Groupᵉ = inv-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  left-inverse-law-mul-product-Concrete-Groupᵉ :
    (xᵉ : type-product-Concrete-Groupᵉ) →
    Idᵉ
      ( mul-product-Concrete-Groupᵉ (inv-product-Concrete-Groupᵉ xᵉ) xᵉ)
      ( unit-product-Concrete-Groupᵉ)
  left-inverse-law-mul-product-Concrete-Groupᵉ =
    left-inverse-law-mul-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  right-inverse-law-mul-product-Concrete-Groupᵉ :
    (xᵉ : type-product-Concrete-Groupᵉ) →
    Idᵉ
      ( mul-product-Concrete-Groupᵉ xᵉ (inv-product-Concrete-Groupᵉ xᵉ))
      ( unit-product-Concrete-Groupᵉ)
  right-inverse-law-mul-product-Concrete-Groupᵉ =
    right-inverse-law-mul-∞-Groupᵉ ∞-group-product-Concrete-Groupᵉ

  group-product-Concrete-Groupᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (pr1ᵉ group-product-Concrete-Groupᵉ) =
    set-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ group-product-Concrete-Groupᵉ)) =
    mul-product-Concrete-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ group-product-Concrete-Groupᵉ)) =
    associative-mul-product-Concrete-Groupᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ group-product-Concrete-Groupᵉ)) =
    unit-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ group-product-Concrete-Groupᵉ))) =
    left-unit-law-mul-product-Concrete-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ group-product-Concrete-Groupᵉ))) =
    right-unit-law-mul-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ group-product-Concrete-Groupᵉ)) =
    inv-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ group-product-Concrete-Groupᵉ))) =
    left-inverse-law-mul-product-Concrete-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ group-product-Concrete-Groupᵉ))) =
    right-inverse-law-mul-product-Concrete-Groupᵉ

  op-group-product-Concrete-Groupᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (pr1ᵉ op-group-product-Concrete-Groupᵉ) =
    set-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ op-group-product-Concrete-Groupᵉ)) =
    mul-product-Concrete-Group'ᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ op-group-product-Concrete-Groupᵉ)) xᵉ yᵉ zᵉ =
    invᵉ (associative-mul-product-Concrete-Groupᵉ zᵉ yᵉ xᵉ)
  pr1ᵉ (pr1ᵉ (pr2ᵉ op-group-product-Concrete-Groupᵉ)) =
    unit-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ op-group-product-Concrete-Groupᵉ))) =
    right-unit-law-mul-product-Concrete-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ op-group-product-Concrete-Groupᵉ))) =
    left-unit-law-mul-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ op-group-product-Concrete-Groupᵉ)) =
    inv-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ op-group-product-Concrete-Groupᵉ))) =
    right-inverse-law-mul-product-Concrete-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ op-group-product-Concrete-Groupᵉ))) =
    left-inverse-law-mul-product-Concrete-Groupᵉ
```

## Property

```agda
  equiv-type-Concrete-Group-product-Concrete-Groupᵉ :
    type-product-Concrete-Groupᵉ ≃ᵉ
    ( type-Concrete-Groupᵉ Gᵉ ×ᵉ type-Concrete-Groupᵉ Rᵉ)
  equiv-type-Concrete-Group-product-Concrete-Groupᵉ =
    equiv-type-∞-Group-product-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( ∞-group-Concrete-Groupᵉ Rᵉ)
```