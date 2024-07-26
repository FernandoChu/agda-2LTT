# Iterated cartesian products of concrete groups

```agda
module group-theory.iterated-cartesian-products-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.0-connected-typesᵉ
open import foundation.1-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-cartesian-product-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import group-theory.cartesian-products-concrete-groupsᵉ
open import group-theory.concrete-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.trivial-concrete-groupsᵉ

open import higher-group-theory.higher-groupsᵉ

open import structured-types.pointed-typesᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ iteratedᵉ Cartesianᵉ productᵉ ofᵉ aᵉ familyᵉ ofᵉ `Concrete-Group`ᵉ overᵉ `Finᵉ n`ᵉ isᵉ
definedᵉ recursivelyᵉ onᵉ `Finᵉ n`.ᵉ

## Definition

```agda
iterated-product-Concrete-Groupᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Gᵉ : Finᵉ nᵉ → Concrete-Groupᵉ lᵉ) →
  Concrete-Groupᵉ lᵉ
iterated-product-Concrete-Groupᵉ zero-ℕᵉ Gᵉ = trivial-Concrete-Groupᵉ
iterated-product-Concrete-Groupᵉ (succ-ℕᵉ nᵉ) Gᵉ =
  product-Concrete-Groupᵉ
    ( Gᵉ (inrᵉ starᵉ))
    ( iterated-product-Concrete-Groupᵉ nᵉ (Gᵉ ∘ᵉ inlᵉ))

module _
  {lᵉ : Level} (nᵉ : ℕᵉ) (Gᵉ : Finᵉ nᵉ → Concrete-Groupᵉ lᵉ)
  where

  ∞-group-iterated-product-Concrete-Groupᵉ : ∞-Groupᵉ lᵉ
  ∞-group-iterated-product-Concrete-Groupᵉ =
    pr1ᵉ (iterated-product-Concrete-Groupᵉ nᵉ Gᵉ)

  classifying-pointed-type-iterated-product-Concrete-Groupᵉ : Pointed-Typeᵉ lᵉ
  classifying-pointed-type-iterated-product-Concrete-Groupᵉ =
    classifying-pointed-type-∞-Groupᵉ ∞-group-iterated-product-Concrete-Groupᵉ

  classifying-type-iterated-product-Concrete-Groupᵉ : UUᵉ lᵉ
  classifying-type-iterated-product-Concrete-Groupᵉ =
    classifying-type-∞-Groupᵉ ∞-group-iterated-product-Concrete-Groupᵉ

  shape-iterated-product-Concrete-Groupᵉ :
    classifying-type-iterated-product-Concrete-Groupᵉ
  shape-iterated-product-Concrete-Groupᵉ =
    shape-∞-Groupᵉ ∞-group-iterated-product-Concrete-Groupᵉ

  is-0-connected-classifying-type-iterated-product-Concrete-Groupᵉ :
    is-0-connectedᵉ classifying-type-iterated-product-Concrete-Groupᵉ
  is-0-connected-classifying-type-iterated-product-Concrete-Groupᵉ =
    is-0-connected-classifying-type-∞-Groupᵉ
      ∞-group-iterated-product-Concrete-Groupᵉ

  mere-eq-classifying-type-iterated-product-Concrete-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-iterated-product-Concrete-Groupᵉ) → mere-eqᵉ Xᵉ Yᵉ
  mere-eq-classifying-type-iterated-product-Concrete-Groupᵉ =
    mere-eq-classifying-type-∞-Groupᵉ ∞-group-iterated-product-Concrete-Groupᵉ

  elim-prop-classifying-type-iterated-product-Concrete-Groupᵉ :
    {l2ᵉ : Level}
    (Pᵉ : classifying-type-iterated-product-Concrete-Groupᵉ → Propᵉ l2ᵉ) →
    type-Propᵉ (Pᵉ shape-iterated-product-Concrete-Groupᵉ) →
    ((Xᵉ : classifying-type-iterated-product-Concrete-Groupᵉ) → type-Propᵉ (Pᵉ Xᵉ))
  elim-prop-classifying-type-iterated-product-Concrete-Groupᵉ =
    elim-prop-classifying-type-∞-Groupᵉ ∞-group-iterated-product-Concrete-Groupᵉ

  type-iterated-product-Concrete-Groupᵉ : UUᵉ lᵉ
  type-iterated-product-Concrete-Groupᵉ =
    type-∞-Groupᵉ ∞-group-iterated-product-Concrete-Groupᵉ

  is-set-type-iterated-product-Concrete-Groupᵉ :
    is-setᵉ type-iterated-product-Concrete-Groupᵉ
  is-set-type-iterated-product-Concrete-Groupᵉ =
    pr2ᵉ (iterated-product-Concrete-Groupᵉ nᵉ Gᵉ)

  set-iterated-product-Concrete-Groupᵉ : Setᵉ lᵉ
  set-iterated-product-Concrete-Groupᵉ =
    type-iterated-product-Concrete-Groupᵉ ,ᵉ
    is-set-type-iterated-product-Concrete-Groupᵉ

  abstract
    is-1-type-classifying-type-iterated-product-Concrete-Groupᵉ :
      is-truncᵉ one-𝕋ᵉ classifying-type-iterated-product-Concrete-Groupᵉ
    is-1-type-classifying-type-iterated-product-Concrete-Groupᵉ Xᵉ Yᵉ =
      apply-universal-property-trunc-Propᵉ
        ( mere-eq-classifying-type-iterated-product-Concrete-Groupᵉ
            shape-iterated-product-Concrete-Groupᵉ
            Xᵉ)
        ( is-set-Propᵉ (Idᵉ Xᵉ Yᵉ))
        ( λ where
          reflᵉ →
            apply-universal-property-trunc-Propᵉ
              ( mere-eq-classifying-type-iterated-product-Concrete-Groupᵉ
                  shape-iterated-product-Concrete-Groupᵉ
                  Yᵉ)
              ( is-set-Propᵉ (Idᵉ shape-iterated-product-Concrete-Groupᵉ Yᵉ))
              ( λ where reflᵉ → is-set-type-iterated-product-Concrete-Groupᵉ))

  classifying-1-type-iterated-product-Concrete-Groupᵉ : Truncated-Typeᵉ lᵉ one-𝕋ᵉ
  classifying-1-type-iterated-product-Concrete-Groupᵉ =
    pairᵉ
      classifying-type-iterated-product-Concrete-Groupᵉ
      is-1-type-classifying-type-iterated-product-Concrete-Groupᵉ

  Id-iterated-product-BG-Setᵉ :
    (Xᵉ Yᵉ : classifying-type-iterated-product-Concrete-Groupᵉ) → Setᵉ lᵉ
  Id-iterated-product-BG-Setᵉ Xᵉ Yᵉ =
    Id-Setᵉ classifying-1-type-iterated-product-Concrete-Groupᵉ Xᵉ Yᵉ

  unit-iterated-product-Concrete-Groupᵉ : type-iterated-product-Concrete-Groupᵉ
  unit-iterated-product-Concrete-Groupᵉ =
    unit-∞-Groupᵉ ∞-group-iterated-product-Concrete-Groupᵉ

  mul-iterated-product-Concrete-Groupᵉ :
    (xᵉ yᵉ : type-iterated-product-Concrete-Groupᵉ) →
    type-iterated-product-Concrete-Groupᵉ
  mul-iterated-product-Concrete-Groupᵉ =
    mul-∞-Groupᵉ ∞-group-iterated-product-Concrete-Groupᵉ

  mul-iterated-product-Concrete-Group'ᵉ :
    (xᵉ yᵉ : type-iterated-product-Concrete-Groupᵉ) →
    type-iterated-product-Concrete-Groupᵉ
  mul-iterated-product-Concrete-Group'ᵉ xᵉ yᵉ =
    mul-iterated-product-Concrete-Groupᵉ yᵉ xᵉ

  associative-mul-iterated-product-Concrete-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-iterated-product-Concrete-Groupᵉ) →
    Idᵉ
      ( mul-iterated-product-Concrete-Groupᵉ
        ( mul-iterated-product-Concrete-Groupᵉ xᵉ yᵉ)
        ( zᵉ))
      ( mul-iterated-product-Concrete-Groupᵉ
        ( xᵉ)
        ( mul-iterated-product-Concrete-Groupᵉ yᵉ zᵉ))
  associative-mul-iterated-product-Concrete-Groupᵉ =
    associative-mul-∞-Groupᵉ ∞-group-iterated-product-Concrete-Groupᵉ

  left-unit-law-mul-iterated-product-Concrete-Groupᵉ :
    (xᵉ : type-iterated-product-Concrete-Groupᵉ) →
    Idᵉ
      ( mul-iterated-product-Concrete-Groupᵉ
        ( unit-iterated-product-Concrete-Groupᵉ)
        ( xᵉ))
      ( xᵉ)
  left-unit-law-mul-iterated-product-Concrete-Groupᵉ =
    left-unit-law-mul-∞-Groupᵉ ∞-group-iterated-product-Concrete-Groupᵉ

  right-unit-law-mul-iterated-product-Concrete-Groupᵉ :
    (yᵉ : type-iterated-product-Concrete-Groupᵉ) →
    Idᵉ
      ( mul-iterated-product-Concrete-Groupᵉ
        ( yᵉ)
        ( unit-iterated-product-Concrete-Groupᵉ))
      ( yᵉ)
  right-unit-law-mul-iterated-product-Concrete-Groupᵉ =
    right-unit-law-mul-∞-Groupᵉ ∞-group-iterated-product-Concrete-Groupᵉ

  coherence-unit-laws-mul-iterated-product-Concrete-Groupᵉ :
    Idᵉ
      ( left-unit-law-mul-iterated-product-Concrete-Groupᵉ
          unit-iterated-product-Concrete-Groupᵉ)
      ( right-unit-law-mul-iterated-product-Concrete-Groupᵉ
          unit-iterated-product-Concrete-Groupᵉ)
  coherence-unit-laws-mul-iterated-product-Concrete-Groupᵉ =
    coherence-unit-laws-mul-∞-Groupᵉ ∞-group-iterated-product-Concrete-Groupᵉ

  inv-iterated-product-Concrete-Groupᵉ :
    type-iterated-product-Concrete-Groupᵉ → type-iterated-product-Concrete-Groupᵉ
  inv-iterated-product-Concrete-Groupᵉ =
    inv-∞-Groupᵉ ∞-group-iterated-product-Concrete-Groupᵉ

  left-inverse-law-mul-iterated-product-Concrete-Groupᵉ :
    (xᵉ : type-iterated-product-Concrete-Groupᵉ) →
    Idᵉ
      ( mul-iterated-product-Concrete-Groupᵉ
        ( inv-iterated-product-Concrete-Groupᵉ xᵉ)
        ( xᵉ))
      ( unit-iterated-product-Concrete-Groupᵉ)
  left-inverse-law-mul-iterated-product-Concrete-Groupᵉ =
    left-inverse-law-mul-∞-Groupᵉ ∞-group-iterated-product-Concrete-Groupᵉ

  right-inverse-law-mul-iterated-product-Concrete-Groupᵉ :
    (xᵉ : type-iterated-product-Concrete-Groupᵉ) →
    Idᵉ
      ( mul-iterated-product-Concrete-Groupᵉ
        ( xᵉ)
        ( inv-iterated-product-Concrete-Groupᵉ xᵉ))
      ( unit-iterated-product-Concrete-Groupᵉ)
  right-inverse-law-mul-iterated-product-Concrete-Groupᵉ =
    right-inverse-law-mul-∞-Groupᵉ ∞-group-iterated-product-Concrete-Groupᵉ

  group-iterated-product-Concrete-Groupᵉ : Groupᵉ lᵉ
  pr1ᵉ (pr1ᵉ group-iterated-product-Concrete-Groupᵉ) =
    set-iterated-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ group-iterated-product-Concrete-Groupᵉ)) =
    mul-iterated-product-Concrete-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ group-iterated-product-Concrete-Groupᵉ)) =
    associative-mul-iterated-product-Concrete-Groupᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ group-iterated-product-Concrete-Groupᵉ)) =
    unit-iterated-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ group-iterated-product-Concrete-Groupᵉ))) =
    left-unit-law-mul-iterated-product-Concrete-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ group-iterated-product-Concrete-Groupᵉ))) =
    right-unit-law-mul-iterated-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ group-iterated-product-Concrete-Groupᵉ)) =
    inv-iterated-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ group-iterated-product-Concrete-Groupᵉ))) =
    left-inverse-law-mul-iterated-product-Concrete-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ group-iterated-product-Concrete-Groupᵉ))) =
    right-inverse-law-mul-iterated-product-Concrete-Groupᵉ

  op-group-iterated-product-Concrete-Groupᵉ : Groupᵉ lᵉ
  pr1ᵉ (pr1ᵉ op-group-iterated-product-Concrete-Groupᵉ) =
    set-iterated-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ op-group-iterated-product-Concrete-Groupᵉ)) =
    mul-iterated-product-Concrete-Group'ᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ op-group-iterated-product-Concrete-Groupᵉ)) xᵉ yᵉ zᵉ =
    invᵉ (associative-mul-iterated-product-Concrete-Groupᵉ zᵉ yᵉ xᵉ)
  pr1ᵉ (pr1ᵉ (pr2ᵉ op-group-iterated-product-Concrete-Groupᵉ)) =
    unit-iterated-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ op-group-iterated-product-Concrete-Groupᵉ))) =
    right-unit-law-mul-iterated-product-Concrete-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ op-group-iterated-product-Concrete-Groupᵉ))) =
    left-unit-law-mul-iterated-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ op-group-iterated-product-Concrete-Groupᵉ)) =
    inv-iterated-product-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ op-group-iterated-product-Concrete-Groupᵉ))) =
    right-inverse-law-mul-iterated-product-Concrete-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ op-group-iterated-product-Concrete-Groupᵉ))) =
    left-inverse-law-mul-iterated-product-Concrete-Groupᵉ
```

## Properties

```agda
equiv-type-Concrete-group-iterated-product-Concrete-Groupᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Gᵉ : Finᵉ nᵉ → Concrete-Groupᵉ lᵉ) →
  ( type-iterated-product-Concrete-Groupᵉ nᵉ Gᵉ) ≃ᵉ
  ( iterated-product-Fin-recursiveᵉ nᵉ (type-Concrete-Groupᵉ ∘ᵉ Gᵉ))
equiv-type-Concrete-group-iterated-product-Concrete-Groupᵉ zero-ℕᵉ Gᵉ =
  equiv-is-contrᵉ
    ( is-proof-irrelevant-is-propᵉ
        ( is-set-is-contrᵉ is-contr-raise-unitᵉ raise-starᵉ raise-starᵉ) reflᵉ)
    is-contr-raise-unitᵉ
equiv-type-Concrete-group-iterated-product-Concrete-Groupᵉ (succ-ℕᵉ nᵉ) Gᵉ =
  equiv-productᵉ
    ( id-equivᵉ)
    ( equiv-type-Concrete-group-iterated-product-Concrete-Groupᵉ nᵉ (Gᵉ ∘ᵉ inlᵉ)) ∘eᵉ
  equiv-type-Concrete-Group-product-Concrete-Groupᵉ
    ( Gᵉ (inrᵉ starᵉ))
    ( iterated-product-Concrete-Groupᵉ nᵉ (Gᵉ ∘ᵉ inlᵉ))
```