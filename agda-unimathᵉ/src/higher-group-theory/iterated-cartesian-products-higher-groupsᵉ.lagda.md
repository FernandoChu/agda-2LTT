# Iterated cartesian products of higher groups

```agda
module higher-group-theory.iterated-cartesian-products-higher-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.0-connected-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-cartesian-product-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.cartesian-products-higher-groupsᵉ
open import higher-group-theory.higher-groupsᵉ
open import higher-group-theory.trivial-higher-groupsᵉ

open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.loop-spacesᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ iteratedᵉ Cartesianᵉ productᵉ ofᵉ aᵉ familyᵉ ofᵉ `∞-Group`ᵉ overᵉ `Finᵉ n`ᵉ isᵉ definedᵉ
recursivelyᵉ onᵉ `Finᵉ n`.ᵉ

## Definition

```agda
iterated-product-∞-Groupᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Gᵉ : Finᵉ nᵉ → (∞-Groupᵉ lᵉ)) → ∞-Groupᵉ lᵉ
iterated-product-∞-Groupᵉ zero-ℕᵉ Gᵉ = trivial-∞-Groupᵉ
iterated-product-∞-Groupᵉ (succ-ℕᵉ nᵉ) Gᵉ =
  product-∞-Groupᵉ
    ( Gᵉ (inrᵉ starᵉ))
    ( iterated-product-∞-Groupᵉ nᵉ (Gᵉ ∘ᵉ inlᵉ))

module _
  {lᵉ : Level} (nᵉ : ℕᵉ) (Gᵉ : Finᵉ nᵉ → ∞-Groupᵉ lᵉ)
  where

  classifying-pointed-type-iterated-product-∞-Groupᵉ :
    Pointed-Typeᵉ lᵉ
  classifying-pointed-type-iterated-product-∞-Groupᵉ =
    pr1ᵉ (iterated-product-∞-Groupᵉ nᵉ Gᵉ)

  classifying-type-iterated-product-∞-Groupᵉ : UUᵉ lᵉ
  classifying-type-iterated-product-∞-Groupᵉ =
    type-Pointed-Typeᵉ
      classifying-pointed-type-iterated-product-∞-Groupᵉ

  shape-iterated-product-∞-Groupᵉ :
    classifying-type-iterated-product-∞-Groupᵉ
  shape-iterated-product-∞-Groupᵉ =
    point-Pointed-Typeᵉ
      classifying-pointed-type-iterated-product-∞-Groupᵉ

  is-0-connected-classifying-type-iterated-product-∞-Groupᵉ :
    is-0-connectedᵉ classifying-type-iterated-product-∞-Groupᵉ
  is-0-connected-classifying-type-iterated-product-∞-Groupᵉ =
    pr2ᵉ (iterated-product-∞-Groupᵉ nᵉ Gᵉ)

  mere-eq-classifying-type-iterated-product-∞-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-iterated-product-∞-Groupᵉ) →
    mere-eqᵉ Xᵉ Yᵉ
  mere-eq-classifying-type-iterated-product-∞-Groupᵉ =
    mere-eq-is-0-connectedᵉ
      is-0-connected-classifying-type-iterated-product-∞-Groupᵉ

  elim-prop-classifying-type-iterated-product-∞-Groupᵉ :
    {l2ᵉ : Level}
    (Pᵉ : classifying-type-iterated-product-∞-Groupᵉ → Propᵉ l2ᵉ) →
    type-Propᵉ (Pᵉ shape-iterated-product-∞-Groupᵉ) →
    ((Xᵉ : classifying-type-iterated-product-∞-Groupᵉ) →
    type-Propᵉ (Pᵉ Xᵉ))
  elim-prop-classifying-type-iterated-product-∞-Groupᵉ =
    apply-dependent-universal-property-is-0-connectedᵉ
      shape-iterated-product-∞-Groupᵉ
      is-0-connected-classifying-type-iterated-product-∞-Groupᵉ

  type-iterated-product-∞-Groupᵉ : UUᵉ (lᵉ)
  type-iterated-product-∞-Groupᵉ =
    type-Ωᵉ classifying-pointed-type-iterated-product-∞-Groupᵉ

  unit-iterated-product-∞-Groupᵉ :
    type-iterated-product-∞-Groupᵉ
  unit-iterated-product-∞-Groupᵉ =
    refl-Ωᵉ classifying-pointed-type-iterated-product-∞-Groupᵉ

  mul-iterated-product-∞-Groupᵉ :
    (xᵉ yᵉ : type-iterated-product-∞-Groupᵉ) →
    type-iterated-product-∞-Groupᵉ
  mul-iterated-product-∞-Groupᵉ =
    mul-Ωᵉ classifying-pointed-type-iterated-product-∞-Groupᵉ

  assoc-mul-iterated-product-∞-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-iterated-product-∞-Groupᵉ) →
    Idᵉ
      ( mul-iterated-product-∞-Groupᵉ
        ( mul-iterated-product-∞-Groupᵉ xᵉ yᵉ)
        ( zᵉ))
      ( mul-iterated-product-∞-Groupᵉ
        ( xᵉ)
        ( mul-iterated-product-∞-Groupᵉ yᵉ zᵉ))
  assoc-mul-iterated-product-∞-Groupᵉ =
    associative-mul-Ωᵉ
      classifying-pointed-type-iterated-product-∞-Groupᵉ

  left-unit-law-mul-iterated-product-∞-Groupᵉ :
    (xᵉ : type-iterated-product-∞-Groupᵉ) →
    Idᵉ
      ( mul-iterated-product-∞-Groupᵉ
        ( unit-iterated-product-∞-Groupᵉ)
        ( xᵉ))
      ( xᵉ)
  left-unit-law-mul-iterated-product-∞-Groupᵉ =
    left-unit-law-mul-Ωᵉ
      classifying-pointed-type-iterated-product-∞-Groupᵉ

  right-unit-law-mul-iterated-product-∞-Groupᵉ :
    (yᵉ : type-iterated-product-∞-Groupᵉ) →
    Idᵉ
      ( mul-iterated-product-∞-Groupᵉ
        ( yᵉ)
        ( unit-iterated-product-∞-Groupᵉ))
      ( yᵉ)
  right-unit-law-mul-iterated-product-∞-Groupᵉ =
    right-unit-law-mul-Ωᵉ
      classifying-pointed-type-iterated-product-∞-Groupᵉ

  coherence-unit-laws-mul-iterated-product-∞-Groupᵉ :
    Idᵉ
      ( left-unit-law-mul-iterated-product-∞-Groupᵉ
          unit-iterated-product-∞-Groupᵉ)
      ( right-unit-law-mul-iterated-product-∞-Groupᵉ
          unit-iterated-product-∞-Groupᵉ)
  coherence-unit-laws-mul-iterated-product-∞-Groupᵉ = reflᵉ

  inv-iterated-product-∞-Groupᵉ :
    type-iterated-product-∞-Groupᵉ → type-iterated-product-∞-Groupᵉ
  inv-iterated-product-∞-Groupᵉ =
    inv-Ωᵉ classifying-pointed-type-iterated-product-∞-Groupᵉ

  left-inverse-law-mul-iterated-product-∞-Groupᵉ :
    (xᵉ : type-iterated-product-∞-Groupᵉ) →
    Idᵉ
      ( mul-iterated-product-∞-Groupᵉ
        ( inv-iterated-product-∞-Groupᵉ xᵉ)
        ( xᵉ))
      ( unit-iterated-product-∞-Groupᵉ)
  left-inverse-law-mul-iterated-product-∞-Groupᵉ =
    left-inverse-law-mul-Ωᵉ
      classifying-pointed-type-iterated-product-∞-Groupᵉ

  right-inverse-law-mul-iterated-product-∞-Groupᵉ :
    (xᵉ : type-iterated-product-∞-Groupᵉ) →
    Idᵉ
      ( mul-iterated-product-∞-Groupᵉ
        ( xᵉ)
        ( inv-iterated-product-∞-Groupᵉ xᵉ))
      ( unit-iterated-product-∞-Groupᵉ)
  right-inverse-law-mul-iterated-product-∞-Groupᵉ =
    right-inverse-law-mul-Ωᵉ
      classifying-pointed-type-iterated-product-∞-Groupᵉ
```

## Properties

### The `type-∞-Group` of a iterated product of a `∞-Group` is the iterated product of the `type-∞-Group`

```agda
equiv-type-∞-Group-iterated-product-∞-Groupᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Gᵉ : Finᵉ nᵉ → ∞-Groupᵉ lᵉ) →
  ( type-iterated-product-∞-Groupᵉ nᵉ Gᵉ) ≃ᵉ
  ( iterated-product-Fin-recursiveᵉ nᵉ (type-∞-Groupᵉ ∘ᵉ Gᵉ))
equiv-type-∞-Group-iterated-product-∞-Groupᵉ zero-ℕᵉ Gᵉ =
  equiv-is-contrᵉ
    ( is-proof-irrelevant-is-propᵉ
        ( is-set-is-contrᵉ is-contr-raise-unitᵉ raise-starᵉ raise-starᵉ) reflᵉ)
    is-contr-raise-unitᵉ
equiv-type-∞-Group-iterated-product-∞-Groupᵉ (succ-ℕᵉ nᵉ) Gᵉ =
  ( ( equiv-productᵉ
        ( id-equivᵉ)
        ( equiv-type-∞-Group-iterated-product-∞-Groupᵉ
            ( nᵉ)
            (Gᵉ ∘ᵉ inlᵉ))) ∘eᵉ
    ( ( equiv-type-∞-Group-product-∞-Groupᵉ
          ( Gᵉ (inrᵉ starᵉ))
          ( iterated-product-∞-Groupᵉ nᵉ (Gᵉ ∘ᵉ inlᵉ)))))
```