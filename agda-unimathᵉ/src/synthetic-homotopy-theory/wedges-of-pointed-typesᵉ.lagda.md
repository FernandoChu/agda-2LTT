# Wedges of pointed types

```agda
module synthetic-homotopy-theory.wedges-of-pointed-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-cartesian-product-typesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.pointed-unit-typeᵉ

open import synthetic-homotopy-theory.cocones-under-pointed-span-diagramsᵉ
open import synthetic-homotopy-theory.cofibersᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.pushouts-of-pointed-typesᵉ
```

</details>

## Idea

Theᵉ **wedge**ᵉ orᵉ **wedgeᵉ sum**ᵉ ofᵉ twoᵉ
[pointedᵉ types](structured-types.pointed-types.mdᵉ) `aᵉ : A`ᵉ andᵉ `bᵉ : B`ᵉ isᵉ
definedᵉ byᵉ theᵉ followingᵉ
[pointedᵉ pushout](synthetic-homotopy-theory.pushouts-of-pointed-types.mdᵉ):

```text
  unitᵉ ------>ᵉ Aᵉ
    |          |
    |          |
    ∨ᵉ        ⌜ᵉ ∨ᵉ
    Bᵉ ----->ᵉ Aᵉ ∨∗ᵉ B,ᵉ
```

andᵉ isᵉ thusᵉ canonicallyᵉ pointedᵉ atᵉ theᵉ identifiedᵉ imageᵉ ofᵉ `a`ᵉ andᵉ `b`.ᵉ

## Definition

```agda
wedge-Pointed-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ) →
  Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
wedge-Pointed-Typeᵉ Aᵉ Bᵉ =
  pushout-Pointed-Typeᵉ
    ( inclusion-point-Pointed-Typeᵉ Aᵉ)
    ( inclusion-point-Pointed-Typeᵉ Bᵉ)

infixr 10 _∨∗ᵉ_
_∨∗ᵉ_ = wedge-Pointed-Typeᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ)
  where

  inl-wedge-Pointed-Typeᵉ : Aᵉ →∗ᵉ (Aᵉ ∨∗ᵉ Bᵉ)
  inl-wedge-Pointed-Typeᵉ =
    inl-pushout-Pointed-Typeᵉ
      ( inclusion-point-Pointed-Typeᵉ Aᵉ)
      ( inclusion-point-Pointed-Typeᵉ Bᵉ)

  map-inl-wedge-Pointed-Typeᵉ :
    type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ (Aᵉ ∨∗ᵉ Bᵉ)
  map-inl-wedge-Pointed-Typeᵉ =
    map-pointed-mapᵉ inl-wedge-Pointed-Typeᵉ

  inr-wedge-Pointed-Typeᵉ : Bᵉ →∗ᵉ Aᵉ ∨∗ᵉ Bᵉ
  inr-wedge-Pointed-Typeᵉ =
    inr-pushout-Pointed-Typeᵉ
      ( inclusion-point-Pointed-Typeᵉ Aᵉ)
      ( inclusion-point-Pointed-Typeᵉ Bᵉ)

  map-inr-wedge-Pointed-Typeᵉ :
    type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ (Aᵉ ∨∗ᵉ Bᵉ)
  map-inr-wedge-Pointed-Typeᵉ =
    map-pointed-mapᵉ inr-wedge-Pointed-Typeᵉ

indexed-wedge-Pointed-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Aᵉ : Iᵉ → Pointed-Typeᵉ l2ᵉ) → Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (indexed-wedge-Pointed-Typeᵉ Iᵉ Aᵉ) =
  cofiberᵉ (λ iᵉ → (iᵉ ,ᵉ point-Pointed-Typeᵉ (Aᵉ iᵉ)))
pr2ᵉ (indexed-wedge-Pointed-Typeᵉ Iᵉ Aᵉ) =
  point-cofiberᵉ (λ iᵉ → (iᵉ ,ᵉ point-Pointed-Typeᵉ (Aᵉ iᵉ)))

⋁∗ᵉ = indexed-wedge-Pointed-Typeᵉ
```

**Note**ᵉ: theᵉ symbolsᵉ usedᵉ forᵉ theᵉ wedgeᵉ sumᵉ `_∨∗_`ᵉ areᵉ theᵉ
[logicalᵉ or](https://codepoints.net/U+2228ᵉ) `∨`ᵉ (agda-inputᵉ: `\vee`ᵉ `\or`ᵉ) andᵉ
theᵉ [asteriskᵉ operator](https://codepoints.net/U+2217ᵉ) `∗`ᵉ (agda-inputᵉ: `\ast`),ᵉ
notᵉ theᵉ [latinᵉ smallᵉ letterᵉ v](https://codepoints.net/U+0076ᵉ) `v`ᵉ orᵉ theᵉ
[asterisk](https://codepoints.net/U+002Aᵉ) `*`.ᵉ Theᵉ `⋁`ᵉ symbolᵉ usedᵉ forᵉ theᵉ
indexedᵉ wedgeᵉ sum,ᵉ `⋁∗`,ᵉ isᵉ theᵉ
[N-aryᵉ logicalᵉ or](https://codepoints.net/U+22C1ᵉ) (agda-inputᵉ: `\bigvee`).ᵉ

## Properties

### The images of the base points `a : A` and `b : B` are identified in `A ∨∗ B`

```agda
glue-wedge-Pointed-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ) →
  map-inl-wedge-Pointed-Typeᵉ Aᵉ Bᵉ (point-Pointed-Typeᵉ Aᵉ) ＝ᵉ
  map-inr-wedge-Pointed-Typeᵉ Aᵉ Bᵉ (point-Pointed-Typeᵉ Bᵉ)
glue-wedge-Pointed-Typeᵉ Aᵉ Bᵉ =
  glue-pushoutᵉ
    ( map-pointed-mapᵉ (inclusion-point-Pointed-Typeᵉ Aᵉ))
    ( map-pointed-mapᵉ (inclusion-point-Pointed-Typeᵉ Bᵉ))
    ( point-Pointed-Typeᵉ unit-Pointed-Typeᵉ)
```

### The inclusion of the wedge sum `A ∨∗ B` into the pointed product `A ×∗ B`

Thereᵉ isᵉ aᵉ canonicalᵉ inclusionᵉ ofᵉ theᵉ wedgeᵉ sumᵉ intoᵉ theᵉ pointedᵉ productᵉ thatᵉ isᵉ
definedᵉ byᵉ theᵉ cogapᵉ mapᵉ inducedᵉ byᵉ theᵉ canonicalᵉ inclusionsᵉ `Aᵉ → Aᵉ ×∗ᵉ Bᵉ ←ᵉ B`.ᵉ

Elementsᵉ ofᵉ theᵉ formᵉ `(x,ᵉ b)`ᵉ andᵉ `(a,ᵉ y)`,ᵉ where `b`ᵉ andᵉ `a`ᵉ areᵉ basepoints,ᵉ
lieᵉ in theᵉ imageᵉ ofᵉ theᵉ inclusionᵉ ofᵉ theᵉ wedgeᵉ sumᵉ intoᵉ theᵉ pointedᵉ product.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ)
  where

  cocone-product-wedge-Pointed-Typeᵉ :
    cocone-Pointed-Typeᵉ
      ( inclusion-point-Pointed-Typeᵉ Aᵉ)
      ( inclusion-point-Pointed-Typeᵉ Bᵉ)
      ( Aᵉ ×∗ᵉ Bᵉ)
  pr1ᵉ cocone-product-wedge-Pointed-Typeᵉ = inl-product-Pointed-Typeᵉ Aᵉ Bᵉ
  pr1ᵉ (pr2ᵉ cocone-product-wedge-Pointed-Typeᵉ) = inr-product-Pointed-Typeᵉ Aᵉ Bᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ cocone-product-wedge-Pointed-Typeᵉ)) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ cocone-product-wedge-Pointed-Typeᵉ)) = reflᵉ

  pointed-map-product-wedge-Pointed-Typeᵉ :
    (Aᵉ ∨∗ᵉ Bᵉ) →∗ᵉ (Aᵉ ×∗ᵉ Bᵉ)
  pointed-map-product-wedge-Pointed-Typeᵉ =
    cogap-Pointed-Typeᵉ
      ( inclusion-point-Pointed-Typeᵉ Aᵉ)
      ( inclusion-point-Pointed-Typeᵉ Bᵉ)
      ( cocone-product-wedge-Pointed-Typeᵉ)

  map-product-wedge-Pointed-Typeᵉ :
    type-Pointed-Typeᵉ (Aᵉ ∨∗ᵉ Bᵉ) → type-Pointed-Typeᵉ (Aᵉ ×∗ᵉ Bᵉ)
  map-product-wedge-Pointed-Typeᵉ = pr1ᵉ pointed-map-product-wedge-Pointed-Typeᵉ

  compute-inl-product-wedge-Pointed-Typeᵉ :
    ( xᵉ : type-Pointed-Typeᵉ Aᵉ) →
    ( map-product-wedge-Pointed-Typeᵉ (map-inl-wedge-Pointed-Typeᵉ Aᵉ Bᵉ xᵉ)) ＝ᵉ
    ( xᵉ ,ᵉ point-Pointed-Typeᵉ Bᵉ)
  compute-inl-product-wedge-Pointed-Typeᵉ =
    compute-inl-cogap-Pointed-Typeᵉ
      ( inclusion-point-Pointed-Typeᵉ Aᵉ)
      ( inclusion-point-Pointed-Typeᵉ Bᵉ)
      ( cocone-product-wedge-Pointed-Typeᵉ)

  compute-inr-product-wedge-Pointed-Typeᵉ :
    ( yᵉ : type-Pointed-Typeᵉ Bᵉ) →
    ( map-product-wedge-Pointed-Typeᵉ (map-inr-wedge-Pointed-Typeᵉ Aᵉ Bᵉ yᵉ)) ＝ᵉ
    ( point-Pointed-Typeᵉ Aᵉ ,ᵉ yᵉ)
  compute-inr-product-wedge-Pointed-Typeᵉ =
    compute-inr-cogap-Pointed-Typeᵉ
      ( inclusion-point-Pointed-Typeᵉ Aᵉ)
      ( inclusion-point-Pointed-Typeᵉ Bᵉ)
      ( cocone-product-wedge-Pointed-Typeᵉ)
```

## See also

-ᵉ [Smashᵉ productsᵉ ofᵉ pointedᵉ types](synthetic-homotopy-theory.smash-products-of-pointed-types.mdᵉ)
  forᵉ aᵉ relatedᵉ construction.ᵉ