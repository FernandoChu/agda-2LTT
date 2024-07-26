# Similarity of order preserving maps between large posets

```agda
module order-theory.similarity-of-order-preserving-maps-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.similarity-of-elements-large-posetsᵉ
open import order-theory.similarity-of-order-preserving-maps-large-preordersᵉ
```

</details>

## Idea

Considerᵉ twoᵉ
[orderᵉ preservingᵉ maps](order-theory.order-preserving-maps-large-posets.mdᵉ)
`fᵉ : hom-Large-Posetᵉ γfᵉ Pᵉ Q`ᵉ andᵉ `gᵉ : hom-Large-Posetᵉ γgᵉ Pᵉ Q`ᵉ betweenᵉ theᵉ sameᵉ
twoᵉ [largeᵉ posets](order-theory.large-posets.mdᵉ) `P`ᵉ andᵉ `Q`,ᵉ butᵉ eachᵉ specifiedᵉ
with theirᵉ ownᵉ universeᵉ levelᵉ reindexingᵉ functions.ᵉ Weᵉ sayᵉ thatᵉ `f`ᵉ andᵉ `g`ᵉ areᵉ
**similar**ᵉ ifᵉ theᵉ valuesᵉ `fᵉ x`ᵉ andᵉ `gᵉ x`ᵉ areᵉ
[similar](order-theory.similarity-of-elements-large-posets.mdᵉ) forᵉ eachᵉ `xᵉ : P`.ᵉ
Inᵉ otherᵉ words,ᵉ aᵉ **similarityᵉ ofᵉ orderᵉ preservingᵉ maps**ᵉ betweenᵉ `f`ᵉ andᵉ `g`ᵉ
consistsᵉ ofᵉ anᵉ assignmentᵉ `xᵉ ↦ᵉ hᵉ x`ᵉ where

```text
  hᵉ xᵉ : fᵉ xᵉ ≈ᵉ gᵉ xᵉ
```

forᵉ eachᵉ `xᵉ : type-Large-Posetᵉ P`.ᵉ Inᵉ informalᵉ writingᵉ weᵉ willᵉ useᵉ theᵉ notationᵉ
`fᵉ ≈ᵉ g`ᵉ to assertᵉ thatᵉ theᵉ orderᵉ preservingᵉ mapᵉ `f`ᵉ isᵉ similarᵉ to theᵉ orderᵉ
preservingᵉ mapᵉ `g`.ᵉ

## Definitions

### Similarity of order preserving maps between large posets

```agda
module _
  {αPᵉ αQᵉ γfᵉ γgᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (fᵉ : hom-Large-Posetᵉ γfᵉ Pᵉ Qᵉ)
  (gᵉ : hom-Large-Posetᵉ γgᵉ Pᵉ Qᵉ)
  where

  sim-hom-Large-Posetᵉ : UUωᵉ
  sim-hom-Large-Posetᵉ =
    sim-hom-Large-Preorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-preorder-Large-Posetᵉ Qᵉ)
      ( fᵉ)
      ( gᵉ)
```

### The reflexive similarity of order preserving maps between large posets

```agda
module _
  {αPᵉ αQᵉ γfᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (fᵉ : hom-Large-Posetᵉ γfᵉ Pᵉ Qᵉ)
  where

  refl-sim-hom-Large-Posetᵉ : sim-hom-Large-Posetᵉ Pᵉ Qᵉ fᵉ fᵉ
  refl-sim-hom-Large-Posetᵉ =
    refl-sim-hom-Large-Preorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-preorder-Large-Posetᵉ Qᵉ)
      ( fᵉ)
```

## Properties

### Order preserving maps with the same universe level reindexing function are homotopic if and only if they are similar

```agda
module _
  {αPᵉ αQᵉ γᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (fᵉ : hom-Large-Posetᵉ γᵉ Pᵉ Qᵉ)
  (gᵉ : hom-Large-Posetᵉ γᵉ Pᵉ Qᵉ)
  where

  sim-htpy-hom-Large-Posetᵉ :
    htpy-hom-Large-Posetᵉ Pᵉ Qᵉ fᵉ gᵉ → sim-hom-Large-Posetᵉ Pᵉ Qᵉ fᵉ gᵉ
  sim-htpy-hom-Large-Posetᵉ =
    sim-htpy-hom-Large-Preorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-preorder-Large-Posetᵉ Qᵉ)
      ( fᵉ)
      ( gᵉ)

  htpy-sim-hom-Large-Posetᵉ :
    sim-hom-Large-Posetᵉ Pᵉ Qᵉ fᵉ gᵉ → htpy-hom-Large-Posetᵉ Pᵉ Qᵉ fᵉ gᵉ
  htpy-sim-hom-Large-Posetᵉ Hᵉ xᵉ =
    eq-sim-Large-Posetᵉ Qᵉ
      ( map-hom-Large-Posetᵉ Pᵉ Qᵉ fᵉ xᵉ)
      ( map-hom-Large-Posetᵉ Pᵉ Qᵉ gᵉ xᵉ)
      ( Hᵉ xᵉ)
```