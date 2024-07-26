# Similarity of order preserving maps between large preorders

```agda
module order-theory.similarity-of-order-preserving-maps-large-preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-preordersᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
open import order-theory.similarity-of-elements-large-preordersᵉ
```

</details>

## Idea

Considerᵉ twoᵉ
[orderᵉ preservingᵉ maps](order-theory.order-preserving-maps-large-preorders.mdᵉ)
`fᵉ : hom-Large-Preorderᵉ γfᵉ Pᵉ Q`ᵉ andᵉ `gᵉ : hom-Large-Preorderᵉ γgᵉ Pᵉ Q`ᵉ betweenᵉ theᵉ
sameᵉ twoᵉ [largeᵉ preorders](order-theory.large-preorders.mdᵉ) `P`ᵉ andᵉ `Q`,ᵉ butᵉ
eachᵉ specifiedᵉ with theirᵉ ownᵉ universeᵉ levelᵉ reindexingᵉ functions.ᵉ Weᵉ sayᵉ thatᵉ
`f`ᵉ andᵉ `g`ᵉ areᵉ **similar**ᵉ ifᵉ theᵉ valuesᵉ `fᵉ x`ᵉ andᵉ `gᵉ x`ᵉ areᵉ
[similar](order-theory.similarity-of-elements-large-preorders.mdᵉ) forᵉ eachᵉ
`xᵉ : P`.ᵉ Inᵉ otherᵉ words,ᵉ aᵉ **similarityᵉ ofᵉ orderᵉ preservingᵉ maps**ᵉ betweenᵉ `f`ᵉ
andᵉ `g`ᵉ consistsᵉ ofᵉ anᵉ assignmentᵉ `xᵉ ↦ᵉ hᵉ x`ᵉ where

```text
  hᵉ xᵉ : fᵉ xᵉ ≈ᵉ gᵉ xᵉ
```

forᵉ eachᵉ `xᵉ : type-Large-Preorderᵉ P`.ᵉ Inᵉ informalᵉ writingᵉ weᵉ willᵉ useᵉ theᵉ
notationᵉ `fᵉ ≈ᵉ g`ᵉ to assertᵉ thatᵉ theᵉ orderᵉ preservingᵉ mapᵉ `f`ᵉ isᵉ similarᵉ to theᵉ
orderᵉ preservingᵉ mapᵉ `g`.ᵉ

## Definitions

### Similarities of order preserving maps between large preorders

```agda
module _
  {αPᵉ αQᵉ γfᵉ γgᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Preorderᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Preorderᵉ αQᵉ βQᵉ)
  (fᵉ : hom-Large-Preorderᵉ γfᵉ Pᵉ Qᵉ)
  (gᵉ : hom-Large-Preorderᵉ γgᵉ Pᵉ Qᵉ)
  where

  sim-hom-Large-Preorderᵉ : UUωᵉ
  sim-hom-Large-Preorderᵉ =
    {lᵉ : Level} (xᵉ : type-Large-Preorderᵉ Pᵉ lᵉ) →
    sim-Large-Preorderᵉ Qᵉ
      ( map-hom-Large-Preorderᵉ fᵉ xᵉ)
      ( map-hom-Large-Preorderᵉ gᵉ xᵉ)
```

### The reflexive similarity of order preserving maps between large preorders

```agda
module _
  {αPᵉ αQᵉ γfᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Preorderᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Preorderᵉ αQᵉ βQᵉ)
  (fᵉ : hom-Large-Preorderᵉ γfᵉ Pᵉ Qᵉ)
  where

  refl-sim-hom-Large-Preorderᵉ : sim-hom-Large-Preorderᵉ Pᵉ Qᵉ fᵉ fᵉ
  refl-sim-hom-Large-Preorderᵉ xᵉ =
    refl-sim-Large-Preorderᵉ Qᵉ (map-hom-Large-Preorderᵉ fᵉ xᵉ)
```

## Properties

### Homotopic order preserving maps are similar

```agda
module _
  {αPᵉ αQᵉ γᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Preorderᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Preorderᵉ αQᵉ βQᵉ)
  (fᵉ : hom-Large-Preorderᵉ γᵉ Pᵉ Qᵉ)
  (gᵉ : hom-Large-Preorderᵉ γᵉ Pᵉ Qᵉ)
  where

  sim-htpy-hom-Large-Preorderᵉ :
    htpy-hom-Large-Preorderᵉ Pᵉ Qᵉ fᵉ gᵉ → sim-hom-Large-Preorderᵉ Pᵉ Qᵉ fᵉ gᵉ
  sim-htpy-hom-Large-Preorderᵉ Hᵉ xᵉ = sim-eq-Large-Preorderᵉ Qᵉ (Hᵉ xᵉ)
```