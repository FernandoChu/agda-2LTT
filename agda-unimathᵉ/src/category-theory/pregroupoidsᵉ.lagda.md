# Pregroupoids

```agda
module category-theory.pregroupoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **pregroupoid**ᵉ isᵉ aᵉ [precategory](category-theory.precategories.mdᵉ) in whichᵉ
everyᵉ morphismᵉ isᵉ anᵉ
[isomorphism](category-theory.isomorphisms-in-precategories.md).ᵉ

## Definitions

### The predicate on precategories of being a pregroupoid

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-pregroupoid-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-pregroupoid-Precategoryᵉ =
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    is-iso-Precategoryᵉ Cᵉ fᵉ

  is-prop-is-pregroupoid-Precategoryᵉ : is-propᵉ is-pregroupoid-Precategoryᵉ
  is-prop-is-pregroupoid-Precategoryᵉ =
    is-prop-iterated-Πᵉ 3 (λ xᵉ yᵉ → is-prop-is-iso-Precategoryᵉ Cᵉ)

  is-pregroupoid-prop-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ is-pregroupoid-prop-Precategoryᵉ = is-pregroupoid-Precategoryᵉ
  pr2ᵉ is-pregroupoid-prop-Precategoryᵉ = is-prop-is-pregroupoid-Precategoryᵉ
```

### The type of pregroupoids

```agda
Pregroupoidᵉ :
  (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Pregroupoidᵉ l1ᵉ l2ᵉ = Σᵉ (Precategoryᵉ l1ᵉ l2ᵉ) (is-pregroupoid-Precategoryᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Pregroupoidᵉ l1ᵉ l2ᵉ)
  where

  precategory-Pregroupoidᵉ : Precategoryᵉ l1ᵉ l2ᵉ
  precategory-Pregroupoidᵉ = pr1ᵉ Gᵉ

  is-pregroupoid-Pregroupoidᵉ :
    is-pregroupoid-Precategoryᵉ precategory-Pregroupoidᵉ
  is-pregroupoid-Pregroupoidᵉ = pr2ᵉ Gᵉ

  obj-Pregroupoidᵉ : UUᵉ l1ᵉ
  obj-Pregroupoidᵉ = obj-Precategoryᵉ precategory-Pregroupoidᵉ

  hom-set-Pregroupoidᵉ : obj-Pregroupoidᵉ → obj-Pregroupoidᵉ → Setᵉ l2ᵉ
  hom-set-Pregroupoidᵉ = hom-set-Precategoryᵉ precategory-Pregroupoidᵉ

  hom-Pregroupoidᵉ : obj-Pregroupoidᵉ → obj-Pregroupoidᵉ → UUᵉ l2ᵉ
  hom-Pregroupoidᵉ = hom-Precategoryᵉ precategory-Pregroupoidᵉ

  id-hom-Pregroupoidᵉ :
    {xᵉ : obj-Pregroupoidᵉ} → hom-Pregroupoidᵉ xᵉ xᵉ
  id-hom-Pregroupoidᵉ = id-hom-Precategoryᵉ precategory-Pregroupoidᵉ

  comp-hom-Pregroupoidᵉ :
    {xᵉ yᵉ zᵉ : obj-Pregroupoidᵉ} → hom-Pregroupoidᵉ yᵉ zᵉ →
    hom-Pregroupoidᵉ xᵉ yᵉ → hom-Pregroupoidᵉ xᵉ zᵉ
  comp-hom-Pregroupoidᵉ = comp-hom-Precategoryᵉ precategory-Pregroupoidᵉ

  associative-comp-hom-Pregroupoidᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Pregroupoidᵉ} (hᵉ : hom-Pregroupoidᵉ zᵉ wᵉ)
    (gᵉ : hom-Pregroupoidᵉ yᵉ zᵉ) (fᵉ : hom-Pregroupoidᵉ xᵉ yᵉ) →
    comp-hom-Pregroupoidᵉ (comp-hom-Pregroupoidᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Pregroupoidᵉ hᵉ (comp-hom-Pregroupoidᵉ gᵉ fᵉ)
  associative-comp-hom-Pregroupoidᵉ =
    associative-comp-hom-Precategoryᵉ precategory-Pregroupoidᵉ

  involutive-eq-associative-comp-hom-Pregroupoidᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Pregroupoidᵉ} (hᵉ : hom-Pregroupoidᵉ zᵉ wᵉ)
    (gᵉ : hom-Pregroupoidᵉ yᵉ zᵉ) (fᵉ : hom-Pregroupoidᵉ xᵉ yᵉ) →
    comp-hom-Pregroupoidᵉ (comp-hom-Pregroupoidᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-Pregroupoidᵉ hᵉ (comp-hom-Pregroupoidᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Pregroupoidᵉ =
    involutive-eq-associative-comp-hom-Precategoryᵉ precategory-Pregroupoidᵉ

  left-unit-law-comp-hom-Pregroupoidᵉ :
    {xᵉ yᵉ : obj-Pregroupoidᵉ} (fᵉ : hom-Pregroupoidᵉ xᵉ yᵉ) →
    ( comp-hom-Pregroupoidᵉ id-hom-Pregroupoidᵉ fᵉ) ＝ᵉ fᵉ
  left-unit-law-comp-hom-Pregroupoidᵉ =
    left-unit-law-comp-hom-Precategoryᵉ precategory-Pregroupoidᵉ

  right-unit-law-comp-hom-Pregroupoidᵉ :
    {xᵉ yᵉ : obj-Pregroupoidᵉ} (fᵉ : hom-Pregroupoidᵉ xᵉ yᵉ) →
    ( comp-hom-Pregroupoidᵉ fᵉ id-hom-Pregroupoidᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Pregroupoidᵉ =
    right-unit-law-comp-hom-Precategoryᵉ precategory-Pregroupoidᵉ

  iso-Pregroupoidᵉ : (xᵉ yᵉ : obj-Pregroupoidᵉ) → UUᵉ l2ᵉ
  iso-Pregroupoidᵉ = iso-Precategoryᵉ precategory-Pregroupoidᵉ
```

## Properties

### The type of isomorphisms in a pregroupoid is equivalent to the type of morphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Pregroupoidᵉ l1ᵉ l2ᵉ)
  where

  inv-compute-iso-Pregroupoidᵉ :
    {xᵉ yᵉ : obj-Pregroupoidᵉ Gᵉ} → iso-Pregroupoidᵉ Gᵉ xᵉ yᵉ ≃ᵉ hom-Pregroupoidᵉ Gᵉ xᵉ yᵉ
  inv-compute-iso-Pregroupoidᵉ {xᵉ} {yᵉ} =
    right-unit-law-Σ-is-contrᵉ
      ( λ fᵉ →
        is-proof-irrelevant-is-propᵉ
          ( is-prop-is-iso-Precategoryᵉ (precategory-Pregroupoidᵉ Gᵉ) fᵉ)
          ( is-pregroupoid-Pregroupoidᵉ Gᵉ xᵉ yᵉ fᵉ))

  compute-iso-Pregroupoidᵉ :
    {xᵉ yᵉ : obj-Pregroupoidᵉ Gᵉ} → hom-Pregroupoidᵉ Gᵉ xᵉ yᵉ ≃ᵉ iso-Pregroupoidᵉ Gᵉ xᵉ yᵉ
  compute-iso-Pregroupoidᵉ = inv-equivᵉ inv-compute-iso-Pregroupoidᵉ
```

## See also

-ᵉ [Coresᵉ ofᵉ precategories](category-theory.cores-precategories.mdᵉ)

## External links

-ᵉ [Groupoids](https://1lab.dev/Cat.Groupoid.htmlᵉ) atᵉ 1labᵉ
-ᵉ [pregroupoid](https://ncatlab.org/nlab/show/pregroupoidᵉ) atᵉ $n$Labᵉ