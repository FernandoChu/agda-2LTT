# Endomorphisms in precategories

```agda
module category-theory.endomorphisms-in-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Definition

### The monoid of endomorphisms on an object in a precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Xᵉ : obj-Precategoryᵉ Cᵉ)
  where

  type-endo-Precategoryᵉ : UUᵉ l2ᵉ
  type-endo-Precategoryᵉ = hom-Precategoryᵉ Cᵉ Xᵉ Xᵉ

  comp-endo-Precategoryᵉ :
    type-endo-Precategoryᵉ → type-endo-Precategoryᵉ → type-endo-Precategoryᵉ
  comp-endo-Precategoryᵉ gᵉ fᵉ = comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ

  id-endo-Precategoryᵉ : type-endo-Precategoryᵉ
  id-endo-Precategoryᵉ = id-hom-Precategoryᵉ Cᵉ

  associative-comp-endo-Precategoryᵉ :
    (hᵉ gᵉ fᵉ : type-endo-Precategoryᵉ) →
    ( comp-endo-Precategoryᵉ (comp-endo-Precategoryᵉ hᵉ gᵉ) fᵉ) ＝ᵉ
    ( comp-endo-Precategoryᵉ hᵉ (comp-endo-Precategoryᵉ gᵉ fᵉ))
  associative-comp-endo-Precategoryᵉ = associative-comp-hom-Precategoryᵉ Cᵉ

  left-unit-law-comp-endo-Precategoryᵉ :
    (fᵉ : type-endo-Precategoryᵉ) →
    comp-endo-Precategoryᵉ id-endo-Precategoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-endo-Precategoryᵉ = left-unit-law-comp-hom-Precategoryᵉ Cᵉ

  right-unit-law-comp-endo-Precategoryᵉ :
    (fᵉ : type-endo-Precategoryᵉ) →
    comp-endo-Precategoryᵉ fᵉ id-endo-Precategoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-endo-Precategoryᵉ = right-unit-law-comp-hom-Precategoryᵉ Cᵉ

  set-endo-Precategoryᵉ : Setᵉ l2ᵉ
  set-endo-Precategoryᵉ = hom-set-Precategoryᵉ Cᵉ Xᵉ Xᵉ

  semigroup-endo-Precategoryᵉ : Semigroupᵉ l2ᵉ
  pr1ᵉ semigroup-endo-Precategoryᵉ = set-endo-Precategoryᵉ
  pr1ᵉ (pr2ᵉ semigroup-endo-Precategoryᵉ) = comp-endo-Precategoryᵉ
  pr2ᵉ (pr2ᵉ semigroup-endo-Precategoryᵉ) = associative-comp-endo-Precategoryᵉ

  monoid-endo-Precategoryᵉ : Monoidᵉ l2ᵉ
  pr1ᵉ monoid-endo-Precategoryᵉ = semigroup-endo-Precategoryᵉ
  pr1ᵉ (pr2ᵉ monoid-endo-Precategoryᵉ) = id-endo-Precategoryᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ monoid-endo-Precategoryᵉ)) = left-unit-law-comp-endo-Precategoryᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ monoid-endo-Precategoryᵉ)) = right-unit-law-comp-endo-Precategoryᵉ
```