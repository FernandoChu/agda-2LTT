# Products of precategories

```agda
module category-theory.products-of-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "product"ᵉ Disambiguation="ofᵉ precategories"ᵉ Agda=product-Precategoryᵉ}}
ofᵉ twoᵉ [precategories](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ `D`ᵉ hasᵉ asᵉ
objectsᵉ [pairs](foundation-core.cartesian-product-types.mdᵉ) `(xᵉ ,ᵉ y)`,ᵉ where `x`ᵉ
isᵉ anᵉ objectᵉ ofᵉ `C`ᵉ andᵉ `y`ᵉ isᵉ anᵉ objectᵉ ofᵉ `D`,ᵉ andᵉ hasᵉ asᵉ morphismsᵉ fromᵉ
`(xᵉ ,ᵉ y)`ᵉ to `(x'ᵉ ,ᵉ y)`ᵉ pairsᵉ `(fᵉ ,ᵉ g)`ᵉ where `fᵉ : xᵉ → x'`ᵉ in `C`ᵉ andᵉ
`gᵉ : yᵉ → y'`ᵉ in `D`.ᵉ Compositionᵉ ofᵉ morphismsᵉ isᵉ givenᵉ componentwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  obj-product-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  obj-product-Precategoryᵉ = obj-Precategoryᵉ Cᵉ ×ᵉ obj-Precategoryᵉ Dᵉ

  hom-set-product-Precategoryᵉ :
    obj-product-Precategoryᵉ → obj-product-Precategoryᵉ → Setᵉ (l2ᵉ ⊔ l4ᵉ)
  hom-set-product-Precategoryᵉ (xᵉ ,ᵉ yᵉ) (x'ᵉ ,ᵉ y'ᵉ) =
    product-Setᵉ (hom-set-Precategoryᵉ Cᵉ xᵉ x'ᵉ) (hom-set-Precategoryᵉ Dᵉ yᵉ y'ᵉ)

  hom-product-Precategoryᵉ :
    obj-product-Precategoryᵉ → obj-product-Precategoryᵉ → UUᵉ (l2ᵉ ⊔ l4ᵉ)
  hom-product-Precategoryᵉ pᵉ qᵉ = type-Setᵉ (hom-set-product-Precategoryᵉ pᵉ qᵉ)

  is-set-hom-product-Precategoryᵉ :
    (pᵉ qᵉ : obj-product-Precategoryᵉ) → is-setᵉ (hom-product-Precategoryᵉ pᵉ qᵉ)
  is-set-hom-product-Precategoryᵉ pᵉ qᵉ =
    is-set-type-Setᵉ (hom-set-product-Precategoryᵉ pᵉ qᵉ)

  comp-hom-product-Precategoryᵉ :
    {pᵉ qᵉ rᵉ : obj-product-Precategoryᵉ}
    (gᵉ : hom-product-Precategoryᵉ qᵉ rᵉ)
    (fᵉ : hom-product-Precategoryᵉ pᵉ qᵉ) →
    hom-product-Precategoryᵉ pᵉ rᵉ
  comp-hom-product-Precategoryᵉ (f'ᵉ ,ᵉ g'ᵉ) (fᵉ ,ᵉ gᵉ) =
    ( comp-hom-Precategoryᵉ Cᵉ f'ᵉ fᵉ ,ᵉ comp-hom-Precategoryᵉ Dᵉ g'ᵉ gᵉ)

  id-hom-product-Precategoryᵉ :
    {pᵉ : obj-product-Precategoryᵉ} → hom-product-Precategoryᵉ pᵉ pᵉ
  id-hom-product-Precategoryᵉ = id-hom-Precategoryᵉ Cᵉ ,ᵉ id-hom-Precategoryᵉ Dᵉ

  associative-comp-hom-product-Precategoryᵉ :
    {pᵉ qᵉ rᵉ sᵉ : obj-product-Precategoryᵉ}
    (hᵉ : hom-product-Precategoryᵉ rᵉ sᵉ)
    (gᵉ : hom-product-Precategoryᵉ qᵉ rᵉ)
    (fᵉ : hom-product-Precategoryᵉ pᵉ qᵉ) →
    comp-hom-product-Precategoryᵉ (comp-hom-product-Precategoryᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-product-Precategoryᵉ hᵉ (comp-hom-product-Precategoryᵉ gᵉ fᵉ)
  associative-comp-hom-product-Precategoryᵉ (f''ᵉ ,ᵉ g''ᵉ) (f'ᵉ ,ᵉ g'ᵉ) (fᵉ ,ᵉ gᵉ) =
    eq-pairᵉ
      ( associative-comp-hom-Precategoryᵉ Cᵉ f''ᵉ f'ᵉ fᵉ)
      ( associative-comp-hom-Precategoryᵉ Dᵉ g''ᵉ g'ᵉ gᵉ)

  left-unit-law-comp-hom-product-Precategoryᵉ :
    {pᵉ qᵉ : obj-product-Precategoryᵉ}
    (fᵉ : hom-product-Precategoryᵉ pᵉ qᵉ) →
    comp-hom-product-Precategoryᵉ id-hom-product-Precategoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-product-Precategoryᵉ (fᵉ ,ᵉ gᵉ) =
    eq-pairᵉ
      ( left-unit-law-comp-hom-Precategoryᵉ Cᵉ fᵉ)
      ( left-unit-law-comp-hom-Precategoryᵉ Dᵉ gᵉ)

  right-unit-law-comp-hom-product-Precategoryᵉ :
    {pᵉ qᵉ : obj-product-Precategoryᵉ}
    (fᵉ : hom-product-Precategoryᵉ pᵉ qᵉ) →
    comp-hom-product-Precategoryᵉ fᵉ id-hom-product-Precategoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-product-Precategoryᵉ (fᵉ ,ᵉ gᵉ) =
    eq-pairᵉ
      ( right-unit-law-comp-hom-Precategoryᵉ Cᵉ fᵉ)
      ( right-unit-law-comp-hom-Precategoryᵉ Dᵉ gᵉ)

  product-Precategoryᵉ : Precategoryᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l4ᵉ)
  product-Precategoryᵉ =
    make-Precategoryᵉ
      ( obj-product-Precategoryᵉ)
      ( hom-set-product-Precategoryᵉ)
      ( comp-hom-product-Precategoryᵉ)
      ( λ xᵉ → id-hom-product-Precategoryᵉ {xᵉ})
      ( associative-comp-hom-product-Precategoryᵉ)
      ( left-unit-law-comp-hom-product-Precategoryᵉ)
      ( right-unit-law-comp-hom-product-Precategoryᵉ)
```