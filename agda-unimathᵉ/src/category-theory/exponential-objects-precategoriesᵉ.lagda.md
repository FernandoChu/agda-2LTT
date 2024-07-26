# Exponential objects in precategories

```agda
module category-theory.exponential-objects-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ
open import category-theory.products-in-precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.uniqueness-quantificationᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Letᵉ `C`ᵉ beᵉ aᵉ categoryᵉ with allᵉ binaryᵉ products.ᵉ Forᵉ objectsᵉ `x`ᵉ andᵉ `y`ᵉ in `C`,ᵉ
anᵉ exponentialᵉ (oftenᵉ denotedᵉ y^xᵉ) consistsᵉ ofᵉ:

-ᵉ anᵉ objectᵉ `e`ᵉ
-ᵉ aᵉ morphismᵉ `evᵉ : homᵉ (eᵉ ×ᵉ xᵉ) y`ᵉ suchᵉ thatᵉ forᵉ everyᵉ objectᵉ `z`ᵉ andᵉ morphismᵉ
  `fᵉ : homᵉ (zᵉ ×ᵉ xᵉ) y`ᵉ thereᵉ existsᵉ aᵉ uniqueᵉ morphismᵉ `gᵉ : homᵉ zᵉ e`ᵉ suchᵉ thatᵉ
-ᵉ `(gᵉ ×ᵉ idᵉ xᵉ) ∘ᵉ evᵉ = f`.ᵉ

Weᵉ sayᵉ thatᵉ `C`ᵉ hasᵉ allᵉ exponentialsᵉ ifᵉ thereᵉ isᵉ aᵉ choiceᵉ ofᵉ anᵉ exponentialᵉ forᵉ
eachᵉ pairᵉ ofᵉ objects.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (pᵉ : has-all-binary-products-Precategoryᵉ Cᵉ)
  where

  is-exponential-obj-Precategoryᵉ :
    (xᵉ yᵉ eᵉ : obj-Precategoryᵉ Cᵉ) →
    hom-Precategoryᵉ Cᵉ (object-product-obj-Precategoryᵉ Cᵉ pᵉ eᵉ xᵉ) yᵉ →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-exponential-obj-Precategoryᵉ xᵉ yᵉ eᵉ evᵉ =
    (zᵉ : obj-Precategoryᵉ Cᵉ)
    (fᵉ : hom-Precategoryᵉ Cᵉ (object-product-obj-Precategoryᵉ Cᵉ pᵉ zᵉ xᵉ) yᵉ) →
    uniquely-exists-structureᵉ
      ( hom-Precategoryᵉ Cᵉ zᵉ eᵉ)
      ( λ gᵉ →
        comp-hom-Precategoryᵉ Cᵉ evᵉ
          ( map-product-obj-Precategoryᵉ Cᵉ pᵉ gᵉ (id-hom-Precategoryᵉ Cᵉ)) ＝ᵉ
          ( fᵉ))

  exponential-obj-Precategoryᵉ :
    obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Cᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  exponential-obj-Precategoryᵉ xᵉ yᵉ =
    Σᵉ (obj-Precategoryᵉ Cᵉ) (λ eᵉ →
    Σᵉ (hom-Precategoryᵉ Cᵉ (object-product-obj-Precategoryᵉ Cᵉ pᵉ eᵉ xᵉ) yᵉ) λ evᵉ →
      is-exponential-obj-Precategoryᵉ xᵉ yᵉ eᵉ evᵉ)

  has-all-exponentials-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-all-exponentials-Precategoryᵉ =
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) → exponential-obj-Precategoryᵉ xᵉ yᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (pᵉ : has-all-binary-products-Precategoryᵉ Cᵉ)
  (tᵉ : has-all-exponentials-Precategoryᵉ Cᵉ pᵉ)
  (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ)
  where

  object-exponential-obj-Precategoryᵉ : obj-Precategoryᵉ Cᵉ
  object-exponential-obj-Precategoryᵉ = pr1ᵉ (tᵉ xᵉ yᵉ)

  eval-exponential-obj-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ
      ( object-product-obj-Precategoryᵉ Cᵉ pᵉ object-exponential-obj-Precategoryᵉ xᵉ)
      ( yᵉ)
  eval-exponential-obj-Precategoryᵉ = pr1ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ))

  module _
    (zᵉ : obj-Precategoryᵉ Cᵉ)
    (fᵉ : hom-Precategoryᵉ Cᵉ (object-product-obj-Precategoryᵉ Cᵉ pᵉ zᵉ xᵉ) yᵉ)
    where

    morphism-into-exponential-obj-Precategoryᵉ :
      hom-Precategoryᵉ Cᵉ zᵉ object-exponential-obj-Precategoryᵉ
    morphism-into-exponential-obj-Precategoryᵉ =
      pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ)) zᵉ fᵉ))

    morphism-into-exponential-obj-Precategory-commᵉ :
      ( comp-hom-Precategoryᵉ Cᵉ
        ( eval-exponential-obj-Precategoryᵉ)
        ( map-product-obj-Precategoryᵉ Cᵉ pᵉ
          ( morphism-into-exponential-obj-Precategoryᵉ)
          ( id-hom-Precategoryᵉ Cᵉ))) ＝ᵉ
      ( fᵉ)
    morphism-into-exponential-obj-Precategory-commᵉ =
      pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ)) zᵉ fᵉ))

    is-unique-morphism-into-exponential-obj-Precategoryᵉ :
      ( gᵉ : hom-Precategoryᵉ Cᵉ zᵉ object-exponential-obj-Precategoryᵉ) →
      ( comp-hom-Precategoryᵉ Cᵉ
        ( eval-exponential-obj-Precategoryᵉ)
        ( map-product-obj-Precategoryᵉ Cᵉ pᵉ gᵉ (id-hom-Precategoryᵉ Cᵉ)) ＝ᵉ fᵉ) →
      morphism-into-exponential-obj-Precategoryᵉ ＝ᵉ gᵉ
    is-unique-morphism-into-exponential-obj-Precategoryᵉ gᵉ qᵉ =
      apᵉ pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ)) zᵉ fᵉ) (gᵉ ,ᵉ qᵉ))
```