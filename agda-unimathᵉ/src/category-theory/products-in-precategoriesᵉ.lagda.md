# Products in precategories

```agda
module category-theory.products-in-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.uniqueness-quantificationᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ productᵉ ofᵉ twoᵉ objectsᵉ `x`ᵉ andᵉ `x`ᵉ in aᵉ categoryᵉ `C`ᵉ consistsᵉ ofᵉ:

-ᵉ anᵉ objectᵉ `p`ᵉ
-ᵉ morphismsᵉ `lᵉ : homᵉ pᵉ x`ᵉ andᵉ `rᵉ : homᵉ pᵉ y`ᵉ suchᵉ thatᵉ forᵉ everyᵉ objectᵉ `z`ᵉ andᵉ
  morphismsᵉ `fᵉ : homᵉ zᵉ x`ᵉ andᵉ `gᵉ : homᵉ zᵉ y`ᵉ thereᵉ existsᵉ aᵉ uniqueᵉ morphismᵉ
  `hᵉ : homᵉ zᵉ p`ᵉ suchᵉ thatᵉ
-ᵉ `lᵉ ∘ᵉ hᵉ = f`ᵉ
-ᵉ `rᵉ ∘ᵉ hᵉ = g`.ᵉ

Weᵉ sayᵉ thatᵉ `C`ᵉ hasᵉ allᵉ binaryᵉ productsᵉ ifᵉ thereᵉ isᵉ aᵉ choiceᵉ ofᵉ aᵉ productᵉ forᵉ
eachᵉ pairᵉ ofᵉ objectsᵉ in `C`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-product-obj-Precategoryᵉ :
    (xᵉ yᵉ pᵉ : obj-Precategoryᵉ Cᵉ) →
    hom-Precategoryᵉ Cᵉ pᵉ xᵉ →
    hom-Precategoryᵉ Cᵉ pᵉ yᵉ →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-product-obj-Precategoryᵉ xᵉ yᵉ pᵉ lᵉ rᵉ =
    (zᵉ : obj-Precategoryᵉ Cᵉ)
    (fᵉ : hom-Precategoryᵉ Cᵉ zᵉ xᵉ) →
    (gᵉ : hom-Precategoryᵉ Cᵉ zᵉ yᵉ) →
    ( uniquely-exists-structureᵉ
      ( hom-Precategoryᵉ Cᵉ zᵉ pᵉ)
      ( λ hᵉ →
        ( comp-hom-Precategoryᵉ Cᵉ lᵉ hᵉ ＝ᵉ fᵉ) ×ᵉ
        ( comp-hom-Precategoryᵉ Cᵉ rᵉ hᵉ ＝ᵉ gᵉ)))

  product-obj-Precategoryᵉ : obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Cᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  product-obj-Precategoryᵉ xᵉ yᵉ =
    Σᵉ (obj-Precategoryᵉ Cᵉ) λ pᵉ →
    Σᵉ (hom-Precategoryᵉ Cᵉ pᵉ xᵉ) λ lᵉ →
    Σᵉ (hom-Precategoryᵉ Cᵉ pᵉ yᵉ) λ rᵉ →
      is-product-obj-Precategoryᵉ xᵉ yᵉ pᵉ lᵉ rᵉ

  has-all-binary-products-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-all-binary-products-Precategoryᵉ =
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) → product-obj-Precategoryᵉ xᵉ yᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (tᵉ : has-all-binary-products-Precategoryᵉ Cᵉ)
  where

  object-product-obj-Precategoryᵉ :
    obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Cᵉ
  object-product-obj-Precategoryᵉ xᵉ yᵉ = pr1ᵉ (tᵉ xᵉ yᵉ)

  pr1-product-obj-Precategoryᵉ :
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) →
    hom-Precategoryᵉ Cᵉ (object-product-obj-Precategoryᵉ xᵉ yᵉ) xᵉ
  pr1-product-obj-Precategoryᵉ xᵉ yᵉ = pr1ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ))

  pr2-product-obj-Precategoryᵉ :
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) →
    hom-Precategoryᵉ Cᵉ (object-product-obj-Precategoryᵉ xᵉ yᵉ) yᵉ
  pr2-product-obj-Precategoryᵉ xᵉ yᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ)))

  module _
    (xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ)
    (fᵉ : hom-Precategoryᵉ Cᵉ zᵉ xᵉ)
    (gᵉ : hom-Precategoryᵉ Cᵉ zᵉ yᵉ)
    where

    morphism-into-product-obj-Precategoryᵉ :
      hom-Precategoryᵉ Cᵉ zᵉ (object-product-obj-Precategoryᵉ xᵉ yᵉ)
    morphism-into-product-obj-Precategoryᵉ =
      pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ))) zᵉ fᵉ gᵉ))

    morphism-into-product-obj-Precategory-comm-pr1ᵉ :
      comp-hom-Precategoryᵉ Cᵉ
        ( pr1-product-obj-Precategoryᵉ xᵉ yᵉ)
        ( morphism-into-product-obj-Precategoryᵉ) ＝ᵉ fᵉ
    morphism-into-product-obj-Precategory-comm-pr1ᵉ =
      pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ))) zᵉ fᵉ gᵉ)))

    morphism-into-product-obj-Precategory-comm-pr2ᵉ :
      comp-hom-Precategoryᵉ Cᵉ
        ( pr2-product-obj-Precategoryᵉ xᵉ yᵉ)
        ( morphism-into-product-obj-Precategoryᵉ) ＝ᵉ gᵉ
    morphism-into-product-obj-Precategory-comm-pr2ᵉ =
      pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ))) zᵉ fᵉ gᵉ)))

    is-unique-morphism-into-product-obj-Precategoryᵉ :
      (hᵉ : hom-Precategoryᵉ Cᵉ zᵉ (object-product-obj-Precategoryᵉ xᵉ yᵉ)) →
      comp-hom-Precategoryᵉ Cᵉ (pr1-product-obj-Precategoryᵉ xᵉ yᵉ) hᵉ ＝ᵉ fᵉ →
      comp-hom-Precategoryᵉ Cᵉ (pr2-product-obj-Precategoryᵉ xᵉ yᵉ) hᵉ ＝ᵉ gᵉ →
      morphism-into-product-obj-Precategoryᵉ ＝ᵉ hᵉ
    is-unique-morphism-into-product-obj-Precategoryᵉ hᵉ comm1ᵉ comm2ᵉ =
      apᵉ pr1ᵉ ((pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ))) zᵉ fᵉ gᵉ)) (hᵉ ,ᵉ (comm1ᵉ ,ᵉ comm2ᵉ)))

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (xᵉ yᵉ pᵉ : obj-Precategoryᵉ Cᵉ)
  (lᵉ : hom-Precategoryᵉ Cᵉ pᵉ xᵉ)
  (rᵉ : hom-Precategoryᵉ Cᵉ pᵉ yᵉ)
  where

  is-prop-is-product-obj-Precategoryᵉ :
    is-propᵉ (is-product-obj-Precategoryᵉ Cᵉ xᵉ yᵉ pᵉ lᵉ rᵉ)
  is-prop-is-product-obj-Precategoryᵉ =
    is-prop-iterated-Πᵉ 3 (λ zᵉ fᵉ gᵉ → is-property-is-contrᵉ)

  is-product-prop-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ is-product-prop-Precategoryᵉ = is-product-obj-Precategoryᵉ Cᵉ xᵉ yᵉ pᵉ lᵉ rᵉ
  pr2ᵉ is-product-prop-Precategoryᵉ = is-prop-is-product-obj-Precategoryᵉ
```

## Properties

### Products of morphisms

Ifᵉ `C`ᵉ hasᵉ allᵉ binaryᵉ productsᵉ thenᵉ forᵉ anyᵉ pairᵉ ofᵉ morphismsᵉ `fᵉ : homᵉ x₁ᵉ y₁`ᵉ
andᵉ `gᵉ : homᵉ x₂ᵉ y₂`ᵉ weᵉ canᵉ constructᵉ aᵉ morphismᵉ
`fᵉ ×ᵉ gᵉ : homᵉ (x₁ᵉ ×ᵉ x₂ᵉ) (y₁ᵉ ×ᵉ y₂)`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (tᵉ : has-all-binary-products-Precategoryᵉ Cᵉ)
  {x₁ᵉ x₂ᵉ y₁ᵉ y₂ᵉ : obj-Precategoryᵉ Cᵉ}
  (fᵉ : hom-Precategoryᵉ Cᵉ x₁ᵉ y₁ᵉ)
  (gᵉ : hom-Precategoryᵉ Cᵉ x₂ᵉ y₂ᵉ)
  where

  map-product-obj-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ
      (object-product-obj-Precategoryᵉ Cᵉ tᵉ x₁ᵉ x₂ᵉ)
      (object-product-obj-Precategoryᵉ Cᵉ tᵉ y₁ᵉ y₂ᵉ)
  map-product-obj-Precategoryᵉ =
    morphism-into-product-obj-Precategoryᵉ Cᵉ tᵉ _ _ _
      (comp-hom-Precategoryᵉ Cᵉ fᵉ (pr1-product-obj-Precategoryᵉ Cᵉ tᵉ x₁ᵉ x₂ᵉ))
      (comp-hom-Precategoryᵉ Cᵉ gᵉ (pr2-product-obj-Precategoryᵉ Cᵉ tᵉ x₁ᵉ x₂ᵉ))
```