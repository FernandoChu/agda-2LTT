# Coproducts in precategories

```agda
module category-theory.coproducts-in-precategoriesᵉ where
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

Weᵉ manuallyᵉ dualizeᵉ theᵉ definitionᵉ ofᵉ productsᵉ in precategoriesᵉ forᵉ convenience.ᵉ
Seeᵉ theᵉ documentationᵉ in thatᵉ fileᵉ forᵉ furtherᵉ information.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-coproduct-obj-Precategoryᵉ :
    (xᵉ yᵉ pᵉ : obj-Precategoryᵉ Cᵉ) →
    hom-Precategoryᵉ Cᵉ xᵉ pᵉ → hom-Precategoryᵉ Cᵉ yᵉ pᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-coproduct-obj-Precategoryᵉ xᵉ yᵉ pᵉ lᵉ rᵉ =
    (zᵉ : obj-Precategoryᵉ Cᵉ)
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ zᵉ) →
    (gᵉ : hom-Precategoryᵉ Cᵉ yᵉ zᵉ) →
    uniquely-exists-structureᵉ
      ( hom-Precategoryᵉ Cᵉ pᵉ zᵉ)
      ( λ hᵉ →
        ( comp-hom-Precategoryᵉ Cᵉ hᵉ lᵉ ＝ᵉ fᵉ) ×ᵉ
        ( comp-hom-Precategoryᵉ Cᵉ hᵉ rᵉ ＝ᵉ gᵉ))

  coproduct-obj-Precategoryᵉ :
    obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Cᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coproduct-obj-Precategoryᵉ xᵉ yᵉ =
    Σᵉ ( obj-Precategoryᵉ Cᵉ)
      ( λ pᵉ →
        Σᵉ ( hom-Precategoryᵉ Cᵉ xᵉ pᵉ)
          ( λ lᵉ →
            Σᵉ (hom-Precategoryᵉ Cᵉ yᵉ pᵉ)
              ( is-coproduct-obj-Precategoryᵉ xᵉ yᵉ pᵉ lᵉ)))

  has-all-binary-coproductsᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-all-binary-coproductsᵉ =
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) → coproduct-obj-Precategoryᵉ xᵉ yᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (tᵉ : has-all-binary-coproductsᵉ Cᵉ)
  where

  object-coproduct-obj-Precategoryᵉ :
    obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Cᵉ
  object-coproduct-obj-Precategoryᵉ xᵉ yᵉ = pr1ᵉ (tᵉ xᵉ yᵉ)

  inl-coproduct-obj-Precategoryᵉ :
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) →
    hom-Precategoryᵉ Cᵉ xᵉ (object-coproduct-obj-Precategoryᵉ xᵉ yᵉ)
  inl-coproduct-obj-Precategoryᵉ xᵉ yᵉ = pr1ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ))

  inr-coproduct-obj-Precategoryᵉ :
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) →
    hom-Precategoryᵉ Cᵉ yᵉ (object-coproduct-obj-Precategoryᵉ xᵉ yᵉ)
  inr-coproduct-obj-Precategoryᵉ xᵉ yᵉ =
    pr1ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ)))

  module _
    (xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ)
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ zᵉ)
    (gᵉ : hom-Precategoryᵉ Cᵉ yᵉ zᵉ)
    where

    morphism-out-of-coproduct-obj-Precategoryᵉ :
      hom-Precategoryᵉ Cᵉ (object-coproduct-obj-Precategoryᵉ xᵉ yᵉ) zᵉ
    morphism-out-of-coproduct-obj-Precategoryᵉ =
      pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ))) zᵉ fᵉ gᵉ))

    morphism-out-of-coproduct-obj-Precategory-comm-inlᵉ :
      comp-hom-Precategoryᵉ
        ( Cᵉ)
        ( morphism-out-of-coproduct-obj-Precategoryᵉ)
        ( inl-coproduct-obj-Precategoryᵉ xᵉ yᵉ) ＝ᵉ fᵉ
    morphism-out-of-coproduct-obj-Precategory-comm-inlᵉ =
      pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ))) zᵉ fᵉ gᵉ)))

    morphism-out-of-coproduct-obj-Precategory-comm-inrᵉ :
      comp-hom-Precategoryᵉ
        ( Cᵉ)
        ( morphism-out-of-coproduct-obj-Precategoryᵉ)
        ( inr-coproduct-obj-Precategoryᵉ xᵉ yᵉ) ＝ᵉ gᵉ
    morphism-out-of-coproduct-obj-Precategory-comm-inrᵉ =
      pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ))) zᵉ fᵉ gᵉ)))

    is-unique-morphism-out-of-coproduct-obj-Precategoryᵉ :
      (hᵉ : hom-Precategoryᵉ Cᵉ (object-coproduct-obj-Precategoryᵉ xᵉ yᵉ) zᵉ) →
      comp-hom-Precategoryᵉ Cᵉ hᵉ (inl-coproduct-obj-Precategoryᵉ xᵉ yᵉ) ＝ᵉ fᵉ →
      comp-hom-Precategoryᵉ Cᵉ hᵉ (inr-coproduct-obj-Precategoryᵉ xᵉ yᵉ) ＝ᵉ gᵉ →
      morphism-out-of-coproduct-obj-Precategoryᵉ ＝ᵉ hᵉ
    is-unique-morphism-out-of-coproduct-obj-Precategoryᵉ hᵉ comm1ᵉ comm2ᵉ =
      apᵉ pr1ᵉ ((pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ))) zᵉ fᵉ gᵉ)) (hᵉ ,ᵉ (comm1ᵉ ,ᵉ comm2ᵉ)))

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (xᵉ yᵉ pᵉ : obj-Precategoryᵉ Cᵉ)
  (lᵉ : hom-Precategoryᵉ Cᵉ xᵉ pᵉ)
  (rᵉ : hom-Precategoryᵉ Cᵉ yᵉ pᵉ)
  where

  is-prop-is-coproduct-obj-Precategoryᵉ :
    is-propᵉ (is-coproduct-obj-Precategoryᵉ Cᵉ xᵉ yᵉ pᵉ lᵉ rᵉ)
  is-prop-is-coproduct-obj-Precategoryᵉ =
    is-prop-iterated-Πᵉ 3 (λ zᵉ fᵉ gᵉ → is-property-is-contrᵉ)

  is-coproduct-prop-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ is-coproduct-prop-Precategoryᵉ = is-coproduct-obj-Precategoryᵉ Cᵉ xᵉ yᵉ pᵉ lᵉ rᵉ
  pr2ᵉ is-coproduct-prop-Precategoryᵉ = is-prop-is-coproduct-obj-Precategoryᵉ
```

## Properties

### Coproducts of morphisms

Ifᵉ `C`ᵉ hasᵉ allᵉ binaryᵉ coproductsᵉ thenᵉ forᵉ anyᵉ pairᵉ ofᵉ morphismsᵉ `fᵉ : homᵉ x₁ᵉ y₁`ᵉ
andᵉ `gᵉ : homᵉ x₂ᵉ y₂`ᵉ weᵉ canᵉ constructᵉ aᵉ morphismᵉ
`fᵉ +ᵉ gᵉ : homᵉ (x₁ᵉ +ᵉ x₂ᵉ) (y₁ᵉ +ᵉ y₂)`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (tᵉ : has-all-binary-coproductsᵉ Cᵉ)
  {x₁ᵉ x₂ᵉ y₁ᵉ y₂ᵉ : obj-Precategoryᵉ Cᵉ}
  (fᵉ : hom-Precategoryᵉ Cᵉ x₁ᵉ y₁ᵉ)
  (gᵉ : hom-Precategoryᵉ Cᵉ x₂ᵉ y₂ᵉ)
  where

  map-coproduct-obj-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ
      (object-coproduct-obj-Precategoryᵉ Cᵉ tᵉ x₁ᵉ x₂ᵉ)
      (object-coproduct-obj-Precategoryᵉ Cᵉ tᵉ y₁ᵉ y₂ᵉ)
  map-coproduct-obj-Precategoryᵉ =
    morphism-out-of-coproduct-obj-Precategoryᵉ Cᵉ tᵉ _ _ _
      (comp-hom-Precategoryᵉ Cᵉ (inl-coproduct-obj-Precategoryᵉ Cᵉ tᵉ y₁ᵉ y₂ᵉ) fᵉ)
      (comp-hom-Precategoryᵉ Cᵉ (inr-coproduct-obj-Precategoryᵉ Cᵉ tᵉ y₁ᵉ y₂ᵉ) gᵉ)
```