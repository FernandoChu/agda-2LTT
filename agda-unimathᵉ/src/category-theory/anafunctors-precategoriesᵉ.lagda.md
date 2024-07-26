# Anafunctors between precategories

```agda
module category-theory.anafunctors-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ **anafunctor**ᵉ isᵉ aᵉ [functor](category-theory.functors-precategories.mdᵉ) thatᵉ
isᵉ onlyᵉ definedᵉ upᵉ to
[isomorphism](category-theory.isomorphisms-in-precategories.md).ᵉ

## Definition

```agda
anafunctor-Precategoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (lᵉ : Level) →
  Precategoryᵉ l1ᵉ l2ᵉ → Precategoryᵉ l3ᵉ l4ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ lsuc lᵉ)
anafunctor-Precategoryᵉ lᵉ Cᵉ Dᵉ =
  Σᵉ ( obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ → UUᵉ lᵉ)
    ( λ F₀ᵉ →
      Σᵉ ( ( Xᵉ Yᵉ : obj-Precategoryᵉ Cᵉ)
          ( Uᵉ : obj-Precategoryᵉ Dᵉ) (uᵉ : F₀ᵉ Xᵉ Uᵉ) →
          ( Vᵉ : obj-Precategoryᵉ Dᵉ) (vᵉ : F₀ᵉ Yᵉ Vᵉ) →
          ( fᵉ : hom-Precategoryᵉ Cᵉ Xᵉ Yᵉ) → hom-Precategoryᵉ Dᵉ Uᵉ Vᵉ)
        ( λ F₁ᵉ →
          ( ( Xᵉ : obj-Precategoryᵉ Cᵉ) →
            type-trunc-Propᵉ (Σᵉ (obj-Precategoryᵉ Dᵉ) (F₀ᵉ Xᵉ))) ×ᵉ
          ( ( ( Xᵉ : obj-Precategoryᵉ Cᵉ)
              ( Uᵉ : obj-Precategoryᵉ Dᵉ) (uᵉ : F₀ᵉ Xᵉ Uᵉ) →
              F₁ᵉ Xᵉ Xᵉ Uᵉ uᵉ Uᵉ uᵉ (id-hom-Precategoryᵉ Cᵉ) ＝ᵉ id-hom-Precategoryᵉ Dᵉ) ×ᵉ
            ( ( Xᵉ Yᵉ Zᵉ : obj-Precategoryᵉ Cᵉ)
              ( Uᵉ : obj-Precategoryᵉ Dᵉ) (uᵉ : F₀ᵉ Xᵉ Uᵉ)
              ( Vᵉ : obj-Precategoryᵉ Dᵉ) (vᵉ : F₀ᵉ Yᵉ Vᵉ)
              ( Wᵉ : obj-Precategoryᵉ Dᵉ) (wᵉ : F₀ᵉ Zᵉ Wᵉ) →
              ( gᵉ : hom-Precategoryᵉ Cᵉ Yᵉ Zᵉ)
              ( fᵉ : hom-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
              ( F₁ᵉ Xᵉ Zᵉ Uᵉ uᵉ Wᵉ wᵉ (comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ)) ＝ᵉ
              ( comp-hom-Precategoryᵉ Dᵉ
                ( F₁ᵉ Yᵉ Zᵉ Vᵉ vᵉ Wᵉ wᵉ gᵉ)
                ( F₁ᵉ Xᵉ Yᵉ Uᵉ uᵉ Vᵉ vᵉ fᵉ))))))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : anafunctor-Precategoryᵉ l5ᵉ Cᵉ Dᵉ)
  where

  object-anafunctor-Precategoryᵉ : obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ → UUᵉ l5ᵉ
  object-anafunctor-Precategoryᵉ = pr1ᵉ Fᵉ

  hom-anafunctor-Precategoryᵉ :
    (Xᵉ Yᵉ : obj-Precategoryᵉ Cᵉ)
    (Uᵉ : obj-Precategoryᵉ Dᵉ) (uᵉ : object-anafunctor-Precategoryᵉ Xᵉ Uᵉ)
    (Vᵉ : obj-Precategoryᵉ Dᵉ) (vᵉ : object-anafunctor-Precategoryᵉ Yᵉ Vᵉ) →
    hom-Precategoryᵉ Cᵉ Xᵉ Yᵉ → hom-Precategoryᵉ Dᵉ Uᵉ Vᵉ
  hom-anafunctor-Precategoryᵉ = pr1ᵉ (pr2ᵉ Fᵉ)
```

## Properties

### Any functor between precategories induces an anafunctor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  anafunctor-functor-Precategoryᵉ :
    functor-Precategoryᵉ Cᵉ Dᵉ → anafunctor-Precategoryᵉ l4ᵉ Cᵉ Dᵉ
  pr1ᵉ (anafunctor-functor-Precategoryᵉ Fᵉ) Xᵉ Yᵉ =
    iso-Precategoryᵉ Dᵉ (obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ Xᵉ) Yᵉ
  pr1ᵉ (pr2ᵉ (anafunctor-functor-Precategoryᵉ Fᵉ)) Xᵉ Yᵉ Uᵉ uᵉ Vᵉ vᵉ fᵉ =
    comp-hom-Precategoryᵉ Dᵉ
      ( comp-hom-Precategoryᵉ Dᵉ
        ( hom-iso-Precategoryᵉ Dᵉ vᵉ)
        ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ))
      ( hom-inv-iso-Precategoryᵉ Dᵉ uᵉ)
  pr1ᵉ (pr2ᵉ (pr2ᵉ (anafunctor-functor-Precategoryᵉ Fᵉ))) Xᵉ =
    unit-trunc-Propᵉ (obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ Xᵉ ,ᵉ id-iso-Precategoryᵉ Dᵉ)
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (anafunctor-functor-Precategoryᵉ Fᵉ)))) Xᵉ Uᵉ uᵉ =
    ( apᵉ
      ( comp-hom-Precategory'ᵉ Dᵉ (hom-inv-iso-Precategoryᵉ Dᵉ uᵉ))
      ( ( apᵉ
          ( comp-hom-Precategoryᵉ Dᵉ (hom-iso-Precategoryᵉ Dᵉ uᵉ))
          ( preserves-id-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ Xᵉ)) ∙ᵉ
        ( right-unit-law-comp-hom-Precategoryᵉ Dᵉ (hom-iso-Precategoryᵉ Dᵉ uᵉ)))) ∙ᵉ
    ( is-section-hom-inv-iso-Precategoryᵉ Dᵉ uᵉ)
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (anafunctor-functor-Precategoryᵉ Fᵉ))))
    Xᵉ Yᵉ Zᵉ Uᵉ uᵉ Vᵉ vᵉ Wᵉ wᵉ gᵉ fᵉ =
    ( apᵉ
      ( comp-hom-Precategory'ᵉ Dᵉ (hom-inv-iso-Precategoryᵉ Dᵉ uᵉ))
      ( ( ( apᵉ
            ( comp-hom-Precategoryᵉ Dᵉ (hom-iso-Precategoryᵉ Dᵉ wᵉ))
            ( preserves-comp-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ gᵉ fᵉ)) ∙ᵉ
          ( ( invᵉ
              ( associative-comp-hom-Precategoryᵉ Dᵉ
                ( hom-iso-Precategoryᵉ Dᵉ wᵉ)
                ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ gᵉ)
                ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ))) ∙ᵉ
            ( apᵉ
              ( comp-hom-Precategory'ᵉ Dᵉ (hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ))
              ( ( invᵉ
                  ( right-unit-law-comp-hom-Precategoryᵉ Dᵉ
                    ( comp-hom-Precategoryᵉ Dᵉ
                      ( hom-iso-Precategoryᵉ Dᵉ wᵉ)
                      ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ gᵉ)))) ∙ᵉ
                ( ( apᵉ
                    ( comp-hom-Precategoryᵉ Dᵉ
                      ( comp-hom-Precategoryᵉ Dᵉ
                        ( hom-iso-Precategoryᵉ Dᵉ wᵉ)
                        ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ gᵉ)))
                      ( invᵉ (is-retraction-hom-inv-iso-Precategoryᵉ Dᵉ vᵉ))) ∙ᵉ
                  ( invᵉ
                    ( associative-comp-hom-Precategoryᵉ Dᵉ
                      ( comp-hom-Precategoryᵉ Dᵉ
                        ( hom-iso-Precategoryᵉ Dᵉ wᵉ)
                        ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ gᵉ))
                      ( hom-inv-iso-Precategoryᵉ Dᵉ vᵉ)
                      ( hom-iso-Precategoryᵉ Dᵉ vᵉ)))))))) ∙ᵉ
        ( associative-comp-hom-Precategoryᵉ Dᵉ
          ( comp-hom-Precategoryᵉ Dᵉ
            ( comp-hom-Precategoryᵉ Dᵉ
              ( hom-iso-Precategoryᵉ Dᵉ wᵉ)
              ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ gᵉ))
            ( hom-inv-iso-Precategoryᵉ Dᵉ vᵉ))
          ( hom-iso-Precategoryᵉ Dᵉ vᵉ)
          ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ)))) ∙ᵉ
    ( associative-comp-hom-Precategoryᵉ Dᵉ
      ( comp-hom-Precategoryᵉ Dᵉ
        ( comp-hom-Precategoryᵉ Dᵉ
          ( hom-iso-Precategoryᵉ Dᵉ wᵉ)
          ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ gᵉ))
        ( hom-inv-iso-Precategoryᵉ Dᵉ vᵉ))
      ( comp-hom-Precategoryᵉ Dᵉ
        ( hom-iso-Precategoryᵉ Dᵉ vᵉ)
        ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ))
      ( hom-inv-iso-Precategoryᵉ Dᵉ uᵉ))
```