# Groupoids

```agda
module category-theory.groupoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.functors-categoriesᵉ
open import category-theory.isomorphisms-in-categoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.pregroupoidsᵉ

open import foundation.1-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **groupoid**ᵉ isᵉ aᵉ [category](category-theory.categories.mdᵉ) in whichᵉ everyᵉ
morphismᵉ isᵉ anᵉ [isomorphism](category-theory.isomorphisms-in-categories.md).ᵉ

## Definition

```agda
is-groupoid-prop-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-groupoid-prop-Categoryᵉ Cᵉ =
  is-pregroupoid-prop-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

is-groupoid-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-groupoid-Categoryᵉ Cᵉ =
  is-pregroupoid-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

Groupoidᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Groupoidᵉ l1ᵉ l2ᵉ = Σᵉ (Categoryᵉ l1ᵉ l2ᵉ) is-groupoid-Categoryᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupoidᵉ l1ᵉ l2ᵉ)
  where

  category-Groupoidᵉ : Categoryᵉ l1ᵉ l2ᵉ
  category-Groupoidᵉ = pr1ᵉ Gᵉ

  precategory-Groupoidᵉ : Precategoryᵉ l1ᵉ l2ᵉ
  precategory-Groupoidᵉ = precategory-Categoryᵉ category-Groupoidᵉ

  obj-Groupoidᵉ : UUᵉ l1ᵉ
  obj-Groupoidᵉ = obj-Categoryᵉ category-Groupoidᵉ

  hom-set-Groupoidᵉ : obj-Groupoidᵉ → obj-Groupoidᵉ → Setᵉ l2ᵉ
  hom-set-Groupoidᵉ = hom-set-Categoryᵉ category-Groupoidᵉ

  hom-Groupoidᵉ : obj-Groupoidᵉ → obj-Groupoidᵉ → UUᵉ l2ᵉ
  hom-Groupoidᵉ = hom-Categoryᵉ category-Groupoidᵉ

  id-hom-Groupoidᵉ :
    {xᵉ : obj-Groupoidᵉ} → hom-Groupoidᵉ xᵉ xᵉ
  id-hom-Groupoidᵉ = id-hom-Categoryᵉ category-Groupoidᵉ

  comp-hom-Groupoidᵉ :
    {xᵉ yᵉ zᵉ : obj-Groupoidᵉ} →
    hom-Groupoidᵉ yᵉ zᵉ → hom-Groupoidᵉ xᵉ yᵉ → hom-Groupoidᵉ xᵉ zᵉ
  comp-hom-Groupoidᵉ = comp-hom-Categoryᵉ category-Groupoidᵉ

  associative-comp-hom-Groupoidᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Groupoidᵉ}
    (hᵉ : hom-Groupoidᵉ zᵉ wᵉ) (gᵉ : hom-Groupoidᵉ yᵉ zᵉ) (fᵉ : hom-Groupoidᵉ xᵉ yᵉ) →
    comp-hom-Groupoidᵉ (comp-hom-Groupoidᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Groupoidᵉ hᵉ (comp-hom-Groupoidᵉ gᵉ fᵉ)
  associative-comp-hom-Groupoidᵉ =
    associative-comp-hom-Categoryᵉ category-Groupoidᵉ

  involutive-eq-associative-comp-hom-Groupoidᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Groupoidᵉ}
    (hᵉ : hom-Groupoidᵉ zᵉ wᵉ) (gᵉ : hom-Groupoidᵉ yᵉ zᵉ) (fᵉ : hom-Groupoidᵉ xᵉ yᵉ) →
    comp-hom-Groupoidᵉ (comp-hom-Groupoidᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-Groupoidᵉ hᵉ (comp-hom-Groupoidᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Groupoidᵉ =
    involutive-eq-associative-comp-hom-Categoryᵉ category-Groupoidᵉ

  left-unit-law-comp-hom-Groupoidᵉ :
    {xᵉ yᵉ : obj-Groupoidᵉ} (fᵉ : hom-Groupoidᵉ xᵉ yᵉ) →
    ( comp-hom-Groupoidᵉ id-hom-Groupoidᵉ fᵉ) ＝ᵉ fᵉ
  left-unit-law-comp-hom-Groupoidᵉ =
    left-unit-law-comp-hom-Categoryᵉ category-Groupoidᵉ

  right-unit-law-comp-hom-Groupoidᵉ :
    {xᵉ yᵉ : obj-Groupoidᵉ} (fᵉ : hom-Groupoidᵉ xᵉ yᵉ) →
    ( comp-hom-Groupoidᵉ fᵉ id-hom-Groupoidᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Groupoidᵉ =
    right-unit-law-comp-hom-Categoryᵉ category-Groupoidᵉ

  iso-Groupoidᵉ : (xᵉ yᵉ : obj-Groupoidᵉ) → UUᵉ l2ᵉ
  iso-Groupoidᵉ = iso-Categoryᵉ category-Groupoidᵉ

  is-groupoid-Groupoidᵉ : is-groupoid-Categoryᵉ category-Groupoidᵉ
  is-groupoid-Groupoidᵉ = pr2ᵉ Gᵉ
```

## Property

### The type of groupoids with respect to universe levels `l1` and `l2` is equivalent to the type of 1-types in `l1`

#### The groupoid associated to a 1-type

```agda
module _
  {lᵉ : Level} (Xᵉ : 1-Typeᵉ lᵉ)
  where

  obj-groupoid-1-Typeᵉ : UUᵉ lᵉ
  obj-groupoid-1-Typeᵉ = type-1-Typeᵉ Xᵉ

  precategory-Groupoid-1-Typeᵉ : Precategoryᵉ lᵉ lᵉ
  precategory-Groupoid-1-Typeᵉ =
    make-Precategoryᵉ
      ( obj-groupoid-1-Typeᵉ)
      ( Id-Setᵉ Xᵉ)
      ( λ qᵉ pᵉ → pᵉ ∙ᵉ qᵉ)
      ( λ xᵉ → reflᵉ)
      ( λ rᵉ qᵉ pᵉ → invᵉ (assocᵉ pᵉ qᵉ rᵉ))
      ( λ pᵉ → right-unitᵉ)
      ( λ pᵉ → left-unitᵉ)

  is-category-groupoid-1-Typeᵉ :
    is-category-Precategoryᵉ precategory-Groupoid-1-Typeᵉ
  is-category-groupoid-1-Typeᵉ xᵉ =
    fundamental-theorem-idᵉ
      ( is-contr-equiv'ᵉ
        ( Σᵉ ( Σᵉ (type-1-Typeᵉ Xᵉ) (λ yᵉ → xᵉ ＝ᵉ yᵉ))
            ( λ (yᵉ ,ᵉ pᵉ) →
              Σᵉ ( Σᵉ (yᵉ ＝ᵉ xᵉ) (λ qᵉ → qᵉ ∙ᵉ pᵉ ＝ᵉ reflᵉ))
                ( λ (qᵉ ,ᵉ lᵉ) → pᵉ ∙ᵉ qᵉ ＝ᵉ reflᵉ)))
        ( ( equiv-totᵉ
            ( λ yᵉ →
              equiv-totᵉ
                ( λ pᵉ →
                  associative-Σᵉ
                    ( yᵉ ＝ᵉ xᵉ)
                    ( λ qᵉ → qᵉ ∙ᵉ pᵉ ＝ᵉ reflᵉ)
                    ( λ (qᵉ ,ᵉ rᵉ) → pᵉ ∙ᵉ qᵉ ＝ᵉ reflᵉ)))) ∘eᵉ
          ( associative-Σᵉ
            ( type-1-Typeᵉ Xᵉ)
            ( λ yᵉ → xᵉ ＝ᵉ yᵉ)
            ( λ (yᵉ ,ᵉ pᵉ) →
              Σᵉ ( Σᵉ (yᵉ ＝ᵉ xᵉ) (λ qᵉ → qᵉ ∙ᵉ pᵉ ＝ᵉ reflᵉ))
                ( λ (qᵉ ,ᵉ lᵉ) → pᵉ ∙ᵉ qᵉ ＝ᵉ reflᵉ))))
        ( is-contr-iterated-Σᵉ 2
          ( is-torsorial-Idᵉ xᵉ ,ᵉ
            ( xᵉ ,ᵉ reflᵉ) ,ᵉ
            ( is-contr-equivᵉ
              ( Σᵉ (xᵉ ＝ᵉ xᵉ) (λ qᵉ → qᵉ ＝ᵉ reflᵉ))
              ( equiv-totᵉ (λ qᵉ → equiv-concatᵉ (invᵉ right-unitᵉ) reflᵉ))
              ( is-torsorial-Id'ᵉ reflᵉ)) ,ᵉ
            ( reflᵉ ,ᵉ reflᵉ) ,ᵉ
            ( is-proof-irrelevant-is-propᵉ
              ( is-1-type-type-1-Typeᵉ Xᵉ xᵉ xᵉ reflᵉ reflᵉ)
              ( reflᵉ)))))
      ( iso-eq-Precategoryᵉ precategory-Groupoid-1-Typeᵉ xᵉ)

  is-groupoid-groupoid-1-Typeᵉ :
    is-pregroupoid-Precategoryᵉ precategory-Groupoid-1-Typeᵉ
  pr1ᵉ (is-groupoid-groupoid-1-Typeᵉ xᵉ yᵉ pᵉ) = invᵉ pᵉ
  pr1ᵉ (pr2ᵉ (is-groupoid-groupoid-1-Typeᵉ xᵉ yᵉ pᵉ)) = left-invᵉ pᵉ
  pr2ᵉ (pr2ᵉ (is-groupoid-groupoid-1-Typeᵉ xᵉ yᵉ pᵉ)) = right-invᵉ pᵉ

  groupoid-1-Typeᵉ : Groupoidᵉ lᵉ lᵉ
  pr1ᵉ (pr1ᵉ groupoid-1-Typeᵉ) = precategory-Groupoid-1-Typeᵉ
  pr2ᵉ (pr1ᵉ groupoid-1-Typeᵉ) = is-category-groupoid-1-Typeᵉ
  pr2ᵉ groupoid-1-Typeᵉ = is-groupoid-groupoid-1-Typeᵉ
```

#### The 1-type associated to a groupoid

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupoidᵉ l1ᵉ l2ᵉ)
  where

  1-type-Groupoidᵉ : 1-Typeᵉ l1ᵉ
  1-type-Groupoidᵉ = obj-1-type-Categoryᵉ (category-Groupoidᵉ Gᵉ)
```

#### The groupoid obtained from the 1-type induced by a groupoid `G` is `G` itself

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupoidᵉ l1ᵉ l2ᵉ)
  where

  functor-equiv-groupoid-1-type-Groupoidᵉ :
    functor-Categoryᵉ
      ( category-Groupoidᵉ (groupoid-1-Typeᵉ (1-type-Groupoidᵉ Gᵉ)))
      ( category-Groupoidᵉ Gᵉ)
  pr1ᵉ functor-equiv-groupoid-1-type-Groupoidᵉ = idᵉ
  pr1ᵉ (pr2ᵉ functor-equiv-groupoid-1-type-Groupoidᵉ) {xᵉ} {.xᵉ} reflᵉ =
    id-hom-Groupoidᵉ Gᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ functor-equiv-groupoid-1-type-Groupoidᵉ)) {xᵉ} reflᵉ reflᵉ =
    invᵉ (right-unit-law-comp-hom-Groupoidᵉ Gᵉ (id-hom-Groupoidᵉ Gᵉ))
  pr2ᵉ (pr2ᵉ (pr2ᵉ functor-equiv-groupoid-1-type-Groupoidᵉ)) xᵉ = reflᵉ
```

#### The 1-type obtained from the groupoid induced by a 1-type `X` is `X` itself

```agda
module _
  {lᵉ : Level} (Xᵉ : 1-Typeᵉ lᵉ)
  where

  equiv-1-type-groupoid-1-Typeᵉ :
    type-equiv-1-Typeᵉ (1-type-Groupoidᵉ (groupoid-1-Typeᵉ Xᵉ)) Xᵉ
  equiv-1-type-groupoid-1-Typeᵉ = id-equivᵉ
```

## External links

-ᵉ [univalentᵉ groupoid](https://ncatlab.org/nlab/show/univalent+groupoidᵉ) atᵉ
  $n$Labᵉ