# Pointed endofunctors on categories

```agda
module category-theory.pointed-endofunctors-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.functors-categoriesᵉ
open import category-theory.natural-transformations-functors-categoriesᵉ
open import category-theory.pointed-endofunctors-precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ [endofunctor](category-theory.functors-categories.mdᵉ) `Fᵉ : Cᵉ → C`ᵉ onᵉ aᵉ
[category](category-theory.categories.mdᵉ) `C`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "pointed"ᵉ Disambiguation="endofunctorᵉ onᵉ aᵉ category"ᵉ Agda=pointed-endofunctor-Categoryᵉ}}
ifᵉ itᵉ comesᵉ equippedᵉ with aᵉ
[naturalᵉ transformation](category-theory.natural-transformations-functors-categories.mdᵉ)
`idᵉ ⇒ᵉ F`ᵉ fromᵉ theᵉ identityᵉ [functor](category-theory.functors-categories.mdᵉ) to
`F`.ᵉ

Moreᵉ explicitly,ᵉ aᵉ
{{#conceptᵉ "pointing"ᵉ Disambiguation="endofunctorᵉ onᵉ aᵉ category"ᵉ Agda=pointing-endofunctor-Categoryᵉ}}
ofᵉ anᵉ endofunctorᵉ `Fᵉ : Cᵉ → C`ᵉ consistsᵉ ofᵉ aᵉ familyᵉ ofᵉ morphismsᵉ `ηᵉ Xᵉ : Xᵉ → Fᵉ X`ᵉ
suchᵉ thatᵉ forᵉ eachᵉ morphismᵉ `fᵉ : Xᵉ → Y`ᵉ in `C`ᵉ theᵉ diagramᵉ

```text
       ηᵉ Xᵉ
    Xᵉ ----->ᵉ Fᵉ Xᵉ
    |         |
  fᵉ |         | Fᵉ fᵉ
    ∨ᵉ         ∨ᵉ
    Yᵉ ----->ᵉ Fᵉ Yᵉ
       ηᵉ Yᵉ
```

[commutes](category-theory.commuting-squares-of-morphisms-in-precategories.md).ᵉ

## Definitions

### The structure of a pointing on an endofunctor on a category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Tᵉ : functor-Categoryᵉ Cᵉ Cᵉ)
  where

  pointing-endofunctor-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  pointing-endofunctor-Categoryᵉ =
    pointing-endofunctor-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ
```

### Pointed endofunctors on a category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  pointed-endofunctor-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  pointed-endofunctor-Categoryᵉ =
    pointed-endofunctor-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  module _
    (Fᵉ : pointed-endofunctor-Categoryᵉ)
    where

    functor-pointed-endofunctor-Categoryᵉ :
      functor-Categoryᵉ Cᵉ Cᵉ
    functor-pointed-endofunctor-Categoryᵉ =
      functor-pointed-endofunctor-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Fᵉ

    obj-pointed-endofunctor-Categoryᵉ : obj-Categoryᵉ Cᵉ → obj-Categoryᵉ Cᵉ
    obj-pointed-endofunctor-Categoryᵉ =
      obj-pointed-endofunctor-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Fᵉ

    hom-pointed-endofunctor-Categoryᵉ :
      {Xᵉ Yᵉ : obj-Categoryᵉ Cᵉ} →
      hom-Categoryᵉ Cᵉ Xᵉ Yᵉ →
      hom-Categoryᵉ Cᵉ
        ( obj-pointed-endofunctor-Categoryᵉ Xᵉ)
        ( obj-pointed-endofunctor-Categoryᵉ Yᵉ)
    hom-pointed-endofunctor-Categoryᵉ =
      hom-pointed-endofunctor-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Fᵉ

    preserves-id-pointed-endofunctor-Categoryᵉ :
      (Xᵉ : obj-Categoryᵉ Cᵉ) →
      hom-pointed-endofunctor-Categoryᵉ (id-hom-Categoryᵉ Cᵉ {Xᵉ}) ＝ᵉ
      id-hom-Categoryᵉ Cᵉ
    preserves-id-pointed-endofunctor-Categoryᵉ =
      preserves-id-pointed-endofunctor-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Fᵉ

    preserves-comp-pointed-endofunctor-Categoryᵉ :
      {Xᵉ Yᵉ Zᵉ : obj-Categoryᵉ Cᵉ}
      (gᵉ : hom-Categoryᵉ Cᵉ Yᵉ Zᵉ) (fᵉ : hom-Categoryᵉ Cᵉ Xᵉ Yᵉ) →
      hom-pointed-endofunctor-Categoryᵉ
        ( comp-hom-Categoryᵉ Cᵉ gᵉ fᵉ) ＝ᵉ
      comp-hom-Categoryᵉ Cᵉ
        ( hom-pointed-endofunctor-Categoryᵉ gᵉ)
        ( hom-pointed-endofunctor-Categoryᵉ fᵉ)
    preserves-comp-pointed-endofunctor-Categoryᵉ =
      preserves-comp-pointed-endofunctor-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Fᵉ

    pointing-pointed-endofunctor-Categoryᵉ :
      natural-transformation-Categoryᵉ Cᵉ Cᵉ
        ( id-functor-Categoryᵉ Cᵉ)
        ( functor-pointed-endofunctor-Categoryᵉ)
    pointing-pointed-endofunctor-Categoryᵉ =
      pointing-pointed-endofunctor-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Fᵉ

    hom-family-pointing-pointed-endofunctor-Categoryᵉ :
      hom-family-functor-Categoryᵉ Cᵉ Cᵉ
        ( id-functor-Categoryᵉ Cᵉ)
        ( functor-pointed-endofunctor-Categoryᵉ)
    hom-family-pointing-pointed-endofunctor-Categoryᵉ =
      hom-family-pointing-pointed-endofunctor-Precategoryᵉ
        ( precategory-Categoryᵉ Cᵉ)
        ( Fᵉ)

    naturality-pointing-pointed-endofunctor-Categoryᵉ :
      is-natural-transformation-Categoryᵉ Cᵉ Cᵉ
        ( id-functor-Categoryᵉ Cᵉ)
        ( functor-pointed-endofunctor-Categoryᵉ)
        ( hom-family-pointing-pointed-endofunctor-Categoryᵉ)
    naturality-pointing-pointed-endofunctor-Categoryᵉ =
      naturality-pointing-pointed-endofunctor-Precategoryᵉ
        ( precategory-Categoryᵉ Cᵉ) Fᵉ
```