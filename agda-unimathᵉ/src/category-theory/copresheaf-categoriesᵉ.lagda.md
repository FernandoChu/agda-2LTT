# Copresheaf categories

```agda
module category-theory.copresheaf-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.category-of-functors-from-small-to-large-categoriesᵉ
open import category-theory.functors-from-small-to-large-precategoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.natural-transformations-functors-from-small-to-large-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.precategory-of-functors-from-small-to-large-precategoriesᵉ

open import foundation.category-of-setsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [precategory](category-theory.precategories.mdᵉ) `C`,ᵉ weᵉ canᵉ formᵉ itsᵉ
**copresheafᵉ [category](category-theory.large-categories.md)**ᵉ asᵉ theᵉ
[largeᵉ categoryᵉ ofᵉ functors](category-theory.functors-from-small-to-large-precategories.mdᵉ)
fromᵉ `C`,ᵉ intoᵉ theᵉ [largeᵉ categoryᵉ ofᵉ sets](foundation.category-of-sets.mdᵉ)

```text
  Cᵉ → Set.ᵉ
```

Toᵉ thisᵉ largeᵉ category,ᵉ thereᵉ isᵉ anᵉ associatedᵉ
[smallᵉ category](category-theory.categories.mdᵉ) ofᵉ smallᵉ copresheaves,ᵉ takingᵉ
valuesᵉ in smallᵉ [sets](foundation-core.sets.md).ᵉ

## Definitions

### The large category of copresheaves on a precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  copresheaf-large-precategory-Precategoryᵉ :
    Large-Precategoryᵉ (λ lᵉ → l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ) (λ lᵉ l'ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ lᵉ ⊔ l'ᵉ)
  copresheaf-large-precategory-Precategoryᵉ =
    functor-large-precategory-Small-Large-Precategoryᵉ Cᵉ Set-Large-Precategoryᵉ

  is-large-category-copresheaf-large-category-Precategoryᵉ :
    is-large-category-Large-Precategoryᵉ copresheaf-large-precategory-Precategoryᵉ
  is-large-category-copresheaf-large-category-Precategoryᵉ =
    is-large-category-functor-large-precategory-is-large-category-Small-Large-Precategoryᵉ
      ( Cᵉ)
      ( Set-Large-Precategoryᵉ)
      ( is-large-category-Set-Large-Precategoryᵉ)

  copresheaf-large-category-Precategoryᵉ :
    Large-Categoryᵉ (λ lᵉ → l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ) (λ lᵉ l'ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ lᵉ ⊔ l'ᵉ)
  large-precategory-Large-Categoryᵉ copresheaf-large-category-Precategoryᵉ =
    copresheaf-large-precategory-Precategoryᵉ
  is-large-category-Large-Categoryᵉ copresheaf-large-category-Precategoryᵉ =
    is-large-category-copresheaf-large-category-Precategoryᵉ

  copresheaf-Precategoryᵉ :
    (lᵉ : Level) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
  copresheaf-Precategoryᵉ =
    obj-Large-Precategoryᵉ copresheaf-large-precategory-Precategoryᵉ

  module _
    {lᵉ : Level} (Pᵉ : copresheaf-Precategoryᵉ lᵉ)
    where

    element-set-copresheaf-Precategoryᵉ : obj-Precategoryᵉ Cᵉ → Setᵉ lᵉ
    element-set-copresheaf-Precategoryᵉ =
      obj-functor-Small-Large-Precategoryᵉ Cᵉ Set-Large-Precategoryᵉ Pᵉ

    element-copresheaf-Precategoryᵉ : obj-Precategoryᵉ Cᵉ → UUᵉ lᵉ
    element-copresheaf-Precategoryᵉ Xᵉ =
      type-Setᵉ (element-set-copresheaf-Precategoryᵉ Xᵉ)

    action-copresheaf-Precategoryᵉ :
      {Xᵉ Yᵉ : obj-Precategoryᵉ Cᵉ} →
      hom-Precategoryᵉ Cᵉ Xᵉ Yᵉ →
      element-copresheaf-Precategoryᵉ Xᵉ → element-copresheaf-Precategoryᵉ Yᵉ
    action-copresheaf-Precategoryᵉ fᵉ =
      hom-functor-Small-Large-Precategoryᵉ Cᵉ Set-Large-Precategoryᵉ Pᵉ fᵉ

    preserves-id-action-copresheaf-Precategoryᵉ :
      {Xᵉ : obj-Precategoryᵉ Cᵉ} →
      action-copresheaf-Precategoryᵉ {Xᵉ} {Xᵉ} (id-hom-Precategoryᵉ Cᵉ) ~ᵉ idᵉ
    preserves-id-action-copresheaf-Precategoryᵉ =
      htpy-eqᵉ
        ( preserves-id-functor-Small-Large-Precategoryᵉ Cᵉ
          ( Set-Large-Precategoryᵉ)
          ( Pᵉ)
          ( _))

    preserves-comp-action-copresheaf-Precategoryᵉ :
      {Xᵉ Yᵉ Zᵉ : obj-Precategoryᵉ Cᵉ}
      (gᵉ : hom-Precategoryᵉ Cᵉ Yᵉ Zᵉ) (fᵉ : hom-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
      action-copresheaf-Precategoryᵉ (comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ) ~ᵉ
      action-copresheaf-Precategoryᵉ gᵉ ∘ᵉ action-copresheaf-Precategoryᵉ fᵉ
    preserves-comp-action-copresheaf-Precategoryᵉ gᵉ fᵉ =
      htpy-eqᵉ
        ( preserves-comp-functor-Small-Large-Precategoryᵉ Cᵉ
          ( Set-Large-Precategoryᵉ)
          ( Pᵉ)
          ( gᵉ)
          ( fᵉ))

  hom-set-copresheaf-Precategoryᵉ :
    {l3ᵉ l4ᵉ : Level}
    (Pᵉ : copresheaf-Precategoryᵉ l3ᵉ)
    (Qᵉ : copresheaf-Precategoryᵉ l4ᵉ) → Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-set-copresheaf-Precategoryᵉ =
    hom-set-Large-Precategoryᵉ copresheaf-large-precategory-Precategoryᵉ

  hom-copresheaf-Precategoryᵉ :
    {l3ᵉ l4ᵉ : Level}
    (Xᵉ : copresheaf-Precategoryᵉ l3ᵉ) (Yᵉ : copresheaf-Precategoryᵉ l4ᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-copresheaf-Precategoryᵉ =
    hom-Large-Precategoryᵉ copresheaf-large-precategory-Precategoryᵉ

  module _
    {l3ᵉ l4ᵉ : Level}
    (Pᵉ : copresheaf-Precategoryᵉ l3ᵉ) (Qᵉ : copresheaf-Precategoryᵉ l4ᵉ)
    (hᵉ : hom-copresheaf-Precategoryᵉ Pᵉ Qᵉ)
    where

    map-hom-copresheaf-Precategoryᵉ :
      (Xᵉ : obj-Precategoryᵉ Cᵉ) →
      element-copresheaf-Precategoryᵉ Pᵉ Xᵉ → element-copresheaf-Precategoryᵉ Qᵉ Xᵉ
    map-hom-copresheaf-Precategoryᵉ =
      hom-natural-transformation-Small-Large-Precategoryᵉ Cᵉ
        ( Set-Large-Precategoryᵉ)
        ( Pᵉ)
        ( Qᵉ)
        ( hᵉ)

    naturality-hom-copresheaf-Precategoryᵉ :
      {Xᵉ Yᵉ : obj-Precategoryᵉ Cᵉ} (fᵉ : hom-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
      coherence-square-mapsᵉ
        ( action-copresheaf-Precategoryᵉ Pᵉ fᵉ)
        ( map-hom-copresheaf-Precategoryᵉ Xᵉ)
        ( map-hom-copresheaf-Precategoryᵉ Yᵉ)
        ( action-copresheaf-Precategoryᵉ Qᵉ fᵉ)
    naturality-hom-copresheaf-Precategoryᵉ fᵉ =
      htpy-eqᵉ
        ( naturality-natural-transformation-Small-Large-Precategoryᵉ Cᵉ
          ( Set-Large-Precategoryᵉ)
          ( Pᵉ)
          ( Qᵉ)
          ( hᵉ)
          ( fᵉ))

  comp-hom-copresheaf-Precategoryᵉ :
    {l3ᵉ l4ᵉ l5ᵉ : Level}
    (Xᵉ : copresheaf-Precategoryᵉ l3ᵉ)
    (Yᵉ : copresheaf-Precategoryᵉ l4ᵉ)
    (Zᵉ : copresheaf-Precategoryᵉ l5ᵉ) →
    hom-copresheaf-Precategoryᵉ Yᵉ Zᵉ →
    hom-copresheaf-Precategoryᵉ Xᵉ Yᵉ →
    hom-copresheaf-Precategoryᵉ Xᵉ Zᵉ
  comp-hom-copresheaf-Precategoryᵉ Xᵉ Yᵉ Zᵉ =
    comp-hom-Large-Precategoryᵉ
      ( copresheaf-large-precategory-Precategoryᵉ)
      { Xᵉ = Xᵉ}
      { Yᵉ}
      { Zᵉ}

  id-hom-copresheaf-Precategoryᵉ :
    {l3ᵉ : Level} (Xᵉ : copresheaf-Precategoryᵉ l3ᵉ) →
    hom-copresheaf-Precategoryᵉ Xᵉ Xᵉ
  id-hom-copresheaf-Precategoryᵉ Xᵉ =
    id-hom-Large-Precategoryᵉ copresheaf-large-precategory-Precategoryᵉ {Xᵉ = Xᵉ}

  associative-comp-hom-copresheaf-Precategoryᵉ :
    {l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
    (Xᵉ : copresheaf-Precategoryᵉ l3ᵉ)
    (Yᵉ : copresheaf-Precategoryᵉ l4ᵉ)
    (Zᵉ : copresheaf-Precategoryᵉ l5ᵉ)
    (Wᵉ : copresheaf-Precategoryᵉ l6ᵉ)
    (hᵉ : hom-copresheaf-Precategoryᵉ Zᵉ Wᵉ)
    (gᵉ : hom-copresheaf-Precategoryᵉ Yᵉ Zᵉ)
    (fᵉ : hom-copresheaf-Precategoryᵉ Xᵉ Yᵉ) →
    comp-hom-copresheaf-Precategoryᵉ Xᵉ Yᵉ Wᵉ
      ( comp-hom-copresheaf-Precategoryᵉ Yᵉ Zᵉ Wᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-copresheaf-Precategoryᵉ Xᵉ Zᵉ Wᵉ
      ( hᵉ)
      ( comp-hom-copresheaf-Precategoryᵉ Xᵉ Yᵉ Zᵉ gᵉ fᵉ)
  associative-comp-hom-copresheaf-Precategoryᵉ Xᵉ Yᵉ Zᵉ Wᵉ =
    associative-comp-hom-Large-Precategoryᵉ
      ( copresheaf-large-precategory-Precategoryᵉ)
      { Xᵉ = Xᵉ}
      { Yᵉ}
      { Zᵉ}
      { Wᵉ}

  left-unit-law-comp-hom-copresheaf-Precategoryᵉ :
    {l3ᵉ l4ᵉ : Level}
    (Xᵉ : copresheaf-Precategoryᵉ l3ᵉ)
    (Yᵉ : copresheaf-Precategoryᵉ l4ᵉ)
    (fᵉ : hom-copresheaf-Precategoryᵉ Xᵉ Yᵉ) →
    comp-hom-copresheaf-Precategoryᵉ Xᵉ Yᵉ Yᵉ
      ( id-hom-copresheaf-Precategoryᵉ Yᵉ)
      ( fᵉ) ＝ᵉ
    fᵉ
  left-unit-law-comp-hom-copresheaf-Precategoryᵉ Xᵉ Yᵉ =
    left-unit-law-comp-hom-Large-Precategoryᵉ
      ( copresheaf-large-precategory-Precategoryᵉ)
      { Xᵉ = Xᵉ}
      { Yᵉ}

  right-unit-law-comp-hom-copresheaf-Precategoryᵉ :
    {l3ᵉ l4ᵉ : Level}
    (Xᵉ : copresheaf-Precategoryᵉ l3ᵉ)
    (Yᵉ : copresheaf-Precategoryᵉ l4ᵉ)
    (fᵉ : hom-copresheaf-Precategoryᵉ Xᵉ Yᵉ) →
    comp-hom-copresheaf-Precategoryᵉ Xᵉ Xᵉ Yᵉ
      ( fᵉ)
      ( id-hom-copresheaf-Precategoryᵉ Xᵉ) ＝ᵉ
    fᵉ
  right-unit-law-comp-hom-copresheaf-Precategoryᵉ Xᵉ Yᵉ =
    right-unit-law-comp-hom-Large-Precategoryᵉ
      ( copresheaf-large-precategory-Precategoryᵉ)
      { Xᵉ = Xᵉ}
      { Yᵉ}
```

### The category of small copresheaves on a precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (lᵉ : Level)
  where

  copresheaf-category-Precategoryᵉ :
    Categoryᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ) (l1ᵉ ⊔ l2ᵉ ⊔ lᵉ)
  copresheaf-category-Precategoryᵉ =
    category-Large-Categoryᵉ (copresheaf-large-category-Precategoryᵉ Cᵉ) lᵉ

  copresheaf-precategory-Precategoryᵉ :
    Precategoryᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ) (l1ᵉ ⊔ l2ᵉ ⊔ lᵉ)
  copresheaf-precategory-Precategoryᵉ =
    precategory-Large-Precategoryᵉ (copresheaf-large-precategory-Precategoryᵉ Cᵉ) lᵉ
```

## See also

-ᵉ [Theᵉ Yonedaᵉ lemma](category-theory.yoneda-lemma-precategories.mdᵉ)

## External links

-ᵉ [Presheafᵉ precategories](https://1lab.dev/Cat.Functor.Base.html#presheaf-precategoriesᵉ)
  atᵉ 1labᵉ
-ᵉ [categoryᵉ ofᵉ presheaves](https://ncatlab.org/nlab/show/category+of+presheavesᵉ)
  atᵉ $n$Labᵉ
-ᵉ [copresheaf](https://ncatlab.org/nlab/show/copresheafᵉ) atᵉ $n$Labᵉ