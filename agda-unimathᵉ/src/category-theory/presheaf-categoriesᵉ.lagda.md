# Presheaf categories

```agda
module category-theory.presheaf-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.copresheaf-categoriesᵉ
open import category-theory.functors-from-small-to-large-precategoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.natural-transformations-functors-from-small-to-large-precategoriesᵉ
open import category-theory.opposite-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.category-of-setsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [precategory](category-theory.precategories.mdᵉ) `C`,ᵉ weᵉ canᵉ formᵉ itsᵉ
**presheafᵉ [category](category-theory.large-categories.md)**ᵉ asᵉ theᵉ
[largeᵉ categoryᵉ ofᵉ functors](category-theory.functors-from-small-to-large-precategories.mdᵉ)
fromᵉ theᵉ [oppositeᵉ of](category-theory.opposite-precategories.mdᵉ) `C`,ᵉ `Cᵒᵖ`,ᵉ
intoᵉ theᵉ [largeᵉ categoryᵉ ofᵉ sets](foundation.category-of-sets.mdᵉ)

```text
  Cᵒᵖᵉ → Set.ᵉ
```

Toᵉ thisᵉ largeᵉ category,ᵉ thereᵉ isᵉ anᵉ associatedᵉ
[smallᵉ category](category-theory.categories.mdᵉ) ofᵉ smallᵉ presheaves,ᵉ takingᵉ
valuesᵉ in smallᵉ [sets](foundation-core.sets.md).ᵉ

## Definitions

### The large category of presheaves on a precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  presheaf-large-precategory-Precategoryᵉ :
    Large-Precategoryᵉ (λ lᵉ → l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ) (λ lᵉ l'ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ lᵉ ⊔ l'ᵉ)
  presheaf-large-precategory-Precategoryᵉ =
    copresheaf-large-precategory-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ)

  is-large-category-presheaf-large-category-Precategoryᵉ :
    is-large-category-Large-Precategoryᵉ presheaf-large-precategory-Precategoryᵉ
  is-large-category-presheaf-large-category-Precategoryᵉ =
    is-large-category-copresheaf-large-category-Precategoryᵉ
      ( opposite-Precategoryᵉ Cᵉ)

  presheaf-large-category-Precategoryᵉ :
    Large-Categoryᵉ (λ lᵉ → l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ) (λ lᵉ l'ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ lᵉ ⊔ l'ᵉ)
  presheaf-large-category-Precategoryᵉ =
    copresheaf-large-category-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ)

  presheaf-Precategoryᵉ : (lᵉ : Level) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
  presheaf-Precategoryᵉ =
    obj-Large-Categoryᵉ presheaf-large-category-Precategoryᵉ

  module _
    {l3ᵉ : Level} (Pᵉ : presheaf-Precategoryᵉ l3ᵉ)
    where

    element-set-presheaf-Precategoryᵉ : obj-Precategoryᵉ Cᵉ → Setᵉ l3ᵉ
    element-set-presheaf-Precategoryᵉ =
      obj-functor-Small-Large-Precategoryᵉ
        ( opposite-Precategoryᵉ Cᵉ)
        ( Set-Large-Precategoryᵉ)
        ( Pᵉ)

    element-presheaf-Precategoryᵉ : obj-Precategoryᵉ Cᵉ → UUᵉ l3ᵉ
    element-presheaf-Precategoryᵉ Xᵉ =
      type-Setᵉ (element-set-presheaf-Precategoryᵉ Xᵉ)

    action-presheaf-Precategoryᵉ :
      {Xᵉ Yᵉ : obj-Precategoryᵉ Cᵉ} →
      hom-Precategoryᵉ Cᵉ Xᵉ Yᵉ →
      element-presheaf-Precategoryᵉ Yᵉ → element-presheaf-Precategoryᵉ Xᵉ
    action-presheaf-Precategoryᵉ =
      hom-functor-Small-Large-Precategoryᵉ
        ( opposite-Precategoryᵉ Cᵉ)
        ( Set-Large-Precategoryᵉ)
        ( Pᵉ)

    preserves-id-action-presheaf-Precategoryᵉ :
      {Xᵉ : obj-Precategoryᵉ Cᵉ} →
      action-presheaf-Precategoryᵉ {Xᵉ} {Xᵉ} (id-hom-Precategoryᵉ Cᵉ) ~ᵉ idᵉ
    preserves-id-action-presheaf-Precategoryᵉ =
      htpy-eqᵉ
        ( preserves-id-functor-Small-Large-Precategoryᵉ
          ( opposite-Precategoryᵉ Cᵉ)
          ( Set-Large-Precategoryᵉ)
          ( Pᵉ)
          ( _))

    preserves-comp-action-presheaf-Precategoryᵉ :
      {Xᵉ Yᵉ Zᵉ : obj-Precategoryᵉ Cᵉ}
      (gᵉ : hom-Precategoryᵉ Cᵉ Yᵉ Zᵉ) (fᵉ : hom-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
      action-presheaf-Precategoryᵉ (comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ) ~ᵉ
      action-presheaf-Precategoryᵉ fᵉ ∘ᵉ action-presheaf-Precategoryᵉ gᵉ
    preserves-comp-action-presheaf-Precategoryᵉ gᵉ fᵉ =
      htpy-eqᵉ
        ( preserves-comp-functor-Small-Large-Precategoryᵉ
          ( opposite-Precategoryᵉ Cᵉ)
          ( Set-Large-Precategoryᵉ)
          ( Pᵉ)
          ( fᵉ)
          ( gᵉ))

  hom-set-presheaf-Precategoryᵉ :
    {l3ᵉ l4ᵉ : Level}
    (Xᵉ : presheaf-Precategoryᵉ l3ᵉ)
    (Yᵉ : presheaf-Precategoryᵉ l4ᵉ) → Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-set-presheaf-Precategoryᵉ =
    hom-set-Large-Categoryᵉ presheaf-large-category-Precategoryᵉ

  hom-presheaf-Precategoryᵉ :
    {l3ᵉ l4ᵉ : Level}
    (Xᵉ : presheaf-Precategoryᵉ l3ᵉ)
    (Yᵉ : presheaf-Precategoryᵉ l4ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-presheaf-Precategoryᵉ =
    hom-Large-Categoryᵉ presheaf-large-category-Precategoryᵉ

  module _
    {l3ᵉ l4ᵉ : Level}
    (Pᵉ : presheaf-Precategoryᵉ l3ᵉ) (Qᵉ : presheaf-Precategoryᵉ l4ᵉ)
    (hᵉ : hom-presheaf-Precategoryᵉ Pᵉ Qᵉ)
    where

    map-hom-presheaf-Precategoryᵉ :
      (Xᵉ : obj-Precategoryᵉ Cᵉ) →
      element-presheaf-Precategoryᵉ Pᵉ Xᵉ → element-presheaf-Precategoryᵉ Qᵉ Xᵉ
    map-hom-presheaf-Precategoryᵉ =
      hom-natural-transformation-Small-Large-Precategoryᵉ
        ( opposite-Precategoryᵉ Cᵉ)
        ( Set-Large-Precategoryᵉ)
        ( Pᵉ)
        ( Qᵉ)
        ( hᵉ)

    naturality-hom-presheaf-Precategoryᵉ :
      {Xᵉ Yᵉ : obj-Precategoryᵉ Cᵉ} (fᵉ : hom-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
      coherence-square-mapsᵉ
        ( action-presheaf-Precategoryᵉ Pᵉ fᵉ)
        ( map-hom-presheaf-Precategoryᵉ Yᵉ)
        ( map-hom-presheaf-Precategoryᵉ Xᵉ)
        ( action-presheaf-Precategoryᵉ Qᵉ fᵉ)
    naturality-hom-presheaf-Precategoryᵉ fᵉ =
      htpy-eqᵉ
        ( naturality-natural-transformation-Small-Large-Precategoryᵉ
          ( opposite-Precategoryᵉ Cᵉ)
          ( Set-Large-Precategoryᵉ)
          ( Pᵉ)
          ( Qᵉ)
          ( hᵉ)
          ( fᵉ))

  comp-hom-presheaf-Precategoryᵉ :
    {l3ᵉ l4ᵉ l5ᵉ : Level}
    (Xᵉ : presheaf-Precategoryᵉ l3ᵉ)
    (Yᵉ : presheaf-Precategoryᵉ l4ᵉ)
    (Zᵉ : presheaf-Precategoryᵉ l5ᵉ) →
    hom-presheaf-Precategoryᵉ Yᵉ Zᵉ → hom-presheaf-Precategoryᵉ Xᵉ Yᵉ →
    hom-presheaf-Precategoryᵉ Xᵉ Zᵉ
  comp-hom-presheaf-Precategoryᵉ Xᵉ Yᵉ Zᵉ =
    comp-hom-Large-Categoryᵉ presheaf-large-category-Precategoryᵉ {Xᵉ = Xᵉ} {Yᵉ} {Zᵉ}

  id-hom-presheaf-Precategoryᵉ :
    {l3ᵉ : Level} (Xᵉ : presheaf-Precategoryᵉ l3ᵉ) →
    hom-presheaf-Precategoryᵉ Xᵉ Xᵉ
  id-hom-presheaf-Precategoryᵉ {l3ᵉ} Xᵉ =
    id-hom-Large-Categoryᵉ presheaf-large-category-Precategoryᵉ {l3ᵉ} {Xᵉ}

  associative-comp-hom-presheaf-Precategoryᵉ :
    {l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
    (Xᵉ : presheaf-Precategoryᵉ l3ᵉ)
    (Yᵉ : presheaf-Precategoryᵉ l4ᵉ)
    (Zᵉ : presheaf-Precategoryᵉ l5ᵉ)
    (Wᵉ : presheaf-Precategoryᵉ l6ᵉ)
    (hᵉ : hom-presheaf-Precategoryᵉ Zᵉ Wᵉ)
    (gᵉ : hom-presheaf-Precategoryᵉ Yᵉ Zᵉ)
    (fᵉ : hom-presheaf-Precategoryᵉ Xᵉ Yᵉ) →
    comp-hom-presheaf-Precategoryᵉ Xᵉ Yᵉ Wᵉ
      ( comp-hom-presheaf-Precategoryᵉ Yᵉ Zᵉ Wᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-presheaf-Precategoryᵉ Xᵉ Zᵉ Wᵉ hᵉ
      ( comp-hom-presheaf-Precategoryᵉ Xᵉ Yᵉ Zᵉ gᵉ fᵉ)
  associative-comp-hom-presheaf-Precategoryᵉ Xᵉ Yᵉ Zᵉ Wᵉ =
    associative-comp-hom-Large-Categoryᵉ
      ( presheaf-large-category-Precategoryᵉ)
      { Xᵉ = Xᵉ}
      { Yᵉ}
      { Zᵉ}
      { Wᵉ}

  involutive-eq-associative-comp-hom-presheaf-Precategoryᵉ :
    {l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
    (Xᵉ : presheaf-Precategoryᵉ l3ᵉ)
    (Yᵉ : presheaf-Precategoryᵉ l4ᵉ)
    (Zᵉ : presheaf-Precategoryᵉ l5ᵉ)
    (Wᵉ : presheaf-Precategoryᵉ l6ᵉ)
    (hᵉ : hom-presheaf-Precategoryᵉ Zᵉ Wᵉ)
    (gᵉ : hom-presheaf-Precategoryᵉ Yᵉ Zᵉ)
    (fᵉ : hom-presheaf-Precategoryᵉ Xᵉ Yᵉ) →
    comp-hom-presheaf-Precategoryᵉ Xᵉ Yᵉ Wᵉ
      ( comp-hom-presheaf-Precategoryᵉ Yᵉ Zᵉ Wᵉ hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-hom-presheaf-Precategoryᵉ Xᵉ Zᵉ Wᵉ hᵉ
      ( comp-hom-presheaf-Precategoryᵉ Xᵉ Yᵉ Zᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-presheaf-Precategoryᵉ Xᵉ Yᵉ Zᵉ Wᵉ =
    involutive-eq-associative-comp-hom-Large-Categoryᵉ
      ( presheaf-large-category-Precategoryᵉ)
      { Xᵉ = Xᵉ}
      { Yᵉ}
      { Zᵉ}
      { Wᵉ}

  left-unit-law-comp-hom-presheaf-Precategoryᵉ :
    {l3ᵉ l4ᵉ : Level}
    (Xᵉ : presheaf-Precategoryᵉ l3ᵉ)
    (Yᵉ : presheaf-Precategoryᵉ l4ᵉ)
    (fᵉ : hom-presheaf-Precategoryᵉ Xᵉ Yᵉ) →
    comp-hom-presheaf-Precategoryᵉ Xᵉ Yᵉ Yᵉ
      ( id-hom-presheaf-Precategoryᵉ Yᵉ)
      ( fᵉ) ＝ᵉ
    fᵉ
  left-unit-law-comp-hom-presheaf-Precategoryᵉ Xᵉ Yᵉ =
    left-unit-law-comp-hom-Large-Categoryᵉ
      ( presheaf-large-category-Precategoryᵉ)
      { Xᵉ = Xᵉ}
      { Yᵉ}

  right-unit-law-comp-hom-presheaf-Precategoryᵉ :
    {l3ᵉ l4ᵉ : Level}
    (Xᵉ : presheaf-Precategoryᵉ l3ᵉ)
    (Yᵉ : presheaf-Precategoryᵉ l4ᵉ)
    (fᵉ : hom-presheaf-Precategoryᵉ Xᵉ Yᵉ) →
    comp-hom-presheaf-Precategoryᵉ Xᵉ Xᵉ Yᵉ fᵉ
      ( id-hom-presheaf-Precategoryᵉ Xᵉ) ＝ᵉ
    fᵉ
  right-unit-law-comp-hom-presheaf-Precategoryᵉ Xᵉ Yᵉ =
    right-unit-law-comp-hom-Large-Categoryᵉ
      ( presheaf-large-category-Precategoryᵉ)
      { Xᵉ = Xᵉ}
      { Yᵉ}
```

### The category of small presheaves on a precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (lᵉ : Level)
  where

  presheaf-precategory-Precategoryᵉ :
    Precategoryᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ) (l1ᵉ ⊔ l2ᵉ ⊔ lᵉ)
  presheaf-precategory-Precategoryᵉ =
    precategory-Large-Categoryᵉ (presheaf-large-category-Precategoryᵉ Cᵉ) lᵉ

  presheaf-category-Precategoryᵉ : Categoryᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ) (l1ᵉ ⊔ l2ᵉ ⊔ lᵉ)
  presheaf-category-Precategoryᵉ =
    category-Large-Categoryᵉ (presheaf-large-category-Precategoryᵉ Cᵉ) lᵉ
```

## See also

-ᵉ [Theᵉ Yonedaᵉ lemma](category-theory.yoneda-lemma-precategories.mdᵉ)

## External links

-ᵉ [Presheafᵉ precategories](https://1lab.dev/Cat.Functor.Base.html#presheaf-precategoriesᵉ)
  atᵉ 1labᵉ
-ᵉ [categoryᵉ ofᵉ presheaves](https://ncatlab.org/nlab/show/category+of+presheavesᵉ)
  atᵉ $n$Labᵉ
-ᵉ [presheaf](https://ncatlab.org/nlab/show/presheafᵉ) atᵉ $n$Labᵉ