# Monads on categories

```agda
module category-theory.monads-on-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.functors-categoriesᵉ
open import category-theory.monads-on-precategoriesᵉ
open import category-theory.natural-transformations-functors-categoriesᵉ
open import category-theory.pointed-endofunctors-categoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "monad"ᵉ Disambiguation="onᵉ aᵉ category"ᵉ Agda=monad-Categoryᵉ}} onᵉ aᵉ
[category](category-theory.categories.mdᵉ) `C`ᵉ consistsᵉ ofᵉ anᵉ
[endofunctor](category-theory.functors-categories.mdᵉ) `Tᵉ : Cᵉ → C`ᵉ togetherᵉ with
twoᵉ
[naturalᵉ transformations](category-theory.natural-transformations-functors-categories.mdᵉ):
`ηᵉ : 1_Cᵉ ⇒ᵉ T`ᵉ andᵉ `μᵉ : T²ᵉ ⇒ᵉ T`,ᵉ where `1_Cᵉ : Cᵉ → C`ᵉ isᵉ theᵉ identityᵉ functorᵉ forᵉ
`C`,ᵉ andᵉ `T²`ᵉ isᵉ theᵉ functorᵉ `Tᵉ ∘ᵉ Tᵉ : Cᵉ → C`.ᵉ Theseᵉ mustᵉ satisfyᵉ theᵉ followingᵉ
{{#conceptᵉ "monadᵉ laws"ᵉ Disambiguation="monadᵉ onᵉ aᵉ category"ᵉ}}:

-ᵉ **Associativity:**ᵉ `μᵉ ∘ᵉ (Tᵉ •ᵉ μᵉ) = μᵉ ∘ᵉ (μᵉ •ᵉ T)`ᵉ
-ᵉ Theᵉ **leftᵉ unitᵉ law:**ᵉ `μᵉ ∘ᵉ (Tᵉ •ᵉ ηᵉ) = 1_T`ᵉ
-ᵉ Theᵉ **rightᵉ unitᵉ law:**ᵉ `μᵉ ∘ᵉ (ηᵉ •ᵉ Tᵉ) = 1_T`.ᵉ

Here,ᵉ `•`ᵉ denotesᵉ
[whiskering](category-theory.natural-transformations-functors-precategories.md#whiskering),ᵉ
andᵉ `1_Tᵉ : Tᵉ ⇒ᵉ T`ᵉ denotesᵉ theᵉ identityᵉ naturalᵉ transformationᵉ forᵉ `T`.ᵉ

## Definitions

### Multiplication structure on a pointed endofunctor on a category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Tᵉ : pointed-endofunctor-Categoryᵉ Cᵉ)
  where

  structure-multiplication-pointed-endofunctor-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  structure-multiplication-pointed-endofunctor-Categoryᵉ =
    structure-multiplication-pointed-endofunctor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( Tᵉ)
```

### Associativity of multiplication on a pointed endofunctor on a category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Tᵉ : pointed-endofunctor-Categoryᵉ Cᵉ)
  (μᵉ : structure-multiplication-pointed-endofunctor-Categoryᵉ Cᵉ Tᵉ)
  where

  associative-mul-pointed-endofunctor-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  associative-mul-pointed-endofunctor-Categoryᵉ =
    associative-mul-pointed-endofunctor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( Tᵉ)
      ( μᵉ)
```

### The left unit law on a multiplication on a pointed endofunctor

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Tᵉ : pointed-endofunctor-Categoryᵉ Cᵉ)
  (μᵉ : structure-multiplication-pointed-endofunctor-Categoryᵉ Cᵉ Tᵉ)
  where

  left-unit-law-mul-pointed-endofunctor-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  left-unit-law-mul-pointed-endofunctor-Categoryᵉ =
    left-unit-law-mul-pointed-endofunctor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( Tᵉ)
      ( μᵉ)
```

### The right unit law on a multiplication on a pointed endofunctor

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Tᵉ : pointed-endofunctor-Categoryᵉ Cᵉ)
  (μᵉ : structure-multiplication-pointed-endofunctor-Categoryᵉ Cᵉ Tᵉ)
  where

  right-unit-law-mul-pointed-endofunctor-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  right-unit-law-mul-pointed-endofunctor-Categoryᵉ =
    right-unit-law-mul-pointed-endofunctor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( Tᵉ)
      ( μᵉ)
```

### The structure of a monad on a pointed endofunctor on a category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Tᵉ : pointed-endofunctor-Categoryᵉ Cᵉ)
  where

  structure-monad-pointed-endofunctor-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  structure-monad-pointed-endofunctor-Categoryᵉ =
    structure-monad-pointed-endofunctor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( Tᵉ)
```

### The type of monads on categories

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  monad-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  monad-Categoryᵉ = monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  module _
    (Tᵉ : monad-Categoryᵉ)
    where

    pointed-endofunctor-monad-Categoryᵉ :
      pointed-endofunctor-Categoryᵉ Cᵉ
    pointed-endofunctor-monad-Categoryᵉ =
      pointed-endofunctor-monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ

    endofunctor-monad-Categoryᵉ :
      functor-Categoryᵉ Cᵉ Cᵉ
    endofunctor-monad-Categoryᵉ =
      endofunctor-monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ

    obj-endofunctor-monad-Categoryᵉ :
      obj-Categoryᵉ Cᵉ → obj-Categoryᵉ Cᵉ
    obj-endofunctor-monad-Categoryᵉ =
      obj-endofunctor-monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ

    hom-endofunctor-monad-Categoryᵉ :
      {Xᵉ Yᵉ : obj-Categoryᵉ Cᵉ} →
      hom-Categoryᵉ Cᵉ Xᵉ Yᵉ →
      hom-Categoryᵉ Cᵉ
        ( obj-endofunctor-monad-Categoryᵉ Xᵉ)
        ( obj-endofunctor-monad-Categoryᵉ Yᵉ)
    hom-endofunctor-monad-Categoryᵉ =
      hom-endofunctor-monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ

    preserves-id-endofunctor-monad-Categoryᵉ :
      (Xᵉ : obj-Categoryᵉ Cᵉ) →
      hom-endofunctor-monad-Categoryᵉ (id-hom-Categoryᵉ Cᵉ {Xᵉ}) ＝ᵉ
      id-hom-Categoryᵉ Cᵉ
    preserves-id-endofunctor-monad-Categoryᵉ =
      preserves-id-endofunctor-monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ

    preserves-comp-endofunctor-monad-Categoryᵉ :
      {Xᵉ Yᵉ Zᵉ : obj-Categoryᵉ Cᵉ} →
      (gᵉ : hom-Categoryᵉ Cᵉ Yᵉ Zᵉ) (fᵉ : hom-Categoryᵉ Cᵉ Xᵉ Yᵉ) →
      hom-endofunctor-monad-Categoryᵉ (comp-hom-Categoryᵉ Cᵉ gᵉ fᵉ) ＝ᵉ
      comp-hom-Categoryᵉ Cᵉ
        ( hom-endofunctor-monad-Categoryᵉ gᵉ)
        ( hom-endofunctor-monad-Categoryᵉ fᵉ)
    preserves-comp-endofunctor-monad-Categoryᵉ =
      preserves-comp-endofunctor-monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ

    unit-monad-Categoryᵉ :
      pointing-endofunctor-Categoryᵉ Cᵉ endofunctor-monad-Categoryᵉ
    unit-monad-Categoryᵉ =
      unit-monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ

    hom-unit-monad-Categoryᵉ :
      hom-family-functor-Categoryᵉ Cᵉ Cᵉ
        ( id-functor-Categoryᵉ Cᵉ)
        ( endofunctor-monad-Categoryᵉ)
    hom-unit-monad-Categoryᵉ =
      hom-unit-monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ

    naturality-unit-monad-Categoryᵉ :
      is-natural-transformation-Categoryᵉ Cᵉ Cᵉ
        ( id-functor-Categoryᵉ Cᵉ)
        ( endofunctor-monad-Categoryᵉ)
        ( hom-unit-monad-Categoryᵉ)
    naturality-unit-monad-Categoryᵉ =
      naturality-unit-monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ

    mul-monad-Categoryᵉ :
      structure-multiplication-pointed-endofunctor-Categoryᵉ Cᵉ
        ( pointed-endofunctor-monad-Categoryᵉ)
    mul-monad-Categoryᵉ =
      mul-monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ

    hom-mul-monad-Categoryᵉ :
      hom-family-functor-Categoryᵉ Cᵉ Cᵉ
        ( comp-functor-Categoryᵉ Cᵉ Cᵉ Cᵉ
          ( endofunctor-monad-Categoryᵉ)
          ( endofunctor-monad-Categoryᵉ))
        ( endofunctor-monad-Categoryᵉ)
    hom-mul-monad-Categoryᵉ =
      hom-mul-monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ

    naturality-mul-monad-Categoryᵉ :
      is-natural-transformation-Categoryᵉ Cᵉ Cᵉ
        ( comp-functor-Categoryᵉ Cᵉ Cᵉ Cᵉ
          ( endofunctor-monad-Categoryᵉ)
          ( endofunctor-monad-Categoryᵉ))
        ( endofunctor-monad-Categoryᵉ)
        ( hom-mul-monad-Categoryᵉ)
    naturality-mul-monad-Categoryᵉ =
      naturality-mul-monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ

    associative-mul-monad-Categoryᵉ :
      associative-mul-pointed-endofunctor-Categoryᵉ Cᵉ
        ( pointed-endofunctor-monad-Categoryᵉ)
        ( mul-monad-Categoryᵉ)
    associative-mul-monad-Categoryᵉ =
      associative-mul-monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ

    left-unit-law-mul-monad-Categoryᵉ :
      left-unit-law-mul-pointed-endofunctor-Categoryᵉ Cᵉ
        ( pointed-endofunctor-monad-Categoryᵉ)
        ( mul-monad-Categoryᵉ)
    left-unit-law-mul-monad-Categoryᵉ =
      left-unit-law-mul-monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ

    right-unit-law-mul-monad-Categoryᵉ :
      right-unit-law-mul-pointed-endofunctor-Categoryᵉ Cᵉ
        ( pointed-endofunctor-monad-Categoryᵉ)
        ( mul-monad-Categoryᵉ)
    right-unit-law-mul-monad-Categoryᵉ =
      right-unit-law-mul-monad-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Tᵉ
```