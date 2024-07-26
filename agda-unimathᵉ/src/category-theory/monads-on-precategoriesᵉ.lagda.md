# Monads on precategories

```agda
module category-theory.monads-on-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ
open import category-theory.pointed-endofunctors-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "monad"ᵉ Disambiguation="onᵉ aᵉ precategory"ᵉ Agda=monad-Precategoryᵉ}}
onᵉ aᵉ [precategory](category-theory.precategories.mdᵉ) `C`ᵉ consistsᵉ ofᵉ anᵉ
[endofunctor](category-theory.functors-precategories.mdᵉ) `Tᵉ : Cᵉ → C`ᵉ togetherᵉ
with twoᵉ
[naturalᵉ transformations](category-theory.natural-transformations-functors-precategories.mdᵉ):
`ηᵉ : 1_Cᵉ ⇒ᵉ T`ᵉ andᵉ `μᵉ : T²ᵉ ⇒ᵉ T`,ᵉ where `1_Cᵉ : Cᵉ → C`ᵉ isᵉ theᵉ identityᵉ functorᵉ forᵉ
`C`,ᵉ andᵉ `T²`ᵉ isᵉ theᵉ functorᵉ `Tᵉ ∘ᵉ Tᵉ : Cᵉ → C`.ᵉ Theseᵉ mustᵉ satisfyᵉ theᵉ followingᵉ
{{#conceptᵉ "monadᵉ laws"ᵉ Disambiguation="monadᵉ onᵉ aᵉ precategory"ᵉ}}:

-ᵉ **Associativity:**ᵉ `μᵉ ∘ᵉ (Tᵉ •ᵉ μᵉ) = μᵉ ∘ᵉ (μᵉ •ᵉ T)`ᵉ
-ᵉ Theᵉ **leftᵉ unitᵉ law:**ᵉ `μᵉ ∘ᵉ (Tᵉ •ᵉ ηᵉ) = 1_T`ᵉ
-ᵉ Theᵉ **rightᵉ unitᵉ law:**ᵉ `μᵉ ∘ᵉ (ηᵉ •ᵉ Tᵉ) = 1_T`.ᵉ

Here,ᵉ `•`ᵉ denotesᵉ
[whiskering](category-theory.natural-transformations-functors-precategories.md#whiskering),ᵉ
andᵉ `1_Tᵉ : Tᵉ ⇒ᵉ T`ᵉ denotesᵉ theᵉ identityᵉ naturalᵉ transformationᵉ forᵉ `T`.ᵉ

## Definitions

### Multiplication structure on a pointed endofunctor on a precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Tᵉ : pointed-endofunctor-Precategoryᵉ Cᵉ)
  where

  structure-multiplication-pointed-endofunctor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  structure-multiplication-pointed-endofunctor-Precategoryᵉ =
    natural-transformation-Precategoryᵉ Cᵉ Cᵉ
      ( comp-functor-Precategoryᵉ Cᵉ Cᵉ Cᵉ
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ))
      ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
```

### Associativity of multiplication on a pointed endofunctor on a precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Tᵉ : pointed-endofunctor-Precategoryᵉ Cᵉ)
  (μᵉ : structure-multiplication-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
  where

  associative-mul-pointed-endofunctor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  associative-mul-pointed-endofunctor-Precategoryᵉ =
    comp-natural-transformation-Precategoryᵉ Cᵉ Cᵉ
      ( comp-functor-Precategoryᵉ Cᵉ Cᵉ Cᵉ
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
        ( comp-functor-Precategoryᵉ Cᵉ Cᵉ Cᵉ
          ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
          ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)))
      ( comp-functor-Precategoryᵉ Cᵉ Cᵉ Cᵉ
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ))
      ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
      ( μᵉ)
      ( left-whisker-natural-transformation-Precategoryᵉ Cᵉ Cᵉ Cᵉ
        ( comp-functor-Precategoryᵉ Cᵉ Cᵉ Cᵉ
          ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
          ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ))
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
        ( μᵉ)) ＝ᵉ
    comp-natural-transformation-Precategoryᵉ Cᵉ Cᵉ
      ( comp-functor-Precategoryᵉ Cᵉ Cᵉ Cᵉ
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
        ( comp-functor-Precategoryᵉ Cᵉ Cᵉ Cᵉ
          ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
          ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)))
      ( comp-functor-Precategoryᵉ Cᵉ Cᵉ Cᵉ
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ))
      ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
      ( μᵉ)
      ( right-whisker-natural-transformation-Precategoryᵉ Cᵉ Cᵉ Cᵉ
        ( comp-functor-Precategoryᵉ Cᵉ Cᵉ Cᵉ
          ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
          ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ))
          ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
          ( μᵉ)
          ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ))
```

### The left unit law on a multiplication on a pointed endofunctor

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Tᵉ : pointed-endofunctor-Precategoryᵉ Cᵉ)
  (μᵉ : structure-multiplication-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
  where

  left-unit-law-mul-pointed-endofunctor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  left-unit-law-mul-pointed-endofunctor-Precategoryᵉ =
    comp-natural-transformation-Precategoryᵉ Cᵉ Cᵉ
      ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
      ( comp-functor-Precategoryᵉ Cᵉ Cᵉ Cᵉ
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ))
      ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
      ( μᵉ)
      ( left-whisker-natural-transformation-Precategoryᵉ Cᵉ Cᵉ Cᵉ
        ( id-functor-Precategoryᵉ Cᵉ)
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
        ( pointing-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)) ＝ᵉ
    id-natural-transformation-Precategoryᵉ Cᵉ Cᵉ
      ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
```

### The right unit law on a multiplication on a pointed endofunctor

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Tᵉ : pointed-endofunctor-Precategoryᵉ Cᵉ)
  (μᵉ : structure-multiplication-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
  where

  right-unit-law-mul-pointed-endofunctor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  right-unit-law-mul-pointed-endofunctor-Precategoryᵉ =
    comp-natural-transformation-Precategoryᵉ Cᵉ Cᵉ
      ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
      ( comp-functor-Precategoryᵉ Cᵉ Cᵉ Cᵉ
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ))
      ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
      ( μᵉ)
      ( right-whisker-natural-transformation-Precategoryᵉ Cᵉ Cᵉ Cᵉ
        ( id-functor-Precategoryᵉ Cᵉ)
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
        ( pointing-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
        ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)) ＝ᵉ
    id-natural-transformation-Precategoryᵉ Cᵉ Cᵉ
      ( functor-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
```

### The structure of a monad on a pointed endofunctor on a precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Tᵉ : pointed-endofunctor-Precategoryᵉ Cᵉ)
  where

  structure-monad-pointed-endofunctor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  structure-monad-pointed-endofunctor-Precategoryᵉ =
    Σᵉ ( structure-multiplication-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ)
      ( λ μᵉ →
        associative-mul-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ μᵉ ×ᵉ
        left-unit-law-mul-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ μᵉ ×ᵉ
        right-unit-law-mul-pointed-endofunctor-Precategoryᵉ Cᵉ Tᵉ μᵉ)
```

### The type of monads on precategories

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  monad-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  monad-Precategoryᵉ =
    Σᵉ ( pointed-endofunctor-Precategoryᵉ Cᵉ)
      ( structure-monad-pointed-endofunctor-Precategoryᵉ Cᵉ)

  module _
    (Tᵉ : monad-Precategoryᵉ)
    where

    pointed-endofunctor-monad-Precategoryᵉ :
      pointed-endofunctor-Precategoryᵉ Cᵉ
    pointed-endofunctor-monad-Precategoryᵉ = pr1ᵉ Tᵉ

    endofunctor-monad-Precategoryᵉ :
      functor-Precategoryᵉ Cᵉ Cᵉ
    endofunctor-monad-Precategoryᵉ =
      functor-pointed-endofunctor-Precategoryᵉ Cᵉ
        ( pointed-endofunctor-monad-Precategoryᵉ)

    obj-endofunctor-monad-Precategoryᵉ :
      obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Cᵉ
    obj-endofunctor-monad-Precategoryᵉ =
      obj-functor-Precategoryᵉ Cᵉ Cᵉ endofunctor-monad-Precategoryᵉ

    hom-endofunctor-monad-Precategoryᵉ :
      {Xᵉ Yᵉ : obj-Precategoryᵉ Cᵉ} →
      hom-Precategoryᵉ Cᵉ Xᵉ Yᵉ →
      hom-Precategoryᵉ Cᵉ
        ( obj-endofunctor-monad-Precategoryᵉ Xᵉ)
        ( obj-endofunctor-monad-Precategoryᵉ Yᵉ)
    hom-endofunctor-monad-Precategoryᵉ =
      hom-functor-Precategoryᵉ Cᵉ Cᵉ endofunctor-monad-Precategoryᵉ

    preserves-id-endofunctor-monad-Precategoryᵉ :
      (Xᵉ : obj-Precategoryᵉ Cᵉ) →
      hom-endofunctor-monad-Precategoryᵉ (id-hom-Precategoryᵉ Cᵉ {Xᵉ}) ＝ᵉ
      id-hom-Precategoryᵉ Cᵉ
    preserves-id-endofunctor-monad-Precategoryᵉ =
      preserves-id-functor-Precategoryᵉ Cᵉ Cᵉ endofunctor-monad-Precategoryᵉ

    preserves-comp-endofunctor-monad-Precategoryᵉ :
      {Xᵉ Yᵉ Zᵉ : obj-Precategoryᵉ Cᵉ} →
      (gᵉ : hom-Precategoryᵉ Cᵉ Yᵉ Zᵉ) (fᵉ : hom-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
      hom-endofunctor-monad-Precategoryᵉ (comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ) ＝ᵉ
      comp-hom-Precategoryᵉ Cᵉ
        ( hom-endofunctor-monad-Precategoryᵉ gᵉ)
        ( hom-endofunctor-monad-Precategoryᵉ fᵉ)
    preserves-comp-endofunctor-monad-Precategoryᵉ =
      preserves-comp-functor-Precategoryᵉ Cᵉ Cᵉ
        ( endofunctor-monad-Precategoryᵉ)

    unit-monad-Precategoryᵉ :
      pointing-endofunctor-Precategoryᵉ Cᵉ endofunctor-monad-Precategoryᵉ
    unit-monad-Precategoryᵉ =
      pointing-pointed-endofunctor-Precategoryᵉ Cᵉ
        ( pointed-endofunctor-monad-Precategoryᵉ)

    hom-unit-monad-Precategoryᵉ :
      hom-family-functor-Precategoryᵉ Cᵉ Cᵉ
        ( id-functor-Precategoryᵉ Cᵉ)
        ( endofunctor-monad-Precategoryᵉ)
    hom-unit-monad-Precategoryᵉ =
      hom-family-pointing-pointed-endofunctor-Precategoryᵉ Cᵉ
        ( pointed-endofunctor-monad-Precategoryᵉ)

    naturality-unit-monad-Precategoryᵉ :
      is-natural-transformation-Precategoryᵉ Cᵉ Cᵉ
        ( id-functor-Precategoryᵉ Cᵉ)
        ( endofunctor-monad-Precategoryᵉ)
        ( hom-unit-monad-Precategoryᵉ)
    naturality-unit-monad-Precategoryᵉ =
      naturality-pointing-pointed-endofunctor-Precategoryᵉ Cᵉ
        ( pointed-endofunctor-monad-Precategoryᵉ)

    mul-monad-Precategoryᵉ :
      structure-multiplication-pointed-endofunctor-Precategoryᵉ Cᵉ
        ( pointed-endofunctor-monad-Precategoryᵉ)
    mul-monad-Precategoryᵉ = pr1ᵉ (pr2ᵉ Tᵉ)

    hom-mul-monad-Precategoryᵉ :
      hom-family-functor-Precategoryᵉ Cᵉ Cᵉ
        ( comp-functor-Precategoryᵉ Cᵉ Cᵉ Cᵉ
          ( endofunctor-monad-Precategoryᵉ)
          ( endofunctor-monad-Precategoryᵉ))
        ( endofunctor-monad-Precategoryᵉ)
    hom-mul-monad-Precategoryᵉ =
      hom-family-natural-transformation-Precategoryᵉ Cᵉ Cᵉ
        ( comp-functor-Precategoryᵉ Cᵉ Cᵉ Cᵉ
          ( endofunctor-monad-Precategoryᵉ)
          ( endofunctor-monad-Precategoryᵉ))
        ( endofunctor-monad-Precategoryᵉ)
        ( mul-monad-Precategoryᵉ)

    naturality-mul-monad-Precategoryᵉ :
      is-natural-transformation-Precategoryᵉ Cᵉ Cᵉ
        ( comp-functor-Precategoryᵉ Cᵉ Cᵉ Cᵉ
          ( endofunctor-monad-Precategoryᵉ)
          ( endofunctor-monad-Precategoryᵉ))
        ( endofunctor-monad-Precategoryᵉ)
        ( hom-mul-monad-Precategoryᵉ)
    naturality-mul-monad-Precategoryᵉ =
      naturality-natural-transformation-Precategoryᵉ Cᵉ Cᵉ
        ( comp-functor-Precategoryᵉ Cᵉ Cᵉ Cᵉ
          ( endofunctor-monad-Precategoryᵉ)
          ( endofunctor-monad-Precategoryᵉ))
        ( endofunctor-monad-Precategoryᵉ)
        ( mul-monad-Precategoryᵉ)

    associative-mul-monad-Precategoryᵉ :
      associative-mul-pointed-endofunctor-Precategoryᵉ Cᵉ
        ( pointed-endofunctor-monad-Precategoryᵉ)
        ( mul-monad-Precategoryᵉ)
    associative-mul-monad-Precategoryᵉ =
      pr1ᵉ (pr2ᵉ (pr2ᵉ Tᵉ))

    left-unit-law-mul-monad-Precategoryᵉ :
      left-unit-law-mul-pointed-endofunctor-Precategoryᵉ Cᵉ
        ( pointed-endofunctor-monad-Precategoryᵉ)
        ( mul-monad-Precategoryᵉ)
    left-unit-law-mul-monad-Precategoryᵉ =
      pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Tᵉ)))

    right-unit-law-mul-monad-Precategoryᵉ :
      right-unit-law-mul-pointed-endofunctor-Precategoryᵉ Cᵉ
        ( pointed-endofunctor-monad-Precategoryᵉ)
        ( mul-monad-Precategoryᵉ)
    right-unit-law-mul-monad-Precategoryᵉ =
      pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Tᵉ)))
```