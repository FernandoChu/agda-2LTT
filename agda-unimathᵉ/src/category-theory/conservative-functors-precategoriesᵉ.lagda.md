# Conservative functors between precategories

```agda
module category-theory.conservative-functors-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [functor](category-theory.functors-precategories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ betweenᵉ
[precategories](category-theory.precategories.mdᵉ) isᵉ **conservative**ᵉ ifᵉ everyᵉ
morphismᵉ thatᵉ isᵉ mappedᵉ to anᵉ
[isomorphism](category-theory.isomorphisms-in-precategories.mdᵉ) in `D`ᵉ isᵉ anᵉ
isomorphismᵉ in `C`.ᵉ

## Definitions

### The predicate on functors of being conservative

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-conservative-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-conservative-functor-Precategoryᵉ =
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    is-iso-Precategoryᵉ Dᵉ (hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ) →
    is-iso-Precategoryᵉ Cᵉ fᵉ

  is-prop-is-conservative-functor-Precategoryᵉ :
    is-propᵉ is-conservative-functor-Precategoryᵉ
  is-prop-is-conservative-functor-Precategoryᵉ =
    is-prop-iterated-implicit-Πᵉ 2
      ( λ xᵉ yᵉ → is-prop-iterated-Πᵉ 2 (λ fᵉ _ → is-prop-is-iso-Precategoryᵉ Cᵉ fᵉ))

  is-conservative-prop-functor-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-conservative-prop-functor-Precategoryᵉ =
    is-conservative-functor-Precategoryᵉ
  pr2ᵉ is-conservative-prop-functor-Precategoryᵉ =
    is-prop-is-conservative-functor-Precategoryᵉ
```

### The type of conservative functors

```agda
conservative-functor-Precategoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
conservative-functor-Precategoryᵉ Cᵉ Dᵉ =
  Σᵉ ( functor-Precategoryᵉ Cᵉ Dᵉ)
    ( is-conservative-functor-Precategoryᵉ Cᵉ Dᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : conservative-functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  functor-conservative-functor-Precategoryᵉ :
    functor-Precategoryᵉ Cᵉ Dᵉ
  functor-conservative-functor-Precategoryᵉ = pr1ᵉ Fᵉ

  is-conservative-conservative-functor-Precategoryᵉ :
    is-conservative-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-conservative-functor-Precategoryᵉ)
  is-conservative-conservative-functor-Precategoryᵉ = pr2ᵉ Fᵉ

  obj-conservative-functor-Precategoryᵉ :
    obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ
  obj-conservative-functor-Precategoryᵉ =
    obj-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-conservative-functor-Precategoryᵉ)

  hom-conservative-functor-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Dᵉ
      ( obj-conservative-functor-Precategoryᵉ xᵉ)
      ( obj-conservative-functor-Precategoryᵉ yᵉ)
  hom-conservative-functor-Precategoryᵉ =
    hom-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-conservative-functor-Precategoryᵉ)
```

## See also

-ᵉ [Essentiallyᵉ injectiveᵉ functors](category-theory.essentially-injective-functors-precategories.mdᵉ)
-ᵉ [Pseudomonicᵉ functors](category-theory.pseudomonic-functors-precategories.mdᵉ)
  areᵉ conservative.ᵉ
-ᵉ [Fullyᵉ faithfulᵉ functors](category-theory.fully-faithful-functors-precategories.mdᵉ)
  areᵉ conservative.ᵉ

## External links

-ᵉ [Conservativeᵉ Functors](https://1lab.dev/Cat.Functor.Conservative.htmlᵉ) atᵉ
  1labᵉ
-ᵉ [conservativeᵉ functor](https://ncatlab.org/nlab/show/conservative+functorᵉ) atᵉ
  $n$Labᵉ
-ᵉ [Conservativeᵉ functor](https://en.wikipedia.org/wiki/Conservative_functorᵉ) atᵉ
  Wikipediaᵉ