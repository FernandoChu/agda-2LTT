# Split essentially surjective functors between precategories

```agda
module category-theory.split-essentially-surjective-functors-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.essential-fibers-of-functors-precategoriesᵉ
open import category-theory.essentially-surjective-functors-precategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [functor](category-theory.functors-precategories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ betweenᵉ
[precategories](category-theory.precategories.mdᵉ) isᵉ **splitᵉ essentiallyᵉ
surjective**ᵉ ifᵉ thereᵉ isᵉ aᵉ sectionᵉ ofᵉ theᵉ
[essentialᵉ fiber](category-theory.essential-fibers-of-functors-precategories.mdᵉ)
overᵉ everyᵉ objectᵉ ofᵉ `D`.ᵉ

## Definitions

### The type of proofs that a functor is split essentially surjective

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-split-essentially-surjective-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-split-essentially-surjective-functor-Precategoryᵉ =
    (yᵉ : obj-Precategoryᵉ Dᵉ) → essential-fiber-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ

  obj-is-split-essentially-surjective-functor-Precategoryᵉ :
    is-split-essentially-surjective-functor-Precategoryᵉ →
    obj-Precategoryᵉ Dᵉ → obj-Precategoryᵉ Cᵉ
  obj-is-split-essentially-surjective-functor-Precategoryᵉ
    is-split-ess-surj-Fᵉ yᵉ =
    pr1ᵉ (is-split-ess-surj-Fᵉ yᵉ)

  iso-is-split-essentially-surjective-functor-Precategoryᵉ :
    ( is-split-ess-surj-Fᵉ :
        is-split-essentially-surjective-functor-Precategoryᵉ) →
    (yᵉ : obj-Precategoryᵉ Dᵉ) →
    iso-Precategoryᵉ Dᵉ
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
        ( obj-is-split-essentially-surjective-functor-Precategoryᵉ
          ( is-split-ess-surj-Fᵉ)
          ( yᵉ)))
      ( yᵉ)
  iso-is-split-essentially-surjective-functor-Precategoryᵉ
    is-split-ess-surj-Fᵉ yᵉ =
    pr2ᵉ (is-split-ess-surj-Fᵉ yᵉ)
```

Weᵉ alsoᵉ record aᵉ variantᵉ with theᵉ oppositeᵉ varianceᵉ:

```agda
  is-split-essentially-surjective-functor-Precategory'ᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-split-essentially-surjective-functor-Precategory'ᵉ =
    (yᵉ : obj-Precategoryᵉ Dᵉ) → essential-fiber-functor-Precategory'ᵉ Cᵉ Dᵉ Fᵉ yᵉ

  obj-is-split-essentially-surjective-functor-Precategory'ᵉ :
    is-split-essentially-surjective-functor-Precategory'ᵉ →
    obj-Precategoryᵉ Dᵉ → obj-Precategoryᵉ Cᵉ
  obj-is-split-essentially-surjective-functor-Precategory'ᵉ
    is-split-ess-surj-F'ᵉ yᵉ =
    pr1ᵉ (is-split-ess-surj-F'ᵉ yᵉ)

  iso-is-split-essentially-surjective-functor-Precategory'ᵉ :
    ( is-split-ess-surj-F'ᵉ :
        is-split-essentially-surjective-functor-Precategory'ᵉ) →
    (yᵉ : obj-Precategoryᵉ Dᵉ) →
    iso-Precategoryᵉ Dᵉ
      ( yᵉ)
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
        ( obj-is-split-essentially-surjective-functor-Precategory'ᵉ
          ( is-split-ess-surj-F'ᵉ)
          ( yᵉ)))
  iso-is-split-essentially-surjective-functor-Precategory'ᵉ
    is-split-ess-surj-F'ᵉ yᵉ =
    pr2ᵉ (is-split-ess-surj-F'ᵉ yᵉ)
```

### The type of split essentially surjective functors

```agda
split-essentially-surjective-functor-Precategoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
split-essentially-surjective-functor-Precategoryᵉ Cᵉ Dᵉ =
  Σᵉ ( functor-Precategoryᵉ Cᵉ Dᵉ)
    ( is-split-essentially-surjective-functor-Precategoryᵉ Cᵉ Dᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : split-essentially-surjective-functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  functor-split-essentially-surjective-functor-Precategoryᵉ :
    functor-Precategoryᵉ Cᵉ Dᵉ
  functor-split-essentially-surjective-functor-Precategoryᵉ = pr1ᵉ Fᵉ

  is-split-essentially-surjective-split-essentially-surjective-functor-Precategoryᵉ :
    is-split-essentially-surjective-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-split-essentially-surjective-functor-Precategoryᵉ)
  is-split-essentially-surjective-split-essentially-surjective-functor-Precategoryᵉ =
    pr2ᵉ Fᵉ

  obj-split-essentially-surjective-functor-Precategoryᵉ :
    obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ
  obj-split-essentially-surjective-functor-Precategoryᵉ =
    obj-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-split-essentially-surjective-functor-Precategoryᵉ)

  hom-split-essentially-surjective-functor-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Dᵉ
      ( obj-split-essentially-surjective-functor-Precategoryᵉ xᵉ)
      ( obj-split-essentially-surjective-functor-Precategoryᵉ yᵉ)
  hom-split-essentially-surjective-functor-Precategoryᵉ =
    hom-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-split-essentially-surjective-functor-Precategoryᵉ)
```

## Properties

### Split essentially surjective functors are essentially surjective

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  is-essentially-surjective-is-split-essentially-surjective-functor-Precategoryᵉ :
    (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ) →
    is-split-essentially-surjective-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    is-essentially-surjective-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-essentially-surjective-is-split-essentially-surjective-functor-Precategoryᵉ
    Fᵉ is-split-ess-surj-Fᵉ =
    unit-trunc-Propᵉ ∘ᵉ is-split-ess-surj-Fᵉ

  essentially-surjective-functor-split-essentially-surjective-functor-Precategoryᵉ :
    split-essentially-surjective-functor-Precategoryᵉ Cᵉ Dᵉ →
    essentially-surjective-functor-Precategoryᵉ Cᵉ Dᵉ
  essentially-surjective-functor-split-essentially-surjective-functor-Precategoryᵉ =
    totᵉ
      ( is-essentially-surjective-is-split-essentially-surjective-functor-Precategoryᵉ)
```

### Being split essentially surjective is a property of fully faithful functors when the codomain is a category

Thisᵉ remainsᵉ to beᵉ shown.ᵉ Thisᵉ isᵉ Lemmaᵉ 6.8ᵉ ofᵉ _Univalentᵉ Categoriesᵉ andᵉ theᵉ
Rezkᵉ completion_.ᵉ

## References

{{#bibliographyᵉ}} {{#referenceᵉ AKS15ᵉ}}

## External links

-ᵉ [Essentialᵉ Fibres](https://1lab.dev/Cat.Functor.Properties.html#essential-fibresᵉ)
  atᵉ 1labᵉ
-ᵉ [splitᵉ essentiallyᵉ surjectiveᵉ functor](https://ncatlab.org/nlab/show/split+essentially+surjective+functorᵉ)
  atᵉ $n$Labᵉ

Aᵉ wikidataᵉ identifierᵉ wasᵉ notᵉ availableᵉ forᵉ thisᵉ concept.ᵉ