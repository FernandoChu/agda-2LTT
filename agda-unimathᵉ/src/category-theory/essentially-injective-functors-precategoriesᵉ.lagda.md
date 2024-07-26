# Essentially injective functors between precategories

```agda
module category-theory.essentially-injective-functors-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [functor](category-theory.functors-precategories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ betweenᵉ
[precategories](category-theory.precategories.mdᵉ) isᵉ **essentiallyᵉ injective**ᵉ
ifᵉ everyᵉ pairᵉ ofᵉ objectsᵉ thatᵉ areᵉ mappedᵉ to
[isomorphic](category-theory.isomorphisms-in-precategories.mdᵉ) objectsᵉ in `D`ᵉ
areᵉ isomorphicᵉ in `C`.ᵉ

## Definitions

### The type of proofs of being essentially injective

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-essentially-injective-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-essentially-injective-functor-Precategoryᵉ =
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) →
    iso-Precategoryᵉ Dᵉ
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ) →
    iso-Precategoryᵉ Cᵉ xᵉ yᵉ
```

### The type of essentially injective functors

```agda
essentially-injective-functor-Precategoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
essentially-injective-functor-Precategoryᵉ Cᵉ Dᵉ =
  Σᵉ ( functor-Precategoryᵉ Cᵉ Dᵉ)
    ( is-essentially-injective-functor-Precategoryᵉ Cᵉ Dᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : essentially-injective-functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  functor-essentially-injective-functor-Precategoryᵉ :
    functor-Precategoryᵉ Cᵉ Dᵉ
  functor-essentially-injective-functor-Precategoryᵉ = pr1ᵉ Fᵉ

  is-essentially-injective-essentially-injective-functor-Precategoryᵉ :
    is-essentially-injective-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-essentially-injective-functor-Precategoryᵉ)
  is-essentially-injective-essentially-injective-functor-Precategoryᵉ = pr2ᵉ Fᵉ

  obj-essentially-injective-functor-Precategoryᵉ :
    obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ
  obj-essentially-injective-functor-Precategoryᵉ =
    obj-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-essentially-injective-functor-Precategoryᵉ)

  hom-essentially-injective-functor-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Dᵉ
      ( obj-essentially-injective-functor-Precategoryᵉ xᵉ)
      ( obj-essentially-injective-functor-Precategoryᵉ yᵉ)
  hom-essentially-injective-functor-Precategoryᵉ =
    hom-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-essentially-injective-functor-Precategoryᵉ)
```

## See also

-ᵉ [Injectiveᵉ maps](foundation-core.injective-maps.mdᵉ)

## External links

-ᵉ [essentiallyᵉ injectiveᵉ functor](https://ncatlab.org/nlab/show/essentially+injective+functorᵉ)
  atᵉ $n$Labᵉ