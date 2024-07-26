# Essential fibers of functors between precategories

```agda
module category-theory.essential-fibers-of-functors-precategoriesᵉ where
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

Givenᵉ aᵉ [functor](category-theory.functors-precategories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ betweenᵉ
[precategories](category-theory.precategories.mdᵉ) andᵉ anᵉ objectᵉ `yᵉ : D`ᵉ weᵉ canᵉ
formᵉ theᵉ **essentialᵉ fiber**ᵉ ofᵉ `y`ᵉ overᵉ `F`ᵉ asᵉ theᵉ
[subprecategory](category-theory.subprecategories.mdᵉ) ofᵉ `C`ᵉ spannedᵉ by...ᵉ TODOᵉ

## Definitions

### The essential fiber over an object

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  essential-fiber-functor-Precategoryᵉ : (yᵉ : obj-Precategoryᵉ Dᵉ) → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  essential-fiber-functor-Precategoryᵉ yᵉ =
    Σᵉ ( obj-Precategoryᵉ Cᵉ)
      ( λ xᵉ → iso-Precategoryᵉ Dᵉ (obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ) yᵉ)

  essential-fiber-functor-Precategory'ᵉ : (yᵉ : obj-Precategoryᵉ Dᵉ) → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  essential-fiber-functor-Precategory'ᵉ yᵉ =
    Σᵉ ( obj-Precategoryᵉ Cᵉ)
      ( λ xᵉ → iso-Precategoryᵉ Dᵉ yᵉ (obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ))
```

## See also

-ᵉ [Essentiallyᵉ surjectiveᵉ functorsᵉ betweenᵉ precategories](category-theory.essentially-surjective-functors-precategories.mdᵉ)
-ᵉ [Splitᵉ essentiallyᵉ surjectiveᵉ functorsᵉ betweenᵉ precategories](category-theory.split-essentially-surjective-functors-precategories.mdᵉ)

## External links

-ᵉ [Essentialᵉ Fibres](https://1lab.dev/Cat.Functor.Properties.html#essential-fibresᵉ)
  atᵉ 1labᵉ
-ᵉ [essentialᵉ fiber](https://ncatlab.org/nlab/show/essential+fiberᵉ) atᵉ $n$Labᵉ