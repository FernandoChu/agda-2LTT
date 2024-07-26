# Essentially surjective functors between precategories

```agda
module category-theory.essentially-surjective-functors-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [functor](category-theory.functors-precategories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ betweenᵉ
[precategories](category-theory.precategories.mdᵉ) isᵉ **essentiallyᵉ surjective**ᵉ
ifᵉ thereᵉ forᵉ everyᵉ objectᵉ `yᵉ : D`ᵉ
[merelyᵉ exists](foundation.existential-quantification.mdᵉ) anᵉ objectᵉ `xᵉ : C`ᵉ suchᵉ
thatᵉ `Fᵉ xᵉ ≅ᵉ y`.ᵉ

## Definitions

### The predicate of being essentially surjective

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-essentially-surjective-prop-functor-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-essentially-surjective-prop-functor-Precategoryᵉ =
    Π-Propᵉ
      ( obj-Precategoryᵉ Dᵉ)
      ( λ yᵉ →
        exists-structure-Propᵉ
          ( obj-Precategoryᵉ Cᵉ)
          ( λ xᵉ → iso-Precategoryᵉ Dᵉ (obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ) yᵉ))

  is-essentially-surjective-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-essentially-surjective-functor-Precategoryᵉ =
    ( yᵉ : obj-Precategoryᵉ Dᵉ) →
    exists-structureᵉ
      ( obj-Precategoryᵉ Cᵉ)
      ( λ xᵉ → iso-Precategoryᵉ Dᵉ (obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ) yᵉ)

  is-prop-is-essentially-surjective-functor-Precategoryᵉ :
    is-propᵉ is-essentially-surjective-functor-Precategoryᵉ
  is-prop-is-essentially-surjective-functor-Precategoryᵉ =
    is-prop-type-Propᵉ is-essentially-surjective-prop-functor-Precategoryᵉ
```

### The type of essentially surjective functors

```agda
essentially-surjective-functor-Precategoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
essentially-surjective-functor-Precategoryᵉ Cᵉ Dᵉ =
  Σᵉ ( functor-Precategoryᵉ Cᵉ Dᵉ)
    ( is-essentially-surjective-functor-Precategoryᵉ Cᵉ Dᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : essentially-surjective-functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  functor-essentially-surjective-functor-Precategoryᵉ :
    functor-Precategoryᵉ Cᵉ Dᵉ
  functor-essentially-surjective-functor-Precategoryᵉ = pr1ᵉ Fᵉ

  is-essentially-surjective-essentially-surjective-functor-Precategoryᵉ :
    is-essentially-surjective-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-essentially-surjective-functor-Precategoryᵉ)
  is-essentially-surjective-essentially-surjective-functor-Precategoryᵉ = pr2ᵉ Fᵉ

  obj-essentially-surjective-functor-Precategoryᵉ :
    obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ
  obj-essentially-surjective-functor-Precategoryᵉ =
    obj-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-essentially-surjective-functor-Precategoryᵉ)

  hom-essentially-surjective-functor-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Dᵉ
      ( obj-essentially-surjective-functor-Precategoryᵉ xᵉ)
      ( obj-essentially-surjective-functor-Precategoryᵉ yᵉ)
  hom-essentially-surjective-functor-Precategoryᵉ =
    hom-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-essentially-surjective-functor-Precategoryᵉ)
```

## Properties

### Precomposing by essentially surjective functors define fully faithful functors

Thisᵉ remainsᵉ to beᵉ shown.ᵉ Thisᵉ isᵉ Lemmaᵉ 8.2ᵉ ofᵉ _Univalentᵉ Categoriesᵉ andᵉ theᵉ
Rezkᵉ completion_.ᵉ

## See also

-ᵉ [Splitᵉ essentiallyᵉ surjectiveᵉ functorᵉ betweenᵉ precategories](category-theory.split-essentially-surjective-functors-precategories.mdᵉ)

## References

{{#bibliographyᵉ}} {{#referenceᵉ AKS15ᵉ}}

## External links

-ᵉ [Essentialᵉ Fibres](https://1lab.dev/Cat.Functor.Properties.html#essential-fibresᵉ)
  atᵉ 1labᵉ
-ᵉ [essentiallyᵉ surjectiveᵉ functor](https://ncatlab.org/nlab/show/essentially+surjective+functorᵉ)
  atᵉ $n$Labᵉ
-ᵉ [Fullyᵉ Faithfulᵉ andᵉ Essentiallyᵉ Surjectiveᵉ Functors](https://kerodon.net/tag/01JGᵉ)
  atᵉ Kerodonᵉ
-ᵉ [Essentiallyᵉ surjectiveᵉ functor](https://en.wikipedia.org/wiki/Essentially_surjective_functorᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [essentiallyᵉ surjectiveᵉ functor](https://www.wikidata.org/wiki/Q140283ᵉ) atᵉ
  wikidataᵉ