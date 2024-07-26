# The Yoneda lemma for categories

```agda
module category-theory.yoneda-lemma-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.copresheaf-categoriesᵉ
open import category-theory.natural-transformations-functors-from-small-to-large-categoriesᵉ
open import category-theory.representable-functors-categoriesᵉ
open import category-theory.yoneda-lemma-precategoriesᵉ

open import foundation.category-of-setsᵉ
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [category](category-theory.categories.mdᵉ) `C`,ᵉ anᵉ objectᵉ `c`,ᵉ andᵉ aᵉ
[functor](category-theory.functors-categories.mdᵉ) `F`ᵉ fromᵉ `C`ᵉ to theᵉ
[categoryᵉ ofᵉ sets](foundation.category-of-sets.mdᵉ)

```text
  Fᵉ : Cᵉ → Set,ᵉ
```

thereᵉ isᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) betweenᵉ theᵉ
[setᵉ ofᵉ naturalᵉ transformations](category-theory.natural-transformations-functors-categories.mdᵉ)
fromᵉ theᵉ functorᵉ
[represented](category-theory.representable-functors-categories.mdᵉ) byᵉ `c`ᵉ to
`F`ᵉ andᵉ theᵉ [set](foundation-core.sets.mdᵉ) `Fᵉ c`.ᵉ

```text
  Nat(Hom(cᵉ ,ᵉ -ᵉ) ,ᵉ Fᵉ) ≃ᵉ Fᵉ cᵉ
```

Moreᵉ precisely,ᵉ theᵉ **Yonedaᵉ lemma**ᵉ assertsᵉ thatᵉ theᵉ mapᵉ fromᵉ theᵉ typeᵉ ofᵉ
naturalᵉ transformationsᵉ to theᵉ typeᵉ `Fᵉ c`ᵉ definedᵉ byᵉ evaluatingᵉ theᵉ componentᵉ ofᵉ
theᵉ naturalᵉ transformationᵉ atᵉ theᵉ objectᵉ `c`ᵉ atᵉ theᵉ identityᵉ arrowᵉ onᵉ `c`ᵉ isᵉ anᵉ
equivalence.ᵉ

## Theorem

### The Yoneda lemma into the large category of sets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (cᵉ : obj-Categoryᵉ Cᵉ)
  (Fᵉ : copresheaf-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) l3ᵉ)
  where

  map-yoneda-Categoryᵉ :
    hom-copresheaf-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (representable-functor-Categoryᵉ Cᵉ cᵉ) Fᵉ →
    element-copresheaf-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Fᵉ cᵉ
  map-yoneda-Categoryᵉ =
    map-yoneda-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) cᵉ Fᵉ
```

Theᵉ inverseᵉ to theᵉ Yonedaᵉ mapᵉ:

```agda
  hom-family-extension-yoneda-Categoryᵉ :
    (uᵉ : element-copresheaf-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Fᵉ cᵉ) →
    hom-family-functor-Small-Large-Categoryᵉ
      Cᵉ Set-Large-Categoryᵉ (representable-functor-Categoryᵉ Cᵉ cᵉ) Fᵉ
  hom-family-extension-yoneda-Categoryᵉ =
    hom-family-extension-yoneda-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) cᵉ Fᵉ

  naturality-extension-yoneda-Categoryᵉ :
    (uᵉ : element-copresheaf-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Fᵉ cᵉ) →
    is-natural-transformation-Small-Large-Categoryᵉ
      Cᵉ Set-Large-Categoryᵉ (representable-functor-Categoryᵉ Cᵉ cᵉ) Fᵉ
      ( hom-family-extension-yoneda-Categoryᵉ uᵉ)
  naturality-extension-yoneda-Categoryᵉ =
    naturality-extension-yoneda-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) cᵉ Fᵉ

  extension-yoneda-Categoryᵉ :
    element-copresheaf-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Fᵉ cᵉ →
    hom-copresheaf-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (representable-functor-Categoryᵉ Cᵉ cᵉ) Fᵉ
  extension-yoneda-Categoryᵉ =
    extension-yoneda-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) cᵉ Fᵉ

  lemma-yoneda-Categoryᵉ : is-equivᵉ map-yoneda-Categoryᵉ
  lemma-yoneda-Categoryᵉ = lemma-yoneda-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) cᵉ Fᵉ

  equiv-lemma-yoneda-Categoryᵉ :
    hom-copresheaf-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (representable-functor-Categoryᵉ Cᵉ cᵉ) Fᵉ ≃ᵉ
    element-copresheaf-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Fᵉ cᵉ
  equiv-lemma-yoneda-Categoryᵉ =
    equiv-lemma-yoneda-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) cᵉ Fᵉ
```

## Corollaries

### The Yoneda lemma for representable functors

Anᵉ importantᵉ special-caseᵉ ofᵉ theᵉ Yonedaᵉ lemmaᵉ isᵉ whenᵉ `F`ᵉ isᵉ itselfᵉ aᵉ
representableᵉ functorᵉ `Fᵉ = Hom(-,ᵉ d)`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (cᵉ dᵉ : obj-Categoryᵉ Cᵉ)
  where

  equiv-lemma-yoneda-representable-Categoryᵉ :
    hom-copresheaf-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( representable-functor-Categoryᵉ Cᵉ cᵉ)
      ( representable-functor-Categoryᵉ Cᵉ dᵉ) ≃ᵉ
    hom-Categoryᵉ Cᵉ dᵉ cᵉ
  equiv-lemma-yoneda-representable-Categoryᵉ =
    equiv-lemma-yoneda-Categoryᵉ Cᵉ cᵉ (representable-functor-Categoryᵉ Cᵉ dᵉ)
```

## See also

-ᵉ [Presheafᵉ categories](category-theory.presheaf-categories.mdᵉ)

## External links

-ᵉ [Theᵉ Yonedaᵉ embedding](https://1lab.dev/Cat.Functor.Hom.html#the-yoneda-embeddingᵉ)
  atᵉ 1labᵉ
-ᵉ [Yonedaᵉ lemma](https://ncatlab.org/nlab/show/Yoneda+lemmaᵉ) atᵉ $n$Labᵉ
-ᵉ [Theᵉ Yonedaᵉ lemma](https://www.math3ma.com/blog/the-yoneda-lemmaᵉ) atᵉ Math3maᵉ
-ᵉ [Yonedaᵉ lemma](https://en.wikipedia.org/wiki/Yoneda_lemmaᵉ) atᵉ Wikipediaᵉ
-ᵉ [Yonedaᵉ lemma](https://www.wikidata.org/wiki/Q320577ᵉ) atᵉ Wikidataᵉ