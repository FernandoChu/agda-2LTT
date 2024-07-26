# The Yoneda lemma for precategories

```agda
module category-theory.yoneda-lemma-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.copresheaf-categoriesᵉ
open import category-theory.functors-from-small-to-large-precategoriesᵉ
open import category-theory.natural-transformations-functors-from-small-to-large-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.representable-functors-precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.category-of-setsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [precategory](category-theory.precategories.mdᵉ) `C`,ᵉ anᵉ objectᵉ `c`,ᵉ andᵉ
aᵉ [functor](category-theory.functors-precategories.mdᵉ) `F`ᵉ fromᵉ `C`ᵉ to theᵉ
[categoryᵉ ofᵉ sets](foundation.category-of-sets.mdᵉ)

```text
  Fᵉ : Cᵉ → Set,ᵉ
```

thereᵉ isᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) betweenᵉ theᵉ
[setᵉ ofᵉ naturalᵉ transformations](category-theory.natural-transformations-functors-precategories.mdᵉ)
fromᵉ theᵉ functorᵉ
[represented](category-theory.representable-functors-precategories.mdᵉ) byᵉ `c`ᵉ to
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
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (cᵉ : obj-Precategoryᵉ Cᵉ)
  (Fᵉ : copresheaf-Precategoryᵉ Cᵉ l3ᵉ)
  where

  map-yoneda-Precategoryᵉ :
    hom-copresheaf-Precategoryᵉ Cᵉ (representable-functor-Precategoryᵉ Cᵉ cᵉ) Fᵉ →
    element-copresheaf-Precategoryᵉ Cᵉ Fᵉ cᵉ
  map-yoneda-Precategoryᵉ σᵉ =
    hom-natural-transformation-Small-Large-Precategoryᵉ
      ( Cᵉ)
      ( Set-Large-Precategoryᵉ)
      ( representable-functor-Precategoryᵉ Cᵉ cᵉ)
      ( Fᵉ)
      ( σᵉ)
      ( cᵉ)
      ( id-hom-Precategoryᵉ Cᵉ)
```

Theᵉ inverseᵉ to theᵉ Yonedaᵉ mapᵉ:

```agda
  hom-family-extension-yoneda-Precategoryᵉ :
    (uᵉ : element-copresheaf-Precategoryᵉ Cᵉ Fᵉ cᵉ) →
    hom-family-functor-Small-Large-Precategoryᵉ
      Cᵉ Set-Large-Precategoryᵉ (representable-functor-Precategoryᵉ Cᵉ cᵉ) Fᵉ
  hom-family-extension-yoneda-Precategoryᵉ uᵉ xᵉ fᵉ =
    hom-functor-Small-Large-Precategoryᵉ Cᵉ Set-Large-Precategoryᵉ Fᵉ fᵉ uᵉ

  naturality-extension-yoneda-Precategoryᵉ :
    (uᵉ : element-copresheaf-Precategoryᵉ Cᵉ Fᵉ cᵉ) →
    is-natural-transformation-Small-Large-Precategoryᵉ
      Cᵉ Set-Large-Precategoryᵉ (representable-functor-Precategoryᵉ Cᵉ cᵉ) Fᵉ
      ( hom-family-extension-yoneda-Precategoryᵉ uᵉ)
  naturality-extension-yoneda-Precategoryᵉ uᵉ gᵉ =
    eq-htpyᵉ
      ( λ fᵉ →
        htpy-eqᵉ
          ( invᵉ
            ( preserves-comp-functor-Small-Large-Precategoryᵉ
                Cᵉ Set-Large-Precategoryᵉ Fᵉ gᵉ fᵉ))
          ( uᵉ))

  extension-yoneda-Precategoryᵉ :
    element-copresheaf-Precategoryᵉ Cᵉ Fᵉ cᵉ →
    hom-copresheaf-Precategoryᵉ Cᵉ (representable-functor-Precategoryᵉ Cᵉ cᵉ) Fᵉ
  pr1ᵉ (extension-yoneda-Precategoryᵉ uᵉ) =
    hom-family-extension-yoneda-Precategoryᵉ uᵉ
  pr2ᵉ (extension-yoneda-Precategoryᵉ uᵉ) =
    naturality-extension-yoneda-Precategoryᵉ uᵉ
```

Theᵉ inverseᵉ isᵉ anᵉ inverseᵉ:

```agda
  is-section-extension-yoneda-Precategoryᵉ :
    ( map-yoneda-Precategoryᵉ ∘ᵉ
      extension-yoneda-Precategoryᵉ) ~ᵉ
    idᵉ
  is-section-extension-yoneda-Precategoryᵉ =
    htpy-eqᵉ
      ( preserves-id-functor-Small-Large-Precategoryᵉ
          Cᵉ Set-Large-Precategoryᵉ Fᵉ cᵉ)

  is-retraction-extension-yoneda-Precategoryᵉ :
    ( extension-yoneda-Precategoryᵉ ∘ᵉ
      map-yoneda-Precategoryᵉ) ~ᵉ
    idᵉ
  is-retraction-extension-yoneda-Precategoryᵉ σᵉ =
    eq-type-subtypeᵉ
      ( is-natural-transformation-prop-Small-Large-Precategoryᵉ
        ( Cᵉ) Set-Large-Precategoryᵉ (representable-functor-Precategoryᵉ Cᵉ cᵉ) Fᵉ)
      ( eq-htpyᵉ
        ( λ xᵉ →
          eq-htpyᵉ
            ( λ fᵉ →
              ( htpy-eqᵉ
                ( pr2ᵉ σᵉ fᵉ)
                ( id-hom-Precategoryᵉ Cᵉ)) ∙ᵉ
              ( apᵉ (pr1ᵉ σᵉ xᵉ) (right-unit-law-comp-hom-Precategoryᵉ Cᵉ fᵉ)))))

  lemma-yoneda-Precategoryᵉ : is-equivᵉ map-yoneda-Precategoryᵉ
  lemma-yoneda-Precategoryᵉ =
    is-equiv-is-invertibleᵉ
      ( extension-yoneda-Precategoryᵉ)
      ( is-section-extension-yoneda-Precategoryᵉ)
      ( is-retraction-extension-yoneda-Precategoryᵉ)

  equiv-lemma-yoneda-Precategoryᵉ :
    hom-copresheaf-Precategoryᵉ Cᵉ (representable-functor-Precategoryᵉ Cᵉ cᵉ) Fᵉ ≃ᵉ
    element-copresheaf-Precategoryᵉ Cᵉ Fᵉ cᵉ
  pr1ᵉ equiv-lemma-yoneda-Precategoryᵉ = map-yoneda-Precategoryᵉ
  pr2ᵉ equiv-lemma-yoneda-Precategoryᵉ = lemma-yoneda-Precategoryᵉ
```

## Corollaries

### The Yoneda lemma for representable functors

Anᵉ importantᵉ special-caseᵉ ofᵉ theᵉ Yonedaᵉ lemmaᵉ isᵉ whenᵉ `F`ᵉ isᵉ itselfᵉ aᵉ
representableᵉ functorᵉ `Fᵉ = Hom(-,ᵉ d)`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (cᵉ dᵉ : obj-Precategoryᵉ Cᵉ)
  where

  equiv-lemma-yoneda-representable-Precategoryᵉ :
    hom-copresheaf-Precategoryᵉ Cᵉ
      ( representable-functor-Precategoryᵉ Cᵉ cᵉ)
      ( representable-functor-Precategoryᵉ Cᵉ dᵉ) ≃ᵉ
    hom-Precategoryᵉ Cᵉ dᵉ cᵉ
  equiv-lemma-yoneda-representable-Precategoryᵉ =
    equiv-lemma-yoneda-Precategoryᵉ Cᵉ cᵉ (representable-functor-Precategoryᵉ Cᵉ dᵉ)
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