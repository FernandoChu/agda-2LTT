# Natural transformations between maps between precategories

```agda
module category-theory.natural-transformations-maps-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-precategoriesᵉ
open import category-theory.maps-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ [precategories](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ `D`,ᵉ aᵉ **naturalᵉ
transformation**ᵉ fromᵉ aᵉ
[mapᵉ ofᵉ precategories](category-theory.maps-precategories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ to
`Gᵉ : Cᵉ → D`ᵉ consistsᵉ ofᵉ :

-ᵉ aᵉ familyᵉ ofᵉ morphismsᵉ `γᵉ : (xᵉ : Cᵉ) → homᵉ (Fᵉ xᵉ) (Gᵉ x)`ᵉ suchᵉ thatᵉ theᵉ followingᵉ
  identityᵉ holdsᵉ:
-ᵉ `(Gᵉ fᵉ) ∘ᵉ (γᵉ xᵉ) = (γᵉ yᵉ) ∘ᵉ (Fᵉ f)`,ᵉ forᵉ allᵉ `fᵉ : homᵉ xᵉ y`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  hom-family-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l4ᵉ)
  hom-family-map-Precategoryᵉ =
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    hom-Precategoryᵉ Dᵉ
      ( obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ xᵉ)

  naturality-hom-family-map-Precategoryᵉ :
    hom-family-map-Precategoryᵉ →
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) → UUᵉ l4ᵉ
  naturality-hom-family-map-Precategoryᵉ γᵉ {xᵉ} {yᵉ} fᵉ =
    coherence-square-hom-Precategoryᵉ Dᵉ
      ( hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ)
      ( γᵉ xᵉ)
      ( γᵉ yᵉ)
      ( hom-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ fᵉ)

  is-natural-transformation-map-Precategoryᵉ :
    hom-family-map-Precategoryᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-natural-transformation-map-Precategoryᵉ γᵉ =
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    naturality-hom-family-map-Precategoryᵉ γᵉ fᵉ

  natural-transformation-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  natural-transformation-map-Precategoryᵉ =
    Σᵉ ( hom-family-map-Precategoryᵉ)
      ( is-natural-transformation-map-Precategoryᵉ)

  hom-family-natural-transformation-map-Precategoryᵉ :
    natural-transformation-map-Precategoryᵉ → hom-family-map-Precategoryᵉ
  hom-family-natural-transformation-map-Precategoryᵉ = pr1ᵉ

  naturality-natural-transformation-map-Precategoryᵉ :
    (γᵉ : natural-transformation-map-Precategoryᵉ) →
    is-natural-transformation-map-Precategoryᵉ
      ( hom-family-natural-transformation-map-Precategoryᵉ γᵉ)
  naturality-natural-transformation-map-Precategoryᵉ = pr2ᵉ
```

## Composition and identity of natural transformations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  id-natural-transformation-map-Precategoryᵉ :
    (Fᵉ : map-Precategoryᵉ Cᵉ Dᵉ) → natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  pr1ᵉ (id-natural-transformation-map-Precategoryᵉ Fᵉ) xᵉ = id-hom-Precategoryᵉ Dᵉ
  pr2ᵉ (id-natural-transformation-map-Precategoryᵉ Fᵉ) fᵉ =
    ( right-unit-law-comp-hom-Precategoryᵉ Dᵉ
      ( hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ)) ∙ᵉ
    ( invᵉ
      ( left-unit-law-comp-hom-Precategoryᵉ Dᵉ
        ( hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ)))

  comp-natural-transformation-map-Precategoryᵉ :
    (Fᵉ Gᵉ Hᵉ : map-Precategoryᵉ Cᵉ Dᵉ) →
    natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ →
    natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ →
    natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  pr1ᵉ (comp-natural-transformation-map-Precategoryᵉ Fᵉ Gᵉ Hᵉ βᵉ αᵉ) xᵉ =
    comp-hom-Precategoryᵉ Dᵉ
      ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ βᵉ xᵉ)
      ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ xᵉ)
  pr2ᵉ (comp-natural-transformation-map-Precategoryᵉ Fᵉ Gᵉ Hᵉ βᵉ αᵉ) {Xᵉ} {Yᵉ} fᵉ =
    ( invᵉ
      ( associative-comp-hom-Precategoryᵉ Dᵉ
        ( hom-map-Precategoryᵉ Cᵉ Dᵉ Hᵉ fᵉ)
        ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ βᵉ Xᵉ)
        ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ Xᵉ))) ∙ᵉ
    ( apᵉ
      ( comp-hom-Precategory'ᵉ Dᵉ
        ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ Xᵉ))
      ( naturality-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ βᵉ fᵉ)) ∙ᵉ
    ( associative-comp-hom-Precategoryᵉ Dᵉ
      ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ βᵉ Yᵉ)
      ( hom-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ fᵉ)
      ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ Xᵉ)) ∙ᵉ
    ( apᵉ
      ( comp-hom-Precategoryᵉ Dᵉ
        ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ βᵉ Yᵉ))
      ( naturality-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ fᵉ)) ∙ᵉ
    ( invᵉ
      ( associative-comp-hom-Precategoryᵉ Dᵉ
        ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ βᵉ Yᵉ)
        ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ Yᵉ)
        ( hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ)))
```

## Properties

### That a family of morphisms is a natural transformation is a proposition

Thisᵉ followsᵉ fromᵉ theᵉ factᵉ thatᵉ theᵉ hom-typesᵉ areᵉ
[sets](foundation-core.sets.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-prop-is-natural-transformation-map-Precategoryᵉ :
    ( γᵉ : hom-family-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-propᵉ (is-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ γᵉ)
  is-prop-is-natural-transformation-map-Precategoryᵉ γᵉ =
    is-prop-implicit-Πᵉ
      ( λ xᵉ →
        is-prop-implicit-Πᵉ
          ( λ yᵉ →
            is-prop-Πᵉ
              ( λ fᵉ →
                is-set-hom-Precategoryᵉ Dᵉ
                  ( obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
                  ( obj-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ yᵉ)
                  ( comp-hom-Precategoryᵉ Dᵉ
                    ( hom-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ fᵉ)
                    ( γᵉ xᵉ))
                  ( comp-hom-Precategoryᵉ Dᵉ
                    ( γᵉ yᵉ)
                    ( hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ)))))

  is-natural-transformation-prop-map-Precategoryᵉ :
    ( γᵉ : hom-family-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ (is-natural-transformation-prop-map-Precategoryᵉ αᵉ) =
    is-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ
  pr2ᵉ (is-natural-transformation-prop-map-Precategoryᵉ αᵉ) =
    is-prop-is-natural-transformation-map-Precategoryᵉ αᵉ
```

### The set of natural transformations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-emb-hom-family-natural-transformation-map-Precategoryᵉ :
    is-embᵉ (hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-emb-hom-family-natural-transformation-map-Precategoryᵉ =
    is-emb-inclusion-subtypeᵉ
      ( is-natural-transformation-prop-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)

  emb-hom-family-natural-transformation-map-Precategoryᵉ :
    natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ ↪ᵉ
    hom-family-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  emb-hom-family-natural-transformation-map-Precategoryᵉ =
    emb-subtypeᵉ (is-natural-transformation-prop-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)

  is-set-natural-transformation-map-Precategoryᵉ :
    is-setᵉ (natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-set-natural-transformation-map-Precategoryᵉ =
    is-set-Σᵉ
      ( is-set-Πᵉ
        ( λ xᵉ →
          is-set-hom-Precategoryᵉ Dᵉ
            ( obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
            ( obj-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ xᵉ)))
      ( λ αᵉ →
        is-set-type-Setᵉ
          ( set-Propᵉ
            ( is-natural-transformation-prop-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ)))

  natural-transformation-map-set-Precategoryᵉ :
    Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ (natural-transformation-map-set-Precategoryᵉ) =
    natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  pr2ᵉ (natural-transformation-map-set-Precategoryᵉ) =
    is-set-natural-transformation-map-Precategoryᵉ

  extensionality-natural-transformation-map-Precategoryᵉ :
    (αᵉ βᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( αᵉ ＝ᵉ βᵉ) ≃ᵉ
    ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ ~ᵉ
      hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ βᵉ)
  extensionality-natural-transformation-map-Precategoryᵉ αᵉ βᵉ =
    ( equiv-funextᵉ) ∘eᵉ
    ( equiv-ap-embᵉ emb-hom-family-natural-transformation-map-Precategoryᵉ)

  eq-htpy-hom-family-natural-transformation-map-Precategoryᵉ :
    (αᵉ βᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ ~ᵉ
      hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ βᵉ) →
    αᵉ ＝ᵉ βᵉ
  eq-htpy-hom-family-natural-transformation-map-Precategoryᵉ αᵉ βᵉ =
    map-inv-equivᵉ (extensionality-natural-transformation-map-Precategoryᵉ αᵉ βᵉ)
```

### Categorical laws for natural transformations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  right-unit-law-comp-natural-transformation-map-Precategoryᵉ :
    (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
    (αᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ αᵉ
      ( id-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ) ＝ᵉ αᵉ
  right-unit-law-comp-natural-transformation-map-Precategoryᵉ Fᵉ Gᵉ αᵉ =
    eq-htpy-hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ αᵉ
        ( id-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ))
      ( αᵉ)
      ( right-unit-law-comp-hom-Precategoryᵉ Dᵉ ∘ᵉ
        hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ)

  left-unit-law-comp-natural-transformation-map-Precategoryᵉ :
    (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
    (αᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
      ( id-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ) αᵉ ＝ᵉ αᵉ
  left-unit-law-comp-natural-transformation-map-Precategoryᵉ Fᵉ Gᵉ αᵉ =
    eq-htpy-hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
        ( id-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ) αᵉ)
      ( αᵉ)
      ( left-unit-law-comp-hom-Precategoryᵉ Dᵉ ∘ᵉ
        hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ)

  associative-comp-natural-transformation-map-Precategoryᵉ :
    (Fᵉ Gᵉ Hᵉ Iᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
    (αᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
    (βᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (γᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ) →
    comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ γᵉ βᵉ) αᵉ ＝ᵉ
    comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ γᵉ
      ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ βᵉ αᵉ)
  associative-comp-natural-transformation-map-Precategoryᵉ Fᵉ Gᵉ Hᵉ Iᵉ αᵉ βᵉ γᵉ =
    eq-htpy-hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Iᵉ _ _
    ( λ xᵉ →
      associative-comp-hom-Precategoryᵉ Dᵉ
        ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ γᵉ xᵉ)
        ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ βᵉ xᵉ)
        ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ xᵉ))

  involutive-eq-associative-comp-natural-transformation-map-Precategoryᵉ :
    (Fᵉ Gᵉ Hᵉ Iᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
    (αᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
    (βᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (γᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ) →
    comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ γᵉ βᵉ) αᵉ ＝ⁱᵉ
    comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ γᵉ
      ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ βᵉ αᵉ)
  involutive-eq-associative-comp-natural-transformation-map-Precategoryᵉ
    Fᵉ Gᵉ Hᵉ Iᵉ αᵉ βᵉ γᵉ =
    involutive-eq-eqᵉ
      ( associative-comp-natural-transformation-map-Precategoryᵉ Fᵉ Gᵉ Hᵉ Iᵉ αᵉ βᵉ γᵉ)
```