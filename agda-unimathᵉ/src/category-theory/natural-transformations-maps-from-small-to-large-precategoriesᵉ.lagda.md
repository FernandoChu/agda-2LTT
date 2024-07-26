# Natural transformations between maps from small to large precategories

```agda
module category-theory.natural-transformations-maps-from-small-to-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-large-precategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.maps-from-small-to-large-precategoriesᵉ
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

Givenᵉ aᵉ smallᵉ [precategory](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ aᵉ
[largeᵉ precategory](category-theory.large-precategories.mdᵉ) `D`,ᵉ aᵉ **naturalᵉ
transformation**ᵉ fromᵉ aᵉ
[mapᵉ ofᵉ precategories](category-theory.maps-from-small-to-large-precategories.mdᵉ)
`Fᵉ : Cᵉ → D`ᵉ to `Gᵉ : Cᵉ → D`ᵉ consistsᵉ ofᵉ :

-ᵉ aᵉ familyᵉ ofᵉ morphismsᵉ `aᵉ : (xᵉ : Cᵉ) → homᵉ (Fᵉ xᵉ) (Gᵉ x)`ᵉ suchᵉ thatᵉ theᵉ followingᵉ
  identityᵉ holdsᵉ:
-ᵉ `(Gᵉ fᵉ) ∘ᵉ (aᵉ xᵉ) = (aᵉ yᵉ) ∘ᵉ (Fᵉ f)`,ᵉ forᵉ allᵉ `fᵉ : homᵉ xᵉ y`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ γFᵉ γGᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  (Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
  (Gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ)
  where

  hom-family-map-Small-Large-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  hom-family-map-Small-Large-Precategoryᵉ =
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    hom-Large-Precategoryᵉ Dᵉ
      ( obj-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ xᵉ)

  naturality-hom-family-map-Small-Large-Precategoryᵉ :
    hom-family-map-Small-Large-Precategoryᵉ →
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) → UUᵉ (βᵉ γFᵉ γGᵉ)
  naturality-hom-family-map-Small-Large-Precategoryᵉ γᵉ {xᵉ} {yᵉ} fᵉ =
    coherence-square-hom-Large-Precategoryᵉ Dᵉ
      ( hom-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ)
      ( γᵉ xᵉ)
      ( γᵉ yᵉ)
      ( hom-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ fᵉ)

  is-natural-transformation-map-Small-Large-Precategoryᵉ :
    hom-family-map-Small-Large-Precategoryᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  is-natural-transformation-map-Small-Large-Precategoryᵉ γᵉ =
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    naturality-hom-family-map-Small-Large-Precategoryᵉ γᵉ fᵉ

  natural-transformation-map-Small-Large-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  natural-transformation-map-Small-Large-Precategoryᵉ =
    Σᵉ ( hom-family-map-Small-Large-Precategoryᵉ)
      ( is-natural-transformation-map-Small-Large-Precategoryᵉ)

  hom-natural-transformation-map-Small-Large-Precategoryᵉ :
    natural-transformation-map-Small-Large-Precategoryᵉ →
    hom-family-map-Small-Large-Precategoryᵉ
  hom-natural-transformation-map-Small-Large-Precategoryᵉ = pr1ᵉ

  naturality-natural-transformation-map-Small-Large-Precategoryᵉ :
    (γᵉ : natural-transformation-map-Small-Large-Precategoryᵉ) →
    is-natural-transformation-map-Small-Large-Precategoryᵉ
      ( hom-natural-transformation-map-Small-Large-Precategoryᵉ γᵉ)
  naturality-natural-transformation-map-Small-Large-Precategoryᵉ = pr2ᵉ
```

## Composition and identity of natural transformations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  id-natural-transformation-map-Small-Large-Precategoryᵉ :
    {γFᵉ : Level} (Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ) →
    natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  pr1ᵉ (id-natural-transformation-map-Small-Large-Precategoryᵉ Fᵉ) xᵉ =
    id-hom-Large-Precategoryᵉ Dᵉ
  pr2ᵉ (id-natural-transformation-map-Small-Large-Precategoryᵉ Fᵉ) fᵉ =
    ( right-unit-law-comp-hom-Large-Precategoryᵉ Dᵉ
      ( hom-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ)) ∙ᵉ
    ( invᵉ
      ( left-unit-law-comp-hom-Large-Precategoryᵉ Dᵉ
        ( hom-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ)))

  comp-natural-transformation-map-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ γHᵉ : Level}
    (Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ) →
    (Gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ) →
    (Hᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γHᵉ) →
    natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ →
    natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ →
    natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  pr1ᵉ (comp-natural-transformation-map-Small-Large-Precategoryᵉ Fᵉ Gᵉ Hᵉ βᵉ αᵉ) xᵉ =
    comp-hom-Large-Precategoryᵉ Dᵉ
      ( hom-natural-transformation-map-Small-Large-Precategoryᵉ
          Cᵉ Dᵉ Gᵉ Hᵉ βᵉ xᵉ)
      ( hom-natural-transformation-map-Small-Large-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ αᵉ xᵉ)
  pr2ᵉ
    ( comp-natural-transformation-map-Small-Large-Precategoryᵉ Fᵉ Gᵉ Hᵉ βᵉ αᵉ)
    { Xᵉ} {Yᵉ} fᵉ =
    ( invᵉ
      ( associative-comp-hom-Large-Precategoryᵉ Dᵉ
        ( hom-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Hᵉ fᵉ)
        ( hom-natural-transformation-map-Small-Large-Precategoryᵉ
            Cᵉ Dᵉ Gᵉ Hᵉ βᵉ Xᵉ)
        ( hom-natural-transformation-map-Small-Large-Precategoryᵉ
            Cᵉ Dᵉ Fᵉ Gᵉ αᵉ Xᵉ))) ∙ᵉ
    ( apᵉ
      ( comp-hom-Large-Precategory'ᵉ Dᵉ
        ( hom-natural-transformation-map-Small-Large-Precategoryᵉ
            Cᵉ Dᵉ Fᵉ Gᵉ αᵉ Xᵉ))
      ( naturality-natural-transformation-map-Small-Large-Precategoryᵉ
          Cᵉ Dᵉ Gᵉ Hᵉ βᵉ fᵉ)) ∙ᵉ
    ( associative-comp-hom-Large-Precategoryᵉ Dᵉ
      ( hom-natural-transformation-map-Small-Large-Precategoryᵉ
          Cᵉ Dᵉ Gᵉ Hᵉ βᵉ Yᵉ)
      ( hom-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ fᵉ)
      ( hom-natural-transformation-map-Small-Large-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ αᵉ Xᵉ)) ∙ᵉ
    ( apᵉ
      ( comp-hom-Large-Precategoryᵉ Dᵉ
        ( hom-natural-transformation-map-Small-Large-Precategoryᵉ
            Cᵉ Dᵉ Gᵉ Hᵉ βᵉ Yᵉ))
      ( naturality-natural-transformation-map-Small-Large-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ αᵉ fᵉ)) ∙ᵉ
    ( invᵉ
      ( associative-comp-hom-Large-Precategoryᵉ Dᵉ
        ( hom-natural-transformation-map-Small-Large-Precategoryᵉ
            Cᵉ Dᵉ Gᵉ Hᵉ βᵉ Yᵉ)
        ( hom-natural-transformation-map-Small-Large-Precategoryᵉ
            Cᵉ Dᵉ Fᵉ Gᵉ αᵉ Yᵉ)
        ( hom-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ)))
```

## Properties

### That a family of morphisms is a natural transformation is a proposition

Thisᵉ followsᵉ fromᵉ theᵉ factᵉ thatᵉ theᵉ hom-typesᵉ areᵉ
[sets](foundation-core.sets.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ γFᵉ γGᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  (Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
  (Gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ)
  where

  is-prop-is-natural-transformation-map-Small-Large-Precategoryᵉ :
    (aᵉ : hom-family-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-propᵉ (is-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ aᵉ)
  is-prop-is-natural-transformation-map-Small-Large-Precategoryᵉ aᵉ =
    is-prop-implicit-Πᵉ
      ( λ xᵉ →
        is-prop-implicit-Πᵉ
          ( λ yᵉ →
            is-prop-Πᵉ
              ( λ fᵉ →
                is-set-hom-Large-Precategoryᵉ Dᵉ
                  ( obj-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
                  ( obj-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ yᵉ)
                  ( comp-hom-Large-Precategoryᵉ Dᵉ
                    ( hom-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ fᵉ)
                    ( aᵉ xᵉ))
                  ( comp-hom-Large-Precategoryᵉ Dᵉ
                    ( aᵉ yᵉ)
                    ( hom-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ)))))

  is-natural-transformation-prop-map-Small-Large-Precategoryᵉ :
    (aᵉ : hom-family-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  pr1ᵉ (is-natural-transformation-prop-map-Small-Large-Precategoryᵉ aᵉ) =
    is-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ aᵉ
  pr2ᵉ (is-natural-transformation-prop-map-Small-Large-Precategoryᵉ aᵉ) =
    is-prop-is-natural-transformation-map-Small-Large-Precategoryᵉ aᵉ
```

### The set of natural transformations

```agda
module _
  {l1ᵉ l2ᵉ γFᵉ γGᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  (Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
  (Gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ)
  where

  is-emb-hom-natural-transformation-map-Small-Large-Precategoryᵉ :
    is-embᵉ
      ( hom-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-emb-hom-natural-transformation-map-Small-Large-Precategoryᵉ =
    is-emb-inclusion-subtypeᵉ
      ( is-natural-transformation-prop-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)

  emb-hom-natural-transformation-map-Small-Large-Precategoryᵉ :
    natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ ↪ᵉ
    hom-family-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  emb-hom-natural-transformation-map-Small-Large-Precategoryᵉ =
    emb-subtypeᵉ
      ( is-natural-transformation-prop-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)

  is-set-natural-transformation-map-Small-Large-Precategoryᵉ :
    is-setᵉ (natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-set-natural-transformation-map-Small-Large-Precategoryᵉ =
    is-set-Σᵉ
      ( is-set-Πᵉ
        ( λ xᵉ →
          is-set-hom-Large-Precategoryᵉ Dᵉ
            ( obj-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
            ( obj-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ xᵉ)))
      ( λ αᵉ →
        is-set-type-Setᵉ
          ( set-Propᵉ
            ( is-natural-transformation-prop-map-Small-Large-Precategoryᵉ
                Cᵉ Dᵉ Fᵉ Gᵉ αᵉ)))

  natural-transformation-map-set-Small-Large-Precategoryᵉ :
    Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  pr1ᵉ (natural-transformation-map-set-Small-Large-Precategoryᵉ) =
    natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  pr2ᵉ (natural-transformation-map-set-Small-Large-Precategoryᵉ) =
    is-set-natural-transformation-map-Small-Large-Precategoryᵉ

  extensionality-natural-transformation-map-Small-Large-Precategoryᵉ :
    (αᵉ βᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( αᵉ ＝ᵉ βᵉ) ≃ᵉ
    ( hom-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ ~ᵉ
      hom-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ βᵉ)
  extensionality-natural-transformation-map-Small-Large-Precategoryᵉ αᵉ βᵉ =
    ( equiv-funextᵉ) ∘eᵉ
    ( equiv-ap-embᵉ
        emb-hom-natural-transformation-map-Small-Large-Precategoryᵉ)

  eq-htpy-hom-natural-transformation-map-Small-Large-Precategoryᵉ :
    (αᵉ βᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( hom-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ ~ᵉ
      hom-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ βᵉ) →
    αᵉ ＝ᵉ βᵉ
  eq-htpy-hom-natural-transformation-map-Small-Large-Precategoryᵉ αᵉ βᵉ =
    map-inv-equivᵉ
      ( extensionality-natural-transformation-map-Small-Large-Precategoryᵉ αᵉ βᵉ)
```

### Categorical laws for natural transformations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  right-unit-law-comp-natural-transformation-map-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ : Level}
    (Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
    (Gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ)
    (aᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ aᵉ
      ( id-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ) ＝ᵉ aᵉ
  right-unit-law-comp-natural-transformation-map-Small-Large-Precategoryᵉ Fᵉ Gᵉ aᵉ =
    eq-htpy-hom-natural-transformation-map-Small-Large-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ
      ( comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ aᵉ
        ( id-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ))
      ( aᵉ)
      ( right-unit-law-comp-hom-Large-Precategoryᵉ Dᵉ ∘ᵉ
        hom-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ aᵉ)

  left-unit-law-comp-natural-transformation-map-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ : Level}
    (Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
    (Gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ)
    (aᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
      ( id-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ) aᵉ ＝ᵉ aᵉ
  left-unit-law-comp-natural-transformation-map-Small-Large-Precategoryᵉ Fᵉ Gᵉ aᵉ =
    eq-htpy-hom-natural-transformation-map-Small-Large-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ
      ( comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
        ( id-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ) aᵉ)
      ( aᵉ)
      ( left-unit-law-comp-hom-Large-Precategoryᵉ Dᵉ ∘ᵉ
        hom-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ aᵉ)

  associative-comp-natural-transformation-map-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ γHᵉ γIᵉ : Level}
    (Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
    (Gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ)
    (Hᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γHᵉ)
    (Iᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γIᵉ)
    (aᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
    (bᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (cᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ) →
    comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ cᵉ bᵉ)
      ( aᵉ) ＝ᵉ
    comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ cᵉ
      ( comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ bᵉ aᵉ)
  associative-comp-natural-transformation-map-Small-Large-Precategoryᵉ
    Fᵉ Gᵉ Hᵉ Iᵉ aᵉ bᵉ cᵉ =
    eq-htpy-hom-natural-transformation-map-Small-Large-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Iᵉ _ _
      ( λ xᵉ →
        associative-comp-hom-Large-Precategoryᵉ Dᵉ
          ( hom-natural-transformation-map-Small-Large-Precategoryᵉ
            Cᵉ Dᵉ Hᵉ Iᵉ cᵉ xᵉ)
          ( hom-natural-transformation-map-Small-Large-Precategoryᵉ
            Cᵉ Dᵉ Gᵉ Hᵉ bᵉ xᵉ)
          ( hom-natural-transformation-map-Small-Large-Precategoryᵉ
            Cᵉ Dᵉ Fᵉ Gᵉ aᵉ xᵉ))

  involutive-eq-associative-comp-natural-transformation-map-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ γHᵉ γIᵉ : Level}
    (Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
    (Gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ)
    (Hᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γHᵉ)
    (Iᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γIᵉ)
    (aᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
    (bᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (cᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ) →
    comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ cᵉ bᵉ)
      ( aᵉ) ＝ⁱᵉ
    comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ cᵉ
      ( comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ bᵉ aᵉ)
  involutive-eq-associative-comp-natural-transformation-map-Small-Large-Precategoryᵉ
    Fᵉ Gᵉ Hᵉ Iᵉ aᵉ bᵉ cᵉ =
    involutive-eq-eqᵉ
      ( associative-comp-natural-transformation-map-Small-Large-Precategoryᵉ
          Fᵉ Gᵉ Hᵉ Iᵉ aᵉ bᵉ cᵉ)
```