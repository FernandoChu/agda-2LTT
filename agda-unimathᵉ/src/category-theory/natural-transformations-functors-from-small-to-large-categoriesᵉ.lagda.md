# Natural transformations between functors from small to large categories

```agda
module category-theory.natural-transformations-functors-from-small-to-large-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.functors-from-small-to-large-categoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.natural-transformations-functors-from-small-to-large-precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ smallᵉ [category](category-theory.categories.mdᵉ) `C`ᵉ andᵉ aᵉ
[largeᵉ category](category-theory.large-categories.mdᵉ) `D`,ᵉ aᵉ **naturalᵉ
transformation**ᵉ fromᵉ aᵉ
[functor](category-theory.functors-from-small-to-large-categories.mdᵉ)
`Fᵉ : Cᵉ → D`ᵉ to `Gᵉ : Cᵉ → D`ᵉ consistsᵉ ofᵉ :

-ᵉ aᵉ familyᵉ ofᵉ morphismsᵉ `aᵉ : (xᵉ : Cᵉ) → homᵉ (Fᵉ xᵉ) (Gᵉ x)`ᵉ suchᵉ thatᵉ theᵉ followingᵉ
  identityᵉ holdsᵉ:
-ᵉ `(Gᵉ fᵉ) ∘ᵉ (aᵉ xᵉ) = (aᵉ yᵉ) ∘ᵉ (Fᵉ f)`,ᵉ forᵉ allᵉ `fᵉ : homᵉ xᵉ y`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ γFᵉ γGᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Categoryᵉ αᵉ βᵉ)
  (Fᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γFᵉ)
  (Gᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γGᵉ)
  where

  hom-family-functor-Small-Large-Categoryᵉ : UUᵉ (l1ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  hom-family-functor-Small-Large-Categoryᵉ =
    hom-family-functor-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ) Fᵉ Gᵉ

  is-natural-transformation-Small-Large-Categoryᵉ :
    hom-family-functor-Small-Large-Categoryᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  is-natural-transformation-Small-Large-Categoryᵉ =
    is-natural-transformation-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ) Fᵉ Gᵉ

  natural-transformation-Small-Large-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  natural-transformation-Small-Large-Categoryᵉ =
    natural-transformation-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ) Fᵉ Gᵉ

  hom-natural-transformation-Small-Large-Categoryᵉ :
    natural-transformation-Small-Large-Categoryᵉ →
    hom-family-functor-Small-Large-Categoryᵉ
  hom-natural-transformation-Small-Large-Categoryᵉ =
    hom-natural-transformation-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ) Fᵉ Gᵉ

  naturality-natural-transformation-Small-Large-Categoryᵉ :
    (γᵉ : natural-transformation-Small-Large-Categoryᵉ) →
    is-natural-transformation-Small-Large-Categoryᵉ
      ( hom-natural-transformation-Small-Large-Categoryᵉ γᵉ)
  naturality-natural-transformation-Small-Large-Categoryᵉ =
    naturality-natural-transformation-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ) Fᵉ Gᵉ
```

## Composition and identity of natural transformations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Categoryᵉ αᵉ βᵉ)
  where

  id-natural-transformation-Small-Large-Categoryᵉ :
    {γFᵉ : Level} (Fᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γFᵉ) →
    natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  id-natural-transformation-Small-Large-Categoryᵉ =
    id-natural-transformation-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ)

  comp-natural-transformation-Small-Large-Categoryᵉ :
    {γFᵉ γGᵉ γHᵉ : Level}
    (Fᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γFᵉ)
    (Gᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γGᵉ)
    (Hᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γHᵉ) →
    natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ →
    natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ →
    natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  comp-natural-transformation-Small-Large-Categoryᵉ =
    comp-natural-transformation-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ)
```

## Properties

### That a family of morphisms is a natural transformation is a proposition

Thisᵉ followsᵉ fromᵉ theᵉ factᵉ thatᵉ theᵉ hom-typesᵉ areᵉ
[sets](foundation-core.sets.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ γFᵉ γGᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Categoryᵉ αᵉ βᵉ)
  (Fᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γFᵉ)
  (Gᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γGᵉ)
  where

  is-prop-is-natural-transformation-Small-Large-Categoryᵉ :
    (γᵉ : hom-family-functor-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-propᵉ (is-natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ γᵉ)
  is-prop-is-natural-transformation-Small-Large-Categoryᵉ =
    is-prop-is-natural-transformation-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ) Fᵉ Gᵉ

  is-natural-transformation-prop-Small-Large-Categoryᵉ :
    (γᵉ : hom-family-functor-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  is-natural-transformation-prop-Small-Large-Categoryᵉ =
    is-natural-transformation-prop-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ) Fᵉ Gᵉ
```

### The set of natural transformations

```agda
module _
  {l1ᵉ l2ᵉ γFᵉ γGᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Categoryᵉ αᵉ βᵉ)
  (Fᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γFᵉ)
  (Gᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γGᵉ)
  where

  is-emb-hom-natural-transformation-Small-Large-Categoryᵉ :
    is-embᵉ (hom-natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-emb-hom-natural-transformation-Small-Large-Categoryᵉ =
    is-emb-hom-family-natural-transformation-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ) Fᵉ Gᵉ

  emb-hom-natural-transformation-Small-Large-Categoryᵉ :
    natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ ↪ᵉ
    hom-family-functor-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  emb-hom-natural-transformation-Small-Large-Categoryᵉ =
    emb-hom-natural-transformation-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ) Fᵉ Gᵉ

  is-set-natural-transformation-Small-Large-Categoryᵉ :
    is-setᵉ (natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-set-natural-transformation-Small-Large-Categoryᵉ =
    is-set-natural-transformation-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ) Fᵉ Gᵉ

  natural-transformation-set-Small-Large-Categoryᵉ :
    Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  pr1ᵉ (natural-transformation-set-Small-Large-Categoryᵉ) =
    natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  pr2ᵉ (natural-transformation-set-Small-Large-Categoryᵉ) =
    is-set-natural-transformation-Small-Large-Categoryᵉ

  extensionality-natural-transformation-Small-Large-Categoryᵉ :
    (aᵉ bᵉ : natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( aᵉ ＝ᵉ bᵉ) ≃ᵉ
    ( hom-natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ aᵉ ~ᵉ
      hom-natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ bᵉ)
  extensionality-natural-transformation-Small-Large-Categoryᵉ =
    extensionality-natural-transformation-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ) Fᵉ Gᵉ

  eq-htpy-hom-natural-transformation-Small-Large-Categoryᵉ :
    (aᵉ bᵉ : natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( hom-natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ aᵉ ~ᵉ
      hom-natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ bᵉ) →
    aᵉ ＝ᵉ bᵉ
  eq-htpy-hom-natural-transformation-Small-Large-Categoryᵉ =
    eq-htpy-hom-natural-transformation-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ) Fᵉ Gᵉ
```

### Categorical laws for natural transformations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Categoryᵉ αᵉ βᵉ)
  where

  right-unit-law-comp-natural-transformation-Small-Large-Categoryᵉ :
    {γFᵉ γGᵉ : Level}
    (Fᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γFᵉ)
    (Gᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γGᵉ)
    (aᵉ : natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ aᵉ
      ( id-natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ) ＝ᵉ aᵉ
  right-unit-law-comp-natural-transformation-Small-Large-Categoryᵉ =
    right-unit-law-comp-natural-transformation-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ)

  left-unit-law-comp-natural-transformation-Small-Large-Categoryᵉ :
    {γFᵉ γGᵉ : Level}
    (Fᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γFᵉ)
    (Gᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γGᵉ)
    (aᵉ : natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
      ( id-natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Gᵉ) aᵉ ＝ᵉ aᵉ
  left-unit-law-comp-natural-transformation-Small-Large-Categoryᵉ =
    left-unit-law-comp-natural-transformation-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ)

  associative-comp-natural-transformation-Small-Large-Categoryᵉ :
    {γFᵉ γGᵉ γHᵉ γIᵉ : Level}
    (Fᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γFᵉ)
    (Gᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γGᵉ)
    (Hᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γHᵉ)
    (Iᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γIᵉ)
    (aᵉ : natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
    (bᵉ : natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (cᵉ : natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ) →
    comp-natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ cᵉ bᵉ) aᵉ ＝ᵉ
    comp-natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ cᵉ
      ( comp-natural-transformation-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ bᵉ aᵉ)
  associative-comp-natural-transformation-Small-Large-Categoryᵉ =
    associative-comp-natural-transformation-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) (large-precategory-Large-Categoryᵉ Dᵉ)
```