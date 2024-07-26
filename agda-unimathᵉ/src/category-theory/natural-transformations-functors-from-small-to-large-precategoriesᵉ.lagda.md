# Natural transformations between functors from small to large precategories

```agda
module category-theory.natural-transformations-functors-from-small-to-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-from-small-to-large-precategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.natural-transformations-maps-from-small-to-large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ smallᵉ [precategory](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ aᵉ
[largeᵉ precategory](category-theory.large-precategories.mdᵉ) `D`,ᵉ aᵉ **naturalᵉ
transformation**ᵉ fromᵉ aᵉ
[functor](category-theory.functors-from-small-to-large-precategories.mdᵉ)
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
  (Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
  (Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ)
  where

  hom-family-functor-Small-Large-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  hom-family-functor-Small-Large-Precategoryᵉ =
    hom-family-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  is-natural-transformation-Small-Large-Precategoryᵉ :
    hom-family-functor-Small-Large-Precategoryᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  is-natural-transformation-Small-Large-Precategoryᵉ =
    is-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  natural-transformation-Small-Large-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  natural-transformation-Small-Large-Precategoryᵉ =
    natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  hom-natural-transformation-Small-Large-Precategoryᵉ :
    natural-transformation-Small-Large-Precategoryᵉ →
    hom-family-functor-Small-Large-Precategoryᵉ
  hom-natural-transformation-Small-Large-Precategoryᵉ =
    hom-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  naturality-natural-transformation-Small-Large-Precategoryᵉ :
    (γᵉ : natural-transformation-Small-Large-Precategoryᵉ) →
    is-natural-transformation-Small-Large-Precategoryᵉ
      ( hom-natural-transformation-Small-Large-Precategoryᵉ γᵉ)
  naturality-natural-transformation-Small-Large-Precategoryᵉ =
    naturality-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
```

## Composition and identity of natural transformations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  id-natural-transformation-Small-Large-Precategoryᵉ :
    {γFᵉ : Level} (Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ) →
    natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  id-natural-transformation-Small-Large-Precategoryᵉ Fᵉ =
    id-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  comp-natural-transformation-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ γHᵉ : Level}
    (Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
    (Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ)
    (Hᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γHᵉ) →
    natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ →
    natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ →
    natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  comp-natural-transformation-Small-Large-Precategoryᵉ Fᵉ Gᵉ Hᵉ =
    comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Hᵉ)
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
  (Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
  (Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ)
  where

  is-prop-is-natural-transformation-Small-Large-Precategoryᵉ :
    (γᵉ : hom-family-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-propᵉ (is-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ γᵉ)
  is-prop-is-natural-transformation-Small-Large-Precategoryᵉ =
    is-prop-is-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  is-natural-transformation-prop-Small-Large-Precategoryᵉ :
    (γᵉ : hom-family-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  is-natural-transformation-prop-Small-Large-Precategoryᵉ =
    is-natural-transformation-prop-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
```

### The set of natural transformations

```agda
module _
  {l1ᵉ l2ᵉ γFᵉ γGᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  (Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
  (Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ)
  where

  is-emb-hom-family-natural-transformation-Small-Large-Precategoryᵉ :
    is-embᵉ (hom-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-emb-hom-family-natural-transformation-Small-Large-Precategoryᵉ =
    is-emb-hom-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  emb-hom-natural-transformation-Small-Large-Precategoryᵉ :
    natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ ↪ᵉ
    hom-family-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  emb-hom-natural-transformation-Small-Large-Precategoryᵉ =
    emb-hom-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  is-set-natural-transformation-Small-Large-Precategoryᵉ :
    is-setᵉ (natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-set-natural-transformation-Small-Large-Precategoryᵉ =
    is-set-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  natural-transformation-set-Small-Large-Precategoryᵉ :
    Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  pr1ᵉ (natural-transformation-set-Small-Large-Precategoryᵉ) =
    natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  pr2ᵉ (natural-transformation-set-Small-Large-Precategoryᵉ) =
    is-set-natural-transformation-Small-Large-Precategoryᵉ

  extensionality-natural-transformation-Small-Large-Precategoryᵉ :
    (aᵉ bᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( aᵉ ＝ᵉ bᵉ) ≃ᵉ
    ( hom-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ aᵉ ~ᵉ
      hom-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ bᵉ)
  extensionality-natural-transformation-Small-Large-Precategoryᵉ =
    extensionality-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  eq-htpy-hom-natural-transformation-Small-Large-Precategoryᵉ :
    (aᵉ bᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( hom-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ aᵉ ~ᵉ
      hom-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ bᵉ) →
    aᵉ ＝ᵉ bᵉ
  eq-htpy-hom-natural-transformation-Small-Large-Precategoryᵉ =
    eq-htpy-hom-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
```

### Categorical laws for natural transformations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  right-unit-law-comp-natural-transformation-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ : Level}
    (Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
    (Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ)
    (aᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ aᵉ
      ( id-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ) ＝ᵉ aᵉ
  right-unit-law-comp-natural-transformation-Small-Large-Precategoryᵉ Fᵉ Gᵉ =
    right-unit-law-comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  left-unit-law-comp-natural-transformation-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ : Level}
    (Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
    (Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ)
    (aᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
      ( id-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ) aᵉ ＝ᵉ aᵉ
  left-unit-law-comp-natural-transformation-Small-Large-Precategoryᵉ Fᵉ Gᵉ =
    left-unit-law-comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  associative-comp-natural-transformation-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ γHᵉ γIᵉ : Level}
    (Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
    (Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ)
    (Hᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γHᵉ)
    (Iᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γIᵉ)
    (aᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
    (bᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (cᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ) →
    comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ cᵉ bᵉ) aᵉ ＝ᵉ
    comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ cᵉ
      ( comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ bᵉ aᵉ)
  associative-comp-natural-transformation-Small-Large-Precategoryᵉ Fᵉ Gᵉ Hᵉ Iᵉ =
    associative-comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Hᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Iᵉ)

  involutive-eq-associative-comp-natural-transformation-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ γHᵉ γIᵉ : Level}
    (Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
    (Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ)
    (Hᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γHᵉ)
    (Iᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γIᵉ)
    (aᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
    (bᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (cᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ) →
    comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ cᵉ bᵉ) aᵉ ＝ⁱᵉ
    comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ cᵉ
      ( comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ bᵉ aᵉ)
  involutive-eq-associative-comp-natural-transformation-Small-Large-Precategoryᵉ
    Fᵉ Gᵉ Hᵉ Iᵉ =
    involutive-eq-associative-comp-natural-transformation-map-Small-Large-Precategoryᵉ
      ( Cᵉ)
      ( Dᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Hᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Iᵉ)
```