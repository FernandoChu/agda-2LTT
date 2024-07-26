# Natural transformations between functors between precategories

```agda
{-# OPTIONSᵉ --allow-unsolved-metasᵉ #-}

module category-theory.natural-transformations-functors-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.natural-transformations-maps-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
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

Givenᵉ [precategories](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ `D`,ᵉ aᵉ **naturalᵉ
transformation**ᵉ fromᵉ aᵉ [functor](category-theory.functors-precategories.mdᵉ)
`Fᵉ : Cᵉ → D`ᵉ to `Gᵉ : Cᵉ → D`ᵉ consistsᵉ ofᵉ :

-ᵉ aᵉ familyᵉ ofᵉ morphismsᵉ `γᵉ : (xᵉ : Cᵉ) → homᵉ (Fᵉ xᵉ) (Gᵉ x)`ᵉ suchᵉ thatᵉ theᵉ followingᵉ
  identityᵉ holdsᵉ:
-ᵉ `(Gᵉ fᵉ) ∘ᵉ (γᵉ xᵉ) = (γᵉ yᵉ) ∘ᵉ (Fᵉ f)`,ᵉ forᵉ allᵉ `fᵉ : homᵉ xᵉ y`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  hom-family-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l4ᵉ)
  hom-family-functor-Precategoryᵉ =
    hom-family-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  is-natural-transformation-Precategoryᵉ :
    hom-family-functor-Precategoryᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-natural-transformation-Precategoryᵉ =
    is-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  natural-transformation-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  natural-transformation-Precategoryᵉ =
    natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  hom-family-natural-transformation-Precategoryᵉ :
    natural-transformation-Precategoryᵉ → hom-family-functor-Precategoryᵉ
  hom-family-natural-transformation-Precategoryᵉ =
    hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  naturality-natural-transformation-Precategoryᵉ :
    (γᵉ : natural-transformation-Precategoryᵉ) →
    is-natural-transformation-Precategoryᵉ
      ( hom-family-natural-transformation-Precategoryᵉ γᵉ)
  naturality-natural-transformation-Precategoryᵉ =
    naturality-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
```

## Composition and identity of natural transformations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  id-natural-transformation-Precategoryᵉ :
    (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ) → natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  id-natural-transformation-Precategoryᵉ Fᵉ =
    id-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  comp-natural-transformation-Precategoryᵉ :
    (Fᵉ Gᵉ Hᵉ : functor-Precategoryᵉ Cᵉ Dᵉ) →
    natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ →
    natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ →
    natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  comp-natural-transformation-Precategoryᵉ Fᵉ Gᵉ Hᵉ =
    comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Hᵉ)
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
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-prop-is-natural-transformation-Precategoryᵉ :
    (γᵉ : hom-family-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-propᵉ (is-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ γᵉ)
  is-prop-is-natural-transformation-Precategoryᵉ =
    is-prop-is-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  is-natural-transformation-prop-Precategoryᵉ :
    (γᵉ : hom-family-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-natural-transformation-prop-Precategoryᵉ =
    is-natural-transformation-prop-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
```

### The set of natural transformations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-emb-hom-family-natural-transformation-Precategoryᵉ :
    is-embᵉ (hom-family-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-emb-hom-family-natural-transformation-Precategoryᵉ =
    is-emb-hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  emb-hom-family-natural-transformation-Precategoryᵉ :
    natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ ↪ᵉ
    hom-family-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  emb-hom-family-natural-transformation-Precategoryᵉ =
    emb-hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  is-set-natural-transformation-Precategoryᵉ :
    is-setᵉ (natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-set-natural-transformation-Precategoryᵉ =
    is-set-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  natural-transformation-set-Precategoryᵉ :
    Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ (natural-transformation-set-Precategoryᵉ) =
    natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  pr2ᵉ (natural-transformation-set-Precategoryᵉ) =
    is-set-natural-transformation-Precategoryᵉ

  extensionality-natural-transformation-Precategoryᵉ :
    (αᵉ βᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( αᵉ ＝ᵉ βᵉ) ≃ᵉ
    ( hom-family-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ ~ᵉ
      hom-family-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ βᵉ)
  extensionality-natural-transformation-Precategoryᵉ =
    extensionality-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  eq-htpy-hom-family-natural-transformation-Precategoryᵉ :
    (αᵉ βᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( hom-family-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ ~ᵉ
      hom-family-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ βᵉ) →
    αᵉ ＝ᵉ βᵉ
  eq-htpy-hom-family-natural-transformation-Precategoryᵉ =
    eq-htpy-hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
```

### Categorical laws for natural transformations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  right-unit-law-comp-natural-transformation-Precategoryᵉ :
    (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
    (αᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ αᵉ
      ( id-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ) ＝ᵉ αᵉ
  right-unit-law-comp-natural-transformation-Precategoryᵉ Fᵉ Gᵉ =
    right-unit-law-comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  left-unit-law-comp-natural-transformation-Precategoryᵉ :
    (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
    (αᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
      ( id-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ) αᵉ ＝ᵉ αᵉ
  left-unit-law-comp-natural-transformation-Precategoryᵉ Fᵉ Gᵉ =
    left-unit-law-comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  associative-comp-natural-transformation-Precategoryᵉ :
    (Fᵉ Gᵉ Hᵉ Iᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
    (αᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
    (βᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (γᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ) →
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ γᵉ βᵉ) αᵉ ＝ᵉ
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ γᵉ
      ( comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ βᵉ αᵉ)
  associative-comp-natural-transformation-Precategoryᵉ Fᵉ Gᵉ Hᵉ Iᵉ =
    associative-comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Hᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Iᵉ)

  involutive-eq-associative-comp-natural-transformation-Precategoryᵉ :
    (Fᵉ Gᵉ Hᵉ Iᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
    (αᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
    (βᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (γᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ) →
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ γᵉ βᵉ) αᵉ ＝ⁱᵉ
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ γᵉ
      ( comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ βᵉ αᵉ)
  involutive-eq-associative-comp-natural-transformation-Precategoryᵉ Fᵉ Gᵉ Hᵉ Iᵉ =
    involutive-eq-associative-comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Hᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Iᵉ)
```

## Whiskering

Ifᵉ `αᵉ : Fᵉ ⇒ᵉ G`ᵉ isᵉ aᵉ naturalᵉ transformationsᵉ betweenᵉ functorsᵉ `F,ᵉ Gᵉ : Cᵉ → D`,ᵉ andᵉ
`Hᵉ : Dᵉ → E`ᵉ isᵉ anotherᵉ functor,ᵉ weᵉ canᵉ formᵉ theᵉ naturalᵉ transformationᵉ
`Hᵉ •ᵉ αᵉ : Hᵉ ∘ᵉ Fᵉ ⇒ᵉ Hᵉ ∘ᵉ G`.ᵉ Itsᵉ componentᵉ atᵉ `x`ᵉ isᵉ `(Hᵉ •ᵉ α)(xᵉ) = H(α(x))`.ᵉ

Onᵉ theᵉ otherᵉ hand,ᵉ ifᵉ weᵉ haveᵉ aᵉ functorᵉ `Kᵉ : Bᵉ → C`,ᵉ weᵉ canᵉ formᵉ aᵉ naturalᵉ
transformationᵉ `αᵉ •ᵉ Kᵉ : Fᵉ ∘ᵉ Kᵉ ⇒ᵉ Gᵉ ∘ᵉ K`.ᵉ Itsᵉ componentᵉ atᵉ `x`ᵉ isᵉ
`(αᵉ •ᵉ K)(xᵉ) = α(K(x))`.ᵉ

Here,ᵉ `•`ᵉ denotesᵉ _whiskering_.ᵉ Noteᵉ thatᵉ thereᵉ areᵉ twoᵉ kindsᵉ ofᵉ whiskering,ᵉ
dependingᵉ onᵉ whetherᵉ theᵉ firstᵉ orᵉ theᵉ secondᵉ parameterᵉ expectsᵉ aᵉ naturalᵉ
transformation.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Eᵉ : Precategoryᵉ l5ᵉ l6ᵉ)
  where

  left-whisker-natural-transformation-Precategoryᵉ :
    (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
    (Hᵉ : functor-Precategoryᵉ Dᵉ Eᵉ)
    (αᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    natural-transformation-Precategoryᵉ
      ( Cᵉ)
      ( Eᵉ)
      ( comp-functor-Precategoryᵉ Cᵉ Dᵉ Eᵉ Hᵉ Fᵉ)
      ( comp-functor-Precategoryᵉ Cᵉ Dᵉ Eᵉ Hᵉ Gᵉ)
  left-whisker-natural-transformation-Precategoryᵉ Fᵉ Gᵉ Hᵉ αᵉ =
    ( λ xᵉ → (pr1ᵉ (pr2ᵉ Hᵉ)) ((pr1ᵉ αᵉ) xᵉ)) ,ᵉ
    ( λ {xᵉ} {yᵉ} → λ fᵉ →
      invᵉ
        ( preserves-comp-functor-Precategoryᵉ
          ( Dᵉ)
          ( Eᵉ)
          ( Hᵉ)
          ( (pr1ᵉ (pr2ᵉ Gᵉ)) fᵉ)
          ( (pr1ᵉ αᵉ) xᵉ)) ∙ᵉ
      ( apᵉ (pr1ᵉ (pr2ᵉ Hᵉ)) ((pr2ᵉ αᵉ) fᵉ)) ∙ᵉ
      ( preserves-comp-functor-Precategoryᵉ
        ( Dᵉ)
        ( Eᵉ)
        ( Hᵉ)
        ( (pr1ᵉ αᵉ) yᵉ)
        ( (pr1ᵉ (pr2ᵉ Fᵉ)) fᵉ)))

  right-whisker-natural-transformation-Precategoryᵉ :
    (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
    (αᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
    (Kᵉ : functor-Precategoryᵉ Eᵉ Cᵉ) →
    natural-transformation-Precategoryᵉ
      ( Eᵉ)
      ( Dᵉ)
      ( comp-functor-Precategoryᵉ Eᵉ Cᵉ Dᵉ Fᵉ Kᵉ)
      ( comp-functor-Precategoryᵉ Eᵉ Cᵉ Dᵉ Gᵉ Kᵉ)
  right-whisker-natural-transformation-Precategoryᵉ Fᵉ Gᵉ αᵉ Kᵉ =
    (λ xᵉ → (pr1ᵉ αᵉ) ((pr1ᵉ Kᵉ) xᵉ)) ,ᵉ (λ fᵉ → (pr2ᵉ αᵉ) ((pr1ᵉ (pr2ᵉ Kᵉ)) fᵉ))
```

## Horizontal composition

Horizontalᵉ compositionᵉ (hereᵉ denotedᵉ byᵉ `*`ᵉ) isᵉ generalizedᵉ
[whiskering](category-theory.natural-transformations-functors-precategories.md#whiskeringᵉ)
(hereᵉ denotedᵉ byᵉ `•`),ᵉ andᵉ alsoᵉ definedᵉ byᵉ it.ᵉ Givenᵉ naturalᵉ transformationsᵉ
`αᵉ : Fᵉ ⇒ᵉ G`,ᵉ `F,ᵉ Gᵉ : Cᵉ → D`,ᵉ andᵉ `βᵉ : Hᵉ ⇒ᵉ I`,ᵉ `H,ᵉ Iᵉ : Dᵉ → E`,ᵉ weᵉ canᵉ formᵉ aᵉ
naturalᵉ transformationᵉ `βᵉ *ᵉ αᵉ : Hᵉ ∘ᵉ Fᵉ ⇒ᵉ Iᵉ ∘ᵉ G`.ᵉ

Moreᵉ precisely,ᵉ `βᵉ *ᵉ αᵉ = (βᵉ •ᵉ Gᵉ) ∘ᵉ (Hᵉ •ᵉ α)`,ᵉ thatᵉ is,ᵉ weᵉ composeᵉ twoᵉ naturalᵉ
transformationsᵉ obtainedᵉ byᵉ whiskering.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Eᵉ : Precategoryᵉ l5ᵉ l6ᵉ)
  where

  horizontal-comp-natural-transformation-Precategoryᵉ :
    (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
    (Hᵉ Iᵉ : functor-Precategoryᵉ Dᵉ Eᵉ)
    (βᵉ : natural-transformation-Precategoryᵉ Dᵉ Eᵉ Hᵉ Iᵉ)
    (αᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    natural-transformation-Precategoryᵉ
      ( Cᵉ)
      ( Eᵉ)
      ( comp-functor-Precategoryᵉ Cᵉ Dᵉ Eᵉ Hᵉ Fᵉ)
      ( comp-functor-Precategoryᵉ Cᵉ Dᵉ Eᵉ Iᵉ Gᵉ)
  horizontal-comp-natural-transformation-Precategoryᵉ Fᵉ Gᵉ Hᵉ Iᵉ βᵉ αᵉ =
    comp-natural-transformation-Precategoryᵉ Cᵉ Eᵉ
      ( comp-functor-Precategoryᵉ Cᵉ Dᵉ Eᵉ Hᵉ Fᵉ)
      ( comp-functor-Precategoryᵉ Cᵉ Dᵉ Eᵉ Hᵉ Gᵉ)
      ( comp-functor-Precategoryᵉ Cᵉ Dᵉ Eᵉ Iᵉ Gᵉ)
      ( right-whisker-natural-transformation-Precategoryᵉ Dᵉ Eᵉ Cᵉ Hᵉ Iᵉ βᵉ Gᵉ)
      ( left-whisker-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Eᵉ Fᵉ Gᵉ Hᵉ αᵉ)
```