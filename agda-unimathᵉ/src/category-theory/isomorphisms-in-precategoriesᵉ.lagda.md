# Isomorphisms in precategories

```agda
module category-theory.isomorphisms-in-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.propositionsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ **isomorphism**ᵉ in aᵉ [precategory](category-theory.precategories.mdᵉ) `C`ᵉ isᵉ aᵉ
morphismᵉ `fᵉ : xᵉ → y`ᵉ in `C`ᵉ forᵉ whichᵉ thereᵉ existsᵉ aᵉ morphismᵉ `gᵉ : yᵉ → x`ᵉ suchᵉ
thatᵉ `fᵉ ∘ᵉ gᵉ ＝ᵉ id`ᵉ andᵉ `gᵉ ∘ᵉ fᵉ ＝ᵉ id`.ᵉ

## Definitions

### The predicate of being an isomorphism in a precategory

```agda
is-iso-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
  UUᵉ l2ᵉ
is-iso-Precategoryᵉ Cᵉ {xᵉ} {yᵉ} fᵉ =
  Σᵉ ( hom-Precategoryᵉ Cᵉ yᵉ xᵉ)
    ( λ gᵉ →
      ( comp-hom-Precategoryᵉ Cᵉ fᵉ gᵉ ＝ᵉ id-hom-Precategoryᵉ Cᵉ) ×ᵉ
      ( comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ ＝ᵉ id-hom-Precategoryᵉ Cᵉ))

module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  {fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ}
  where

  hom-inv-is-iso-Precategoryᵉ :
    is-iso-Precategoryᵉ Cᵉ fᵉ → hom-Precategoryᵉ Cᵉ yᵉ xᵉ
  hom-inv-is-iso-Precategoryᵉ = pr1ᵉ

  is-section-hom-inv-is-iso-Precategoryᵉ :
    (Hᵉ : is-iso-Precategoryᵉ Cᵉ fᵉ) →
    comp-hom-Precategoryᵉ Cᵉ fᵉ (hom-inv-is-iso-Precategoryᵉ Hᵉ) ＝ᵉ
    id-hom-Precategoryᵉ Cᵉ
  is-section-hom-inv-is-iso-Precategoryᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  is-retraction-hom-inv-is-iso-Precategoryᵉ :
    (Hᵉ : is-iso-Precategoryᵉ Cᵉ fᵉ) →
    comp-hom-Precategoryᵉ Cᵉ (hom-inv-is-iso-Precategoryᵉ Hᵉ) fᵉ ＝ᵉ
    id-hom-Precategoryᵉ Cᵉ
  is-retraction-hom-inv-is-iso-Precategoryᵉ = pr2ᵉ ∘ᵉ pr2ᵉ
```

### Isomorphisms in a precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ)
  where

  iso-Precategoryᵉ : UUᵉ l2ᵉ
  iso-Precategoryᵉ = Σᵉ (hom-Precategoryᵉ Cᵉ xᵉ yᵉ) (is-iso-Precategoryᵉ Cᵉ)

module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  (fᵉ : iso-Precategoryᵉ Cᵉ xᵉ yᵉ)
  where

  hom-iso-Precategoryᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ
  hom-iso-Precategoryᵉ = pr1ᵉ fᵉ

  is-iso-iso-Precategoryᵉ :
    is-iso-Precategoryᵉ Cᵉ hom-iso-Precategoryᵉ
  is-iso-iso-Precategoryᵉ = pr2ᵉ fᵉ

  hom-inv-iso-Precategoryᵉ : hom-Precategoryᵉ Cᵉ yᵉ xᵉ
  hom-inv-iso-Precategoryᵉ =
    hom-inv-is-iso-Precategoryᵉ Cᵉ
      ( is-iso-iso-Precategoryᵉ)

  is-section-hom-inv-iso-Precategoryᵉ :
    ( comp-hom-Precategoryᵉ Cᵉ
      ( hom-iso-Precategoryᵉ)
      ( hom-inv-iso-Precategoryᵉ)) ＝ᵉ
    ( id-hom-Precategoryᵉ Cᵉ)
  is-section-hom-inv-iso-Precategoryᵉ =
    is-section-hom-inv-is-iso-Precategoryᵉ Cᵉ
      ( is-iso-iso-Precategoryᵉ)

  is-retraction-hom-inv-iso-Precategoryᵉ :
    ( comp-hom-Precategoryᵉ Cᵉ
      ( hom-inv-iso-Precategoryᵉ)
      ( hom-iso-Precategoryᵉ)) ＝ᵉ
    ( id-hom-Precategoryᵉ Cᵉ)
  is-retraction-hom-inv-iso-Precategoryᵉ =
    is-retraction-hom-inv-is-iso-Precategoryᵉ Cᵉ
      ( is-iso-iso-Precategoryᵉ)
```

## Examples

### The identity isomorphisms

Forᵉ anyᵉ objectᵉ `xᵉ : A`,ᵉ theᵉ identityᵉ morphismᵉ `id_xᵉ : homᵉ xᵉ x`ᵉ isᵉ anᵉ isomorphismᵉ
fromᵉ `x`ᵉ to `x`ᵉ sinceᵉ `id_xᵉ ∘ᵉ id_xᵉ = id_x`ᵉ (itᵉ isᵉ itsᵉ ownᵉ inverse).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ : obj-Precategoryᵉ Cᵉ}
  where

  is-iso-id-hom-Precategoryᵉ :
    is-iso-Precategoryᵉ Cᵉ (id-hom-Precategoryᵉ Cᵉ {xᵉ})
  pr1ᵉ is-iso-id-hom-Precategoryᵉ = id-hom-Precategoryᵉ Cᵉ
  pr1ᵉ (pr2ᵉ is-iso-id-hom-Precategoryᵉ) =
    left-unit-law-comp-hom-Precategoryᵉ Cᵉ (id-hom-Precategoryᵉ Cᵉ)
  pr2ᵉ (pr2ᵉ is-iso-id-hom-Precategoryᵉ) =
    left-unit-law-comp-hom-Precategoryᵉ Cᵉ (id-hom-Precategoryᵉ Cᵉ)

  id-iso-Precategoryᵉ : iso-Precategoryᵉ Cᵉ xᵉ xᵉ
  pr1ᵉ id-iso-Precategoryᵉ = id-hom-Precategoryᵉ Cᵉ
  pr2ᵉ id-iso-Precategoryᵉ = is-iso-id-hom-Precategoryᵉ
```

### Equalities induce isomorphisms

Anᵉ equalityᵉ betweenᵉ objectsᵉ `xᵉ yᵉ : A`ᵉ givesᵉ riseᵉ to anᵉ isomorphismᵉ betweenᵉ them.ᵉ
Thisᵉ isᵉ because,ᵉ byᵉ theᵉ J-rule,ᵉ itᵉ isᵉ enoughᵉ to constructᵉ anᵉ isomorphismᵉ givenᵉ
`reflᵉ : xᵉ ＝ᵉ x`,ᵉ fromᵉ `x`ᵉ to itself.ᵉ Weᵉ takeᵉ theᵉ identityᵉ morphismᵉ asᵉ suchᵉ anᵉ
isomorphism.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  iso-eq-Precategoryᵉ :
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) → xᵉ ＝ᵉ yᵉ → iso-Precategoryᵉ Cᵉ xᵉ yᵉ
  pr1ᵉ (iso-eq-Precategoryᵉ xᵉ yᵉ pᵉ) = hom-eq-Precategoryᵉ Cᵉ xᵉ yᵉ pᵉ
  pr2ᵉ (iso-eq-Precategoryᵉ xᵉ .xᵉ reflᵉ) = is-iso-id-hom-Precategoryᵉ Cᵉ

  compute-hom-iso-eq-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    (pᵉ : xᵉ ＝ᵉ yᵉ) →
    hom-eq-Precategoryᵉ Cᵉ xᵉ yᵉ pᵉ ＝ᵉ
    hom-iso-Precategoryᵉ Cᵉ (iso-eq-Precategoryᵉ xᵉ yᵉ pᵉ)
  compute-hom-iso-eq-Precategoryᵉ pᵉ = reflᵉ
```

## Properties

### Being an isomorphism is a proposition

Letᵉ `fᵉ : homᵉ xᵉ y`ᵉ andᵉ supposeᵉ `gᵉ g'ᵉ : homᵉ yᵉ x`ᵉ areᵉ bothᵉ two-sidedᵉ inversesᵉ to
`f`.ᵉ Itᵉ isᵉ enoughᵉ to showᵉ thatᵉ `gᵉ = g'`ᵉ sinceᵉ theᵉ equalitiesᵉ areᵉ
[propositions](foundation-core.propositions.mdᵉ) (sinceᵉ theᵉ hom-typesᵉ areᵉ sets).ᵉ
Butᵉ weᵉ haveᵉ theᵉ followingᵉ chainᵉ ofᵉ equalitiesᵉ:
`gᵉ = gᵉ ∘ᵉ id_yᵉ = gᵉ ∘ᵉ (fᵉ ∘ᵉ g'ᵉ) = (gᵉ ∘ᵉ fᵉ) ∘ᵉ g'ᵉ = id_xᵉ ∘ᵉ g'ᵉ = g'`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  where

  all-elements-equal-is-iso-Precategoryᵉ :
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ)
    (Hᵉ Kᵉ : is-iso-Precategoryᵉ Cᵉ fᵉ) → Hᵉ ＝ᵉ Kᵉ
  all-elements-equal-is-iso-Precategoryᵉ fᵉ
    (gᵉ ,ᵉ pᵉ ,ᵉ qᵉ) (g'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) =
    eq-type-subtypeᵉ
      ( λ gᵉ →
        product-Propᵉ
          ( Id-Propᵉ
            ( hom-set-Precategoryᵉ Cᵉ yᵉ yᵉ)
            ( comp-hom-Precategoryᵉ Cᵉ fᵉ gᵉ)
            ( id-hom-Precategoryᵉ Cᵉ))
          ( Id-Propᵉ
            ( hom-set-Precategoryᵉ Cᵉ xᵉ xᵉ)
            ( comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ)
            ( id-hom-Precategoryᵉ Cᵉ)))
      ( ( invᵉ (right-unit-law-comp-hom-Precategoryᵉ Cᵉ gᵉ)) ∙ᵉ
        ( apᵉ ( comp-hom-Precategoryᵉ Cᵉ gᵉ) (invᵉ p'ᵉ)) ∙ᵉ
        ( invᵉ (associative-comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ g'ᵉ)) ∙ᵉ
        ( apᵉ ( comp-hom-Precategory'ᵉ Cᵉ g'ᵉ) qᵉ) ∙ᵉ
        ( left-unit-law-comp-hom-Precategoryᵉ Cᵉ g'ᵉ))

  is-prop-is-iso-Precategoryᵉ :
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    is-propᵉ (is-iso-Precategoryᵉ Cᵉ fᵉ)
  is-prop-is-iso-Precategoryᵉ fᵉ =
    is-prop-all-elements-equalᵉ
      ( all-elements-equal-is-iso-Precategoryᵉ fᵉ)

  is-iso-prop-Precategoryᵉ :
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) → Propᵉ l2ᵉ
  pr1ᵉ (is-iso-prop-Precategoryᵉ fᵉ) = is-iso-Precategoryᵉ Cᵉ fᵉ
  pr2ᵉ (is-iso-prop-Precategoryᵉ fᵉ) = is-prop-is-iso-Precategoryᵉ fᵉ
```

### Equality of isomorphism is equality of their underlying morphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  where

  eq-iso-eq-hom-Precategoryᵉ :
    (fᵉ gᵉ : iso-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    hom-iso-Precategoryᵉ Cᵉ fᵉ ＝ᵉ hom-iso-Precategoryᵉ Cᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-iso-eq-hom-Precategoryᵉ fᵉ gᵉ =
    eq-type-subtypeᵉ (is-iso-prop-Precategoryᵉ Cᵉ)
```

### The type of isomorphisms form a set

Theᵉ typeᵉ ofᵉ isomorphismsᵉ betweenᵉ objectsᵉ `xᵉ yᵉ : A`ᵉ isᵉ aᵉ
[subtype](foundation-core.subtypes.mdᵉ) ofᵉ theᵉ [set](foundation-core.sets.mdᵉ)
`homᵉ xᵉ y`ᵉ sinceᵉ beingᵉ anᵉ isomorphismᵉ isᵉ aᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  where

  is-set-iso-Precategoryᵉ : is-setᵉ (iso-Precategoryᵉ Cᵉ xᵉ yᵉ)
  is-set-iso-Precategoryᵉ =
    is-set-type-subtypeᵉ
      ( is-iso-prop-Precategoryᵉ Cᵉ)
      ( is-set-hom-Precategoryᵉ Cᵉ xᵉ yᵉ)

  iso-set-Precategoryᵉ : Setᵉ l2ᵉ
  pr1ᵉ iso-set-Precategoryᵉ = iso-Precategoryᵉ Cᵉ xᵉ yᵉ
  pr2ᵉ iso-set-Precategoryᵉ = is-set-iso-Precategoryᵉ
```

### Isomorphisms are closed under composition

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ}
  {gᵉ : hom-Precategoryᵉ Cᵉ yᵉ zᵉ}
  {fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ}
  where

  hom-comp-is-iso-Precategoryᵉ :
    is-iso-Precategoryᵉ Cᵉ gᵉ →
    is-iso-Precategoryᵉ Cᵉ fᵉ →
    hom-Precategoryᵉ Cᵉ zᵉ xᵉ
  hom-comp-is-iso-Precategoryᵉ qᵉ pᵉ =
    comp-hom-Precategoryᵉ Cᵉ
      ( hom-inv-is-iso-Precategoryᵉ Cᵉ pᵉ)
      ( hom-inv-is-iso-Precategoryᵉ Cᵉ qᵉ)

  is-section-comp-is-iso-Precategoryᵉ :
    (qᵉ : is-iso-Precategoryᵉ Cᵉ gᵉ)
    (pᵉ : is-iso-Precategoryᵉ Cᵉ fᵉ) →
    comp-hom-Precategoryᵉ Cᵉ
      ( comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ)
      ( hom-comp-is-iso-Precategoryᵉ qᵉ pᵉ) ＝ᵉ
    id-hom-Precategoryᵉ Cᵉ
  is-section-comp-is-iso-Precategoryᵉ qᵉ pᵉ =
    ( associative-comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ _) ∙ᵉ
    ( apᵉ
      ( comp-hom-Precategoryᵉ Cᵉ gᵉ)
      ( ( invᵉ
          ( associative-comp-hom-Precategoryᵉ Cᵉ fᵉ
            ( hom-inv-is-iso-Precategoryᵉ Cᵉ pᵉ)
            ( hom-inv-is-iso-Precategoryᵉ Cᵉ qᵉ))) ∙ᵉ
        ( apᵉ
          ( λ hᵉ →
            comp-hom-Precategoryᵉ Cᵉ hᵉ (hom-inv-is-iso-Precategoryᵉ Cᵉ qᵉ))
          ( is-section-hom-inv-is-iso-Precategoryᵉ Cᵉ pᵉ) ∙ᵉ
          ( left-unit-law-comp-hom-Precategoryᵉ Cᵉ
            ( hom-inv-is-iso-Precategoryᵉ Cᵉ qᵉ))))) ∙ᵉ
    ( is-section-hom-inv-is-iso-Precategoryᵉ Cᵉ qᵉ)

  is-retraction-comp-is-iso-Precategoryᵉ :
    (qᵉ : is-iso-Precategoryᵉ Cᵉ gᵉ)
    (pᵉ : is-iso-Precategoryᵉ Cᵉ fᵉ) →
    ( comp-hom-Precategoryᵉ Cᵉ
      ( hom-comp-is-iso-Precategoryᵉ qᵉ pᵉ)
      ( comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ)) ＝ᵉ
    ( id-hom-Precategoryᵉ Cᵉ)
  is-retraction-comp-is-iso-Precategoryᵉ qᵉ pᵉ =
    ( associative-comp-hom-Precategoryᵉ Cᵉ
      ( hom-inv-is-iso-Precategoryᵉ Cᵉ pᵉ)
      ( hom-inv-is-iso-Precategoryᵉ Cᵉ qᵉ)
      ( comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ)) ∙ᵉ
    ( apᵉ
      ( comp-hom-Precategoryᵉ
        ( Cᵉ)
        ( hom-inv-is-iso-Precategoryᵉ Cᵉ pᵉ))
      ( ( invᵉ
          ( associative-comp-hom-Precategoryᵉ Cᵉ
            ( hom-inv-is-iso-Precategoryᵉ Cᵉ qᵉ)
            ( gᵉ)
            ( fᵉ))) ∙ᵉ
        ( apᵉ
            ( λ hᵉ → comp-hom-Precategoryᵉ Cᵉ hᵉ fᵉ)
            ( is-retraction-hom-inv-is-iso-Precategoryᵉ Cᵉ qᵉ)) ∙ᵉ
        ( left-unit-law-comp-hom-Precategoryᵉ Cᵉ fᵉ))) ∙ᵉ
    ( is-retraction-hom-inv-is-iso-Precategoryᵉ Cᵉ pᵉ)

  is-iso-comp-is-iso-Precategoryᵉ :
    is-iso-Precategoryᵉ Cᵉ gᵉ → is-iso-Precategoryᵉ Cᵉ fᵉ →
    is-iso-Precategoryᵉ Cᵉ (comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ)
  pr1ᵉ (is-iso-comp-is-iso-Precategoryᵉ qᵉ pᵉ) =
    hom-comp-is-iso-Precategoryᵉ qᵉ pᵉ
  pr1ᵉ (pr2ᵉ (is-iso-comp-is-iso-Precategoryᵉ qᵉ pᵉ)) =
    is-section-comp-is-iso-Precategoryᵉ qᵉ pᵉ
  pr2ᵉ (pr2ᵉ (is-iso-comp-is-iso-Precategoryᵉ qᵉ pᵉ)) =
    is-retraction-comp-is-iso-Precategoryᵉ qᵉ pᵉ
```

### The composition operation on isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ}
  (gᵉ : iso-Precategoryᵉ Cᵉ yᵉ zᵉ)
  (fᵉ : iso-Precategoryᵉ Cᵉ xᵉ yᵉ)
  where

  hom-comp-iso-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ xᵉ zᵉ
  hom-comp-iso-Precategoryᵉ =
    comp-hom-Precategoryᵉ Cᵉ
      ( hom-iso-Precategoryᵉ Cᵉ gᵉ)
      ( hom-iso-Precategoryᵉ Cᵉ fᵉ)

  is-iso-comp-iso-Precategoryᵉ :
    is-iso-Precategoryᵉ Cᵉ hom-comp-iso-Precategoryᵉ
  is-iso-comp-iso-Precategoryᵉ =
    is-iso-comp-is-iso-Precategoryᵉ Cᵉ
      ( is-iso-iso-Precategoryᵉ Cᵉ gᵉ)
      ( is-iso-iso-Precategoryᵉ Cᵉ fᵉ)

  comp-iso-Precategoryᵉ : iso-Precategoryᵉ Cᵉ xᵉ zᵉ
  pr1ᵉ comp-iso-Precategoryᵉ = hom-comp-iso-Precategoryᵉ
  pr2ᵉ comp-iso-Precategoryᵉ = is-iso-comp-iso-Precategoryᵉ

  hom-inv-comp-iso-Precategoryᵉ : hom-Precategoryᵉ Cᵉ zᵉ xᵉ
  hom-inv-comp-iso-Precategoryᵉ =
    hom-inv-iso-Precategoryᵉ Cᵉ comp-iso-Precategoryᵉ

  is-section-inv-comp-iso-Precategoryᵉ :
    ( comp-hom-Precategoryᵉ Cᵉ
      ( hom-comp-iso-Precategoryᵉ)
      ( hom-inv-comp-iso-Precategoryᵉ)) ＝ᵉ
    ( id-hom-Precategoryᵉ Cᵉ)
  is-section-inv-comp-iso-Precategoryᵉ =
    is-section-hom-inv-iso-Precategoryᵉ Cᵉ comp-iso-Precategoryᵉ

  is-retraction-inv-comp-iso-Precategoryᵉ :
    ( comp-hom-Precategoryᵉ Cᵉ
      ( hom-inv-comp-iso-Precategoryᵉ)
      ( hom-comp-iso-Precategoryᵉ)) ＝ᵉ
    ( id-hom-Precategoryᵉ Cᵉ)
  is-retraction-inv-comp-iso-Precategoryᵉ =
    is-retraction-hom-inv-iso-Precategoryᵉ Cᵉ comp-iso-Precategoryᵉ
```

### Inverses of isomorphisms are isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  {fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ}
  where

  is-iso-inv-is-iso-Precategoryᵉ :
    (pᵉ : is-iso-Precategoryᵉ Cᵉ fᵉ) →
    is-iso-Precategoryᵉ Cᵉ (hom-inv-iso-Precategoryᵉ Cᵉ (fᵉ ,ᵉ pᵉ))
  pr1ᵉ (is-iso-inv-is-iso-Precategoryᵉ pᵉ) = fᵉ
  pr1ᵉ (pr2ᵉ (is-iso-inv-is-iso-Precategoryᵉ pᵉ)) =
    is-retraction-hom-inv-is-iso-Precategoryᵉ Cᵉ pᵉ
  pr2ᵉ (pr2ᵉ (is-iso-inv-is-iso-Precategoryᵉ pᵉ)) =
    is-section-hom-inv-is-iso-Precategoryᵉ Cᵉ pᵉ
```

### Inverses of isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  where

  inv-iso-Precategoryᵉ :
    iso-Precategoryᵉ Cᵉ xᵉ yᵉ → iso-Precategoryᵉ Cᵉ yᵉ xᵉ
  pr1ᵉ (inv-iso-Precategoryᵉ fᵉ) = hom-inv-iso-Precategoryᵉ Cᵉ fᵉ
  pr2ᵉ (inv-iso-Precategoryᵉ fᵉ) =
    is-iso-inv-is-iso-Precategoryᵉ Cᵉ (is-iso-iso-Precategoryᵉ Cᵉ fᵉ)

  is-iso-inv-iso-Precategoryᵉ :
    (fᵉ : iso-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    is-iso-Precategoryᵉ Cᵉ (hom-inv-iso-Precategoryᵉ Cᵉ fᵉ)
  is-iso-inv-iso-Precategoryᵉ fᵉ =
    is-iso-iso-Precategoryᵉ Cᵉ (inv-iso-Precategoryᵉ fᵉ)
```

### Groupoid laws of isomorphisms in precategories

#### Composition of isomorphisms satisfies the unit laws

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  (fᵉ : iso-Precategoryᵉ Cᵉ xᵉ yᵉ)
  where

  left-unit-law-comp-iso-Precategoryᵉ :
    comp-iso-Precategoryᵉ Cᵉ (id-iso-Precategoryᵉ Cᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-iso-Precategoryᵉ =
    eq-iso-eq-hom-Precategoryᵉ Cᵉ
      ( comp-iso-Precategoryᵉ Cᵉ (id-iso-Precategoryᵉ Cᵉ) fᵉ)
      ( fᵉ)
      ( left-unit-law-comp-hom-Precategoryᵉ Cᵉ
        ( hom-iso-Precategoryᵉ Cᵉ fᵉ))

  right-unit-law-comp-iso-Precategoryᵉ :
    comp-iso-Precategoryᵉ Cᵉ fᵉ (id-iso-Precategoryᵉ Cᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-iso-Precategoryᵉ =
    eq-iso-eq-hom-Precategoryᵉ Cᵉ
      ( comp-iso-Precategoryᵉ Cᵉ fᵉ (id-iso-Precategoryᵉ Cᵉ))
      ( fᵉ)
      ( right-unit-law-comp-hom-Precategoryᵉ Cᵉ
        ( hom-iso-Precategoryᵉ Cᵉ fᵉ))
```

#### Composition of isomorphisms is associative

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ zᵉ wᵉ : obj-Precategoryᵉ Cᵉ}
  (hᵉ : iso-Precategoryᵉ Cᵉ zᵉ wᵉ)
  (gᵉ : iso-Precategoryᵉ Cᵉ yᵉ zᵉ)
  (fᵉ : iso-Precategoryᵉ Cᵉ xᵉ yᵉ)
  where

  associative-comp-iso-Precategoryᵉ :
    ( comp-iso-Precategoryᵉ Cᵉ (comp-iso-Precategoryᵉ Cᵉ hᵉ gᵉ) fᵉ) ＝ᵉ
    ( comp-iso-Precategoryᵉ Cᵉ hᵉ (comp-iso-Precategoryᵉ Cᵉ gᵉ fᵉ))
  associative-comp-iso-Precategoryᵉ =
    eq-iso-eq-hom-Precategoryᵉ Cᵉ
      ( comp-iso-Precategoryᵉ Cᵉ (comp-iso-Precategoryᵉ Cᵉ hᵉ gᵉ) fᵉ)
      ( comp-iso-Precategoryᵉ Cᵉ hᵉ (comp-iso-Precategoryᵉ Cᵉ gᵉ fᵉ))
      ( associative-comp-hom-Precategoryᵉ Cᵉ
        ( hom-iso-Precategoryᵉ Cᵉ hᵉ)
        ( hom-iso-Precategoryᵉ Cᵉ gᵉ)
        ( hom-iso-Precategoryᵉ Cᵉ fᵉ))
```

#### Composition of isomorphisms satisfies inverse laws

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  (fᵉ : iso-Precategoryᵉ Cᵉ xᵉ yᵉ)
  where

  left-inverse-law-comp-iso-Precategoryᵉ :
    ( comp-iso-Precategoryᵉ Cᵉ (inv-iso-Precategoryᵉ Cᵉ fᵉ) fᵉ) ＝ᵉ
    ( id-iso-Precategoryᵉ Cᵉ)
  left-inverse-law-comp-iso-Precategoryᵉ =
    eq-iso-eq-hom-Precategoryᵉ Cᵉ
      ( comp-iso-Precategoryᵉ Cᵉ (inv-iso-Precategoryᵉ Cᵉ fᵉ) fᵉ)
      ( id-iso-Precategoryᵉ Cᵉ)
      ( is-retraction-hom-inv-iso-Precategoryᵉ Cᵉ fᵉ)

  right-inverse-law-comp-iso-Precategoryᵉ :
    ( comp-iso-Precategoryᵉ Cᵉ fᵉ (inv-iso-Precategoryᵉ Cᵉ fᵉ)) ＝ᵉ
    ( id-iso-Precategoryᵉ Cᵉ)
  right-inverse-law-comp-iso-Precategoryᵉ =
    eq-iso-eq-hom-Precategoryᵉ Cᵉ
      ( comp-iso-Precategoryᵉ Cᵉ fᵉ (inv-iso-Precategoryᵉ Cᵉ fᵉ))
      ( id-iso-Precategoryᵉ Cᵉ)
      ( is-section-hom-inv-iso-Precategoryᵉ Cᵉ fᵉ)
```

### The inverse operation is a fibered involution on isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-fibered-involution-inv-iso-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    inv-iso-Precategoryᵉ Cᵉ {yᵉ} {xᵉ} ∘ᵉ inv-iso-Precategoryᵉ Cᵉ {xᵉ} {yᵉ} ~ᵉ idᵉ
  is-fibered-involution-inv-iso-Precategoryᵉ fᵉ = reflᵉ

  is-equiv-inv-iso-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} → is-equivᵉ (inv-iso-Precategoryᵉ Cᵉ {xᵉ} {yᵉ})
  is-equiv-inv-iso-Precategoryᵉ =
    is-equiv-is-invertibleᵉ
      ( inv-iso-Precategoryᵉ Cᵉ)
      ( is-fibered-involution-inv-iso-Precategoryᵉ)
      ( is-fibered-involution-inv-iso-Precategoryᵉ)

  equiv-inv-iso-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} → iso-Precategoryᵉ Cᵉ xᵉ yᵉ ≃ᵉ iso-Precategoryᵉ Cᵉ yᵉ xᵉ
  pr1ᵉ equiv-inv-iso-Precategoryᵉ = inv-iso-Precategoryᵉ Cᵉ
  pr2ᵉ equiv-inv-iso-Precategoryᵉ = is-equiv-inv-iso-Precategoryᵉ
```

### A morphism `f` is an isomorphism if and only if precomposition by `f` is an equivalence

**Proof:**ᵉ Ifᵉ `f`ᵉ isᵉ anᵉ isomorphismᵉ with inverseᵉ `f⁻¹`,ᵉ thenᵉ precomposingᵉ with
`f⁻¹`ᵉ isᵉ anᵉ inverseᵉ ofᵉ precomposingᵉ with `f`.ᵉ Theᵉ onlyᵉ interestingᵉ directionᵉ isᵉ
thereforeᵉ theᵉ converse.ᵉ

Supposeᵉ thatᵉ precomposingᵉ with `f`ᵉ isᵉ anᵉ equivalence,ᵉ forᵉ anyᵉ objectᵉ `z`.ᵉ Thenᵉ

```text
  -ᵉ ∘ᵉ fᵉ : homᵉ yᵉ xᵉ → homᵉ xᵉ xᵉ
```

isᵉ anᵉ equivalence.ᵉ Inᵉ particular,ᵉ thereᵉ isᵉ aᵉ uniqueᵉ morphismᵉ `gᵉ : yᵉ → x`ᵉ suchᵉ
thatᵉ `gᵉ ∘ᵉ fᵉ ＝ᵉ id`.ᵉ Thusᵉ weᵉ haveᵉ aᵉ retractionᵉ ofᵉ `f`.ᵉ Toᵉ seeᵉ thatᵉ `g`ᵉ isᵉ alsoᵉ aᵉ
section,ᵉ noteᵉ thatᵉ theᵉ mapᵉ

```text
  -ᵉ ∘ᵉ fᵉ : homᵉ yᵉ yᵉ → homᵉ xᵉ yᵉ
```

isᵉ anᵉ equivalence.ᵉ Inᵉ particular,ᵉ itᵉ isᵉ injective.ᵉ Thereforeᵉ itᵉ sufficesᵉ to showᵉ
thatᵉ `(fᵉ ∘ᵉ gᵉ) ∘ᵉ fᵉ ＝ᵉ idᵉ ∘ᵉ f`.ᵉ Toᵉ seeᵉ this,ᵉ weᵉ calculateᵉ

```text
  (fᵉ ∘ᵉ gᵉ) ∘ᵉ fᵉ ＝ᵉ fᵉ ∘ᵉ (gᵉ ∘ᵉ fᵉ) ＝ᵉ fᵉ ∘ᵉ idᵉ ＝ᵉ fᵉ ＝ᵉ idᵉ ∘ᵉ f.ᵉ
```

Thisᵉ completesᵉ theᵉ proof.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  {fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ}
  (Hᵉ : (zᵉ : obj-Precategoryᵉ Cᵉ) → is-equivᵉ (precomp-hom-Precategoryᵉ Cᵉ fᵉ zᵉ))
  where

  hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ : hom-Precategoryᵉ Cᵉ yᵉ xᵉ
  hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ =
    map-inv-is-equivᵉ (Hᵉ xᵉ) (id-hom-Precategoryᵉ Cᵉ)

  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ :
    ( comp-hom-Precategoryᵉ Cᵉ
      ( hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ)
      ( fᵉ)) ＝ᵉ
    ( id-hom-Precategoryᵉ Cᵉ)
  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ =
    is-section-map-inv-is-equivᵉ (Hᵉ xᵉ) (id-hom-Precategoryᵉ Cᵉ)

  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ :
    ( comp-hom-Precategoryᵉ Cᵉ
      ( fᵉ)
      ( hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ)) ＝ᵉ
    ( id-hom-Precategoryᵉ Cᵉ)
  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ =
    is-injective-is-equivᵉ
      ( Hᵉ yᵉ)
      ( ( associative-comp-hom-Precategoryᵉ Cᵉ
          ( fᵉ)
          ( hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ)
          ( fᵉ)) ∙ᵉ
        ( apᵉ
          ( comp-hom-Precategoryᵉ Cᵉ fᵉ)
          ( is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ)) ∙ᵉ
        ( right-unit-law-comp-hom-Precategoryᵉ Cᵉ fᵉ) ∙ᵉ
        ( invᵉ (left-unit-law-comp-hom-Precategoryᵉ Cᵉ fᵉ)))

  is-iso-is-equiv-precomp-hom-Precategoryᵉ : is-iso-Precategoryᵉ Cᵉ fᵉ
  pr1ᵉ is-iso-is-equiv-precomp-hom-Precategoryᵉ =
    hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ
  pr1ᵉ (pr2ᵉ is-iso-is-equiv-precomp-hom-Precategoryᵉ) =
    is-section-hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ
  pr2ᵉ (pr2ᵉ is-iso-is-equiv-precomp-hom-Precategoryᵉ) =
    is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ

module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  {fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ}
  (is-iso-fᵉ : is-iso-Precategoryᵉ Cᵉ fᵉ)
  (zᵉ : obj-Precategoryᵉ Cᵉ)
  where

  map-inv-precomp-hom-is-iso-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ xᵉ zᵉ → hom-Precategoryᵉ Cᵉ yᵉ zᵉ
  map-inv-precomp-hom-is-iso-Precategoryᵉ =
    precomp-hom-Precategoryᵉ Cᵉ (hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ) zᵉ

  is-section-map-inv-precomp-hom-is-iso-Precategoryᵉ :
    is-sectionᵉ
      ( precomp-hom-Precategoryᵉ Cᵉ fᵉ zᵉ)
      ( map-inv-precomp-hom-is-iso-Precategoryᵉ)
  is-section-map-inv-precomp-hom-is-iso-Precategoryᵉ gᵉ =
    ( associative-comp-hom-Precategoryᵉ Cᵉ
      ( gᵉ)
      ( hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ)
      ( fᵉ)) ∙ᵉ
    ( apᵉ
      ( comp-hom-Precategoryᵉ Cᵉ gᵉ)
      ( is-retraction-hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ)) ∙ᵉ
    ( right-unit-law-comp-hom-Precategoryᵉ Cᵉ gᵉ)

  is-retraction-map-inv-precomp-hom-is-iso-Precategoryᵉ :
    is-retractionᵉ
      ( precomp-hom-Precategoryᵉ Cᵉ fᵉ zᵉ)
      ( map-inv-precomp-hom-is-iso-Precategoryᵉ)
  is-retraction-map-inv-precomp-hom-is-iso-Precategoryᵉ gᵉ =
    ( associative-comp-hom-Precategoryᵉ Cᵉ
      ( gᵉ)
      ( fᵉ)
      ( hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ)) ∙ᵉ
    ( apᵉ
      ( comp-hom-Precategoryᵉ Cᵉ gᵉ)
      ( is-section-hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ)) ∙ᵉ
    ( right-unit-law-comp-hom-Precategoryᵉ Cᵉ gᵉ)

  is-equiv-precomp-hom-is-iso-Precategoryᵉ :
    is-equivᵉ (precomp-hom-Precategoryᵉ Cᵉ fᵉ zᵉ)
  is-equiv-precomp-hom-is-iso-Precategoryᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-precomp-hom-is-iso-Precategoryᵉ)
      ( is-section-map-inv-precomp-hom-is-iso-Precategoryᵉ)
      ( is-retraction-map-inv-precomp-hom-is-iso-Precategoryᵉ)

  equiv-precomp-hom-is-iso-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ yᵉ zᵉ ≃ᵉ hom-Precategoryᵉ Cᵉ xᵉ zᵉ
  pr1ᵉ equiv-precomp-hom-is-iso-Precategoryᵉ =
    precomp-hom-Precategoryᵉ Cᵉ fᵉ zᵉ
  pr2ᵉ equiv-precomp-hom-is-iso-Precategoryᵉ =
    is-equiv-precomp-hom-is-iso-Precategoryᵉ

module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  (fᵉ : iso-Precategoryᵉ Cᵉ xᵉ yᵉ)
  (zᵉ : obj-Precategoryᵉ Cᵉ)
  where

  is-equiv-precomp-hom-iso-Precategoryᵉ :
    is-equivᵉ (precomp-hom-Precategoryᵉ Cᵉ (hom-iso-Precategoryᵉ Cᵉ fᵉ) zᵉ)
  is-equiv-precomp-hom-iso-Precategoryᵉ =
    is-equiv-precomp-hom-is-iso-Precategoryᵉ Cᵉ (is-iso-iso-Precategoryᵉ Cᵉ fᵉ) zᵉ

  equiv-precomp-hom-iso-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ yᵉ zᵉ ≃ᵉ hom-Precategoryᵉ Cᵉ xᵉ zᵉ
  equiv-precomp-hom-iso-Precategoryᵉ =
    equiv-precomp-hom-is-iso-Precategoryᵉ Cᵉ (is-iso-iso-Precategoryᵉ Cᵉ fᵉ) zᵉ
```

### A morphism `f` is an isomorphism if and only if postcomposition by `f` is an equivalence

**Proof:**ᵉ Ifᵉ `f`ᵉ isᵉ anᵉ isomorphismᵉ with inverseᵉ `f⁻¹`,ᵉ thenᵉ postcomposingᵉ with
`f⁻¹`ᵉ isᵉ anᵉ inverseᵉ ofᵉ postcomposingᵉ with `f`.ᵉ Theᵉ onlyᵉ interestingᵉ directionᵉ isᵉ
thereforeᵉ theᵉ converse.ᵉ

Supposeᵉ thatᵉ postcomposingᵉ with `f`ᵉ isᵉ anᵉ equivalence,ᵉ forᵉ anyᵉ objectᵉ `z`.ᵉ Thenᵉ

```text
  fᵉ ∘ᵉ -ᵉ : homᵉ yᵉ xᵉ → homᵉ yᵉ yᵉ
```

isᵉ anᵉ equivalence.ᵉ Inᵉ particular,ᵉ thereᵉ isᵉ aᵉ uniqueᵉ morphismᵉ `gᵉ : yᵉ → x`ᵉ suchᵉ
thatᵉ `fᵉ ∘ᵉ gᵉ ＝ᵉ id`.ᵉ Thusᵉ weᵉ haveᵉ aᵉ sectionᵉ ofᵉ `f`.ᵉ Toᵉ seeᵉ thatᵉ `g`ᵉ isᵉ alsoᵉ aᵉ
retraction,ᵉ noteᵉ thatᵉ theᵉ mapᵉ

```text
  fᵉ ∘ᵉ -ᵉ : homᵉ xᵉ xᵉ → homᵉ xᵉ yᵉ
```

isᵉ anᵉ equivalence.ᵉ Inᵉ particular,ᵉ itᵉ isᵉ injective.ᵉ Thereforeᵉ itᵉ sufficesᵉ to showᵉ
thatᵉ `fᵉ ∘ᵉ (gᵉ ∘ᵉ fᵉ) ＝ᵉ fᵉ ∘ᵉ id`.ᵉ Toᵉ seeᵉ this,ᵉ weᵉ calculateᵉ

```text
  fᵉ ∘ᵉ (gᵉ ∘ᵉ fᵉ) ＝ᵉ (fᵉ ∘ᵉ gᵉ) ∘ᵉ fᵉ ＝ᵉ idᵉ ∘ᵉ fᵉ ＝ᵉ fᵉ ＝ᵉ fᵉ ∘ᵉ id.ᵉ
```

Thisᵉ completesᵉ theᵉ proof.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  {fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ}
  (Hᵉ : (zᵉ : obj-Precategoryᵉ Cᵉ) → is-equivᵉ (postcomp-hom-Precategoryᵉ Cᵉ fᵉ zᵉ))
  where

  hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ : hom-Precategoryᵉ Cᵉ yᵉ xᵉ
  hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ =
    map-inv-is-equivᵉ (Hᵉ yᵉ) (id-hom-Precategoryᵉ Cᵉ)

  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ :
    ( comp-hom-Precategoryᵉ Cᵉ
      ( fᵉ)
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ)) ＝ᵉ
    ( id-hom-Precategoryᵉ Cᵉ)
  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ =
    is-section-map-inv-is-equivᵉ (Hᵉ yᵉ) (id-hom-Precategoryᵉ Cᵉ)

  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ :
    comp-hom-Precategoryᵉ Cᵉ
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ)
      ( fᵉ) ＝ᵉ
    ( id-hom-Precategoryᵉ Cᵉ)
  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ =
    is-injective-is-equivᵉ
      ( Hᵉ xᵉ)
      ( ( invᵉ
          ( associative-comp-hom-Precategoryᵉ Cᵉ
            ( fᵉ)
            ( hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ)
            ( fᵉ))) ∙ᵉ
        ( apᵉ
          ( comp-hom-Precategory'ᵉ Cᵉ fᵉ)
          ( is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ)) ∙ᵉ
        ( left-unit-law-comp-hom-Precategoryᵉ Cᵉ fᵉ) ∙ᵉ
        ( invᵉ (right-unit-law-comp-hom-Precategoryᵉ Cᵉ fᵉ)))

  is-iso-is-equiv-postcomp-hom-Precategoryᵉ : is-iso-Precategoryᵉ Cᵉ fᵉ
  pr1ᵉ is-iso-is-equiv-postcomp-hom-Precategoryᵉ =
    hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ
  pr1ᵉ (pr2ᵉ is-iso-is-equiv-postcomp-hom-Precategoryᵉ) =
    is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ
  pr2ᵉ (pr2ᵉ is-iso-is-equiv-postcomp-hom-Precategoryᵉ) =
    is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ

module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  {fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ}
  (is-iso-fᵉ : is-iso-Precategoryᵉ Cᵉ fᵉ)
  (zᵉ : obj-Precategoryᵉ Cᵉ)
  where

  map-inv-postcomp-hom-is-iso-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ zᵉ yᵉ → hom-Precategoryᵉ Cᵉ zᵉ xᵉ
  map-inv-postcomp-hom-is-iso-Precategoryᵉ =
    postcomp-hom-Precategoryᵉ Cᵉ (hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ) zᵉ

  is-section-map-inv-postcomp-hom-is-iso-Precategoryᵉ :
    is-sectionᵉ
      ( postcomp-hom-Precategoryᵉ Cᵉ fᵉ zᵉ)
      ( map-inv-postcomp-hom-is-iso-Precategoryᵉ)
  is-section-map-inv-postcomp-hom-is-iso-Precategoryᵉ gᵉ =
    ( invᵉ
      ( associative-comp-hom-Precategoryᵉ Cᵉ
        ( fᵉ)
        ( hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ)
        ( gᵉ))) ∙ᵉ
    ( apᵉ
      ( comp-hom-Precategory'ᵉ Cᵉ gᵉ)
      ( is-section-hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ)) ∙ᵉ
    ( left-unit-law-comp-hom-Precategoryᵉ Cᵉ gᵉ)

  is-retraction-map-inv-postcomp-hom-is-iso-Precategoryᵉ :
    is-retractionᵉ
      ( postcomp-hom-Precategoryᵉ Cᵉ fᵉ zᵉ)
      ( map-inv-postcomp-hom-is-iso-Precategoryᵉ)
  is-retraction-map-inv-postcomp-hom-is-iso-Precategoryᵉ gᵉ =
    ( invᵉ
      ( associative-comp-hom-Precategoryᵉ Cᵉ
        ( hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ)
        ( fᵉ)
        ( gᵉ))) ∙ᵉ
    ( apᵉ
      ( comp-hom-Precategory'ᵉ Cᵉ gᵉ)
      ( is-retraction-hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ)) ∙ᵉ
    ( left-unit-law-comp-hom-Precategoryᵉ Cᵉ gᵉ)

  is-equiv-postcomp-hom-is-iso-Precategoryᵉ :
    is-equivᵉ (postcomp-hom-Precategoryᵉ Cᵉ fᵉ zᵉ)
  is-equiv-postcomp-hom-is-iso-Precategoryᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-postcomp-hom-is-iso-Precategoryᵉ)
      ( is-section-map-inv-postcomp-hom-is-iso-Precategoryᵉ)
      ( is-retraction-map-inv-postcomp-hom-is-iso-Precategoryᵉ)

  equiv-postcomp-hom-is-iso-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ zᵉ xᵉ ≃ᵉ hom-Precategoryᵉ Cᵉ zᵉ yᵉ
  pr1ᵉ equiv-postcomp-hom-is-iso-Precategoryᵉ =
    postcomp-hom-Precategoryᵉ Cᵉ fᵉ zᵉ
  pr2ᵉ equiv-postcomp-hom-is-iso-Precategoryᵉ =
    is-equiv-postcomp-hom-is-iso-Precategoryᵉ

module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  (fᵉ : iso-Precategoryᵉ Cᵉ xᵉ yᵉ)
  (zᵉ : obj-Precategoryᵉ Cᵉ)
  where

  is-equiv-postcomp-hom-iso-Precategoryᵉ :
    is-equivᵉ (postcomp-hom-Precategoryᵉ Cᵉ (hom-iso-Precategoryᵉ Cᵉ fᵉ) zᵉ)
  is-equiv-postcomp-hom-iso-Precategoryᵉ =
    is-equiv-postcomp-hom-is-iso-Precategoryᵉ Cᵉ (is-iso-iso-Precategoryᵉ Cᵉ fᵉ) zᵉ

  equiv-postcomp-hom-iso-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ zᵉ xᵉ ≃ᵉ hom-Precategoryᵉ Cᵉ zᵉ yᵉ
  equiv-postcomp-hom-iso-Precategoryᵉ =
    equiv-postcomp-hom-is-iso-Precategoryᵉ Cᵉ (is-iso-iso-Precategoryᵉ Cᵉ fᵉ) zᵉ
```

### When `hom x y` is a proposition, The type of isomorphisms from `x` to `y` is a proposition

Theᵉ typeᵉ ofᵉ isomorphismsᵉ betweenᵉ objectsᵉ `xᵉ yᵉ : A`ᵉ isᵉ aᵉ subtypeᵉ ofᵉ `homᵉ xᵉ y`,ᵉ soᵉ
whenᵉ thisᵉ typeᵉ isᵉ aᵉ proposition,ᵉ thenᵉ theᵉ typeᵉ ofᵉ isomorphismsᵉ fromᵉ `x`ᵉ to `y`ᵉ
formᵉ aᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  where

  is-prop-iso-is-prop-hom-Precategoryᵉ :
    is-propᵉ (hom-Precategoryᵉ Cᵉ xᵉ yᵉ) → is-propᵉ (iso-Precategoryᵉ Cᵉ xᵉ yᵉ)
  is-prop-iso-is-prop-hom-Precategoryᵉ =
    is-prop-type-subtypeᵉ (is-iso-prop-Precategoryᵉ Cᵉ)

  iso-prop-is-prop-hom-Precategoryᵉ :
    is-propᵉ (hom-Precategoryᵉ Cᵉ xᵉ yᵉ) → Propᵉ l2ᵉ
  pr1ᵉ (iso-prop-is-prop-hom-Precategoryᵉ is-prop-hom-C-x-yᵉ) =
    iso-Precategoryᵉ Cᵉ xᵉ yᵉ
  pr2ᵉ (iso-prop-is-prop-hom-Precategoryᵉ is-prop-hom-C-x-yᵉ) =
    is-prop-iso-is-prop-hom-Precategoryᵉ is-prop-hom-C-x-yᵉ
```

### When `hom x y` and `hom y x` are propositions, it suffices to provide a morphism in each direction to construct an isomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  where

  is-iso-is-prop-hom-Precategory'ᵉ :
    is-propᵉ (hom-Precategoryᵉ Cᵉ xᵉ xᵉ) →
    is-propᵉ (hom-Precategoryᵉ Cᵉ yᵉ yᵉ) →
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    hom-Precategoryᵉ Cᵉ yᵉ xᵉ →
    is-iso-Precategoryᵉ Cᵉ fᵉ
  pr1ᵉ (is-iso-is-prop-hom-Precategory'ᵉ _ _ fᵉ gᵉ) = gᵉ
  pr1ᵉ (pr2ᵉ (is-iso-is-prop-hom-Precategory'ᵉ _ is-prop-hom-C-y-yᵉ fᵉ gᵉ)) =
    eq-is-propᵉ is-prop-hom-C-y-yᵉ
  pr2ᵉ (pr2ᵉ (is-iso-is-prop-hom-Precategory'ᵉ is-prop-hom-C-x-xᵉ _ fᵉ gᵉ)) =
    eq-is-propᵉ is-prop-hom-C-x-xᵉ

  iso-is-prop-hom-Precategory'ᵉ :
    is-propᵉ (hom-Precategoryᵉ Cᵉ xᵉ xᵉ) →
    is-propᵉ (hom-Precategoryᵉ Cᵉ yᵉ yᵉ) →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Cᵉ yᵉ xᵉ →
    iso-Precategoryᵉ Cᵉ xᵉ yᵉ
  pr1ᵉ (iso-is-prop-hom-Precategory'ᵉ _ _ fᵉ gᵉ) = fᵉ
  pr2ᵉ (iso-is-prop-hom-Precategory'ᵉ is-prop-hom-C-x-xᵉ is-prop-hom-C-y-yᵉ fᵉ gᵉ) =
    is-iso-is-prop-hom-Precategory'ᵉ is-prop-hom-C-x-xᵉ is-prop-hom-C-y-yᵉ fᵉ gᵉ

  is-iso-is-prop-hom-Precategoryᵉ :
    ((x'ᵉ y'ᵉ : obj-Precategoryᵉ Cᵉ) → is-propᵉ (hom-Precategoryᵉ Cᵉ x'ᵉ y'ᵉ)) →
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) → hom-Precategoryᵉ Cᵉ yᵉ xᵉ →
    is-iso-Precategoryᵉ Cᵉ fᵉ
  is-iso-is-prop-hom-Precategoryᵉ is-prop-hom-Cᵉ =
    is-iso-is-prop-hom-Precategory'ᵉ (is-prop-hom-Cᵉ xᵉ xᵉ) (is-prop-hom-Cᵉ yᵉ yᵉ)

  iso-is-prop-hom-Precategoryᵉ :
    ((x'ᵉ y'ᵉ : obj-Precategoryᵉ Cᵉ) → is-propᵉ (hom-Precategoryᵉ Cᵉ x'ᵉ y'ᵉ)) →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Cᵉ yᵉ xᵉ →
    iso-Precategoryᵉ Cᵉ xᵉ yᵉ
  iso-is-prop-hom-Precategoryᵉ is-prop-hom-Cᵉ =
    iso-is-prop-hom-Precategory'ᵉ (is-prop-hom-Cᵉ xᵉ xᵉ) (is-prop-hom-Cᵉ yᵉ yᵉ)
```

### Functoriality of `iso-eq`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ}
  where

  preserves-concat-iso-eq-Precategoryᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    iso-eq-Precategoryᵉ Cᵉ xᵉ zᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ
    comp-iso-Precategoryᵉ Cᵉ
      ( iso-eq-Precategoryᵉ Cᵉ yᵉ zᵉ qᵉ)
      ( iso-eq-Precategoryᵉ Cᵉ xᵉ yᵉ pᵉ)
  preserves-concat-iso-eq-Precategoryᵉ reflᵉ qᵉ =
    invᵉ (right-unit-law-comp-iso-Precategoryᵉ Cᵉ (iso-eq-Precategoryᵉ Cᵉ yᵉ zᵉ qᵉ))
```