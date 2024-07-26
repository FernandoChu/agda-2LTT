# Isomorphisms in large precategories

```agda
module category-theory.isomorphisms-in-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.large-precategoriesᵉ

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

Anᵉ **isomorphism**ᵉ in aᵉ
[largeᵉ precategory](category-theory.large-precategories.mdᵉ) `C`ᵉ isᵉ aᵉ morphismᵉ
`fᵉ : Xᵉ → Y`ᵉ in `C`ᵉ forᵉ whichᵉ thereᵉ existsᵉ aᵉ morphismᵉ `gᵉ : Yᵉ → X`ᵉ suchᵉ thatᵉ
`fᵉ ∘ᵉ gᵉ ＝ᵉ id`ᵉ andᵉ `gᵉ ∘ᵉ fᵉ ＝ᵉ id`.ᵉ

## Definitions

### The predicate of being an isomorphism

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  (fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  is-iso-Large-Precategoryᵉ : UUᵉ (βᵉ l1ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l2ᵉ)
  is-iso-Large-Precategoryᵉ =
    Σᵉ ( hom-Large-Precategoryᵉ Cᵉ Yᵉ Xᵉ)
      ( λ gᵉ →
        ( comp-hom-Large-Precategoryᵉ Cᵉ fᵉ gᵉ ＝ᵉ id-hom-Large-Precategoryᵉ Cᵉ) ×ᵉ
        ( comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ ＝ᵉ id-hom-Large-Precategoryᵉ Cᵉ))

  hom-inv-is-iso-Large-Precategoryᵉ :
    is-iso-Large-Precategoryᵉ → hom-Large-Precategoryᵉ Cᵉ Yᵉ Xᵉ
  hom-inv-is-iso-Large-Precategoryᵉ = pr1ᵉ

  is-section-hom-inv-is-iso-Large-Precategoryᵉ :
    (Hᵉ : is-iso-Large-Precategoryᵉ) →
    comp-hom-Large-Precategoryᵉ Cᵉ fᵉ (hom-inv-is-iso-Large-Precategoryᵉ Hᵉ) ＝ᵉ
    id-hom-Large-Precategoryᵉ Cᵉ
  is-section-hom-inv-is-iso-Large-Precategoryᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  is-retraction-hom-inv-is-iso-Large-Precategoryᵉ :
    (Hᵉ : is-iso-Large-Precategoryᵉ) →
    comp-hom-Large-Precategoryᵉ Cᵉ (hom-inv-is-iso-Large-Precategoryᵉ Hᵉ) fᵉ ＝ᵉ
    id-hom-Large-Precategoryᵉ Cᵉ
  is-retraction-hom-inv-is-iso-Large-Precategoryᵉ = pr2ᵉ ∘ᵉ pr2ᵉ
```

### Isomorphisms in a large precategory

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) (Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ)
  where

  iso-Large-Precategoryᵉ : UUᵉ (βᵉ l1ᵉ l1ᵉ ⊔ βᵉ l1ᵉ l2ᵉ ⊔ βᵉ l2ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l2ᵉ)
  iso-Large-Precategoryᵉ =
    Σᵉ (hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ) (is-iso-Large-Precategoryᵉ Cᵉ)

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  (fᵉ : iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  hom-iso-Large-Precategoryᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ
  hom-iso-Large-Precategoryᵉ = pr1ᵉ fᵉ

  is-iso-iso-Large-Precategoryᵉ :
    is-iso-Large-Precategoryᵉ Cᵉ hom-iso-Large-Precategoryᵉ
  is-iso-iso-Large-Precategoryᵉ = pr2ᵉ fᵉ

  hom-inv-iso-Large-Precategoryᵉ : hom-Large-Precategoryᵉ Cᵉ Yᵉ Xᵉ
  hom-inv-iso-Large-Precategoryᵉ = pr1ᵉ (pr2ᵉ fᵉ)

  is-section-hom-inv-iso-Large-Precategoryᵉ :
    ( comp-hom-Large-Precategoryᵉ Cᵉ
      ( hom-iso-Large-Precategoryᵉ)
      ( hom-inv-iso-Large-Precategoryᵉ)) ＝ᵉ
    ( id-hom-Large-Precategoryᵉ Cᵉ)
  is-section-hom-inv-iso-Large-Precategoryᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ fᵉ))

  is-retraction-hom-inv-iso-Large-Precategoryᵉ :
    ( comp-hom-Large-Precategoryᵉ Cᵉ
      ( hom-inv-iso-Large-Precategoryᵉ)
      ( hom-iso-Large-Precategoryᵉ)) ＝ᵉ
    ( id-hom-Large-Precategoryᵉ Cᵉ)
  is-retraction-hom-inv-iso-Large-Precategoryᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ fᵉ))
```

## Examples

### The identity isomorphisms

Forᵉ anyᵉ objectᵉ `xᵉ : A`,ᵉ theᵉ identityᵉ morphismᵉ `id_xᵉ : homᵉ xᵉ x`ᵉ isᵉ anᵉ isomorphismᵉ
fromᵉ `x`ᵉ to `x`ᵉ sinceᵉ `id_xᵉ ∘ᵉ id_xᵉ = id_x`ᵉ (itᵉ isᵉ itsᵉ ownᵉ inverse).ᵉ

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ : Level} {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
  where

  is-iso-id-hom-Large-Precategoryᵉ :
    is-iso-Large-Precategoryᵉ Cᵉ (id-hom-Large-Precategoryᵉ Cᵉ {Xᵉ = Xᵉ})
  pr1ᵉ is-iso-id-hom-Large-Precategoryᵉ = id-hom-Large-Precategoryᵉ Cᵉ
  pr1ᵉ (pr2ᵉ is-iso-id-hom-Large-Precategoryᵉ) =
    left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ (id-hom-Large-Precategoryᵉ Cᵉ)
  pr2ᵉ (pr2ᵉ is-iso-id-hom-Large-Precategoryᵉ) =
    left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ (id-hom-Large-Precategoryᵉ Cᵉ)

  id-iso-Large-Precategoryᵉ : iso-Large-Precategoryᵉ Cᵉ Xᵉ Xᵉ
  pr1ᵉ id-iso-Large-Precategoryᵉ = id-hom-Large-Precategoryᵉ Cᵉ
  pr2ᵉ id-iso-Large-Precategoryᵉ = is-iso-id-hom-Large-Precategoryᵉ
```

## Properties

### Being an isomorphism is a proposition

Letᵉ `fᵉ : homᵉ xᵉ y`ᵉ andᵉ supposeᵉ `gᵉ g'ᵉ : homᵉ yᵉ x`ᵉ areᵉ bothᵉ two-sidedᵉ inversesᵉ to
`f`.ᵉ Itᵉ isᵉ enoughᵉ to showᵉ thatᵉ `gᵉ = g'`ᵉ sinceᵉ theᵉ equalitiesᵉ areᵉ propositionsᵉ
(sinceᵉ theᵉ hom-typesᵉ areᵉ sets).ᵉ Butᵉ weᵉ haveᵉ theᵉ followingᵉ chainᵉ ofᵉ equalitiesᵉ:
`gᵉ = gᵉ ∘ᵉ id_yᵉ = gᵉ ∘ᵉ (fᵉ ∘ᵉ g'ᵉ) = (gᵉ ∘ᵉ fᵉ) ∘ᵉ g'ᵉ = id_xᵉ ∘ᵉ g'ᵉ = g'`.ᵉ

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  where

  all-elements-equal-is-iso-Large-Precategoryᵉ :
    (fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
    (Hᵉ Kᵉ : is-iso-Large-Precategoryᵉ Cᵉ fᵉ) → Hᵉ ＝ᵉ Kᵉ
  all-elements-equal-is-iso-Large-Precategoryᵉ fᵉ (gᵉ ,ᵉ pᵉ ,ᵉ qᵉ) (g'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) =
    eq-type-subtypeᵉ
      ( λ gᵉ →
        product-Propᵉ
          ( Id-Propᵉ
            ( hom-set-Large-Precategoryᵉ Cᵉ Yᵉ Yᵉ)
            ( comp-hom-Large-Precategoryᵉ Cᵉ fᵉ gᵉ)
            ( id-hom-Large-Precategoryᵉ Cᵉ))
          ( Id-Propᵉ
            ( hom-set-Large-Precategoryᵉ Cᵉ Xᵉ Xᵉ)
            ( comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ)
            ( id-hom-Large-Precategoryᵉ Cᵉ)))
      ( ( invᵉ (right-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ gᵉ)) ∙ᵉ
        ( apᵉ ( comp-hom-Large-Precategoryᵉ Cᵉ gᵉ) (invᵉ p'ᵉ)) ∙ᵉ
        ( invᵉ (associative-comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ g'ᵉ)) ∙ᵉ
        ( apᵉ ( comp-hom-Large-Precategory'ᵉ Cᵉ g'ᵉ) qᵉ) ∙ᵉ
        ( left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ g'ᵉ))

  is-prop-is-iso-Large-Precategoryᵉ :
    (fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
    is-propᵉ (is-iso-Large-Precategoryᵉ Cᵉ fᵉ)
  is-prop-is-iso-Large-Precategoryᵉ fᵉ =
    is-prop-all-elements-equalᵉ
      ( all-elements-equal-is-iso-Large-Precategoryᵉ fᵉ)

  is-iso-prop-Large-Precategoryᵉ :
    (fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ) → Propᵉ (βᵉ l1ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l2ᵉ)
  pr1ᵉ (is-iso-prop-Large-Precategoryᵉ fᵉ) =
    is-iso-Large-Precategoryᵉ Cᵉ fᵉ
  pr2ᵉ (is-iso-prop-Large-Precategoryᵉ fᵉ) =
    is-prop-is-iso-Large-Precategoryᵉ fᵉ
```

### Equality of isomorphism is equality of their underlying morphisms

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  where

  eq-iso-eq-hom-Large-Precategoryᵉ :
    (fᵉ gᵉ : iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
    hom-iso-Large-Precategoryᵉ Cᵉ fᵉ ＝ᵉ hom-iso-Large-Precategoryᵉ Cᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-iso-eq-hom-Large-Precategoryᵉ fᵉ gᵉ =
    eq-type-subtypeᵉ (is-iso-prop-Large-Precategoryᵉ Cᵉ)
```

### The type of isomorphisms form a set

Theᵉ typeᵉ ofᵉ isomorphismsᵉ betweenᵉ objectsᵉ `xᵉ yᵉ : A`ᵉ isᵉ aᵉ subtypeᵉ ofᵉ theᵉ setᵉ
`homᵉ xᵉ y`ᵉ sinceᵉ beingᵉ anᵉ isomorphismᵉ isᵉ aᵉ proposition.ᵉ

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  where

  is-set-iso-Large-Precategoryᵉ : is-setᵉ (iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
  is-set-iso-Large-Precategoryᵉ =
    is-set-type-subtypeᵉ
      ( is-iso-prop-Large-Precategoryᵉ Cᵉ)
      ( is-set-hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)

  iso-set-Large-Precategoryᵉ : Setᵉ (βᵉ l1ᵉ l1ᵉ ⊔ βᵉ l1ᵉ l2ᵉ ⊔ βᵉ l2ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l2ᵉ)
  pr1ᵉ iso-set-Large-Precategoryᵉ = iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ
  pr2ᵉ iso-set-Large-Precategoryᵉ = is-set-iso-Large-Precategoryᵉ
```

### Equalities induce isomorphisms

Anᵉ equalityᵉ betweenᵉ objectsᵉ `Xᵉ Yᵉ : A`ᵉ givesᵉ riseᵉ to anᵉ isomorphismᵉ betweenᵉ them.ᵉ
Thisᵉ isᵉ because,ᵉ byᵉ theᵉ J-rule,ᵉ itᵉ isᵉ enoughᵉ to constructᵉ anᵉ isomorphismᵉ givenᵉ
`reflᵉ : Xᵉ ＝ᵉ X`,ᵉ fromᵉ `X`ᵉ to itself.ᵉ Weᵉ takeᵉ theᵉ identityᵉ morphismᵉ asᵉ suchᵉ anᵉ
isomorphism.ᵉ

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ : Level}
  where

  iso-eq-Large-Precategoryᵉ :
    (Xᵉ Yᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) → Xᵉ ＝ᵉ Yᵉ → iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ
  pr1ᵉ (iso-eq-Large-Precategoryᵉ Xᵉ Yᵉ pᵉ) = hom-eq-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ pᵉ
  pr2ᵉ (iso-eq-Large-Precategoryᵉ Xᵉ .Xᵉ reflᵉ) = is-iso-id-hom-Large-Precategoryᵉ Cᵉ

  compute-iso-eq-Large-Precategoryᵉ :
    (Xᵉ Yᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) →
    iso-eq-Precategoryᵉ (precategory-Large-Precategoryᵉ Cᵉ l1ᵉ) Xᵉ Yᵉ ~ᵉ
    iso-eq-Large-Precategoryᵉ Xᵉ Yᵉ
  compute-iso-eq-Large-Precategoryᵉ Xᵉ Yᵉ pᵉ =
    eq-iso-eq-hom-Large-Precategoryᵉ Cᵉ
      ( iso-eq-Precategoryᵉ (precategory-Large-Precategoryᵉ Cᵉ l1ᵉ) Xᵉ Yᵉ pᵉ)
      ( iso-eq-Large-Precategoryᵉ Xᵉ Yᵉ pᵉ)
      ( compute-hom-eq-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ pᵉ)
```

### Isomorphisms are closed under composition

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
  {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  {Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ}
  {gᵉ : hom-Large-Precategoryᵉ Cᵉ Yᵉ Zᵉ}
  {fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ}
  where

  hom-comp-is-iso-Large-Precategoryᵉ :
    is-iso-Large-Precategoryᵉ Cᵉ gᵉ →
    is-iso-Large-Precategoryᵉ Cᵉ fᵉ →
    hom-Large-Precategoryᵉ Cᵉ Zᵉ Xᵉ
  hom-comp-is-iso-Large-Precategoryᵉ qᵉ pᵉ =
    comp-hom-Large-Precategoryᵉ Cᵉ
      ( hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ pᵉ)
      ( hom-inv-is-iso-Large-Precategoryᵉ Cᵉ gᵉ qᵉ)

  is-section-comp-is-iso-Large-Precategoryᵉ :
    (qᵉ : is-iso-Large-Precategoryᵉ Cᵉ gᵉ)
    (pᵉ : is-iso-Large-Precategoryᵉ Cᵉ fᵉ) →
    comp-hom-Large-Precategoryᵉ Cᵉ
      ( comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ)
      ( hom-comp-is-iso-Large-Precategoryᵉ qᵉ pᵉ) ＝ᵉ
    id-hom-Large-Precategoryᵉ Cᵉ
  is-section-comp-is-iso-Large-Precategoryᵉ qᵉ pᵉ =
    ( associative-comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ _) ∙ᵉ
    ( apᵉ
      ( comp-hom-Large-Precategoryᵉ Cᵉ gᵉ)
      ( ( invᵉ
          ( associative-comp-hom-Large-Precategoryᵉ Cᵉ fᵉ
            ( hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ pᵉ)
            ( hom-inv-is-iso-Large-Precategoryᵉ Cᵉ gᵉ qᵉ))) ∙ᵉ
        ( apᵉ
          ( λ hᵉ → comp-hom-Large-Precategoryᵉ Cᵉ hᵉ _)
          ( is-section-hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ pᵉ)) ∙ᵉ
        ( left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ
          ( hom-inv-is-iso-Large-Precategoryᵉ Cᵉ gᵉ qᵉ)))) ∙ᵉ
    ( is-section-hom-inv-is-iso-Large-Precategoryᵉ Cᵉ gᵉ qᵉ)

  is-retraction-comp-is-iso-Large-Precategoryᵉ :
    (qᵉ : is-iso-Large-Precategoryᵉ Cᵉ gᵉ)
    (pᵉ : is-iso-Large-Precategoryᵉ Cᵉ fᵉ) →
    comp-hom-Large-Precategoryᵉ Cᵉ
      ( hom-comp-is-iso-Large-Precategoryᵉ qᵉ pᵉ)
      ( comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ) ＝ᵉ
    id-hom-Large-Precategoryᵉ Cᵉ
  is-retraction-comp-is-iso-Large-Precategoryᵉ qᵉ pᵉ =
    ( associative-comp-hom-Large-Precategoryᵉ Cᵉ
      ( hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ pᵉ)
      ( hom-inv-is-iso-Large-Precategoryᵉ Cᵉ gᵉ qᵉ)
      ( comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ)) ∙ᵉ
    ( apᵉ
      ( comp-hom-Large-Precategoryᵉ
        ( Cᵉ)
        ( hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ pᵉ))
      ( ( invᵉ
          ( associative-comp-hom-Large-Precategoryᵉ Cᵉ
            ( hom-inv-is-iso-Large-Precategoryᵉ Cᵉ gᵉ qᵉ)
            ( gᵉ)
            ( fᵉ))) ∙ᵉ
        ( apᵉ
          ( λ hᵉ → comp-hom-Large-Precategoryᵉ Cᵉ hᵉ fᵉ)
          ( is-retraction-hom-inv-is-iso-Large-Precategoryᵉ Cᵉ gᵉ qᵉ)) ∙ᵉ
        ( left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ fᵉ))) ∙ᵉ
    ( is-retraction-hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ pᵉ)

  is-iso-comp-is-iso-Large-Precategoryᵉ :
    is-iso-Large-Precategoryᵉ Cᵉ gᵉ → is-iso-Large-Precategoryᵉ Cᵉ fᵉ →
    is-iso-Large-Precategoryᵉ Cᵉ (comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ)
  pr1ᵉ (is-iso-comp-is-iso-Large-Precategoryᵉ qᵉ pᵉ) =
    hom-comp-is-iso-Large-Precategoryᵉ qᵉ pᵉ
  pr1ᵉ (pr2ᵉ (is-iso-comp-is-iso-Large-Precategoryᵉ qᵉ pᵉ)) =
    is-section-comp-is-iso-Large-Precategoryᵉ qᵉ pᵉ
  pr2ᵉ (pr2ᵉ (is-iso-comp-is-iso-Large-Precategoryᵉ qᵉ pᵉ)) =
    is-retraction-comp-is-iso-Large-Precategoryᵉ qᵉ pᵉ
```

### Composition of isomorphisms

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
  {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  {Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ}
  (gᵉ : iso-Large-Precategoryᵉ Cᵉ Yᵉ Zᵉ)
  (fᵉ : iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  hom-comp-iso-Large-Precategoryᵉ :
    hom-Large-Precategoryᵉ Cᵉ Xᵉ Zᵉ
  hom-comp-iso-Large-Precategoryᵉ =
    comp-hom-Large-Precategoryᵉ Cᵉ
      ( hom-iso-Large-Precategoryᵉ Cᵉ gᵉ)
      ( hom-iso-Large-Precategoryᵉ Cᵉ fᵉ)

  is-iso-comp-iso-Large-Precategoryᵉ :
    is-iso-Large-Precategoryᵉ Cᵉ hom-comp-iso-Large-Precategoryᵉ
  is-iso-comp-iso-Large-Precategoryᵉ =
    is-iso-comp-is-iso-Large-Precategoryᵉ Cᵉ
      ( is-iso-iso-Large-Precategoryᵉ Cᵉ gᵉ)
      ( is-iso-iso-Large-Precategoryᵉ Cᵉ fᵉ)

  comp-iso-Large-Precategoryᵉ :
    iso-Large-Precategoryᵉ Cᵉ Xᵉ Zᵉ
  pr1ᵉ comp-iso-Large-Precategoryᵉ = hom-comp-iso-Large-Precategoryᵉ
  pr2ᵉ comp-iso-Large-Precategoryᵉ = is-iso-comp-iso-Large-Precategoryᵉ

  hom-inv-comp-iso-Large-Precategoryᵉ :
    hom-Large-Precategoryᵉ Cᵉ Zᵉ Xᵉ
  hom-inv-comp-iso-Large-Precategoryᵉ =
    hom-inv-iso-Large-Precategoryᵉ Cᵉ comp-iso-Large-Precategoryᵉ

  is-section-inv-comp-iso-Large-Precategoryᵉ :
    comp-hom-Large-Precategoryᵉ Cᵉ
      ( hom-comp-iso-Large-Precategoryᵉ)
      ( hom-inv-comp-iso-Large-Precategoryᵉ) ＝ᵉ
    id-hom-Large-Precategoryᵉ Cᵉ
  is-section-inv-comp-iso-Large-Precategoryᵉ =
    is-section-hom-inv-iso-Large-Precategoryᵉ Cᵉ comp-iso-Large-Precategoryᵉ

  is-retraction-inv-comp-iso-Large-Precategoryᵉ :
    comp-hom-Large-Precategoryᵉ Cᵉ
      ( hom-inv-comp-iso-Large-Precategoryᵉ)
      ( hom-comp-iso-Large-Precategoryᵉ) ＝ᵉ
    id-hom-Large-Precategoryᵉ Cᵉ
  is-retraction-inv-comp-iso-Large-Precategoryᵉ =
    is-retraction-hom-inv-iso-Large-Precategoryᵉ Cᵉ comp-iso-Large-Precategoryᵉ
```

### Inverses of isomorphisms are isomorphisms

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  {fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ}
  where

  is-iso-inv-is-iso-Large-Precategoryᵉ :
    (pᵉ : is-iso-Large-Precategoryᵉ Cᵉ fᵉ) →
    is-iso-Large-Precategoryᵉ Cᵉ (hom-inv-iso-Large-Precategoryᵉ Cᵉ (fᵉ ,ᵉ pᵉ))
  pr1ᵉ (is-iso-inv-is-iso-Large-Precategoryᵉ pᵉ) = fᵉ
  pr1ᵉ (pr2ᵉ (is-iso-inv-is-iso-Large-Precategoryᵉ pᵉ)) =
    is-retraction-hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ pᵉ
  pr2ᵉ (pr2ᵉ (is-iso-inv-is-iso-Large-Precategoryᵉ pᵉ)) =
    is-section-hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ pᵉ
```

### Inverses of isomorphisms

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  where

  inv-iso-Large-Precategoryᵉ :
    iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ → iso-Large-Precategoryᵉ Cᵉ Yᵉ Xᵉ
  pr1ᵉ (inv-iso-Large-Precategoryᵉ fᵉ) = hom-inv-iso-Large-Precategoryᵉ Cᵉ fᵉ
  pr2ᵉ (inv-iso-Large-Precategoryᵉ fᵉ) =
    is-iso-inv-is-iso-Large-Precategoryᵉ Cᵉ
      ( is-iso-iso-Large-Precategoryᵉ Cᵉ fᵉ)
```

### Composition of isomorphisms satisfies the unit laws

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  (fᵉ : iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  left-unit-law-comp-iso-Large-Precategoryᵉ :
    comp-iso-Large-Precategoryᵉ Cᵉ (id-iso-Large-Precategoryᵉ Cᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-iso-Large-Precategoryᵉ =
    eq-iso-eq-hom-Large-Precategoryᵉ Cᵉ
      ( comp-iso-Large-Precategoryᵉ Cᵉ (id-iso-Large-Precategoryᵉ Cᵉ) fᵉ)
      ( fᵉ)
      ( left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ
        ( hom-iso-Large-Precategoryᵉ Cᵉ fᵉ))

  right-unit-law-comp-iso-Large-Precategoryᵉ :
    comp-iso-Large-Precategoryᵉ Cᵉ fᵉ (id-iso-Large-Precategoryᵉ Cᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-iso-Large-Precategoryᵉ =
    eq-iso-eq-hom-Large-Precategoryᵉ Cᵉ
      ( comp-iso-Large-Precategoryᵉ Cᵉ fᵉ (id-iso-Large-Precategoryᵉ Cᵉ))
      ( fᵉ)
      ( right-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ
        ( hom-iso-Large-Precategoryᵉ Cᵉ fᵉ))
```

### Composition of isomorphisms is associative

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
  {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  {Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ}
  {Wᵉ : obj-Large-Precategoryᵉ Cᵉ l4ᵉ}
  (hᵉ : iso-Large-Precategoryᵉ Cᵉ Zᵉ Wᵉ)
  (gᵉ : iso-Large-Precategoryᵉ Cᵉ Yᵉ Zᵉ)
  (fᵉ : iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  associative-comp-iso-Large-Precategoryᵉ :
    comp-iso-Large-Precategoryᵉ Cᵉ (comp-iso-Large-Precategoryᵉ Cᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-iso-Large-Precategoryᵉ Cᵉ hᵉ (comp-iso-Large-Precategoryᵉ Cᵉ gᵉ fᵉ)
  associative-comp-iso-Large-Precategoryᵉ =
    eq-iso-eq-hom-Large-Precategoryᵉ Cᵉ
      ( comp-iso-Large-Precategoryᵉ Cᵉ (comp-iso-Large-Precategoryᵉ Cᵉ hᵉ gᵉ) fᵉ)
      ( comp-iso-Large-Precategoryᵉ Cᵉ hᵉ (comp-iso-Large-Precategoryᵉ Cᵉ gᵉ fᵉ))
      ( associative-comp-hom-Large-Precategoryᵉ Cᵉ
        ( hom-iso-Large-Precategoryᵉ Cᵉ hᵉ)
        ( hom-iso-Large-Precategoryᵉ Cᵉ gᵉ)
        ( hom-iso-Large-Precategoryᵉ Cᵉ fᵉ))
```

### Composition of isomorphisms satisfies inverse laws

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  (fᵉ : iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  left-inverse-law-comp-iso-Large-Precategoryᵉ :
    comp-iso-Large-Precategoryᵉ Cᵉ (inv-iso-Large-Precategoryᵉ Cᵉ fᵉ) fᵉ ＝ᵉ
    id-iso-Large-Precategoryᵉ Cᵉ
  left-inverse-law-comp-iso-Large-Precategoryᵉ =
    eq-iso-eq-hom-Large-Precategoryᵉ Cᵉ
      ( comp-iso-Large-Precategoryᵉ Cᵉ (inv-iso-Large-Precategoryᵉ Cᵉ fᵉ) fᵉ)
      ( id-iso-Large-Precategoryᵉ Cᵉ)
      ( is-retraction-hom-inv-iso-Large-Precategoryᵉ Cᵉ fᵉ)

  right-inverse-law-comp-iso-Large-Precategoryᵉ :
    comp-iso-Large-Precategoryᵉ Cᵉ fᵉ (inv-iso-Large-Precategoryᵉ Cᵉ fᵉ) ＝ᵉ
    id-iso-Large-Precategoryᵉ Cᵉ
  right-inverse-law-comp-iso-Large-Precategoryᵉ =
    eq-iso-eq-hom-Large-Precategoryᵉ Cᵉ
      ( comp-iso-Large-Precategoryᵉ Cᵉ fᵉ (inv-iso-Large-Precategoryᵉ Cᵉ fᵉ))
      ( id-iso-Large-Precategoryᵉ Cᵉ)
      ( is-section-hom-inv-iso-Large-Precategoryᵉ Cᵉ fᵉ)
```

### A morphism `f` is an isomorphism if and only if precomposition by `f` is an equivalence

**Proof:**ᵉ Ifᵉ `f`ᵉ isᵉ anᵉ isomorphismᵉ with inverseᵉ `f⁻¹`,ᵉ thenᵉ precomposingᵉ with
`f⁻¹`ᵉ isᵉ anᵉ inverseᵉ ofᵉ precomposingᵉ with `f`.ᵉ Theᵉ onlyᵉ interestingᵉ directionᵉ isᵉ
thereforeᵉ theᵉ converse.ᵉ

Supposeᵉ thatᵉ precomposingᵉ with `f`ᵉ isᵉ anᵉ equivalence,ᵉ forᵉ anyᵉ objectᵉ `Z`.ᵉ Thenᵉ

```text
  -ᵉ ∘ᵉ fᵉ : homᵉ Yᵉ Xᵉ → homᵉ Xᵉ Xᵉ
```

isᵉ anᵉ equivalence.ᵉ Inᵉ particular,ᵉ thereᵉ isᵉ aᵉ uniqueᵉ morphismᵉ `gᵉ : Yᵉ → X`ᵉ suchᵉ
thatᵉ `gᵉ ∘ᵉ fᵉ ＝ᵉ id`.ᵉ Thusᵉ weᵉ haveᵉ aᵉ retractionᵉ ofᵉ `f`.ᵉ Toᵉ seeᵉ thatᵉ `g`ᵉ isᵉ alsoᵉ aᵉ
section,ᵉ noteᵉ thatᵉ theᵉ mapᵉ

```text
  -ᵉ ∘ᵉ fᵉ : homᵉ Yᵉ Yᵉ → homᵉ Xᵉ Yᵉ
```

isᵉ anᵉ equivalence.ᵉ Inᵉ particular,ᵉ itᵉ isᵉ injective.ᵉ Thereforeᵉ itᵉ sufficesᵉ to showᵉ
thatᵉ `(fᵉ ∘ᵉ gᵉ) ∘ᵉ fᵉ ＝ᵉ idᵉ ∘ᵉ f`.ᵉ Toᵉ seeᵉ this,ᵉ weᵉ calculateᵉ

```text
  (fᵉ ∘ᵉ gᵉ) ∘ᵉ fᵉ ＝ᵉ fᵉ ∘ᵉ (gᵉ ∘ᵉ fᵉ) ＝ᵉ fᵉ ∘ᵉ idᵉ ＝ᵉ fᵉ ＝ᵉ idᵉ ∘ᵉ f.ᵉ
```

Thisᵉ completesᵉ theᵉ proof.ᵉ

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  {fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ}
  (Hᵉ :
    {l3ᵉ : Level} (Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ) →
    is-equivᵉ (precomp-hom-Large-Precategoryᵉ Cᵉ fᵉ Zᵉ))
  where

  hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ :
    hom-Large-Precategoryᵉ Cᵉ Yᵉ Xᵉ
  hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ =
    map-inv-is-equivᵉ (Hᵉ Xᵉ) (id-hom-Large-Precategoryᵉ Cᵉ)

  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ :
    comp-hom-Large-Precategoryᵉ Cᵉ
      ( hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ)
      ( fᵉ) ＝ᵉ
    id-hom-Large-Precategoryᵉ Cᵉ
  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ =
    is-section-map-inv-is-equivᵉ (Hᵉ Xᵉ) (id-hom-Large-Precategoryᵉ Cᵉ)

  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ :
    comp-hom-Large-Precategoryᵉ Cᵉ
      ( fᵉ)
      ( hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ) ＝ᵉ
    id-hom-Large-Precategoryᵉ Cᵉ
  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ =
    is-injective-is-equivᵉ
      ( Hᵉ Yᵉ)
      ( ( associative-comp-hom-Large-Precategoryᵉ Cᵉ
          ( fᵉ)
          ( hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ)
          ( fᵉ)) ∙ᵉ
        ( apᵉ
          ( comp-hom-Large-Precategoryᵉ Cᵉ fᵉ)
          ( is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ)) ∙ᵉ
        ( right-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ fᵉ) ∙ᵉ
        ( invᵉ (left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ fᵉ)))

  is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ :
    is-iso-Large-Precategoryᵉ Cᵉ fᵉ
  pr1ᵉ is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ =
    hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ
  pr1ᵉ (pr2ᵉ is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ) =
    is-section-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ
  pr2ᵉ (pr2ᵉ is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ) =
    is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  {fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ}
  (is-iso-fᵉ : is-iso-Large-Precategoryᵉ Cᵉ fᵉ)
  (Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ)
  where

  map-inv-precomp-hom-is-iso-Large-Precategoryᵉ :
    hom-Large-Precategoryᵉ Cᵉ Xᵉ Zᵉ → hom-Large-Precategoryᵉ Cᵉ Yᵉ Zᵉ
  map-inv-precomp-hom-is-iso-Large-Precategoryᵉ =
    precomp-hom-Large-Precategoryᵉ Cᵉ
      ( hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ is-iso-fᵉ)
      ( Zᵉ)

  is-section-map-inv-precomp-hom-is-iso-Large-Precategoryᵉ :
    is-sectionᵉ
      ( precomp-hom-Large-Precategoryᵉ Cᵉ fᵉ Zᵉ)
      ( map-inv-precomp-hom-is-iso-Large-Precategoryᵉ)
  is-section-map-inv-precomp-hom-is-iso-Large-Precategoryᵉ gᵉ =
    ( associative-comp-hom-Large-Precategoryᵉ Cᵉ
      ( gᵉ)
      ( hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ is-iso-fᵉ)
      ( fᵉ)) ∙ᵉ
    ( apᵉ
      ( comp-hom-Large-Precategoryᵉ Cᵉ gᵉ)
      ( is-retraction-hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ is-iso-fᵉ)) ∙ᵉ
    ( right-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ gᵉ)

  is-retraction-map-inv-precomp-hom-is-iso-Large-Precategoryᵉ :
    is-retractionᵉ
      ( precomp-hom-Large-Precategoryᵉ Cᵉ fᵉ Zᵉ)
      ( map-inv-precomp-hom-is-iso-Large-Precategoryᵉ)
  is-retraction-map-inv-precomp-hom-is-iso-Large-Precategoryᵉ gᵉ =
    ( associative-comp-hom-Large-Precategoryᵉ Cᵉ
      ( gᵉ)
      ( fᵉ)
      ( hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ is-iso-fᵉ)) ∙ᵉ
    ( apᵉ
      ( comp-hom-Large-Precategoryᵉ Cᵉ gᵉ)
      ( is-section-hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ is-iso-fᵉ)) ∙ᵉ
    ( right-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ gᵉ)

  is-equiv-precomp-hom-is-iso-Large-Precategoryᵉ :
    is-equivᵉ (precomp-hom-Large-Precategoryᵉ Cᵉ fᵉ Zᵉ)
  is-equiv-precomp-hom-is-iso-Large-Precategoryᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-precomp-hom-is-iso-Large-Precategoryᵉ)
      ( is-section-map-inv-precomp-hom-is-iso-Large-Precategoryᵉ)
      ( is-retraction-map-inv-precomp-hom-is-iso-Large-Precategoryᵉ)

  equiv-precomp-hom-is-iso-Large-Precategoryᵉ :
    hom-Large-Precategoryᵉ Cᵉ Yᵉ Zᵉ ≃ᵉ hom-Large-Precategoryᵉ Cᵉ Xᵉ Zᵉ
  pr1ᵉ equiv-precomp-hom-is-iso-Large-Precategoryᵉ =
    precomp-hom-Large-Precategoryᵉ Cᵉ fᵉ Zᵉ
  pr2ᵉ equiv-precomp-hom-is-iso-Large-Precategoryᵉ =
    is-equiv-precomp-hom-is-iso-Large-Precategoryᵉ

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  (fᵉ : iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
  (Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ)
  where

  is-equiv-precomp-hom-iso-Large-Precategoryᵉ :
    is-equivᵉ (precomp-hom-Large-Precategoryᵉ Cᵉ (hom-iso-Large-Precategoryᵉ Cᵉ fᵉ) Zᵉ)
  is-equiv-precomp-hom-iso-Large-Precategoryᵉ =
    is-equiv-precomp-hom-is-iso-Large-Precategoryᵉ Cᵉ
      ( is-iso-iso-Large-Precategoryᵉ Cᵉ fᵉ)
      ( Zᵉ)

  equiv-precomp-hom-iso-Large-Precategoryᵉ :
    hom-Large-Precategoryᵉ Cᵉ Yᵉ Zᵉ ≃ᵉ hom-Large-Precategoryᵉ Cᵉ Xᵉ Zᵉ
  equiv-precomp-hom-iso-Large-Precategoryᵉ =
    equiv-precomp-hom-is-iso-Large-Precategoryᵉ Cᵉ
      ( is-iso-iso-Large-Precategoryᵉ Cᵉ fᵉ)
      ( Zᵉ)
```

### A morphism `f` is an isomorphism if and only if postcomposition by `f` is an equivalence

**Proof:**ᵉ Ifᵉ `f`ᵉ isᵉ anᵉ isomorphismᵉ with inverseᵉ `f⁻¹`,ᵉ thenᵉ postcomposingᵉ with
`f⁻¹`ᵉ isᵉ anᵉ inverseᵉ ofᵉ postcomposingᵉ with `f`.ᵉ Theᵉ onlyᵉ interestingᵉ directionᵉ isᵉ
thereforeᵉ theᵉ converse.ᵉ

Supposeᵉ thatᵉ postcomposingᵉ with `f`ᵉ isᵉ anᵉ equivalence,ᵉ forᵉ anyᵉ objectᵉ `Z`.ᵉ Thenᵉ

```text
  fᵉ ∘ᵉ -ᵉ : homᵉ Yᵉ Xᵉ → homᵉ Yᵉ Yᵉ
```

isᵉ anᵉ equivalence.ᵉ Inᵉ particular,ᵉ thereᵉ isᵉ aᵉ uniqueᵉ morphismᵉ `gᵉ : Yᵉ → X`ᵉ suchᵉ
thatᵉ `fᵉ ∘ᵉ gᵉ ＝ᵉ id`.ᵉ Thusᵉ weᵉ haveᵉ aᵉ sectionᵉ ofᵉ `f`.ᵉ Toᵉ seeᵉ thatᵉ `g`ᵉ isᵉ alsoᵉ aᵉ
retraction,ᵉ noteᵉ thatᵉ theᵉ mapᵉ

```text
  fᵉ ∘ᵉ -ᵉ : homᵉ Xᵉ Xᵉ → homᵉ Xᵉ Yᵉ
```

isᵉ anᵉ equivalence.ᵉ Inᵉ particular,ᵉ itᵉ isᵉ injective.ᵉ Thereforeᵉ itᵉ sufficesᵉ to showᵉ
thatᵉ `fᵉ ∘ᵉ (gᵉ ∘ᵉ fᵉ) ＝ᵉ fᵉ ∘ᵉ id`.ᵉ Toᵉ seeᵉ this,ᵉ weᵉ calculateᵉ

```text
  fᵉ ∘ᵉ (gᵉ ∘ᵉ fᵉ) ＝ᵉ (fᵉ ∘ᵉ gᵉ) ∘ᵉ fᵉ ＝ᵉ idᵉ ∘ᵉ fᵉ ＝ᵉ fᵉ ＝ᵉ fᵉ ∘ᵉ id.ᵉ
```

Thisᵉ completesᵉ theᵉ proof.ᵉ

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  {fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ}
  (Hᵉ :
    {l3ᵉ : Level} (Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ) →
    is-equivᵉ (postcomp-hom-Large-Precategoryᵉ Cᵉ Zᵉ fᵉ))
  where

  hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ :
    hom-Large-Precategoryᵉ Cᵉ Yᵉ Xᵉ
  hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ =
    map-inv-is-equivᵉ (Hᵉ Yᵉ) (id-hom-Large-Precategoryᵉ Cᵉ)

  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ :
    comp-hom-Large-Precategoryᵉ Cᵉ
      ( fᵉ)
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ) ＝ᵉ
    id-hom-Large-Precategoryᵉ Cᵉ
  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ =
    is-section-map-inv-is-equivᵉ (Hᵉ Yᵉ) (id-hom-Large-Precategoryᵉ Cᵉ)

  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ :
    comp-hom-Large-Precategoryᵉ Cᵉ
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ)
      ( fᵉ) ＝ᵉ
    id-hom-Large-Precategoryᵉ Cᵉ
  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ =
    is-injective-is-equivᵉ
      ( Hᵉ Xᵉ)
      ( ( invᵉ
          ( associative-comp-hom-Large-Precategoryᵉ Cᵉ
            ( fᵉ)
            ( hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ)
            ( fᵉ))) ∙ᵉ
        ( apᵉ
          ( comp-hom-Large-Precategory'ᵉ Cᵉ fᵉ)
          ( is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ)) ∙ᵉ
        ( left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ fᵉ) ∙ᵉ
        ( invᵉ (right-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ fᵉ)))

  is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ :
    is-iso-Large-Precategoryᵉ Cᵉ fᵉ
  pr1ᵉ is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ =
    hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ
  pr1ᵉ (pr2ᵉ is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ) =
    is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ
  pr2ᵉ (pr2ᵉ is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ) =
    is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  {fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ}
  (is-iso-fᵉ : is-iso-Large-Precategoryᵉ Cᵉ fᵉ)
  (Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ)
  where

  map-inv-postcomp-hom-is-iso-Large-Precategoryᵉ :
    hom-Large-Precategoryᵉ Cᵉ Zᵉ Yᵉ → hom-Large-Precategoryᵉ Cᵉ Zᵉ Xᵉ
  map-inv-postcomp-hom-is-iso-Large-Precategoryᵉ =
    postcomp-hom-Large-Precategoryᵉ Cᵉ
      ( Zᵉ)
      ( hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ is-iso-fᵉ)

  is-section-map-inv-postcomp-hom-is-iso-Large-Precategoryᵉ :
    is-sectionᵉ
      ( postcomp-hom-Large-Precategoryᵉ Cᵉ Zᵉ fᵉ)
      ( map-inv-postcomp-hom-is-iso-Large-Precategoryᵉ)
  is-section-map-inv-postcomp-hom-is-iso-Large-Precategoryᵉ gᵉ =
    ( invᵉ
      ( associative-comp-hom-Large-Precategoryᵉ Cᵉ
        ( fᵉ)
        ( hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ is-iso-fᵉ)
        ( gᵉ))) ∙ᵉ
    ( apᵉ
      ( comp-hom-Large-Precategory'ᵉ Cᵉ gᵉ)
      ( is-section-hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ is-iso-fᵉ)) ∙ᵉ
    ( left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ gᵉ)

  is-retraction-map-inv-postcomp-hom-is-iso-Large-Precategoryᵉ :
    is-retractionᵉ
      ( postcomp-hom-Large-Precategoryᵉ Cᵉ Zᵉ fᵉ)
      ( map-inv-postcomp-hom-is-iso-Large-Precategoryᵉ)
  is-retraction-map-inv-postcomp-hom-is-iso-Large-Precategoryᵉ gᵉ =
    ( invᵉ
      ( associative-comp-hom-Large-Precategoryᵉ Cᵉ
        ( hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ is-iso-fᵉ)
        ( fᵉ)
        ( gᵉ))) ∙ᵉ
    ( apᵉ
      ( comp-hom-Large-Precategory'ᵉ Cᵉ gᵉ)
      ( is-retraction-hom-inv-is-iso-Large-Precategoryᵉ Cᵉ fᵉ is-iso-fᵉ)) ∙ᵉ
    ( left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ gᵉ)

  is-equiv-postcomp-hom-is-iso-Large-Precategoryᵉ :
    is-equivᵉ (postcomp-hom-Large-Precategoryᵉ Cᵉ Zᵉ fᵉ)
  is-equiv-postcomp-hom-is-iso-Large-Precategoryᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-postcomp-hom-is-iso-Large-Precategoryᵉ)
      ( is-section-map-inv-postcomp-hom-is-iso-Large-Precategoryᵉ)
      ( is-retraction-map-inv-postcomp-hom-is-iso-Large-Precategoryᵉ)

  equiv-postcomp-hom-is-iso-Large-Precategoryᵉ :
    hom-Large-Precategoryᵉ Cᵉ Zᵉ Xᵉ ≃ᵉ hom-Large-Precategoryᵉ Cᵉ Zᵉ Yᵉ
  pr1ᵉ equiv-postcomp-hom-is-iso-Large-Precategoryᵉ =
    postcomp-hom-Large-Precategoryᵉ Cᵉ Zᵉ fᵉ
  pr2ᵉ equiv-postcomp-hom-is-iso-Large-Precategoryᵉ =
    is-equiv-postcomp-hom-is-iso-Large-Precategoryᵉ

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  (fᵉ : iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
  (Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ)
  where

  is-equiv-postcomp-hom-iso-Large-Precategoryᵉ :
    is-equivᵉ
      ( postcomp-hom-Large-Precategoryᵉ Cᵉ Zᵉ (hom-iso-Large-Precategoryᵉ Cᵉ fᵉ))
  is-equiv-postcomp-hom-iso-Large-Precategoryᵉ =
    is-equiv-postcomp-hom-is-iso-Large-Precategoryᵉ Cᵉ
      ( is-iso-iso-Large-Precategoryᵉ Cᵉ fᵉ)
      ( Zᵉ)

  equiv-postcomp-hom-iso-Large-Precategoryᵉ :
    hom-Large-Precategoryᵉ Cᵉ Zᵉ Xᵉ ≃ᵉ hom-Large-Precategoryᵉ Cᵉ Zᵉ Yᵉ
  equiv-postcomp-hom-iso-Large-Precategoryᵉ =
    equiv-postcomp-hom-is-iso-Large-Precategoryᵉ Cᵉ
      ( is-iso-iso-Large-Precategoryᵉ Cᵉ fᵉ)
      ( Zᵉ)
```