# Isomorphisms in large categories

```agda
module category-theory.isomorphisms-in-large-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-categoriesᵉ
open import category-theory.isomorphisms-in-large-precategoriesᵉ
open import category-theory.large-categoriesᵉ

open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ **isomorphism**ᵉ in aᵉ [largeᵉ category](category-theory.large-categories.mdᵉ)
`C`ᵉ isᵉ aᵉ morphismᵉ `fᵉ : Xᵉ → Y`ᵉ in `C`ᵉ forᵉ whichᵉ thereᵉ existsᵉ aᵉ morphismᵉ
`gᵉ : Yᵉ → X`ᵉ suchᵉ thatᵉ `fᵉ ∘ᵉ gᵉ ＝ᵉ id`ᵉ andᵉ `gᵉ ∘ᵉ fᵉ ＝ᵉ id`.ᵉ

## Definitions

### The predicate of being an isomorphism

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  (fᵉ : hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  is-iso-Large-Categoryᵉ : UUᵉ (βᵉ l1ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l2ᵉ)
  is-iso-Large-Categoryᵉ =
    is-iso-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) fᵉ

  hom-inv-is-iso-Large-Categoryᵉ :
    is-iso-Large-Categoryᵉ → hom-Large-Categoryᵉ Cᵉ Yᵉ Xᵉ
  hom-inv-is-iso-Large-Categoryᵉ =
    hom-inv-is-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( fᵉ)

  is-section-hom-inv-is-iso-Large-Categoryᵉ :
    (Hᵉ : is-iso-Large-Categoryᵉ) →
    comp-hom-Large-Categoryᵉ Cᵉ fᵉ (hom-inv-is-iso-Large-Categoryᵉ Hᵉ) ＝ᵉ
    id-hom-Large-Categoryᵉ Cᵉ
  is-section-hom-inv-is-iso-Large-Categoryᵉ =
    is-section-hom-inv-is-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( fᵉ)

  is-retraction-hom-inv-is-iso-Large-Categoryᵉ :
    (Hᵉ : is-iso-Large-Categoryᵉ) →
    comp-hom-Large-Categoryᵉ Cᵉ (hom-inv-is-iso-Large-Categoryᵉ Hᵉ) fᵉ ＝ᵉ
    id-hom-Large-Categoryᵉ Cᵉ
  is-retraction-hom-inv-is-iso-Large-Categoryᵉ =
    is-retraction-hom-inv-is-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( fᵉ)
```

### Isomorphisms in a large category

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  (Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ) (Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ)
  where

  iso-Large-Categoryᵉ : UUᵉ (βᵉ l1ᵉ l1ᵉ ⊔ βᵉ l1ᵉ l2ᵉ ⊔ βᵉ l2ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l2ᵉ)
  iso-Large-Categoryᵉ =
    iso-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) Xᵉ Yᵉ

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  (fᵉ : iso-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  hom-iso-Large-Categoryᵉ : hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ
  hom-iso-Large-Categoryᵉ =
    hom-iso-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) fᵉ

  is-iso-iso-Large-Categoryᵉ :
    is-iso-Large-Categoryᵉ Cᵉ hom-iso-Large-Categoryᵉ
  is-iso-iso-Large-Categoryᵉ =
    is-iso-iso-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) fᵉ

  hom-inv-iso-Large-Categoryᵉ : hom-Large-Categoryᵉ Cᵉ Yᵉ Xᵉ
  hom-inv-iso-Large-Categoryᵉ =
    hom-inv-iso-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) fᵉ

  is-section-hom-inv-iso-Large-Categoryᵉ :
    ( comp-hom-Large-Categoryᵉ Cᵉ
      ( hom-iso-Large-Categoryᵉ)
      ( hom-inv-iso-Large-Categoryᵉ)) ＝ᵉ
    ( id-hom-Large-Categoryᵉ Cᵉ)
  is-section-hom-inv-iso-Large-Categoryᵉ =
    is-section-hom-inv-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( fᵉ)

  is-retraction-hom-inv-iso-Large-Categoryᵉ :
    ( comp-hom-Large-Categoryᵉ Cᵉ
      ( hom-inv-iso-Large-Categoryᵉ)
      ( hom-iso-Large-Categoryᵉ)) ＝ᵉ
    ( id-hom-Large-Categoryᵉ Cᵉ)
  is-retraction-hom-inv-iso-Large-Categoryᵉ =
    is-retraction-hom-inv-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( fᵉ)
```

## Examples

### The identity isomorphisms

Forᵉ anyᵉ objectᵉ `xᵉ : A`,ᵉ theᵉ identityᵉ morphismᵉ `id_xᵉ : homᵉ xᵉ x`ᵉ isᵉ anᵉ isomorphismᵉ
fromᵉ `x`ᵉ to `x`ᵉ sinceᵉ `id_xᵉ ∘ᵉ id_xᵉ = id_x`ᵉ (itᵉ isᵉ itsᵉ ownᵉ inverse).ᵉ

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ : Level} {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ}
  where

  is-iso-id-hom-Large-Categoryᵉ :
    is-iso-Large-Categoryᵉ Cᵉ (id-hom-Large-Categoryᵉ Cᵉ {Xᵉ = Xᵉ})
  is-iso-id-hom-Large-Categoryᵉ =
    is-iso-id-hom-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ)

  id-iso-Large-Categoryᵉ : iso-Large-Categoryᵉ Cᵉ Xᵉ Xᵉ
  id-iso-Large-Categoryᵉ =
    id-iso-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ)
```

### Equalities induce isomorphisms

Anᵉ equalityᵉ betweenᵉ objectsᵉ `Xᵉ Yᵉ : A`ᵉ givesᵉ riseᵉ to anᵉ isomorphismᵉ betweenᵉ them.ᵉ
Thisᵉ isᵉ because,ᵉ byᵉ theᵉ J-rule,ᵉ itᵉ isᵉ enoughᵉ to constructᵉ anᵉ isomorphismᵉ givenᵉ
`reflᵉ : Xᵉ ＝ᵉ X`,ᵉ fromᵉ `X`ᵉ to itself.ᵉ Weᵉ takeᵉ theᵉ identityᵉ morphismᵉ asᵉ suchᵉ anᵉ
isomorphism.ᵉ

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ : Level}
  (Xᵉ Yᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ)
  where

  iso-eq-Large-Categoryᵉ :
    Xᵉ ＝ᵉ Yᵉ → iso-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ
  iso-eq-Large-Categoryᵉ =
    iso-eq-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) Xᵉ Yᵉ

  eq-iso-Large-Categoryᵉ :
    iso-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
  eq-iso-Large-Categoryᵉ =
    map-inv-is-equivᵉ (is-large-category-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ)

  compute-iso-eq-Large-Categoryᵉ :
    iso-eq-Categoryᵉ (category-Large-Categoryᵉ Cᵉ l1ᵉ) Xᵉ Yᵉ ~ᵉ
    iso-eq-Large-Categoryᵉ
  compute-iso-eq-Large-Categoryᵉ =
    compute-iso-eq-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) Xᵉ Yᵉ

  extensionality-obj-Large-Categoryᵉ :
    (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ iso-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ
  pr1ᵉ extensionality-obj-Large-Categoryᵉ =
    iso-eq-Large-Categoryᵉ
  pr2ᵉ extensionality-obj-Large-Categoryᵉ =
    is-large-category-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ : Level}
  (Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ)
  where

  is-torsorial-iso-Large-Categoryᵉ :
    is-torsorialᵉ (iso-Large-Categoryᵉ Cᵉ Xᵉ)
  is-torsorial-iso-Large-Categoryᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (obj-Large-Categoryᵉ Cᵉ l1ᵉ) (Xᵉ ＝ᵉ_))
      ( equiv-totᵉ (extensionality-obj-Large-Categoryᵉ Cᵉ Xᵉ))
      ( is-torsorial-Idᵉ Xᵉ)

  is-torsorial-iso-Large-Category'ᵉ :
    is-torsorialᵉ (λ Yᵉ → iso-Large-Categoryᵉ Cᵉ Yᵉ Xᵉ)
  is-torsorial-iso-Large-Category'ᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (obj-Large-Categoryᵉ Cᵉ l1ᵉ) (_＝ᵉ Xᵉ))
      ( equiv-totᵉ (λ Yᵉ → extensionality-obj-Large-Categoryᵉ Cᵉ Yᵉ Xᵉ))
      ( is-torsorial-Id'ᵉ Xᵉ)
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
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  where

  all-elements-equal-is-iso-Large-Categoryᵉ :
    (fᵉ : hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ)
    (Hᵉ Kᵉ : is-iso-Large-Categoryᵉ Cᵉ fᵉ) → Hᵉ ＝ᵉ Kᵉ
  all-elements-equal-is-iso-Large-Categoryᵉ =
    all-elements-equal-is-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)

  is-prop-is-iso-Large-Categoryᵉ :
    (fᵉ : hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ) →
    is-propᵉ (is-iso-Large-Categoryᵉ Cᵉ fᵉ)
  is-prop-is-iso-Large-Categoryᵉ fᵉ =
    is-prop-all-elements-equalᵉ
      ( all-elements-equal-is-iso-Large-Categoryᵉ fᵉ)

  is-iso-prop-Large-Categoryᵉ :
    (fᵉ : hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ) → Propᵉ (βᵉ l1ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l2ᵉ)
  is-iso-prop-Large-Categoryᵉ =
    is-iso-prop-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ)
```

### Equality of isomorphism is equality of their underlying morphisms

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  where

  eq-iso-eq-hom-Large-Categoryᵉ :
    (fᵉ gᵉ : iso-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ) →
    hom-iso-Large-Categoryᵉ Cᵉ fᵉ ＝ᵉ hom-iso-Large-Categoryᵉ Cᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-iso-eq-hom-Large-Categoryᵉ =
    eq-iso-eq-hom-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ)
```

### The type of isomorphisms form a set

Theᵉ typeᵉ ofᵉ isomorphismsᵉ betweenᵉ objectsᵉ `xᵉ yᵉ : A`ᵉ isᵉ aᵉ subtypeᵉ ofᵉ theᵉ setᵉ
`homᵉ xᵉ y`ᵉ sinceᵉ beingᵉ anᵉ isomorphismᵉ isᵉ aᵉ proposition.ᵉ

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  where

  is-set-iso-Large-Categoryᵉ : is-setᵉ (iso-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ)
  is-set-iso-Large-Categoryᵉ =
    is-set-iso-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ)

  iso-set-Large-Categoryᵉ : Setᵉ (βᵉ l1ᵉ l1ᵉ ⊔ βᵉ l1ᵉ l2ᵉ ⊔ βᵉ l2ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l2ᵉ)
  iso-set-Large-Categoryᵉ =
    iso-set-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) {Xᵉ = Xᵉ} {Yᵉ}
```

### Isomorphisms are closed under composition

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ}
  {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  {Zᵉ : obj-Large-Categoryᵉ Cᵉ l3ᵉ}
  {gᵉ : hom-Large-Categoryᵉ Cᵉ Yᵉ Zᵉ}
  {fᵉ : hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ}
  where

  hom-comp-is-iso-Large-Categoryᵉ :
    is-iso-Large-Categoryᵉ Cᵉ gᵉ →
    is-iso-Large-Categoryᵉ Cᵉ fᵉ →
    hom-Large-Categoryᵉ Cᵉ Zᵉ Xᵉ
  hom-comp-is-iso-Large-Categoryᵉ =
    hom-comp-is-iso-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ)

  is-section-comp-is-iso-Large-Categoryᵉ :
    (qᵉ : is-iso-Large-Categoryᵉ Cᵉ gᵉ)
    (pᵉ : is-iso-Large-Categoryᵉ Cᵉ fᵉ) →
    comp-hom-Large-Categoryᵉ Cᵉ
      ( comp-hom-Large-Categoryᵉ Cᵉ gᵉ fᵉ)
      ( hom-comp-is-iso-Large-Categoryᵉ qᵉ pᵉ) ＝ᵉ
    id-hom-Large-Categoryᵉ Cᵉ
  is-section-comp-is-iso-Large-Categoryᵉ =
    is-section-comp-is-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)

  is-retraction-comp-is-iso-Large-Categoryᵉ :
    (qᵉ : is-iso-Large-Categoryᵉ Cᵉ gᵉ)
    (pᵉ : is-iso-Large-Categoryᵉ Cᵉ fᵉ) →
    comp-hom-Large-Categoryᵉ Cᵉ
      ( hom-comp-is-iso-Large-Categoryᵉ qᵉ pᵉ)
      ( comp-hom-Large-Categoryᵉ Cᵉ gᵉ fᵉ) ＝ᵉ
    id-hom-Large-Categoryᵉ Cᵉ
  is-retraction-comp-is-iso-Large-Categoryᵉ =
    is-retraction-comp-is-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)

  is-iso-comp-is-iso-Large-Categoryᵉ :
    is-iso-Large-Categoryᵉ Cᵉ gᵉ → is-iso-Large-Categoryᵉ Cᵉ fᵉ →
    is-iso-Large-Categoryᵉ Cᵉ (comp-hom-Large-Categoryᵉ Cᵉ gᵉ fᵉ)
  is-iso-comp-is-iso-Large-Categoryᵉ =
    is-iso-comp-is-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
```

### Composition of isomorphisms

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ}
  {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  {Zᵉ : obj-Large-Categoryᵉ Cᵉ l3ᵉ}
  (gᵉ : iso-Large-Categoryᵉ Cᵉ Yᵉ Zᵉ)
  (fᵉ : iso-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  hom-comp-iso-Large-Categoryᵉ :
    hom-Large-Categoryᵉ Cᵉ Xᵉ Zᵉ
  hom-comp-iso-Large-Categoryᵉ =
    hom-comp-iso-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) gᵉ fᵉ

  is-iso-comp-iso-Large-Categoryᵉ :
    is-iso-Large-Categoryᵉ Cᵉ hom-comp-iso-Large-Categoryᵉ
  is-iso-comp-iso-Large-Categoryᵉ =
    is-iso-comp-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  comp-iso-Large-Categoryᵉ :
    iso-Large-Categoryᵉ Cᵉ Xᵉ Zᵉ
  comp-iso-Large-Categoryᵉ =
    comp-iso-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) gᵉ fᵉ

  hom-inv-comp-iso-Large-Categoryᵉ :
    hom-Large-Categoryᵉ Cᵉ Zᵉ Xᵉ
  hom-inv-comp-iso-Large-Categoryᵉ =
    hom-inv-iso-Large-Categoryᵉ Cᵉ comp-iso-Large-Categoryᵉ

  is-section-inv-comp-iso-Large-Categoryᵉ :
    comp-hom-Large-Categoryᵉ Cᵉ
      ( hom-comp-iso-Large-Categoryᵉ)
      ( hom-inv-comp-iso-Large-Categoryᵉ) ＝ᵉ
    id-hom-Large-Categoryᵉ Cᵉ
  is-section-inv-comp-iso-Large-Categoryᵉ =
    is-section-hom-inv-iso-Large-Categoryᵉ Cᵉ comp-iso-Large-Categoryᵉ

  is-retraction-inv-comp-iso-Large-Categoryᵉ :
    comp-hom-Large-Categoryᵉ Cᵉ
      ( hom-inv-comp-iso-Large-Categoryᵉ)
      ( hom-comp-iso-Large-Categoryᵉ) ＝ᵉ
    id-hom-Large-Categoryᵉ Cᵉ
  is-retraction-inv-comp-iso-Large-Categoryᵉ =
    is-retraction-hom-inv-iso-Large-Categoryᵉ Cᵉ comp-iso-Large-Categoryᵉ
```

### Inverses of isomorphisms are isomorphisms

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  {fᵉ : hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ}
  where

  is-iso-inv-is-iso-Large-Categoryᵉ :
    (pᵉ : is-iso-Large-Categoryᵉ Cᵉ fᵉ) →
    is-iso-Large-Categoryᵉ Cᵉ (hom-inv-iso-Large-Categoryᵉ Cᵉ (fᵉ ,ᵉ pᵉ))
  pr1ᵉ (is-iso-inv-is-iso-Large-Categoryᵉ pᵉ) = fᵉ
  pr1ᵉ (pr2ᵉ (is-iso-inv-is-iso-Large-Categoryᵉ pᵉ)) =
    is-retraction-hom-inv-is-iso-Large-Categoryᵉ Cᵉ fᵉ pᵉ
  pr2ᵉ (pr2ᵉ (is-iso-inv-is-iso-Large-Categoryᵉ pᵉ)) =
    is-section-hom-inv-is-iso-Large-Categoryᵉ Cᵉ fᵉ pᵉ
```

### Inverses of isomorphisms

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  where

  inv-iso-Large-Categoryᵉ :
    iso-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ →
    iso-Large-Categoryᵉ Cᵉ Yᵉ Xᵉ
  pr1ᵉ (inv-iso-Large-Categoryᵉ fᵉ) = hom-inv-iso-Large-Categoryᵉ Cᵉ fᵉ
  pr2ᵉ (inv-iso-Large-Categoryᵉ fᵉ) =
    is-iso-inv-is-iso-Large-Categoryᵉ Cᵉ
      ( is-iso-iso-Large-Categoryᵉ Cᵉ fᵉ)
```

### Composition of isomorphisms satisfies the unit laws

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  (fᵉ : iso-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  left-unit-law-comp-iso-Large-Categoryᵉ :
    comp-iso-Large-Categoryᵉ Cᵉ (id-iso-Large-Categoryᵉ Cᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-iso-Large-Categoryᵉ =
    left-unit-law-comp-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( fᵉ)

  right-unit-law-comp-iso-Large-Categoryᵉ :
    comp-iso-Large-Categoryᵉ Cᵉ fᵉ (id-iso-Large-Categoryᵉ Cᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-iso-Large-Categoryᵉ =
    right-unit-law-comp-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( fᵉ)
```

### Composition of isomorphisms is associative

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ}
  {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  {Zᵉ : obj-Large-Categoryᵉ Cᵉ l3ᵉ}
  {Wᵉ : obj-Large-Categoryᵉ Cᵉ l4ᵉ}
  (hᵉ : iso-Large-Categoryᵉ Cᵉ Zᵉ Wᵉ)
  (gᵉ : iso-Large-Categoryᵉ Cᵉ Yᵉ Zᵉ)
  (fᵉ : iso-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  associative-comp-iso-Large-Categoryᵉ :
    comp-iso-Large-Categoryᵉ Cᵉ (comp-iso-Large-Categoryᵉ Cᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-iso-Large-Categoryᵉ Cᵉ hᵉ (comp-iso-Large-Categoryᵉ Cᵉ gᵉ fᵉ)
  associative-comp-iso-Large-Categoryᵉ =
    associative-comp-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( hᵉ)
      ( gᵉ)
      ( fᵉ)
```

### Composition of isomorphisms satisfies inverse laws

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  (fᵉ : iso-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  left-inverse-law-comp-iso-Large-Categoryᵉ :
    comp-iso-Large-Categoryᵉ Cᵉ (inv-iso-Large-Categoryᵉ Cᵉ fᵉ) fᵉ ＝ᵉ
    id-iso-Large-Categoryᵉ Cᵉ
  left-inverse-law-comp-iso-Large-Categoryᵉ =
    left-inverse-law-comp-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( fᵉ)

  right-inverse-law-comp-iso-Large-Categoryᵉ :
    comp-iso-Large-Categoryᵉ Cᵉ fᵉ (inv-iso-Large-Categoryᵉ Cᵉ fᵉ) ＝ᵉ
    id-iso-Large-Categoryᵉ Cᵉ
  right-inverse-law-comp-iso-Large-Categoryᵉ =
    right-inverse-law-comp-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( fᵉ)
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
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  {fᵉ : hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ}
  (Hᵉ :
    {l3ᵉ : Level} (Zᵉ : obj-Large-Categoryᵉ Cᵉ l3ᵉ) →
    is-equivᵉ (precomp-hom-Large-Categoryᵉ Cᵉ fᵉ Zᵉ))
  where

  hom-inv-is-iso-is-equiv-precomp-hom-Large-Categoryᵉ :
    hom-Large-Categoryᵉ Cᵉ Yᵉ Xᵉ
  hom-inv-is-iso-is-equiv-precomp-hom-Large-Categoryᵉ =
    hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Hᵉ)

  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Large-Categoryᵉ :
    comp-hom-Large-Categoryᵉ Cᵉ
      ( hom-inv-is-iso-is-equiv-precomp-hom-Large-Categoryᵉ)
      ( fᵉ) ＝ᵉ
    id-hom-Large-Categoryᵉ Cᵉ
  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Large-Categoryᵉ =
    is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Hᵉ)

  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Large-Categoryᵉ :
    comp-hom-Large-Categoryᵉ Cᵉ
      ( fᵉ)
      ( hom-inv-is-iso-is-equiv-precomp-hom-Large-Categoryᵉ) ＝ᵉ
    id-hom-Large-Categoryᵉ Cᵉ
  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Large-Categoryᵉ =
    is-section-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Hᵉ)

  is-iso-is-equiv-precomp-hom-Large-Categoryᵉ :
    is-iso-Large-Categoryᵉ Cᵉ fᵉ
  is-iso-is-equiv-precomp-hom-Large-Categoryᵉ =
    is-iso-is-equiv-precomp-hom-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Hᵉ)

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  {fᵉ : hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ}
  (is-iso-fᵉ : is-iso-Large-Categoryᵉ Cᵉ fᵉ)
  (Zᵉ : obj-Large-Categoryᵉ Cᵉ l3ᵉ)
  where

  map-inv-precomp-hom-is-iso-Large-Categoryᵉ :
    hom-Large-Categoryᵉ Cᵉ Xᵉ Zᵉ → hom-Large-Categoryᵉ Cᵉ Yᵉ Zᵉ
  map-inv-precomp-hom-is-iso-Large-Categoryᵉ =
    precomp-hom-Large-Categoryᵉ Cᵉ
      ( hom-inv-is-iso-Large-Categoryᵉ Cᵉ fᵉ is-iso-fᵉ)
      ( Zᵉ)

  is-equiv-precomp-hom-is-iso-Large-Categoryᵉ :
    is-equivᵉ (precomp-hom-Large-Categoryᵉ Cᵉ fᵉ Zᵉ)
  is-equiv-precomp-hom-is-iso-Large-Categoryᵉ =
    is-equiv-precomp-hom-is-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( is-iso-fᵉ)
      ( Zᵉ)

  equiv-precomp-hom-is-iso-Large-Categoryᵉ :
    hom-Large-Categoryᵉ Cᵉ Yᵉ Zᵉ ≃ᵉ hom-Large-Categoryᵉ Cᵉ Xᵉ Zᵉ
  equiv-precomp-hom-is-iso-Large-Categoryᵉ =
    equiv-precomp-hom-is-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( is-iso-fᵉ)
      ( Zᵉ)

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  (fᵉ : iso-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ)
  (Zᵉ : obj-Large-Categoryᵉ Cᵉ l3ᵉ)
  where

  is-equiv-precomp-hom-iso-Large-Categoryᵉ :
    is-equivᵉ (precomp-hom-Large-Categoryᵉ Cᵉ (hom-iso-Large-Categoryᵉ Cᵉ fᵉ) Zᵉ)
  is-equiv-precomp-hom-iso-Large-Categoryᵉ =
    is-equiv-precomp-hom-is-iso-Large-Categoryᵉ Cᵉ
      ( is-iso-iso-Large-Categoryᵉ Cᵉ fᵉ)
      ( Zᵉ)

  equiv-precomp-hom-iso-Large-Categoryᵉ :
    hom-Large-Categoryᵉ Cᵉ Yᵉ Zᵉ ≃ᵉ hom-Large-Categoryᵉ Cᵉ Xᵉ Zᵉ
  equiv-precomp-hom-iso-Large-Categoryᵉ =
    equiv-precomp-hom-is-iso-Large-Categoryᵉ Cᵉ
      ( is-iso-iso-Large-Categoryᵉ Cᵉ fᵉ)
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
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  {fᵉ : hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ}
  (Hᵉ :
    {l3ᵉ : Level} (Zᵉ : obj-Large-Categoryᵉ Cᵉ l3ᵉ) →
    is-equivᵉ (postcomp-hom-Large-Categoryᵉ Cᵉ Zᵉ fᵉ))
  where

  hom-inv-is-iso-is-equiv-postcomp-hom-Large-Categoryᵉ :
    hom-Large-Categoryᵉ Cᵉ Yᵉ Xᵉ
  hom-inv-is-iso-is-equiv-postcomp-hom-Large-Categoryᵉ =
    hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Hᵉ)

  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Categoryᵉ :
    comp-hom-Large-Categoryᵉ Cᵉ
      ( fᵉ)
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Large-Categoryᵉ) ＝ᵉ
    id-hom-Large-Categoryᵉ Cᵉ
  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Categoryᵉ =
    is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Hᵉ)

  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Categoryᵉ :
    comp-hom-Large-Categoryᵉ Cᵉ
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Large-Categoryᵉ)
      ( fᵉ) ＝ᵉ
    id-hom-Large-Categoryᵉ Cᵉ
  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Categoryᵉ =
    is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Hᵉ)

  is-iso-is-equiv-postcomp-hom-Large-Categoryᵉ :
    is-iso-Large-Categoryᵉ Cᵉ fᵉ
  is-iso-is-equiv-postcomp-hom-Large-Categoryᵉ =
    is-iso-is-equiv-postcomp-hom-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Hᵉ)

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  {fᵉ : hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ}
  (is-iso-fᵉ : is-iso-Large-Categoryᵉ Cᵉ fᵉ)
  (Zᵉ : obj-Large-Categoryᵉ Cᵉ l3ᵉ)
  where

  map-inv-postcomp-hom-is-iso-Large-Categoryᵉ :
    hom-Large-Categoryᵉ Cᵉ Zᵉ Yᵉ → hom-Large-Categoryᵉ Cᵉ Zᵉ Xᵉ
  map-inv-postcomp-hom-is-iso-Large-Categoryᵉ =
    postcomp-hom-Large-Categoryᵉ Cᵉ
      ( Zᵉ)
      ( hom-inv-is-iso-Large-Categoryᵉ Cᵉ fᵉ is-iso-fᵉ)

  is-equiv-postcomp-hom-is-iso-Large-Categoryᵉ :
    is-equivᵉ (postcomp-hom-Large-Categoryᵉ Cᵉ Zᵉ fᵉ)
  is-equiv-postcomp-hom-is-iso-Large-Categoryᵉ =
    is-equiv-postcomp-hom-is-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( is-iso-fᵉ)
      ( Zᵉ)

  equiv-postcomp-hom-is-iso-Large-Categoryᵉ :
    hom-Large-Categoryᵉ Cᵉ Zᵉ Xᵉ ≃ᵉ hom-Large-Categoryᵉ Cᵉ Zᵉ Yᵉ
  equiv-postcomp-hom-is-iso-Large-Categoryᵉ =
    equiv-postcomp-hom-is-iso-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( is-iso-fᵉ)
      ( Zᵉ)

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
  (fᵉ : iso-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ)
  (Zᵉ : obj-Large-Categoryᵉ Cᵉ l3ᵉ)
  where

  is-equiv-postcomp-hom-iso-Large-Categoryᵉ :
    is-equivᵉ
      ( postcomp-hom-Large-Categoryᵉ Cᵉ Zᵉ (hom-iso-Large-Categoryᵉ Cᵉ fᵉ))
  is-equiv-postcomp-hom-iso-Large-Categoryᵉ =
    is-equiv-postcomp-hom-is-iso-Large-Categoryᵉ Cᵉ
      ( is-iso-iso-Large-Categoryᵉ Cᵉ fᵉ)
      ( Zᵉ)

  equiv-postcomp-hom-iso-Large-Categoryᵉ :
    hom-Large-Categoryᵉ Cᵉ Zᵉ Xᵉ ≃ᵉ hom-Large-Categoryᵉ Cᵉ Zᵉ Yᵉ
  equiv-postcomp-hom-iso-Large-Categoryᵉ =
    equiv-postcomp-hom-is-iso-Large-Categoryᵉ Cᵉ
      ( is-iso-iso-Large-Categoryᵉ Cᵉ fᵉ)
      ( Zᵉ)
```