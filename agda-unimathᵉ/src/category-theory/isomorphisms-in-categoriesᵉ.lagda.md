# Isomorphisms in categories

```agda
module category-theory.isomorphisms-in-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ **isomorphism**ᵉ in aᵉ [category](category-theory.categories.mdᵉ) `C`ᵉ isᵉ aᵉ
morphismᵉ `fᵉ : xᵉ → y`ᵉ in `C`ᵉ forᵉ whichᵉ thereᵉ existsᵉ aᵉ morphismᵉ `gᵉ : yᵉ → x`ᵉ suchᵉ
thatᵉ `fᵉ ∘ᵉ gᵉ ＝ᵉ id`ᵉ andᵉ `gᵉ ∘ᵉ fᵉ ＝ᵉ id`.ᵉ

## Definitions

### The predicate of being an isomorphism in a category

```agda
is-iso-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) →
  UUᵉ l2ᵉ
is-iso-Categoryᵉ Cᵉ = is-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  {fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ}
  where

  hom-inv-is-iso-Categoryᵉ :
    is-iso-Categoryᵉ Cᵉ fᵉ → hom-Categoryᵉ Cᵉ yᵉ xᵉ
  hom-inv-is-iso-Categoryᵉ =
    hom-inv-is-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  is-section-hom-inv-is-iso-Categoryᵉ :
    (Hᵉ : is-iso-Categoryᵉ Cᵉ fᵉ) →
    comp-hom-Categoryᵉ Cᵉ fᵉ (hom-inv-is-iso-Categoryᵉ Hᵉ) ＝ᵉ
    id-hom-Categoryᵉ Cᵉ
  is-section-hom-inv-is-iso-Categoryᵉ =
    is-section-hom-inv-is-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  is-retraction-hom-inv-is-iso-Categoryᵉ :
    (Hᵉ : is-iso-Categoryᵉ Cᵉ fᵉ) →
    comp-hom-Categoryᵉ Cᵉ (hom-inv-is-iso-Categoryᵉ Hᵉ) fᵉ ＝ᵉ
    id-hom-Categoryᵉ Cᵉ
  is-retraction-hom-inv-is-iso-Categoryᵉ =
    is-retraction-hom-inv-is-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### Isomorphisms in a category

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (xᵉ yᵉ : obj-Categoryᵉ Cᵉ)
  where

  iso-Categoryᵉ : UUᵉ l2ᵉ
  iso-Categoryᵉ = iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) xᵉ yᵉ

module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  (fᵉ : iso-Categoryᵉ Cᵉ xᵉ yᵉ)
  where

  hom-iso-Categoryᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ
  hom-iso-Categoryᵉ = hom-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) fᵉ

  is-iso-iso-Categoryᵉ :
    is-iso-Categoryᵉ Cᵉ hom-iso-Categoryᵉ
  is-iso-iso-Categoryᵉ =
    is-iso-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) fᵉ

  hom-inv-iso-Categoryᵉ : hom-Categoryᵉ Cᵉ yᵉ xᵉ
  hom-inv-iso-Categoryᵉ = hom-inv-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) fᵉ

  is-section-hom-inv-iso-Categoryᵉ :
    ( comp-hom-Categoryᵉ Cᵉ
      ( hom-iso-Categoryᵉ)
      ( hom-inv-iso-Categoryᵉ)) ＝ᵉ
    ( id-hom-Categoryᵉ Cᵉ)
  is-section-hom-inv-iso-Categoryᵉ =
    is-section-hom-inv-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) fᵉ

  is-retraction-hom-inv-iso-Categoryᵉ :
    ( comp-hom-Categoryᵉ Cᵉ
      ( hom-inv-iso-Categoryᵉ)
      ( hom-iso-Categoryᵉ)) ＝ᵉ
    ( id-hom-Categoryᵉ Cᵉ)
  is-retraction-hom-inv-iso-Categoryᵉ =
    is-retraction-hom-inv-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) fᵉ
```

## Examples

### The identity isomorphisms

Forᵉ anyᵉ objectᵉ `xᵉ : A`,ᵉ theᵉ identityᵉ morphismᵉ `id_xᵉ : homᵉ xᵉ x`ᵉ isᵉ anᵉ isomorphismᵉ
fromᵉ `x`ᵉ to `x`ᵉ sinceᵉ `id_xᵉ ∘ᵉ id_xᵉ = id_x`ᵉ (itᵉ isᵉ itsᵉ ownᵉ inverse).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ : obj-Categoryᵉ Cᵉ}
  where

  is-iso-id-hom-Categoryᵉ : is-iso-Categoryᵉ Cᵉ (id-hom-Categoryᵉ Cᵉ {xᵉ})
  is-iso-id-hom-Categoryᵉ = is-iso-id-hom-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  id-iso-Categoryᵉ : iso-Categoryᵉ Cᵉ xᵉ xᵉ
  id-iso-Categoryᵉ = id-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### Equalities induce isomorphisms

Anᵉ equalityᵉ betweenᵉ objectsᵉ `xᵉ yᵉ : A`ᵉ givesᵉ riseᵉ to anᵉ isomorphismᵉ betweenᵉ them.ᵉ
Thisᵉ isᵉ because,ᵉ byᵉ theᵉ J-rule,ᵉ itᵉ isᵉ enoughᵉ to constructᵉ anᵉ isomorphismᵉ givenᵉ
`reflᵉ : xᵉ ＝ᵉ x`,ᵉ fromᵉ `x`ᵉ to itself.ᵉ Weᵉ takeᵉ theᵉ identityᵉ morphismᵉ asᵉ suchᵉ anᵉ
isomorphism.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  iso-eq-Categoryᵉ :
    (xᵉ yᵉ : obj-Categoryᵉ Cᵉ) →
    xᵉ ＝ᵉ yᵉ → iso-Categoryᵉ Cᵉ xᵉ yᵉ
  iso-eq-Categoryᵉ = iso-eq-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  compute-hom-iso-eq-Categoryᵉ :
    {xᵉ yᵉ : obj-Categoryᵉ Cᵉ} →
    (pᵉ : xᵉ ＝ᵉ yᵉ) →
    hom-eq-Categoryᵉ Cᵉ xᵉ yᵉ pᵉ ＝ᵉ
    hom-iso-Categoryᵉ Cᵉ (iso-eq-Categoryᵉ xᵉ yᵉ pᵉ)
  compute-hom-iso-eq-Categoryᵉ =
    compute-hom-iso-eq-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
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
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  where

  is-prop-is-iso-Categoryᵉ :
    (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) → is-propᵉ (is-iso-Categoryᵉ Cᵉ fᵉ)
  is-prop-is-iso-Categoryᵉ =
    is-prop-is-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  is-iso-prop-Categoryᵉ :
    (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) → Propᵉ l2ᵉ
  is-iso-prop-Categoryᵉ =
    is-iso-prop-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### Equality of isomorphism is equality of their underlying morphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  where

  eq-iso-eq-hom-Categoryᵉ :
    (fᵉ gᵉ : iso-Categoryᵉ Cᵉ xᵉ yᵉ) →
    hom-iso-Categoryᵉ Cᵉ fᵉ ＝ᵉ hom-iso-Categoryᵉ Cᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-iso-eq-hom-Categoryᵉ =
    eq-iso-eq-hom-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### The type of isomorphisms form a set

Theᵉ typeᵉ ofᵉ isomorphismsᵉ betweenᵉ objectsᵉ `xᵉ yᵉ : A`ᵉ isᵉ aᵉ
[subtype](foundation-core.subtypes.mdᵉ) ofᵉ theᵉ [set](foundation-core.sets.mdᵉ)
`homᵉ xᵉ y`ᵉ sinceᵉ beingᵉ anᵉ isomorphismᵉ isᵉ aᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  where

  is-set-iso-Categoryᵉ : is-setᵉ (iso-Categoryᵉ Cᵉ xᵉ yᵉ)
  is-set-iso-Categoryᵉ = is-set-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  iso-set-Categoryᵉ : Setᵉ l2ᵉ
  pr1ᵉ iso-set-Categoryᵉ = iso-Categoryᵉ Cᵉ xᵉ yᵉ
  pr2ᵉ iso-set-Categoryᵉ = is-set-iso-Categoryᵉ
```

### Isomorphisms are closed under composition

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ zᵉ : obj-Categoryᵉ Cᵉ}
  {gᵉ : hom-Categoryᵉ Cᵉ yᵉ zᵉ}
  {fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ}
  where

  hom-comp-is-iso-Categoryᵉ :
    is-iso-Categoryᵉ Cᵉ gᵉ →
    is-iso-Categoryᵉ Cᵉ fᵉ →
    hom-Categoryᵉ Cᵉ zᵉ xᵉ
  hom-comp-is-iso-Categoryᵉ =
    hom-comp-is-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  is-section-comp-is-iso-Categoryᵉ :
    (qᵉ : is-iso-Categoryᵉ Cᵉ gᵉ)
    (pᵉ : is-iso-Categoryᵉ Cᵉ fᵉ) →
    comp-hom-Categoryᵉ Cᵉ
      ( comp-hom-Categoryᵉ Cᵉ gᵉ fᵉ)
      ( hom-comp-is-iso-Categoryᵉ qᵉ pᵉ) ＝ᵉ
    id-hom-Categoryᵉ Cᵉ
  is-section-comp-is-iso-Categoryᵉ =
    is-section-comp-is-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  is-retraction-comp-is-iso-Categoryᵉ :
    (qᵉ : is-iso-Categoryᵉ Cᵉ gᵉ)
    (pᵉ : is-iso-Categoryᵉ Cᵉ fᵉ) →
    ( comp-hom-Categoryᵉ Cᵉ
      ( hom-comp-is-iso-Categoryᵉ qᵉ pᵉ)
      ( comp-hom-Categoryᵉ Cᵉ gᵉ fᵉ)) ＝ᵉ
    ( id-hom-Categoryᵉ Cᵉ)
  is-retraction-comp-is-iso-Categoryᵉ =
    is-retraction-comp-is-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  is-iso-comp-is-iso-Categoryᵉ :
    is-iso-Categoryᵉ Cᵉ gᵉ → is-iso-Categoryᵉ Cᵉ fᵉ →
    is-iso-Categoryᵉ Cᵉ (comp-hom-Categoryᵉ Cᵉ gᵉ fᵉ)
  is-iso-comp-is-iso-Categoryᵉ =
    is-iso-comp-is-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### Composition of isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ zᵉ : obj-Categoryᵉ Cᵉ}
  (gᵉ : iso-Categoryᵉ Cᵉ yᵉ zᵉ)
  (fᵉ : iso-Categoryᵉ Cᵉ xᵉ yᵉ)
  where

  hom-comp-iso-Categoryᵉ : hom-Categoryᵉ Cᵉ xᵉ zᵉ
  hom-comp-iso-Categoryᵉ = hom-comp-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) gᵉ fᵉ

  is-iso-comp-iso-Categoryᵉ :
    is-iso-Categoryᵉ Cᵉ hom-comp-iso-Categoryᵉ
  is-iso-comp-iso-Categoryᵉ =
    is-iso-comp-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) gᵉ fᵉ

  comp-iso-Categoryᵉ : iso-Categoryᵉ Cᵉ xᵉ zᵉ
  comp-iso-Categoryᵉ = comp-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) gᵉ fᵉ

  hom-inv-comp-iso-Categoryᵉ : hom-Categoryᵉ Cᵉ zᵉ xᵉ
  hom-inv-comp-iso-Categoryᵉ =
    hom-inv-comp-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) gᵉ fᵉ

  is-section-inv-comp-iso-Categoryᵉ :
    ( comp-hom-Categoryᵉ Cᵉ
      ( hom-comp-iso-Categoryᵉ)
      ( hom-inv-comp-iso-Categoryᵉ)) ＝ᵉ
    ( id-hom-Categoryᵉ Cᵉ)
  is-section-inv-comp-iso-Categoryᵉ =
    is-section-inv-comp-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) gᵉ fᵉ

  is-retraction-inv-comp-iso-Categoryᵉ :
    ( comp-hom-Categoryᵉ Cᵉ
      ( hom-inv-comp-iso-Categoryᵉ)
      ( hom-comp-iso-Categoryᵉ)) ＝ᵉ
    ( id-hom-Categoryᵉ Cᵉ)
  is-retraction-inv-comp-iso-Categoryᵉ =
    is-retraction-inv-comp-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) gᵉ fᵉ
```

### Inverses of isomorphisms are isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  {fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ}
  where

  is-iso-inv-is-iso-Categoryᵉ :
    (pᵉ : is-iso-Categoryᵉ Cᵉ fᵉ) →
    is-iso-Categoryᵉ Cᵉ (hom-inv-iso-Categoryᵉ Cᵉ (fᵉ ,ᵉ pᵉ))
  is-iso-inv-is-iso-Categoryᵉ =
    is-iso-inv-is-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### Inverses of isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  where

  inv-iso-Categoryᵉ :
    iso-Categoryᵉ Cᵉ xᵉ yᵉ → iso-Categoryᵉ Cᵉ yᵉ xᵉ
  inv-iso-Categoryᵉ = inv-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### Groupoid laws of isomorphisms in categories

#### Composition of isomorphisms satisfies the unit laws

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  (fᵉ : iso-Categoryᵉ Cᵉ xᵉ yᵉ)
  where

  left-unit-law-comp-iso-Categoryᵉ :
    comp-iso-Categoryᵉ Cᵉ (id-iso-Categoryᵉ Cᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-iso-Categoryᵉ =
    left-unit-law-comp-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) fᵉ

  right-unit-law-comp-iso-Categoryᵉ :
    comp-iso-Categoryᵉ Cᵉ fᵉ (id-iso-Categoryᵉ Cᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-iso-Categoryᵉ =
    right-unit-law-comp-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) fᵉ
```

#### Composition of isomorphisms is associative

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ zᵉ wᵉ : obj-Categoryᵉ Cᵉ}
  (hᵉ : iso-Categoryᵉ Cᵉ zᵉ wᵉ)
  (gᵉ : iso-Categoryᵉ Cᵉ yᵉ zᵉ)
  (fᵉ : iso-Categoryᵉ Cᵉ xᵉ yᵉ)
  where

  associative-comp-iso-Categoryᵉ :
    ( comp-iso-Categoryᵉ Cᵉ (comp-iso-Categoryᵉ Cᵉ hᵉ gᵉ) fᵉ) ＝ᵉ
    ( comp-iso-Categoryᵉ Cᵉ hᵉ (comp-iso-Categoryᵉ Cᵉ gᵉ fᵉ))
  associative-comp-iso-Categoryᵉ =
    associative-comp-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) hᵉ gᵉ fᵉ
```

#### Composition of isomorphisms satisfies inverse laws

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  (fᵉ : iso-Categoryᵉ Cᵉ xᵉ yᵉ)
  where

  left-inverse-law-comp-iso-Categoryᵉ :
    ( comp-iso-Categoryᵉ Cᵉ (inv-iso-Categoryᵉ Cᵉ fᵉ) fᵉ) ＝ᵉ
    ( id-iso-Categoryᵉ Cᵉ)
  left-inverse-law-comp-iso-Categoryᵉ =
    left-inverse-law-comp-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) fᵉ

  right-inverse-law-comp-iso-Categoryᵉ :
    ( comp-iso-Categoryᵉ Cᵉ fᵉ (inv-iso-Categoryᵉ Cᵉ fᵉ)) ＝ᵉ
    ( id-iso-Categoryᵉ Cᵉ)
  right-inverse-law-comp-iso-Categoryᵉ =
    right-inverse-law-comp-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) fᵉ
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
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  {fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ}
  (Hᵉ : (zᵉ : obj-Categoryᵉ Cᵉ) → is-equivᵉ (precomp-hom-Categoryᵉ Cᵉ fᵉ zᵉ))
  where

  hom-inv-is-iso-is-equiv-precomp-hom-Categoryᵉ : hom-Categoryᵉ Cᵉ yᵉ xᵉ
  hom-inv-is-iso-is-equiv-precomp-hom-Categoryᵉ =
    hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Hᵉ

  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Categoryᵉ :
    ( comp-hom-Categoryᵉ Cᵉ
      ( hom-inv-is-iso-is-equiv-precomp-hom-Categoryᵉ)
      ( fᵉ)) ＝ᵉ
    ( id-hom-Categoryᵉ Cᵉ)
  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Categoryᵉ =
    is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Hᵉ

  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Categoryᵉ :
    ( comp-hom-Categoryᵉ Cᵉ
      ( fᵉ)
      ( hom-inv-is-iso-is-equiv-precomp-hom-Categoryᵉ)) ＝ᵉ
    ( id-hom-Categoryᵉ Cᵉ)
  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Categoryᵉ =
    is-section-hom-inv-is-iso-is-equiv-precomp-hom-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Hᵉ

  is-iso-is-equiv-precomp-hom-Categoryᵉ : is-iso-Categoryᵉ Cᵉ fᵉ
  is-iso-is-equiv-precomp-hom-Categoryᵉ =
    is-iso-is-equiv-precomp-hom-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Hᵉ

module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  {fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ}
  (is-iso-fᵉ : is-iso-Categoryᵉ Cᵉ fᵉ)
  (zᵉ : obj-Categoryᵉ Cᵉ)
  where

  map-inv-precomp-hom-is-iso-Categoryᵉ : hom-Categoryᵉ Cᵉ xᵉ zᵉ → hom-Categoryᵉ Cᵉ yᵉ zᵉ
  map-inv-precomp-hom-is-iso-Categoryᵉ =
    precomp-hom-Categoryᵉ Cᵉ (hom-inv-is-iso-Categoryᵉ Cᵉ is-iso-fᵉ) zᵉ

  is-equiv-precomp-hom-is-iso-Categoryᵉ : is-equivᵉ (precomp-hom-Categoryᵉ Cᵉ fᵉ zᵉ)
  is-equiv-precomp-hom-is-iso-Categoryᵉ =
    is-equiv-precomp-hom-is-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) is-iso-fᵉ zᵉ

  equiv-precomp-hom-is-iso-Categoryᵉ : hom-Categoryᵉ Cᵉ yᵉ zᵉ ≃ᵉ hom-Categoryᵉ Cᵉ xᵉ zᵉ
  equiv-precomp-hom-is-iso-Categoryᵉ =
    equiv-precomp-hom-is-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) is-iso-fᵉ zᵉ

module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  (fᵉ : iso-Categoryᵉ Cᵉ xᵉ yᵉ)
  (zᵉ : obj-Categoryᵉ Cᵉ)
  where

  is-equiv-precomp-hom-iso-Categoryᵉ :
    is-equivᵉ (precomp-hom-Categoryᵉ Cᵉ (hom-iso-Categoryᵉ Cᵉ fᵉ) zᵉ)
  is-equiv-precomp-hom-iso-Categoryᵉ =
    is-equiv-precomp-hom-is-iso-Categoryᵉ Cᵉ (is-iso-iso-Categoryᵉ Cᵉ fᵉ) zᵉ

  equiv-precomp-hom-iso-Categoryᵉ :
    hom-Categoryᵉ Cᵉ yᵉ zᵉ ≃ᵉ hom-Categoryᵉ Cᵉ xᵉ zᵉ
  equiv-precomp-hom-iso-Categoryᵉ =
    equiv-precomp-hom-is-iso-Categoryᵉ Cᵉ (is-iso-iso-Categoryᵉ Cᵉ fᵉ) zᵉ
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
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  {fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ}
  (Hᵉ : (zᵉ : obj-Categoryᵉ Cᵉ) → is-equivᵉ (postcomp-hom-Categoryᵉ Cᵉ fᵉ zᵉ))
  where

  hom-inv-is-iso-is-equiv-postcomp-hom-Categoryᵉ : hom-Categoryᵉ Cᵉ yᵉ xᵉ
  hom-inv-is-iso-is-equiv-postcomp-hom-Categoryᵉ =
    hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Hᵉ

  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Categoryᵉ :
    ( comp-hom-Categoryᵉ Cᵉ
      ( fᵉ)
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Categoryᵉ)) ＝ᵉ
    ( id-hom-Categoryᵉ Cᵉ)
  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Categoryᵉ =
    is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Hᵉ

  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Categoryᵉ :
    comp-hom-Categoryᵉ Cᵉ
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Categoryᵉ)
      ( fᵉ) ＝ᵉ
    ( id-hom-Categoryᵉ Cᵉ)
  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Categoryᵉ =
    is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Hᵉ

  is-iso-is-equiv-postcomp-hom-Categoryᵉ : is-iso-Categoryᵉ Cᵉ fᵉ
  is-iso-is-equiv-postcomp-hom-Categoryᵉ =
    is-iso-is-equiv-postcomp-hom-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Hᵉ

module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  {fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ}
  (is-iso-fᵉ : is-iso-Categoryᵉ Cᵉ fᵉ)
  (zᵉ : obj-Categoryᵉ Cᵉ)
  where

  map-inv-postcomp-hom-is-iso-Categoryᵉ : hom-Categoryᵉ Cᵉ zᵉ yᵉ → hom-Categoryᵉ Cᵉ zᵉ xᵉ
  map-inv-postcomp-hom-is-iso-Categoryᵉ =
    postcomp-hom-Categoryᵉ Cᵉ (hom-inv-is-iso-Categoryᵉ Cᵉ is-iso-fᵉ) zᵉ

  is-equiv-postcomp-hom-is-iso-Categoryᵉ : is-equivᵉ (postcomp-hom-Categoryᵉ Cᵉ fᵉ zᵉ)
  is-equiv-postcomp-hom-is-iso-Categoryᵉ =
    is-equiv-postcomp-hom-is-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) is-iso-fᵉ zᵉ

  equiv-postcomp-hom-is-iso-Categoryᵉ : hom-Categoryᵉ Cᵉ zᵉ xᵉ ≃ᵉ hom-Categoryᵉ Cᵉ zᵉ yᵉ
  equiv-postcomp-hom-is-iso-Categoryᵉ =
    equiv-postcomp-hom-is-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) is-iso-fᵉ zᵉ

module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  (fᵉ : iso-Categoryᵉ Cᵉ xᵉ yᵉ)
  (zᵉ : obj-Categoryᵉ Cᵉ)
  where

  is-equiv-postcomp-hom-iso-Categoryᵉ :
    is-equivᵉ (postcomp-hom-Categoryᵉ Cᵉ (hom-iso-Categoryᵉ Cᵉ fᵉ) zᵉ)
  is-equiv-postcomp-hom-iso-Categoryᵉ =
    is-equiv-postcomp-hom-is-iso-Categoryᵉ Cᵉ (is-iso-iso-Categoryᵉ Cᵉ fᵉ) zᵉ

  equiv-postcomp-hom-iso-Categoryᵉ : hom-Categoryᵉ Cᵉ zᵉ xᵉ ≃ᵉ hom-Categoryᵉ Cᵉ zᵉ yᵉ
  equiv-postcomp-hom-iso-Categoryᵉ =
    equiv-postcomp-hom-is-iso-Categoryᵉ Cᵉ (is-iso-iso-Categoryᵉ Cᵉ fᵉ) zᵉ
```

### When `hom x y` is a proposition, the type of isomorphisms from `x` to `y` is a proposition

Theᵉ typeᵉ ofᵉ isomorphismsᵉ betweenᵉ objectsᵉ `xᵉ yᵉ : A`ᵉ isᵉ aᵉ subtypeᵉ ofᵉ `homᵉ xᵉ y`,ᵉ soᵉ
whenᵉ thisᵉ typeᵉ isᵉ aᵉ proposition,ᵉ thenᵉ theᵉ typeᵉ ofᵉ isomorphismsᵉ fromᵉ `x`ᵉ to `y`ᵉ
formᵉ aᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  where

  is-prop-iso-is-prop-hom-Categoryᵉ :
    is-propᵉ (hom-Categoryᵉ Cᵉ xᵉ yᵉ) → is-propᵉ (iso-Categoryᵉ Cᵉ xᵉ yᵉ)
  is-prop-iso-is-prop-hom-Categoryᵉ =
    is-prop-iso-is-prop-hom-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  iso-prop-is-prop-hom-Categoryᵉ :
    is-propᵉ (hom-Categoryᵉ Cᵉ xᵉ yᵉ) → Propᵉ l2ᵉ
  iso-prop-is-prop-hom-Categoryᵉ =
    iso-prop-is-prop-hom-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### When `hom x y` and `hom y x` are propositions, it suffices to provide a morphism in each direction to construct an isomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  where

  is-iso-is-prop-hom-Category'ᵉ :
    is-propᵉ (hom-Categoryᵉ Cᵉ xᵉ xᵉ) →
    is-propᵉ (hom-Categoryᵉ Cᵉ yᵉ yᵉ) →
    (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) →
    hom-Categoryᵉ Cᵉ yᵉ xᵉ →
    is-iso-Categoryᵉ Cᵉ fᵉ
  is-iso-is-prop-hom-Category'ᵉ =
    is-iso-is-prop-hom-Precategory'ᵉ (precategory-Categoryᵉ Cᵉ)

  iso-is-prop-hom-Category'ᵉ :
    is-propᵉ (hom-Categoryᵉ Cᵉ xᵉ xᵉ) →
    is-propᵉ (hom-Categoryᵉ Cᵉ yᵉ yᵉ) →
    hom-Categoryᵉ Cᵉ xᵉ yᵉ →
    hom-Categoryᵉ Cᵉ yᵉ xᵉ →
    iso-Categoryᵉ Cᵉ xᵉ yᵉ
  iso-is-prop-hom-Category'ᵉ =
    iso-is-prop-hom-Precategory'ᵉ (precategory-Categoryᵉ Cᵉ)

  is-iso-is-prop-hom-Categoryᵉ :
    ((x'ᵉ y'ᵉ : obj-Categoryᵉ Cᵉ) → is-propᵉ (hom-Categoryᵉ Cᵉ x'ᵉ y'ᵉ)) →
    (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) → hom-Categoryᵉ Cᵉ yᵉ xᵉ →
    is-iso-Categoryᵉ Cᵉ fᵉ
  is-iso-is-prop-hom-Categoryᵉ =
    is-iso-is-prop-hom-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  iso-is-prop-hom-Categoryᵉ :
    ((x'ᵉ y'ᵉ : obj-Categoryᵉ Cᵉ) → is-propᵉ (hom-Categoryᵉ Cᵉ x'ᵉ y'ᵉ)) →
    hom-Categoryᵉ Cᵉ xᵉ yᵉ →
    hom-Categoryᵉ Cᵉ yᵉ xᵉ →
    iso-Categoryᵉ Cᵉ xᵉ yᵉ
  iso-is-prop-hom-Categoryᵉ =
    iso-is-prop-hom-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### Functoriality of `iso-eq`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ zᵉ : obj-Categoryᵉ Cᵉ}
  where

  preserves-concat-iso-eq-Categoryᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    iso-eq-Categoryᵉ Cᵉ xᵉ zᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ
    comp-iso-Categoryᵉ Cᵉ (iso-eq-Categoryᵉ Cᵉ yᵉ zᵉ qᵉ) (iso-eq-Categoryᵉ Cᵉ xᵉ yᵉ pᵉ)
  preserves-concat-iso-eq-Categoryᵉ =
    preserves-concat-iso-eq-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### Extensionality of the type of objects in a category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  extensionality-obj-Categoryᵉ :
    (xᵉ yᵉ : obj-Categoryᵉ Cᵉ) → (xᵉ ＝ᵉ yᵉ) ≃ᵉ iso-Categoryᵉ Cᵉ xᵉ yᵉ
  pr1ᵉ (extensionality-obj-Categoryᵉ xᵉ yᵉ) = iso-eq-Categoryᵉ Cᵉ xᵉ yᵉ
  pr2ᵉ (extensionality-obj-Categoryᵉ xᵉ yᵉ) = is-category-Categoryᵉ Cᵉ xᵉ yᵉ

  eq-iso-Categoryᵉ :
    {xᵉ yᵉ : obj-Categoryᵉ Cᵉ} → iso-Categoryᵉ Cᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-iso-Categoryᵉ {xᵉ} {yᵉ} = map-inv-equivᵉ (extensionality-obj-Categoryᵉ xᵉ yᵉ)

  is-section-eq-iso-Categoryᵉ :
    {xᵉ yᵉ : obj-Categoryᵉ Cᵉ} (fᵉ : iso-Categoryᵉ Cᵉ xᵉ yᵉ) →
    iso-eq-Categoryᵉ Cᵉ xᵉ yᵉ (eq-iso-Categoryᵉ fᵉ) ＝ᵉ fᵉ
  is-section-eq-iso-Categoryᵉ {xᵉ} {yᵉ} =
    is-section-map-inv-equivᵉ (extensionality-obj-Categoryᵉ xᵉ yᵉ)

  is-retraction-eq-iso-Categoryᵉ :
    {xᵉ yᵉ : obj-Categoryᵉ Cᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
    eq-iso-Categoryᵉ (iso-eq-Categoryᵉ Cᵉ xᵉ yᵉ pᵉ) ＝ᵉ pᵉ
  is-retraction-eq-iso-Categoryᵉ {xᵉ} {yᵉ} =
    is-retraction-map-inv-equivᵉ (extensionality-obj-Categoryᵉ xᵉ yᵉ)

module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Xᵉ : obj-Categoryᵉ Cᵉ)
  where

  is-torsorial-iso-Categoryᵉ :
    is-torsorialᵉ (iso-Categoryᵉ Cᵉ Xᵉ)
  is-torsorial-iso-Categoryᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (obj-Categoryᵉ Cᵉ) (Xᵉ ＝ᵉ_))
      ( equiv-totᵉ (extensionality-obj-Categoryᵉ Cᵉ Xᵉ))
      ( is-torsorial-Idᵉ Xᵉ)

  is-torsorial-iso-Category'ᵉ :
    is-torsorialᵉ (λ Yᵉ → iso-Categoryᵉ Cᵉ Yᵉ Xᵉ)
  is-torsorial-iso-Category'ᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (obj-Categoryᵉ Cᵉ) (_＝ᵉ Xᵉ))
      ( equiv-totᵉ (λ Yᵉ → extensionality-obj-Categoryᵉ Cᵉ Yᵉ Xᵉ))
      ( is-torsorial-Id'ᵉ Xᵉ)
```

### Functoriality of `eq-iso`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  preserves-comp-eq-iso-Categoryᵉ :
    { xᵉ yᵉ zᵉ : obj-Categoryᵉ Cᵉ}
    ( gᵉ : iso-Categoryᵉ Cᵉ yᵉ zᵉ)
    ( fᵉ : iso-Categoryᵉ Cᵉ xᵉ yᵉ) →
    ( eq-iso-Categoryᵉ Cᵉ (comp-iso-Categoryᵉ Cᵉ gᵉ fᵉ)) ＝ᵉ
    ( eq-iso-Categoryᵉ Cᵉ fᵉ ∙ᵉ eq-iso-Categoryᵉ Cᵉ gᵉ)
  preserves-comp-eq-iso-Categoryᵉ gᵉ fᵉ =
    ( apᵉ
      ( eq-iso-Categoryᵉ Cᵉ)
      ( ap-binaryᵉ
        ( comp-iso-Categoryᵉ Cᵉ)
        ( invᵉ (is-section-eq-iso-Categoryᵉ Cᵉ gᵉ))
        ( invᵉ (is-section-eq-iso-Categoryᵉ Cᵉ fᵉ)))) ∙ᵉ
    ( apᵉ
      ( eq-iso-Categoryᵉ Cᵉ)
      ( invᵉ
        ( preserves-concat-iso-eq-Categoryᵉ Cᵉ
          ( eq-iso-Categoryᵉ Cᵉ fᵉ)
          ( eq-iso-Categoryᵉ Cᵉ gᵉ)))) ∙ᵉ
    ( is-retraction-eq-iso-Categoryᵉ Cᵉ
      ( eq-iso-Categoryᵉ Cᵉ fᵉ ∙ᵉ eq-iso-Categoryᵉ Cᵉ gᵉ))
```