# Large categories

```agda
module category-theory.large-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.isomorphisms-in-large-precategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **largeᵉ category**ᵉ in Homotopyᵉ Typeᵉ Theoryᵉ isᵉ aᵉ
[largeᵉ precategory](category-theory.large-precategories.mdᵉ) forᵉ whichᵉ theᵉ
[identities](foundation-core.identity-types.mdᵉ) betweenᵉ theᵉ objectsᵉ areᵉ theᵉ
[isomorphisms](category-theory.isomorphisms-in-large-categories.md).ᵉ Moreᵉ
specifically,ᵉ anᵉ equalityᵉ betweenᵉ objectsᵉ givesᵉ riseᵉ to anᵉ isomorphismᵉ betweenᵉ
them,ᵉ byᵉ theᵉ J-rule.ᵉ Aᵉ largeᵉ precategoryᵉ isᵉ aᵉ largeᵉ categoryᵉ ifᵉ thisᵉ functionᵉ isᵉ
anᵉ equivalence.ᵉ Noteᵉ thatᵉ beingᵉ aᵉ largeᵉ categoryᵉ isᵉ aᵉ
[proposition](foundation-core.propositions.mdᵉ) sinceᵉ `is-equiv`ᵉ isᵉ aᵉ
proposition.ᵉ

## Definition

### The predicate on large precategories of being a large category

```agda
is-large-category-Large-Precategoryᵉ :
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} →
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) → UUωᵉ
is-large-category-Large-Precategoryᵉ Cᵉ =
  {lᵉ : Level} (Xᵉ Yᵉ : obj-Large-Precategoryᵉ Cᵉ lᵉ) →
  is-equivᵉ (iso-eq-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
```

### The large type of large categories

```agda
record
  Large-Categoryᵉ (αᵉ : Level → Level) (βᵉ : Level → Level → Level) : UUωᵉ
  where
  constructor
    make-Large-Categoryᵉ

  field
    large-precategory-Large-Categoryᵉ :
      Large-Precategoryᵉ αᵉ βᵉ

    is-large-category-Large-Categoryᵉ :
      is-large-category-Large-Precategoryᵉ large-precategory-Large-Categoryᵉ

open Large-Categoryᵉ public
```

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ)
  where

  obj-Large-Categoryᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)
  obj-Large-Categoryᵉ =
    obj-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ)

  hom-set-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ : Level} →
    obj-Large-Categoryᵉ l1ᵉ →
    obj-Large-Categoryᵉ l2ᵉ →
    Setᵉ (βᵉ l1ᵉ l2ᵉ)
  hom-set-Large-Categoryᵉ =
    hom-set-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ)

  hom-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Categoryᵉ l1ᵉ)
    (Yᵉ : obj-Large-Categoryᵉ l2ᵉ) →
    UUᵉ (βᵉ l1ᵉ l2ᵉ)
  hom-Large-Categoryᵉ Xᵉ Yᵉ = type-Setᵉ (hom-set-Large-Categoryᵉ Xᵉ Yᵉ)

  is-set-hom-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Categoryᵉ l1ᵉ)
    (Yᵉ : obj-Large-Categoryᵉ l2ᵉ) →
    is-setᵉ (hom-Large-Categoryᵉ Xᵉ Yᵉ)
  is-set-hom-Large-Categoryᵉ Xᵉ Yᵉ =
    is-set-type-Setᵉ (hom-set-Large-Categoryᵉ Xᵉ Yᵉ)

  comp-hom-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    {Xᵉ : obj-Large-Categoryᵉ l1ᵉ}
    {Yᵉ : obj-Large-Categoryᵉ l2ᵉ}
    {Zᵉ : obj-Large-Categoryᵉ l3ᵉ} →
    hom-Large-Categoryᵉ Yᵉ Zᵉ →
    hom-Large-Categoryᵉ Xᵉ Yᵉ →
    hom-Large-Categoryᵉ Xᵉ Zᵉ
  comp-hom-Large-Categoryᵉ =
    comp-hom-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ)

  id-hom-Large-Categoryᵉ :
    {l1ᵉ : Level} {Xᵉ : obj-Large-Categoryᵉ l1ᵉ} →
    hom-Large-Categoryᵉ Xᵉ Xᵉ
  id-hom-Large-Categoryᵉ =
    id-hom-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ)

  involutive-eq-associative-comp-hom-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Xᵉ : obj-Large-Categoryᵉ l1ᵉ}
    {Yᵉ : obj-Large-Categoryᵉ l2ᵉ}
    {Zᵉ : obj-Large-Categoryᵉ l3ᵉ}
    {Wᵉ : obj-Large-Categoryᵉ l4ᵉ} →
    (hᵉ : hom-Large-Categoryᵉ Zᵉ Wᵉ)
    (gᵉ : hom-Large-Categoryᵉ Yᵉ Zᵉ)
    (fᵉ : hom-Large-Categoryᵉ Xᵉ Yᵉ) →
    ( comp-hom-Large-Categoryᵉ (comp-hom-Large-Categoryᵉ hᵉ gᵉ) fᵉ) ＝ⁱᵉ
    ( comp-hom-Large-Categoryᵉ hᵉ (comp-hom-Large-Categoryᵉ gᵉ fᵉ))
  involutive-eq-associative-comp-hom-Large-Categoryᵉ =
    involutive-eq-associative-comp-hom-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)

  associative-comp-hom-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Xᵉ : obj-Large-Categoryᵉ l1ᵉ}
    {Yᵉ : obj-Large-Categoryᵉ l2ᵉ}
    {Zᵉ : obj-Large-Categoryᵉ l3ᵉ}
    {Wᵉ : obj-Large-Categoryᵉ l4ᵉ} →
    (hᵉ : hom-Large-Categoryᵉ Zᵉ Wᵉ)
    (gᵉ : hom-Large-Categoryᵉ Yᵉ Zᵉ)
    (fᵉ : hom-Large-Categoryᵉ Xᵉ Yᵉ) →
    ( comp-hom-Large-Categoryᵉ (comp-hom-Large-Categoryᵉ hᵉ gᵉ) fᵉ) ＝ᵉ
    ( comp-hom-Large-Categoryᵉ hᵉ (comp-hom-Large-Categoryᵉ gᵉ fᵉ))
  associative-comp-hom-Large-Categoryᵉ =
    associative-comp-hom-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ)

  left-unit-law-comp-hom-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {Xᵉ : obj-Large-Categoryᵉ l1ᵉ}
    {Yᵉ : obj-Large-Categoryᵉ l2ᵉ}
    (fᵉ : hom-Large-Categoryᵉ Xᵉ Yᵉ) →
    ( comp-hom-Large-Categoryᵉ id-hom-Large-Categoryᵉ fᵉ) ＝ᵉ fᵉ
  left-unit-law-comp-hom-Large-Categoryᵉ =
    left-unit-law-comp-hom-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)

  right-unit-law-comp-hom-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {Xᵉ : obj-Large-Categoryᵉ l1ᵉ}
    {Yᵉ : obj-Large-Categoryᵉ l2ᵉ}
    (fᵉ : hom-Large-Categoryᵉ Xᵉ Yᵉ) →
    ( comp-hom-Large-Categoryᵉ fᵉ id-hom-Large-Categoryᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Large-Categoryᵉ =
    right-unit-law-comp-hom-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)

  ap-comp-hom-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    {Xᵉ : obj-Large-Categoryᵉ l1ᵉ}
    {Yᵉ : obj-Large-Categoryᵉ l2ᵉ}
    {Zᵉ : obj-Large-Categoryᵉ l3ᵉ}
    {gᵉ g'ᵉ : hom-Large-Categoryᵉ Yᵉ Zᵉ} (pᵉ : gᵉ ＝ᵉ g'ᵉ)
    {fᵉ f'ᵉ : hom-Large-Categoryᵉ Xᵉ Yᵉ} (qᵉ : fᵉ ＝ᵉ f'ᵉ) →
    comp-hom-Large-Categoryᵉ gᵉ fᵉ ＝ᵉ comp-hom-Large-Categoryᵉ g'ᵉ f'ᵉ
  ap-comp-hom-Large-Categoryᵉ pᵉ qᵉ =
    ap-binaryᵉ comp-hom-Large-Categoryᵉ pᵉ qᵉ

  comp-hom-Large-Category'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    {Xᵉ : obj-Large-Categoryᵉ l1ᵉ}
    {Yᵉ : obj-Large-Categoryᵉ l2ᵉ}
    {Zᵉ : obj-Large-Categoryᵉ l3ᵉ} →
    hom-Large-Categoryᵉ Xᵉ Yᵉ →
    hom-Large-Categoryᵉ Yᵉ Zᵉ →
    hom-Large-Categoryᵉ Xᵉ Zᵉ
  comp-hom-Large-Category'ᵉ fᵉ gᵉ = comp-hom-Large-Categoryᵉ gᵉ fᵉ
```

### Categories obtained from large categories

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  (is-large-category-Cᵉ : is-large-category-Large-Precategoryᵉ Cᵉ)
  where

  is-category-is-large-category-Large-Precategoryᵉ :
    (lᵉ : Level) → is-category-Precategoryᵉ (precategory-Large-Precategoryᵉ Cᵉ lᵉ)
  is-category-is-large-category-Large-Precategoryᵉ lᵉ Xᵉ Yᵉ =
    is-equiv-htpyᵉ
      ( iso-eq-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
      ( compute-iso-eq-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
      ( is-large-category-Cᵉ Xᵉ Yᵉ)

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ)
  where

  precategory-Large-Categoryᵉ : (lᵉ : Level) → Precategoryᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  precategory-Large-Categoryᵉ =
    precategory-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ)

  is-category-Large-Categoryᵉ :
    (lᵉ : Level) → is-category-Precategoryᵉ (precategory-Large-Categoryᵉ lᵉ)
  is-category-Large-Categoryᵉ =
    is-category-is-large-category-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( is-large-category-Large-Categoryᵉ Cᵉ)

  category-Large-Categoryᵉ : (lᵉ : Level) → Categoryᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  pr1ᵉ (category-Large-Categoryᵉ lᵉ) = precategory-Large-Categoryᵉ lᵉ
  pr2ᵉ (category-Large-Categoryᵉ lᵉ) = is-category-Large-Categoryᵉ lᵉ
```

### Equalities induce morphisms

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ)
  {l1ᵉ : Level} (Xᵉ Yᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ)
  where

  hom-eq-Large-Categoryᵉ : Xᵉ ＝ᵉ Yᵉ → hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ
  hom-eq-Large-Categoryᵉ =
    hom-eq-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) Xᵉ Yᵉ

  hom-inv-eq-Large-Categoryᵉ : Xᵉ ＝ᵉ Yᵉ → hom-Large-Categoryᵉ Cᵉ Yᵉ Xᵉ
  hom-inv-eq-Large-Categoryᵉ =
    hom-inv-eq-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) Xᵉ Yᵉ

  compute-hom-eq-Large-Categoryᵉ :
    hom-eq-Categoryᵉ (category-Large-Categoryᵉ Cᵉ l1ᵉ) Xᵉ Yᵉ ~ᵉ hom-eq-Large-Categoryᵉ
  compute-hom-eq-Large-Categoryᵉ =
    compute-hom-eq-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) Xᵉ Yᵉ
```

### Pre- and postcomposing by a morphism

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ)
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  where

  precomp-hom-Large-Categoryᵉ :
    {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ}
    {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
    (fᵉ : hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ) →
    (Zᵉ : obj-Large-Categoryᵉ Cᵉ l3ᵉ) →
    hom-Large-Categoryᵉ Cᵉ Yᵉ Zᵉ → hom-Large-Categoryᵉ Cᵉ Xᵉ Zᵉ
  precomp-hom-Large-Categoryᵉ fᵉ Zᵉ gᵉ =
    comp-hom-Large-Categoryᵉ Cᵉ gᵉ fᵉ

  postcomp-hom-Large-Categoryᵉ :
    (Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ)
    {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
    {Zᵉ : obj-Large-Categoryᵉ Cᵉ l3ᵉ}
    (fᵉ : hom-Large-Categoryᵉ Cᵉ Yᵉ Zᵉ) →
    hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ → hom-Large-Categoryᵉ Cᵉ Xᵉ Zᵉ
  postcomp-hom-Large-Categoryᵉ Xᵉ fᵉ gᵉ =
    comp-hom-Large-Categoryᵉ Cᵉ fᵉ gᵉ
```