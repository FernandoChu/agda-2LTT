# Strict categories

```agda
module category-theory.strict-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.nonunital-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.preunivalent-categoriesᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "strictᵉ category"ᵉ Agda=Strict-Categoryᵉ}} isᵉ aᵉ
[precategory](category-theory.precategories.mdᵉ) forᵉ whichᵉ theᵉ typeᵉ ofᵉ objectsᵉ
formᵉ aᵉ [set](foundation-core.sets.md).ᵉ Suchᵉ categoriesᵉ areᵉ theᵉ set-theoreticᵉ
analogueᵉ to [(univalentᵉ) categories](category-theory.categories.md),ᵉ andᵉ haveᵉ
theᵉ disadvantagesᵉ thatᵉ strictᵉ categoricalᵉ constructionsᵉ mayᵉ generallyᵉ failᵉ to beᵉ
invariantᵉ underᵉ equivalences,ᵉ andᵉ thatᵉ theᵉ
([essentiallyᵉ surjective](category-theory.essentially-surjective-functors-precategories.md)/[fully-faithful](category-theory.fully-faithful-functors-precategories.md))-factorizationᵉ
systemᵉ onᵉ [functors](category-theory.functors-precategories.mdᵉ) requiresᵉ theᵉ
[axiomᵉ ofᵉ choice](foundation.axiom-of-choice.md).ᵉ

## Definitions

### The predicate on precategories of being a strict category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-strict-category-prop-Precategoryᵉ : Propᵉ l1ᵉ
  is-strict-category-prop-Precategoryᵉ =
    is-set-Propᵉ (obj-Precategoryᵉ Cᵉ)

  is-strict-category-Precategoryᵉ : UUᵉ l1ᵉ
  is-strict-category-Precategoryᵉ =
    type-Propᵉ is-strict-category-prop-Precategoryᵉ
```

### The predicate on preunivalent categories of being a strict category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Preunivalent-Categoryᵉ l1ᵉ l2ᵉ)
  where

  is-strict-category-prop-Preunivalent-Categoryᵉ : Propᵉ l1ᵉ
  is-strict-category-prop-Preunivalent-Categoryᵉ =
    is-strict-category-prop-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)

  is-strict-category-Preunivalent-Categoryᵉ : UUᵉ l1ᵉ
  is-strict-category-Preunivalent-Categoryᵉ =
    type-Propᵉ is-strict-category-prop-Preunivalent-Categoryᵉ
```

### The predicate on categories of being a strict category

Weᵉ noteᵉ thatᵉ [(univalentᵉ) categories](category-theory.categories.mdᵉ) thatᵉ areᵉ
strictᵉ formᵉ aᵉ veryᵉ restrictedᵉ classᵉ ofᵉ strictᵉ categoriesᵉ where everyᵉ
[isomorphism](category-theory.isomorphisms-in-categories.md)-setᵉ isᵉ aᵉ
[proposition](foundation-core.propositions.md).ᵉ Suchᵉ aᵉ categoryᵉ isᵉ calledᵉ
[gaunt](category-theory.gaunt-categories.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  is-strict-category-prop-Categoryᵉ : Propᵉ l1ᵉ
  is-strict-category-prop-Categoryᵉ =
    is-strict-category-prop-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  is-strict-category-Categoryᵉ : UUᵉ l1ᵉ
  is-strict-category-Categoryᵉ = type-Propᵉ is-strict-category-prop-Categoryᵉ
```

### The type of strict categories

```agda
Strict-Categoryᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Strict-Categoryᵉ l1ᵉ l2ᵉ = Σᵉ (Precategoryᵉ l1ᵉ l2ᵉ) is-strict-category-Precategoryᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Strict-Categoryᵉ l1ᵉ l2ᵉ)
  where

  precategory-Strict-Categoryᵉ : Precategoryᵉ l1ᵉ l2ᵉ
  precategory-Strict-Categoryᵉ = pr1ᵉ Cᵉ

  obj-Strict-Categoryᵉ : UUᵉ l1ᵉ
  obj-Strict-Categoryᵉ = obj-Precategoryᵉ precategory-Strict-Categoryᵉ

  is-set-obj-Strict-Categoryᵉ : is-setᵉ obj-Strict-Categoryᵉ
  is-set-obj-Strict-Categoryᵉ = pr2ᵉ Cᵉ

  hom-set-Strict-Categoryᵉ : obj-Strict-Categoryᵉ → obj-Strict-Categoryᵉ → Setᵉ l2ᵉ
  hom-set-Strict-Categoryᵉ = hom-set-Precategoryᵉ precategory-Strict-Categoryᵉ

  hom-Strict-Categoryᵉ : obj-Strict-Categoryᵉ → obj-Strict-Categoryᵉ → UUᵉ l2ᵉ
  hom-Strict-Categoryᵉ = hom-Precategoryᵉ precategory-Strict-Categoryᵉ

  is-set-hom-Strict-Categoryᵉ :
    (xᵉ yᵉ : obj-Strict-Categoryᵉ) → is-setᵉ (hom-Strict-Categoryᵉ xᵉ yᵉ)
  is-set-hom-Strict-Categoryᵉ =
    is-set-hom-Precategoryᵉ precategory-Strict-Categoryᵉ

  comp-hom-Strict-Categoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Strict-Categoryᵉ} →
    hom-Strict-Categoryᵉ yᵉ zᵉ → hom-Strict-Categoryᵉ xᵉ yᵉ → hom-Strict-Categoryᵉ xᵉ zᵉ
  comp-hom-Strict-Categoryᵉ = comp-hom-Precategoryᵉ precategory-Strict-Categoryᵉ

  associative-comp-hom-Strict-Categoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Strict-Categoryᵉ}
    (hᵉ : hom-Strict-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Strict-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Strict-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Strict-Categoryᵉ (comp-hom-Strict-Categoryᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Strict-Categoryᵉ hᵉ (comp-hom-Strict-Categoryᵉ gᵉ fᵉ)
  associative-comp-hom-Strict-Categoryᵉ =
    associative-comp-hom-Precategoryᵉ precategory-Strict-Categoryᵉ

  associative-composition-operation-Strict-Categoryᵉ :
    associative-composition-operation-binary-family-Setᵉ hom-set-Strict-Categoryᵉ
  associative-composition-operation-Strict-Categoryᵉ =
    associative-composition-operation-Precategoryᵉ precategory-Strict-Categoryᵉ

  id-hom-Strict-Categoryᵉ : {xᵉ : obj-Strict-Categoryᵉ} → hom-Strict-Categoryᵉ xᵉ xᵉ
  id-hom-Strict-Categoryᵉ = id-hom-Precategoryᵉ precategory-Strict-Categoryᵉ

  left-unit-law-comp-hom-Strict-Categoryᵉ :
    {xᵉ yᵉ : obj-Strict-Categoryᵉ} (fᵉ : hom-Strict-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Strict-Categoryᵉ id-hom-Strict-Categoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Strict-Categoryᵉ =
    left-unit-law-comp-hom-Precategoryᵉ precategory-Strict-Categoryᵉ

  right-unit-law-comp-hom-Strict-Categoryᵉ :
    {xᵉ yᵉ : obj-Strict-Categoryᵉ} (fᵉ : hom-Strict-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Strict-Categoryᵉ fᵉ id-hom-Strict-Categoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-Strict-Categoryᵉ =
    right-unit-law-comp-hom-Precategoryᵉ precategory-Strict-Categoryᵉ

  is-unital-composition-operation-Strict-Categoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      hom-set-Strict-Categoryᵉ
      comp-hom-Strict-Categoryᵉ
  is-unital-composition-operation-Strict-Categoryᵉ =
    is-unital-composition-operation-Precategoryᵉ precategory-Strict-Categoryᵉ

  is-strict-category-Strict-Categoryᵉ :
    is-strict-category-Precategoryᵉ precategory-Strict-Categoryᵉ
  is-strict-category-Strict-Categoryᵉ = pr2ᵉ Cᵉ
```

### The underlying nonunital precategory of a strict category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Strict-Categoryᵉ l1ᵉ l2ᵉ)
  where

  nonunital-precategory-Strict-Categoryᵉ : Nonunital-Precategoryᵉ l1ᵉ l2ᵉ
  nonunital-precategory-Strict-Categoryᵉ =
    nonunital-precategory-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ)
```

### The underlying preunivalent category of a strict category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Strict-Categoryᵉ l1ᵉ l2ᵉ)
  where

  abstract
    is-preunivalent-Strict-Categoryᵉ :
      is-preunivalent-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ)
    is-preunivalent-Strict-Categoryᵉ xᵉ yᵉ =
      is-emb-is-injectiveᵉ
        ( is-set-type-subtypeᵉ
          ( is-iso-prop-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ))
          ( is-set-hom-Strict-Categoryᵉ Cᵉ xᵉ yᵉ))
        ( λ _ → eq-is-propᵉ (is-set-obj-Strict-Categoryᵉ Cᵉ xᵉ yᵉ))

  preunivalent-category-Strict-Categoryᵉ : Preunivalent-Categoryᵉ l1ᵉ l2ᵉ
  pr1ᵉ preunivalent-category-Strict-Categoryᵉ = precategory-Strict-Categoryᵉ Cᵉ
  pr2ᵉ preunivalent-category-Strict-Categoryᵉ = is-preunivalent-Strict-Categoryᵉ
```

### The total hom-set of a strict category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Strict-Categoryᵉ l1ᵉ l2ᵉ)
  where

  total-hom-Strict-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  total-hom-Strict-Categoryᵉ =
    total-hom-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ)

  obj-total-hom-Strict-Categoryᵉ :
    total-hom-Strict-Categoryᵉ → obj-Strict-Categoryᵉ Cᵉ ×ᵉ obj-Strict-Categoryᵉ Cᵉ
  obj-total-hom-Strict-Categoryᵉ =
    obj-total-hom-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ)

  is-set-total-hom-Strict-Categoryᵉ :
    is-setᵉ total-hom-Strict-Categoryᵉ
  is-set-total-hom-Strict-Categoryᵉ =
    is-trunc-total-hom-is-trunc-obj-Precategoryᵉ
      ( precategory-Strict-Categoryᵉ Cᵉ)
      ( is-set-obj-Strict-Categoryᵉ Cᵉ)

  total-hom-set-Strict-Categoryᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  total-hom-set-Strict-Categoryᵉ =
    total-hom-truncated-type-is-trunc-obj-Precategoryᵉ
      ( precategory-Strict-Categoryᵉ Cᵉ)
      ( is-set-obj-Strict-Categoryᵉ Cᵉ)
```

### Equalities induce morphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Strict-Categoryᵉ l1ᵉ l2ᵉ)
  where

  hom-eq-Strict-Categoryᵉ :
    (xᵉ yᵉ : obj-Strict-Categoryᵉ Cᵉ) → xᵉ ＝ᵉ yᵉ → hom-Strict-Categoryᵉ Cᵉ xᵉ yᵉ
  hom-eq-Strict-Categoryᵉ = hom-eq-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ)

  hom-inv-eq-Strict-Categoryᵉ :
    (xᵉ yᵉ : obj-Strict-Categoryᵉ Cᵉ) → xᵉ ＝ᵉ yᵉ → hom-Strict-Categoryᵉ Cᵉ yᵉ xᵉ
  hom-inv-eq-Strict-Categoryᵉ =
    hom-inv-eq-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ)
```

### Pre- and postcomposition by a morphism

```agda
precomp-hom-Strict-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Strict-Categoryᵉ l1ᵉ l2ᵉ) {xᵉ yᵉ : obj-Strict-Categoryᵉ Cᵉ}
  (fᵉ : hom-Strict-Categoryᵉ Cᵉ xᵉ yᵉ) (zᵉ : obj-Strict-Categoryᵉ Cᵉ) →
  hom-Strict-Categoryᵉ Cᵉ yᵉ zᵉ → hom-Strict-Categoryᵉ Cᵉ xᵉ zᵉ
precomp-hom-Strict-Categoryᵉ Cᵉ =
  precomp-hom-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ)

postcomp-hom-Strict-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Strict-Categoryᵉ l1ᵉ l2ᵉ) {xᵉ yᵉ : obj-Strict-Categoryᵉ Cᵉ}
  (fᵉ : hom-Strict-Categoryᵉ Cᵉ xᵉ yᵉ) (zᵉ : obj-Strict-Categoryᵉ Cᵉ) →
  hom-Strict-Categoryᵉ Cᵉ zᵉ xᵉ → hom-Strict-Categoryᵉ Cᵉ zᵉ yᵉ
postcomp-hom-Strict-Categoryᵉ Cᵉ =
  postcomp-hom-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ)
```

## See also

-ᵉ [Preunivalentᵉ categories](category-theory.preunivalent-categories.mdᵉ) forᵉ theᵉ
  commonᵉ generalizationᵉ ofᵉ (univalentᵉ) categoriesᵉ andᵉ strictᵉ categories.ᵉ
-ᵉ [Gauntᵉ categories](category-theory.gaunt-categories.mdᵉ) forᵉ theᵉ commonᵉ
  intersectionᵉ ofᵉ (univalentᵉ) categoriesᵉ andᵉ strictᵉ categories.ᵉ

## External links

-ᵉ [Strictᵉ Precategories](https://1lab.dev/Cat.Strict.html#strict-precategoriesᵉ)
  atᵉ 1labᵉ
-ᵉ [strictᵉ category](https://ncatlab.org/nlab/show/strict+categoryᵉ) atᵉ $n$Labᵉ
-ᵉ [Categoryᵉ (mathematics)](<https://en.wikipedia.org/wiki/Category_(mathematics)>ᵉ)
  atᵉ Wikipediaᵉ