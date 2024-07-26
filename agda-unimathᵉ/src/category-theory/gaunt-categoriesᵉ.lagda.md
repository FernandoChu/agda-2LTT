# Gaunt categories

```agda
module category-theory.gaunt-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.isomorphism-induction-categoriesᵉ
open import category-theory.isomorphisms-in-categoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.nonunital-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.preunivalent-categoriesᵉ
open import category-theory.rigid-objects-categoriesᵉ
open import category-theory.strict-categoriesᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **gauntᵉ category**ᵉ isᵉ aᵉ [category](category-theory.categories.mdᵉ) suchᵉ thatᵉ
oneᵉ ofᵉ theᵉ followingᵉ equivalentᵉ conditionsᵉ holdᵉ:

1.ᵉ Theᵉ
   [isomorphism](category-theory.isomorphisms-in-categories.md)-[sets](foundation-core.sets.mdᵉ)
   areᵉ [propositions](foundation-core.propositions.md).ᵉ
2.ᵉ Theᵉ objectsᵉ formᵉ aᵉ set.ᵉ
3.ᵉ Everyᵉ objectᵉ isᵉ [rigid](category-theory.rigid-objects-categories.md),ᵉ meaningᵉ
   itsᵉ [automorphismᵉ group](group-theory.automorphism-groups.mdᵉ) isᵉ
   [trivial](group-theory.trivial-groups.md).ᵉ

Gauntᵉ categoriesᵉ formsᵉ theᵉ commonᵉ intersectionᵉ ofᵉ (univalentᵉ) categoriesᵉ andᵉ
[strictᵉ categories](category-theory.strict-categories.md).ᵉ Weᵉ haveᵉ theᵉ followingᵉ
diagramᵉ relatingᵉ theᵉ differentᵉ notionsᵉ ofᵉ "category"ᵉ:

```text
        Gauntᵉ categoriesᵉ
              /ᵉ   \ᵉ
            /ᵉ       \ᵉ
          ∨ᵉ           ∨ᵉ
  Categoriesᵉ         Strictᵉ categoriesᵉ
          \ᵉ           /ᵉ
            \ᵉ       /ᵉ
              ∨ᵉ   ∨ᵉ
      Preunivalentᵉ categoriesᵉ
                |
                |
                ∨ᵉ
          Precategoriesᵉ
```

## Definitions

### The predicate on precategories that there is at most one isomorphism between any two objects

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-prop-iso-prop-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-prop-iso-prop-Precategoryᵉ =
    Π-Propᵉ
      ( obj-Precategoryᵉ Cᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( obj-Precategoryᵉ Cᵉ)
          ( λ yᵉ → is-prop-Propᵉ (iso-Precategoryᵉ Cᵉ xᵉ yᵉ)))

  is-prop-iso-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-prop-iso-Precategoryᵉ = type-Propᵉ is-prop-iso-prop-Precategoryᵉ

  is-property-is-prop-iso-Precategoryᵉ : is-propᵉ is-prop-iso-Precategoryᵉ
  is-property-is-prop-iso-Precategoryᵉ =
    is-prop-type-Propᵉ is-prop-iso-prop-Precategoryᵉ
```

### The predicate on precategories of being gaunt

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-gaunt-prop-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-gaunt-prop-Precategoryᵉ =
    product-Propᵉ
      ( is-category-prop-Precategoryᵉ Cᵉ)
      ( is-prop-iso-prop-Precategoryᵉ Cᵉ)

  is-gaunt-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-gaunt-Precategoryᵉ = type-Propᵉ is-gaunt-prop-Precategoryᵉ
```

### The predicate on categories of being gaunt

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  is-gaunt-prop-Categoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-gaunt-prop-Categoryᵉ = is-prop-iso-prop-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  is-gaunt-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-gaunt-Categoryᵉ = type-Propᵉ is-gaunt-prop-Categoryᵉ
```

### The type of gaunt categories

```agda
Gaunt-Categoryᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Gaunt-Categoryᵉ l1ᵉ l2ᵉ = Σᵉ (Categoryᵉ l1ᵉ l2ᵉ) (is-gaunt-Categoryᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Gaunt-Categoryᵉ l1ᵉ l2ᵉ)
  where

  category-Gaunt-Categoryᵉ : Categoryᵉ l1ᵉ l2ᵉ
  category-Gaunt-Categoryᵉ = pr1ᵉ Cᵉ

  obj-Gaunt-Categoryᵉ : UUᵉ l1ᵉ
  obj-Gaunt-Categoryᵉ = obj-Categoryᵉ category-Gaunt-Categoryᵉ

  hom-set-Gaunt-Categoryᵉ :
    obj-Gaunt-Categoryᵉ → obj-Gaunt-Categoryᵉ → Setᵉ l2ᵉ
  hom-set-Gaunt-Categoryᵉ =
    hom-set-Categoryᵉ category-Gaunt-Categoryᵉ

  hom-Gaunt-Categoryᵉ :
    obj-Gaunt-Categoryᵉ → obj-Gaunt-Categoryᵉ → UUᵉ l2ᵉ
  hom-Gaunt-Categoryᵉ = hom-Categoryᵉ category-Gaunt-Categoryᵉ

  is-set-hom-Gaunt-Categoryᵉ :
    (xᵉ yᵉ : obj-Gaunt-Categoryᵉ) → is-setᵉ (hom-Gaunt-Categoryᵉ xᵉ yᵉ)
  is-set-hom-Gaunt-Categoryᵉ =
    is-set-hom-Categoryᵉ category-Gaunt-Categoryᵉ

  comp-hom-Gaunt-Categoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Gaunt-Categoryᵉ} →
    hom-Gaunt-Categoryᵉ yᵉ zᵉ →
    hom-Gaunt-Categoryᵉ xᵉ yᵉ →
    hom-Gaunt-Categoryᵉ xᵉ zᵉ
  comp-hom-Gaunt-Categoryᵉ =
    comp-hom-Categoryᵉ category-Gaunt-Categoryᵉ

  associative-comp-hom-Gaunt-Categoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Gaunt-Categoryᵉ}
    (hᵉ : hom-Gaunt-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Gaunt-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Gaunt-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Gaunt-Categoryᵉ (comp-hom-Gaunt-Categoryᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Gaunt-Categoryᵉ hᵉ (comp-hom-Gaunt-Categoryᵉ gᵉ fᵉ)
  associative-comp-hom-Gaunt-Categoryᵉ =
    associative-comp-hom-Categoryᵉ category-Gaunt-Categoryᵉ

  involutive-eq-associative-comp-hom-Gaunt-Categoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Gaunt-Categoryᵉ}
    (hᵉ : hom-Gaunt-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Gaunt-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Gaunt-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Gaunt-Categoryᵉ (comp-hom-Gaunt-Categoryᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-Gaunt-Categoryᵉ hᵉ (comp-hom-Gaunt-Categoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Gaunt-Categoryᵉ =
    involutive-eq-associative-comp-hom-Categoryᵉ category-Gaunt-Categoryᵉ

  associative-composition-operation-Gaunt-Categoryᵉ :
    associative-composition-operation-binary-family-Setᵉ
      hom-set-Gaunt-Categoryᵉ
  associative-composition-operation-Gaunt-Categoryᵉ =
    associative-composition-operation-Categoryᵉ
      ( category-Gaunt-Categoryᵉ)

  id-hom-Gaunt-Categoryᵉ :
    {xᵉ : obj-Gaunt-Categoryᵉ} → hom-Gaunt-Categoryᵉ xᵉ xᵉ
  id-hom-Gaunt-Categoryᵉ =
    id-hom-Categoryᵉ category-Gaunt-Categoryᵉ

  left-unit-law-comp-hom-Gaunt-Categoryᵉ :
    {xᵉ yᵉ : obj-Gaunt-Categoryᵉ} (fᵉ : hom-Gaunt-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Gaunt-Categoryᵉ id-hom-Gaunt-Categoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Gaunt-Categoryᵉ =
    left-unit-law-comp-hom-Categoryᵉ category-Gaunt-Categoryᵉ

  right-unit-law-comp-hom-Gaunt-Categoryᵉ :
    {xᵉ yᵉ : obj-Gaunt-Categoryᵉ} (fᵉ : hom-Gaunt-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Gaunt-Categoryᵉ fᵉ id-hom-Gaunt-Categoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-Gaunt-Categoryᵉ =
    right-unit-law-comp-hom-Categoryᵉ category-Gaunt-Categoryᵉ

  is-unital-composition-operation-Gaunt-Categoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      hom-set-Gaunt-Categoryᵉ
      comp-hom-Gaunt-Categoryᵉ
  is-unital-composition-operation-Gaunt-Categoryᵉ =
    is-unital-composition-operation-Categoryᵉ
      ( category-Gaunt-Categoryᵉ)

  is-gaunt-Gaunt-Categoryᵉ :
    is-gaunt-Categoryᵉ category-Gaunt-Categoryᵉ
  is-gaunt-Gaunt-Categoryᵉ = pr2ᵉ Cᵉ
```

### The underlying nonunital precategory of a gaunt category

```agda
nonunital-precategory-Gaunt-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} → Gaunt-Categoryᵉ l1ᵉ l2ᵉ → Nonunital-Precategoryᵉ l1ᵉ l2ᵉ
nonunital-precategory-Gaunt-Categoryᵉ Cᵉ =
  nonunital-precategory-Categoryᵉ (category-Gaunt-Categoryᵉ Cᵉ)
```

### The underlying precategory of a gaunt category

```agda
precategory-Gaunt-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} → Gaunt-Categoryᵉ l1ᵉ l2ᵉ → Precategoryᵉ l1ᵉ l2ᵉ
precategory-Gaunt-Categoryᵉ Cᵉ = precategory-Categoryᵉ (category-Gaunt-Categoryᵉ Cᵉ)
```

### The underlying preunivalent category of a gaunt category

```agda
preunivalent-category-Gaunt-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} → Gaunt-Categoryᵉ l1ᵉ l2ᵉ → Preunivalent-Categoryᵉ l1ᵉ l2ᵉ
preunivalent-category-Gaunt-Categoryᵉ Cᵉ =
  preunivalent-category-Categoryᵉ (category-Gaunt-Categoryᵉ Cᵉ)
```

### The total hom-type of a gaunt category

```agda
total-hom-Gaunt-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Gaunt-Categoryᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
total-hom-Gaunt-Categoryᵉ Cᵉ =
  total-hom-Categoryᵉ (category-Gaunt-Categoryᵉ Cᵉ)

obj-total-hom-Gaunt-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Gaunt-Categoryᵉ l1ᵉ l2ᵉ) →
  total-hom-Gaunt-Categoryᵉ Cᵉ →
  obj-Gaunt-Categoryᵉ Cᵉ ×ᵉ obj-Gaunt-Categoryᵉ Cᵉ
obj-total-hom-Gaunt-Categoryᵉ Cᵉ =
  obj-total-hom-Categoryᵉ (category-Gaunt-Categoryᵉ Cᵉ)
```

### Equalities induce morphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Gaunt-Categoryᵉ l1ᵉ l2ᵉ)
  where

  hom-eq-Gaunt-Categoryᵉ :
    (xᵉ yᵉ : obj-Gaunt-Categoryᵉ Cᵉ) → xᵉ ＝ᵉ yᵉ → hom-Gaunt-Categoryᵉ Cᵉ xᵉ yᵉ
  hom-eq-Gaunt-Categoryᵉ =
    hom-eq-Categoryᵉ (category-Gaunt-Categoryᵉ Cᵉ)

  hom-inv-eq-Gaunt-Categoryᵉ :
    (xᵉ yᵉ : obj-Gaunt-Categoryᵉ Cᵉ) → xᵉ ＝ᵉ yᵉ → hom-Gaunt-Categoryᵉ Cᵉ yᵉ xᵉ
  hom-inv-eq-Gaunt-Categoryᵉ =
    hom-inv-eq-Categoryᵉ (category-Gaunt-Categoryᵉ Cᵉ)
```

## Properties

### Preunivalent categories whose isomorphism-sets are propositions are strict categories

```agda
is-strict-category-is-prop-iso-Preunivalent-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Preunivalent-Categoryᵉ l1ᵉ l2ᵉ) →
  is-prop-iso-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ) →
  is-strict-category-Preunivalent-Categoryᵉ Cᵉ
is-strict-category-is-prop-iso-Preunivalent-Categoryᵉ Cᵉ is-prop-iso-Cᵉ xᵉ yᵉ =
  is-prop-embᵉ (emb-iso-eq-Preunivalent-Categoryᵉ Cᵉ) (is-prop-iso-Cᵉ xᵉ yᵉ)
```

### Gaunt categories are strict

```agda
is-strict-category-is-gaunt-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) →
  is-gaunt-Categoryᵉ Cᵉ → is-strict-category-Categoryᵉ Cᵉ
is-strict-category-is-gaunt-Categoryᵉ Cᵉ =
  is-strict-category-is-prop-iso-Preunivalent-Categoryᵉ
    ( preunivalent-category-Categoryᵉ Cᵉ)
```

### A strict category is gaunt if `iso-eq` is surjective

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Strict-Categoryᵉ l1ᵉ l2ᵉ)
  where

  is-category-is-surjective-iso-eq-Strict-Categoryᵉ :
    is-surjective-iso-eq-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ) →
    is-category-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ)
  is-category-is-surjective-iso-eq-Strict-Categoryᵉ =
    is-category-is-surjective-iso-eq-Preunivalent-Categoryᵉ
      ( preunivalent-category-Strict-Categoryᵉ Cᵉ)

  is-prop-iso-is-category-Strict-Categoryᵉ :
    is-category-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ) →
    is-prop-iso-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ)
  is-prop-iso-is-category-Strict-Categoryᵉ is-category-Cᵉ xᵉ yᵉ =
    is-prop-is-equiv'ᵉ (is-category-Cᵉ xᵉ yᵉ) (is-set-obj-Strict-Categoryᵉ Cᵉ xᵉ yᵉ)

  is-prop-iso-is-surjective-iso-eq-Strict-Categoryᵉ :
    is-surjective-iso-eq-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ) →
    is-prop-iso-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ)
  is-prop-iso-is-surjective-iso-eq-Strict-Categoryᵉ is-surj-iso-eq-Cᵉ =
    is-prop-iso-is-category-Strict-Categoryᵉ
      ( is-category-is-surjective-iso-eq-Strict-Categoryᵉ is-surj-iso-eq-Cᵉ)

  is-gaunt-is-surjective-iso-eq-Strict-Categoryᵉ :
    is-surjective-iso-eq-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ) →
    is-gaunt-Precategoryᵉ (precategory-Strict-Categoryᵉ Cᵉ)
  pr1ᵉ (is-gaunt-is-surjective-iso-eq-Strict-Categoryᵉ is-surj-iso-eq-Cᵉ) =
    is-category-is-surjective-iso-eq-Strict-Categoryᵉ is-surj-iso-eq-Cᵉ
  pr2ᵉ (is-gaunt-is-surjective-iso-eq-Strict-Categoryᵉ is-surj-iso-eq-Cᵉ) =
    is-prop-iso-is-surjective-iso-eq-Strict-Categoryᵉ is-surj-iso-eq-Cᵉ
```

### A category is gaunt if and only if every object is rigid

**Proof:**ᵉ Usingᵉ theᵉ factᵉ thatᵉ aᵉ typeᵉ isᵉ aᵉ
[proposition](foundation-core.propositions.mdᵉ) ifᵉ andᵉ onlyᵉ ifᵉ havingᵉ anᵉ
inhabitantᵉ impliesᵉ itᵉ isᵉ [contractible](foundation-core.contractible-types.md),ᵉ
weᵉ canᵉ applyᵉ
[isomorphismᵉ induction](category-theory.isomorphism-induction-categories.mdᵉ) to
getᵉ ourᵉ result.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  is-gaunt-is-rigid-Categoryᵉ :
    ((xᵉ : obj-Categoryᵉ Cᵉ) → is-rigid-obj-Categoryᵉ Cᵉ xᵉ) → is-gaunt-Categoryᵉ Cᵉ
  is-gaunt-is-rigid-Categoryᵉ is-rigid-obj-Cᵉ xᵉ yᵉ =
    is-prop-is-proof-irrelevantᵉ (ind-iso-Categoryᵉ Cᵉ _ (is-rigid-obj-Cᵉ xᵉ))

  is-rigid-is-gaunt-Categoryᵉ :
    is-gaunt-Categoryᵉ Cᵉ → (xᵉ : obj-Categoryᵉ Cᵉ) → is-rigid-obj-Categoryᵉ Cᵉ xᵉ
  is-rigid-is-gaunt-Categoryᵉ is-gaunt-Cᵉ xᵉ =
    is-proof-irrelevant-is-propᵉ (is-gaunt-Cᵉ xᵉ xᵉ) (id-iso-Categoryᵉ Cᵉ)
```

## See also

-ᵉ [Posets](order-theory.posets.mdᵉ) areᵉ gaunt.ᵉ

## External links

-ᵉ [Gauntᵉ (pre)categories](https://1lab.dev/Cat.Gaunt.htmlᵉ) atᵉ 1labᵉ
-ᵉ [gauntᵉ category](https://ncatlab.org/nlab/show/gaunt+category#in_type_theoryᵉ)
  atᵉ $n$Labᵉ