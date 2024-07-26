# Categories

```agda
module category-theory.categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.nonunital-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.preunivalent-categoriesᵉ

open import foundation.1-typesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "category"ᵉ Agda=Categoryᵉ}} in Homotopyᵉ Typeᵉ Theoryᵉ isᵉ aᵉ
[precategory](category-theory.precategories.mdᵉ) forᵉ whichᵉ theᵉ
[identifications](foundation-core.identity-types.mdᵉ) betweenᵉ theᵉ objectsᵉ areᵉ theᵉ
[isomorphisms](category-theory.isomorphisms-in-precategories.md).ᵉ Moreᵉ
specifically,ᵉ anᵉ equalityᵉ betweenᵉ objectsᵉ givesᵉ riseᵉ to anᵉ isomorphismᵉ betweenᵉ
them,ᵉ byᵉ theᵉ J-rule.ᵉ Aᵉ precategoryᵉ isᵉ aᵉ categoryᵉ ifᵉ thisᵉ function,ᵉ calledᵉ
`iso-eq`,ᵉ isᵉ anᵉ [equivalence](foundation-core.equivalences.md).ᵉ Inᵉ particular,ᵉ
beingᵉ aᵉ categoryᵉ isᵉ aᵉ [proposition](foundation-core.propositions.mdᵉ) sinceᵉ
`is-equiv`ᵉ isᵉ aᵉ proposition.ᵉ

## Definitions

### The predicate on precategories of being a category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-category-prop-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-category-prop-Precategoryᵉ =
    Π-Propᵉ
      ( obj-Precategoryᵉ Cᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( obj-Precategoryᵉ Cᵉ)
          ( λ yᵉ → is-equiv-Propᵉ (iso-eq-Precategoryᵉ Cᵉ xᵉ yᵉ)))

  is-category-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-category-Precategoryᵉ = type-Propᵉ is-category-prop-Precategoryᵉ

  is-prop-is-category-Precategoryᵉ : is-propᵉ is-category-Precategoryᵉ
  is-prop-is-category-Precategoryᵉ =
    is-prop-type-Propᵉ is-category-prop-Precategoryᵉ
```

### The type of categories

```agda
Categoryᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Categoryᵉ l1ᵉ l2ᵉ = Σᵉ (Precategoryᵉ l1ᵉ l2ᵉ) (is-category-Precategoryᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  precategory-Categoryᵉ : Precategoryᵉ l1ᵉ l2ᵉ
  precategory-Categoryᵉ = pr1ᵉ Cᵉ

  obj-Categoryᵉ : UUᵉ l1ᵉ
  obj-Categoryᵉ = obj-Precategoryᵉ precategory-Categoryᵉ

  hom-set-Categoryᵉ : obj-Categoryᵉ → obj-Categoryᵉ → Setᵉ l2ᵉ
  hom-set-Categoryᵉ = hom-set-Precategoryᵉ precategory-Categoryᵉ

  hom-Categoryᵉ : obj-Categoryᵉ → obj-Categoryᵉ → UUᵉ l2ᵉ
  hom-Categoryᵉ = hom-Precategoryᵉ precategory-Categoryᵉ

  is-set-hom-Categoryᵉ :
    (xᵉ yᵉ : obj-Categoryᵉ) → is-setᵉ (hom-Categoryᵉ xᵉ yᵉ)
  is-set-hom-Categoryᵉ = is-set-hom-Precategoryᵉ precategory-Categoryᵉ

  comp-hom-Categoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Categoryᵉ} →
    hom-Categoryᵉ yᵉ zᵉ → hom-Categoryᵉ xᵉ yᵉ → hom-Categoryᵉ xᵉ zᵉ
  comp-hom-Categoryᵉ = comp-hom-Precategoryᵉ precategory-Categoryᵉ

  associative-comp-hom-Categoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Categoryᵉ}
    (hᵉ : hom-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Categoryᵉ (comp-hom-Categoryᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Categoryᵉ hᵉ (comp-hom-Categoryᵉ gᵉ fᵉ)
  associative-comp-hom-Categoryᵉ =
    associative-comp-hom-Precategoryᵉ precategory-Categoryᵉ

  involutive-eq-associative-comp-hom-Categoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Categoryᵉ}
    (hᵉ : hom-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Categoryᵉ (comp-hom-Categoryᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-Categoryᵉ hᵉ (comp-hom-Categoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Categoryᵉ =
    involutive-eq-associative-comp-hom-Precategoryᵉ precategory-Categoryᵉ

  associative-composition-operation-Categoryᵉ :
    associative-composition-operation-binary-family-Setᵉ hom-set-Categoryᵉ
  associative-composition-operation-Categoryᵉ =
    associative-composition-operation-Precategoryᵉ precategory-Categoryᵉ

  id-hom-Categoryᵉ : {xᵉ : obj-Categoryᵉ} → hom-Categoryᵉ xᵉ xᵉ
  id-hom-Categoryᵉ = id-hom-Precategoryᵉ precategory-Categoryᵉ

  left-unit-law-comp-hom-Categoryᵉ :
    {xᵉ yᵉ : obj-Categoryᵉ} (fᵉ : hom-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Categoryᵉ id-hom-Categoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Categoryᵉ =
    left-unit-law-comp-hom-Precategoryᵉ precategory-Categoryᵉ

  right-unit-law-comp-hom-Categoryᵉ :
    {xᵉ yᵉ : obj-Categoryᵉ} (fᵉ : hom-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Categoryᵉ fᵉ id-hom-Categoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-Categoryᵉ =
    right-unit-law-comp-hom-Precategoryᵉ precategory-Categoryᵉ

  is-unital-composition-operation-Categoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      hom-set-Categoryᵉ
      comp-hom-Categoryᵉ
  is-unital-composition-operation-Categoryᵉ =
    is-unital-composition-operation-Precategoryᵉ precategory-Categoryᵉ

  is-category-Categoryᵉ :
    is-category-Precategoryᵉ precategory-Categoryᵉ
  is-category-Categoryᵉ = pr2ᵉ Cᵉ
```

### The underlying nonunital precategory of a category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  nonunital-precategory-Categoryᵉ : Nonunital-Precategoryᵉ l1ᵉ l2ᵉ
  nonunital-precategory-Categoryᵉ =
    nonunital-precategory-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### The underlying preunivalent category of a category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  is-preunivalent-category-Categoryᵉ :
    is-preunivalent-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
  is-preunivalent-category-Categoryᵉ xᵉ yᵉ =
    is-emb-is-equivᵉ (is-category-Categoryᵉ Cᵉ xᵉ yᵉ)

  preunivalent-category-Categoryᵉ : Preunivalent-Categoryᵉ l1ᵉ l2ᵉ
  pr1ᵉ preunivalent-category-Categoryᵉ = precategory-Categoryᵉ Cᵉ
  pr2ᵉ preunivalent-category-Categoryᵉ = is-preunivalent-category-Categoryᵉ
```

### The total hom-type of a category

```agda
total-hom-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
total-hom-Categoryᵉ Cᵉ = total-hom-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

obj-total-hom-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) →
  total-hom-Categoryᵉ Cᵉ →
  obj-Categoryᵉ Cᵉ ×ᵉ obj-Categoryᵉ Cᵉ
obj-total-hom-Categoryᵉ Cᵉ = obj-total-hom-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### Equalities induce morphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (xᵉ yᵉ : obj-Categoryᵉ Cᵉ)
  where

  hom-eq-Categoryᵉ : xᵉ ＝ᵉ yᵉ → hom-Categoryᵉ Cᵉ xᵉ yᵉ
  hom-eq-Categoryᵉ = hom-eq-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) xᵉ yᵉ

  hom-inv-eq-Categoryᵉ : xᵉ ＝ᵉ yᵉ → hom-Categoryᵉ Cᵉ yᵉ xᵉ
  hom-inv-eq-Categoryᵉ = hom-inv-eq-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) xᵉ yᵉ
```

### Pre- and postcomposition by a morphism

```agda
precomp-hom-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) (zᵉ : obj-Categoryᵉ Cᵉ) →
  hom-Categoryᵉ Cᵉ yᵉ zᵉ → hom-Categoryᵉ Cᵉ xᵉ zᵉ
precomp-hom-Categoryᵉ Cᵉ = precomp-hom-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

postcomp-hom-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) (zᵉ : obj-Categoryᵉ Cᵉ) →
  hom-Categoryᵉ Cᵉ zᵉ xᵉ → hom-Categoryᵉ Cᵉ zᵉ yᵉ
postcomp-hom-Categoryᵉ Cᵉ = postcomp-hom-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

## Properties

### The objects in a category form a 1-type

Theᵉ typeᵉ ofᵉ identitiesᵉ betweenᵉ twoᵉ objectsᵉ in aᵉ categoryᵉ isᵉ equivalentᵉ to theᵉ
typeᵉ ofᵉ isomorphismsᵉ betweenᵉ them.ᵉ Butᵉ thisᵉ typeᵉ isᵉ aᵉ set,ᵉ andᵉ thusᵉ theᵉ identityᵉ
typeᵉ isᵉ aᵉ set.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  is-1-type-obj-Categoryᵉ : is-1-typeᵉ (obj-Categoryᵉ Cᵉ)
  is-1-type-obj-Categoryᵉ =
    is-1-type-obj-Preunivalent-Categoryᵉ (preunivalent-category-Categoryᵉ Cᵉ)

  obj-1-type-Categoryᵉ : 1-Typeᵉ l1ᵉ
  obj-1-type-Categoryᵉ =
    obj-1-type-Preunivalent-Categoryᵉ (preunivalent-category-Categoryᵉ Cᵉ)
```

### The total hom-type of a category is a 1-type

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  is-1-type-total-hom-Categoryᵉ :
    is-1-typeᵉ (total-hom-Categoryᵉ Cᵉ)
  is-1-type-total-hom-Categoryᵉ =
    is-1-type-total-hom-Preunivalent-Categoryᵉ (preunivalent-category-Categoryᵉ Cᵉ)

  total-hom-1-type-Categoryᵉ : 1-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  total-hom-1-type-Categoryᵉ =
    total-hom-1-type-Preunivalent-Categoryᵉ (preunivalent-category-Categoryᵉ Cᵉ)
```

### A preunivalent category is a category if and only if `iso-eq` is surjective

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-surjective-iso-eq-prop-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-surjective-iso-eq-prop-Precategoryᵉ =
    Π-Propᵉ
      ( obj-Precategoryᵉ Cᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( obj-Precategoryᵉ Cᵉ)
          ( λ yᵉ →
            is-surjective-Propᵉ
              ( iso-eq-Precategoryᵉ Cᵉ xᵉ yᵉ)))

  is-surjective-iso-eq-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-surjective-iso-eq-Precategoryᵉ =
    type-Propᵉ is-surjective-iso-eq-prop-Precategoryᵉ

  is-prop-is-surjective-iso-eq-Precategoryᵉ :
    is-propᵉ is-surjective-iso-eq-Precategoryᵉ
  is-prop-is-surjective-iso-eq-Precategoryᵉ =
    is-prop-type-Propᵉ is-surjective-iso-eq-prop-Precategoryᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Preunivalent-Categoryᵉ l1ᵉ l2ᵉ)
  where

  is-category-is-surjective-iso-eq-Preunivalent-Categoryᵉ :
    is-surjective-iso-eq-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ) →
    is-category-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)
  is-category-is-surjective-iso-eq-Preunivalent-Categoryᵉ
    is-surjective-iso-eq-Cᵉ xᵉ yᵉ =
    is-equiv-is-emb-is-surjectiveᵉ
      ( is-surjective-iso-eq-Cᵉ xᵉ yᵉ)
      ( is-preunivalent-Preunivalent-Categoryᵉ Cᵉ xᵉ yᵉ)

  is-surjective-iso-eq-is-category-Preunivalent-Categoryᵉ :
    is-category-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ) →
    is-surjective-iso-eq-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)
  is-surjective-iso-eq-is-category-Preunivalent-Categoryᵉ
    is-category-Cᵉ xᵉ yᵉ =
    is-surjective-is-equivᵉ (is-category-Cᵉ xᵉ yᵉ)

  is-equiv-is-category-is-surjective-iso-eq-Preunivalent-Categoryᵉ :
    is-equivᵉ is-category-is-surjective-iso-eq-Preunivalent-Categoryᵉ
  is-equiv-is-category-is-surjective-iso-eq-Preunivalent-Categoryᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-is-surjective-iso-eq-Precategoryᵉ
        ( precategory-Preunivalent-Categoryᵉ Cᵉ))
      ( is-prop-is-category-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ))
      ( is-surjective-iso-eq-is-category-Preunivalent-Categoryᵉ)

  is-equiv-is-surjective-iso-eq-is-category-Preunivalent-Categoryᵉ :
    is-equivᵉ is-surjective-iso-eq-is-category-Preunivalent-Categoryᵉ
  is-equiv-is-surjective-iso-eq-is-category-Preunivalent-Categoryᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-is-category-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ))
      ( is-prop-is-surjective-iso-eq-Precategoryᵉ
        ( precategory-Preunivalent-Categoryᵉ Cᵉ))
      ( is-category-is-surjective-iso-eq-Preunivalent-Categoryᵉ)

  equiv-is-category-is-surjective-iso-eq-Preunivalent-Categoryᵉ :
    is-surjective-iso-eq-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ) ≃ᵉ
    is-category-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)
  pr1ᵉ equiv-is-category-is-surjective-iso-eq-Preunivalent-Categoryᵉ =
    is-category-is-surjective-iso-eq-Preunivalent-Categoryᵉ
  pr2ᵉ equiv-is-category-is-surjective-iso-eq-Preunivalent-Categoryᵉ =
    is-equiv-is-category-is-surjective-iso-eq-Preunivalent-Categoryᵉ

  equiv-is-surjective-iso-eq-is-category-Preunivalent-Categoryᵉ :
    is-category-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ) ≃ᵉ
    is-surjective-iso-eq-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)
  pr1ᵉ equiv-is-surjective-iso-eq-is-category-Preunivalent-Categoryᵉ =
    is-surjective-iso-eq-is-category-Preunivalent-Categoryᵉ
  pr2ᵉ equiv-is-surjective-iso-eq-is-category-Preunivalent-Categoryᵉ =
    is-equiv-is-surjective-iso-eq-is-category-Preunivalent-Categoryᵉ
```