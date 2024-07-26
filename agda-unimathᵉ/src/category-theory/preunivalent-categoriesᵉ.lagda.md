# Preunivalent categories

```agda
module category-theory.preunivalent-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.1-typesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **preunivalentᵉ category**ᵉ isᵉ aᵉ [precategory](category-theory.precategories.mdᵉ)
forᵉ whichᵉ theᵉ [identifications](foundation-core.identity-types.mdᵉ) betweenᵉ theᵉ
objectsᵉ [embed](foundation-core.embeddings.mdᵉ) intoᵉ theᵉ
[isomorphisms](category-theory.isomorphisms-in-precategories.md).ᵉ Moreᵉ
specifically,ᵉ anᵉ equalityᵉ betweenᵉ objectsᵉ givesᵉ riseᵉ to anᵉ isomorphismᵉ betweenᵉ
them,ᵉ byᵉ theᵉ J-rule.ᵉ Aᵉ precategoryᵉ isᵉ aᵉ preunivalentᵉ categoryᵉ ifᵉ thisᵉ function,ᵉ
calledᵉ `iso-eq`,ᵉ isᵉ anᵉ embedding.ᵉ

Theᵉ ideaᵉ ofᵉ [preunivalence](foundation.preunivalence.mdᵉ) isᵉ thatᵉ itᵉ isᵉ aᵉ commonᵉ
generalizationᵉ ofᵉ univalentᵉ mathematicsᵉ andᵉ mathematicsᵉ with Axiomᵉ K.ᵉ Henceᵉ
preunivalentᵉ categoriesᵉ generalizeᵉ bothᵉ
[(univalentᵉ) categories](category-theory.categories.mdᵉ) andᵉ
[strictᵉ categories](category-theory.strict-categories.md),ᵉ whichᵉ areᵉ
precategoriesᵉ whoseᵉ objectsᵉ formᵉ aᵉ [set](foundation-core.sets.md).ᵉ

Theᵉ preunivalenceᵉ conditionᵉ onᵉ precategoriesᵉ statesᵉ thatᵉ theᵉ typeᵉ ofᵉ objectsᵉ isᵉ
aᵉ subgroupoidᵉ ofᵉ theᵉ [groupoid](category-theory.groupoids.mdᵉ) ofᵉ isomorphisms.ᵉ
Forᵉ univalentᵉ categoriesᵉ theᵉ groupoidᵉ ofᵉ objectsᵉ isᵉ equivalentᵉ to theᵉ groupoidᵉ
ofᵉ isomorphisms,ᵉ whileᵉ forᵉ strictᵉ categoriesᵉ theᵉ groupoidᵉ ofᵉ objectsᵉ isᵉ
discrete.ᵉ Indeed,ᵉ in thisᵉ senseᵉ preunivalenceᵉ providesᵉ aᵉ generalizationᵉ ofᵉ bothᵉ
notionsᵉ ofᵉ "category",ᵉ with _noᵉ moreᵉ structure_.ᵉ Thisᵉ isᵉ opposedᵉ to theᵉ evenᵉ
moreᵉ generalᵉ notionᵉ ofᵉ precategory,ᵉ where theᵉ homotopyᵉ structureᵉ onᵉ theᵉ objectsᵉ
canᵉ beᵉ almostᵉ completelyᵉ unrelatedᵉ to theᵉ homotopyᵉ structureᵉ ofᵉ theᵉ morphisms.ᵉ

## Definitions

### The predicate on precategories of being a preunivalent category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-preunivalent-prop-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-preunivalent-prop-Precategoryᵉ =
    Π-Propᵉ
      ( obj-Precategoryᵉ Cᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( obj-Precategoryᵉ Cᵉ)
          ( λ yᵉ → is-emb-Propᵉ (iso-eq-Precategoryᵉ Cᵉ xᵉ yᵉ)))

  is-preunivalent-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-preunivalent-Precategoryᵉ = type-Propᵉ is-preunivalent-prop-Precategoryᵉ
```

### The type of preunivalent categories

```agda
Preunivalent-Categoryᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Preunivalent-Categoryᵉ l1ᵉ l2ᵉ =
  Σᵉ (Precategoryᵉ l1ᵉ l2ᵉ) (is-preunivalent-Precategoryᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Preunivalent-Categoryᵉ l1ᵉ l2ᵉ)
  where

  precategory-Preunivalent-Categoryᵉ : Precategoryᵉ l1ᵉ l2ᵉ
  precategory-Preunivalent-Categoryᵉ = pr1ᵉ Cᵉ

  obj-Preunivalent-Categoryᵉ : UUᵉ l1ᵉ
  obj-Preunivalent-Categoryᵉ = obj-Precategoryᵉ precategory-Preunivalent-Categoryᵉ

  hom-set-Preunivalent-Categoryᵉ :
    obj-Preunivalent-Categoryᵉ → obj-Preunivalent-Categoryᵉ → Setᵉ l2ᵉ
  hom-set-Preunivalent-Categoryᵉ =
    hom-set-Precategoryᵉ precategory-Preunivalent-Categoryᵉ

  hom-Preunivalent-Categoryᵉ :
    obj-Preunivalent-Categoryᵉ → obj-Preunivalent-Categoryᵉ → UUᵉ l2ᵉ
  hom-Preunivalent-Categoryᵉ = hom-Precategoryᵉ precategory-Preunivalent-Categoryᵉ

  is-set-hom-Preunivalent-Categoryᵉ :
    (xᵉ yᵉ : obj-Preunivalent-Categoryᵉ) → is-setᵉ (hom-Preunivalent-Categoryᵉ xᵉ yᵉ)
  is-set-hom-Preunivalent-Categoryᵉ =
    is-set-hom-Precategoryᵉ precategory-Preunivalent-Categoryᵉ

  comp-hom-Preunivalent-Categoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Preunivalent-Categoryᵉ} →
    hom-Preunivalent-Categoryᵉ yᵉ zᵉ →
    hom-Preunivalent-Categoryᵉ xᵉ yᵉ →
    hom-Preunivalent-Categoryᵉ xᵉ zᵉ
  comp-hom-Preunivalent-Categoryᵉ =
    comp-hom-Precategoryᵉ precategory-Preunivalent-Categoryᵉ

  associative-comp-hom-Preunivalent-Categoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Preunivalent-Categoryᵉ}
    (hᵉ : hom-Preunivalent-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Preunivalent-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Preunivalent-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Preunivalent-Categoryᵉ (comp-hom-Preunivalent-Categoryᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Preunivalent-Categoryᵉ hᵉ (comp-hom-Preunivalent-Categoryᵉ gᵉ fᵉ)
  associative-comp-hom-Preunivalent-Categoryᵉ =
    associative-comp-hom-Precategoryᵉ precategory-Preunivalent-Categoryᵉ

  involutive-eq-associative-comp-hom-Preunivalent-Categoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Preunivalent-Categoryᵉ}
    (hᵉ : hom-Preunivalent-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Preunivalent-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Preunivalent-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Preunivalent-Categoryᵉ (comp-hom-Preunivalent-Categoryᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-Preunivalent-Categoryᵉ hᵉ (comp-hom-Preunivalent-Categoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Preunivalent-Categoryᵉ =
    involutive-eq-associative-comp-hom-Precategoryᵉ
      ( precategory-Preunivalent-Categoryᵉ)

  associative-composition-operation-Preunivalent-Categoryᵉ :
    associative-composition-operation-binary-family-Setᵉ
      hom-set-Preunivalent-Categoryᵉ
  associative-composition-operation-Preunivalent-Categoryᵉ =
    associative-composition-operation-Precategoryᵉ
      ( precategory-Preunivalent-Categoryᵉ)

  id-hom-Preunivalent-Categoryᵉ :
    {xᵉ : obj-Preunivalent-Categoryᵉ} → hom-Preunivalent-Categoryᵉ xᵉ xᵉ
  id-hom-Preunivalent-Categoryᵉ =
    id-hom-Precategoryᵉ precategory-Preunivalent-Categoryᵉ

  left-unit-law-comp-hom-Preunivalent-Categoryᵉ :
    {xᵉ yᵉ : obj-Preunivalent-Categoryᵉ} (fᵉ : hom-Preunivalent-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Preunivalent-Categoryᵉ id-hom-Preunivalent-Categoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Preunivalent-Categoryᵉ =
    left-unit-law-comp-hom-Precategoryᵉ precategory-Preunivalent-Categoryᵉ

  right-unit-law-comp-hom-Preunivalent-Categoryᵉ :
    {xᵉ yᵉ : obj-Preunivalent-Categoryᵉ} (fᵉ : hom-Preunivalent-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Preunivalent-Categoryᵉ fᵉ id-hom-Preunivalent-Categoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-Preunivalent-Categoryᵉ =
    right-unit-law-comp-hom-Precategoryᵉ precategory-Preunivalent-Categoryᵉ

  is-unital-composition-operation-Preunivalent-Categoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      hom-set-Preunivalent-Categoryᵉ
      comp-hom-Preunivalent-Categoryᵉ
  is-unital-composition-operation-Preunivalent-Categoryᵉ =
    is-unital-composition-operation-Precategoryᵉ
      ( precategory-Preunivalent-Categoryᵉ)

  is-preunivalent-Preunivalent-Categoryᵉ :
    is-preunivalent-Precategoryᵉ precategory-Preunivalent-Categoryᵉ
  is-preunivalent-Preunivalent-Categoryᵉ = pr2ᵉ Cᵉ

  emb-iso-eq-Preunivalent-Categoryᵉ :
    {xᵉ yᵉ : obj-Preunivalent-Categoryᵉ} →
    (xᵉ ＝ᵉ yᵉ) ↪ᵉ (iso-Precategoryᵉ precategory-Preunivalent-Categoryᵉ xᵉ yᵉ)
  pr1ᵉ (emb-iso-eq-Preunivalent-Categoryᵉ {xᵉ} {yᵉ}) =
    iso-eq-Precategoryᵉ precategory-Preunivalent-Categoryᵉ xᵉ yᵉ
  pr2ᵉ (emb-iso-eq-Preunivalent-Categoryᵉ {xᵉ} {yᵉ}) =
    is-preunivalent-Preunivalent-Categoryᵉ xᵉ yᵉ
```

### The total hom-type of a preunivalent category

```agda
total-hom-Preunivalent-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Preunivalent-Categoryᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
total-hom-Preunivalent-Categoryᵉ Cᵉ =
  total-hom-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)

obj-total-hom-Preunivalent-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Preunivalent-Categoryᵉ l1ᵉ l2ᵉ) →
  total-hom-Preunivalent-Categoryᵉ Cᵉ →
  obj-Preunivalent-Categoryᵉ Cᵉ ×ᵉ obj-Preunivalent-Categoryᵉ Cᵉ
obj-total-hom-Preunivalent-Categoryᵉ Cᵉ =
  obj-total-hom-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)
```

### Equalities induce morphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Preunivalent-Categoryᵉ l1ᵉ l2ᵉ)
  where

  hom-eq-Preunivalent-Categoryᵉ :
    (xᵉ yᵉ : obj-Preunivalent-Categoryᵉ Cᵉ) →
    xᵉ ＝ᵉ yᵉ → hom-Preunivalent-Categoryᵉ Cᵉ xᵉ yᵉ
  hom-eq-Preunivalent-Categoryᵉ =
    hom-eq-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)

  hom-inv-eq-Preunivalent-Categoryᵉ :
    (xᵉ yᵉ : obj-Preunivalent-Categoryᵉ Cᵉ) →
    xᵉ ＝ᵉ yᵉ → hom-Preunivalent-Categoryᵉ Cᵉ yᵉ xᵉ
  hom-inv-eq-Preunivalent-Categoryᵉ =
    hom-inv-eq-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)
```

### Pre- and postcomposition by a morphism

```agda
precomp-hom-Preunivalent-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Preunivalent-Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Preunivalent-Categoryᵉ Cᵉ}
  (fᵉ : hom-Preunivalent-Categoryᵉ Cᵉ xᵉ yᵉ)
  (zᵉ : obj-Preunivalent-Categoryᵉ Cᵉ) →
  hom-Preunivalent-Categoryᵉ Cᵉ yᵉ zᵉ →
  hom-Preunivalent-Categoryᵉ Cᵉ xᵉ zᵉ
precomp-hom-Preunivalent-Categoryᵉ Cᵉ =
  precomp-hom-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)

postcomp-hom-Preunivalent-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Preunivalent-Categoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Preunivalent-Categoryᵉ Cᵉ}
  (fᵉ : hom-Preunivalent-Categoryᵉ Cᵉ xᵉ yᵉ)
  (zᵉ : obj-Preunivalent-Categoryᵉ Cᵉ) →
  hom-Preunivalent-Categoryᵉ Cᵉ zᵉ xᵉ →
  hom-Preunivalent-Categoryᵉ Cᵉ zᵉ yᵉ
postcomp-hom-Preunivalent-Categoryᵉ Cᵉ =
  postcomp-hom-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)
```

## Properties

### The objects in a preunivalent category form a 1-type

Theᵉ typeᵉ ofᵉ identitiesᵉ betweenᵉ twoᵉ objectsᵉ in aᵉ preunivalentᵉ categoryᵉ embedsᵉ
intoᵉ theᵉ typeᵉ ofᵉ isomorphismsᵉ betweenᵉ them.ᵉ Butᵉ thisᵉ typeᵉ isᵉ aᵉ set,ᵉ andᵉ thusᵉ theᵉ
identityᵉ typeᵉ isᵉ aᵉ set.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Preunivalent-Categoryᵉ l1ᵉ l2ᵉ)
  where

  is-1-type-obj-Preunivalent-Categoryᵉ : is-1-typeᵉ (obj-Preunivalent-Categoryᵉ Cᵉ)
  is-1-type-obj-Preunivalent-Categoryᵉ xᵉ yᵉ =
    is-set-is-embᵉ
      ( iso-eq-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ) xᵉ yᵉ)
      ( is-preunivalent-Preunivalent-Categoryᵉ Cᵉ xᵉ yᵉ)
      ( is-set-iso-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ))

  obj-1-type-Preunivalent-Categoryᵉ : 1-Typeᵉ l1ᵉ
  pr1ᵉ obj-1-type-Preunivalent-Categoryᵉ = obj-Preunivalent-Categoryᵉ Cᵉ
  pr2ᵉ obj-1-type-Preunivalent-Categoryᵉ = is-1-type-obj-Preunivalent-Categoryᵉ
```

### The total hom-type of a preunivalent category is a 1-type

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Preunivalent-Categoryᵉ l1ᵉ l2ᵉ)
  where

  is-1-type-total-hom-Preunivalent-Categoryᵉ :
    is-1-typeᵉ (total-hom-Preunivalent-Categoryᵉ Cᵉ)
  is-1-type-total-hom-Preunivalent-Categoryᵉ =
    is-trunc-total-hom-is-trunc-obj-Precategoryᵉ
      ( precategory-Preunivalent-Categoryᵉ Cᵉ)
      ( is-1-type-obj-Preunivalent-Categoryᵉ Cᵉ)

  total-hom-1-type-Preunivalent-Categoryᵉ : 1-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  total-hom-1-type-Preunivalent-Categoryᵉ =
    total-hom-truncated-type-is-trunc-obj-Precategoryᵉ
      ( precategory-Preunivalent-Categoryᵉ Cᵉ)
      ( is-1-type-obj-Preunivalent-Categoryᵉ Cᵉ)
```

## See also

-ᵉ [Theᵉ preunivalenceᵉ axiom](foundation.preunivalence.mdᵉ)