# Large preorders

```agda
module order-theory.large-preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.preordersᵉ
```

</details>

## Idea

Aᵉ **largeᵉ preorder**ᵉ consistsᵉ ofᵉ typesᵉ indexedᵉ byᵉ aᵉ universeᵉ levels,ᵉ andᵉ anᵉ
orderingᵉ relationᵉ comparingᵉ objectsᵉ ofᵉ arbitraryᵉ universeᵉ levels.ᵉ Thisᵉ levelᵉ ofᵉ
generalityᵉ thereforeᵉ accommodatesᵉ theᵉ inclusionᵉ relationᵉ onᵉ subtypesᵉ ofᵉ
differentᵉ universeᵉ levels.ᵉ Manyᵉ [preorders](order-theory.preorders.mdᵉ) in
agda-unimathᵉ naturallyᵉ ariseᵉ asᵉ largeᵉ preorders.ᵉ

## Definitions

### Large preorders

```agda
record
  Large-Preorderᵉ (αᵉ : Level → Level) (βᵉ : Level → Level → Level) : UUωᵉ where
  constructor
    make-Large-Preorderᵉ
  field
    type-Large-Preorderᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)
    leq-prop-Large-Preorderᵉ : Large-Relation-Propᵉ βᵉ type-Large-Preorderᵉ
    refl-leq-Large-Preorderᵉ :
      is-reflexive-Large-Relation-Propᵉ
        ( type-Large-Preorderᵉ)
        ( leq-prop-Large-Preorderᵉ)
    transitive-leq-Large-Preorderᵉ :
      is-transitive-Large-Relation-Propᵉ
        ( type-Large-Preorderᵉ)
        ( leq-prop-Large-Preorderᵉ)

open Large-Preorderᵉ public

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Xᵉ : Large-Preorderᵉ αᵉ βᵉ)
  where

  leq-Large-Preorderᵉ : Large-Relationᵉ βᵉ (type-Large-Preorderᵉ Xᵉ)
  leq-Large-Preorderᵉ =
    large-relation-Large-Relation-Propᵉ
      ( type-Large-Preorderᵉ Xᵉ)
      ( leq-prop-Large-Preorderᵉ Xᵉ)

  is-prop-leq-Large-Preorderᵉ :
    is-prop-Large-Relationᵉ (type-Large-Preorderᵉ Xᵉ) (leq-Large-Preorderᵉ)
  is-prop-leq-Large-Preorderᵉ =
    is-prop-large-relation-Large-Relation-Propᵉ
      ( type-Large-Preorderᵉ Xᵉ)
      ( leq-prop-Large-Preorderᵉ Xᵉ)

  leq-eq-Large-Preorderᵉ :
    {l1ᵉ : Level}
    {xᵉ yᵉ : type-Large-Preorderᵉ Xᵉ l1ᵉ} →
    (xᵉ ＝ᵉ yᵉ) → leq-Large-Preorderᵉ xᵉ yᵉ
  leq-eq-Large-Preorderᵉ {xᵉ = xᵉ} reflᵉ = refl-leq-Large-Preorderᵉ Xᵉ xᵉ
```

### The predicate on large precategories to be a large preorder

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  is-large-preorder-Large-Precategoryᵉ : UUωᵉ
  is-large-preorder-Large-Precategoryᵉ =
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) (Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ) →
    is-propᵉ (hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)

  large-preorder-Large-Precategoryᵉ :
    is-large-preorder-Large-Precategoryᵉ → Large-Preorderᵉ αᵉ βᵉ
  type-Large-Preorderᵉ
    ( large-preorder-Large-Precategoryᵉ Hᵉ) =
    obj-Large-Precategoryᵉ Cᵉ
  pr1ᵉ (leq-prop-Large-Preorderᵉ (large-preorder-Large-Precategoryᵉ Hᵉ) Xᵉ Yᵉ) =
    hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ
  pr2ᵉ (leq-prop-Large-Preorderᵉ (large-preorder-Large-Precategoryᵉ Hᵉ) Xᵉ Yᵉ) =
    Hᵉ Xᵉ Yᵉ
  refl-leq-Large-Preorderᵉ
    ( large-preorder-Large-Precategoryᵉ Hᵉ)
    ( Xᵉ) =
    id-hom-Large-Precategoryᵉ Cᵉ
  transitive-leq-Large-Preorderᵉ
    ( large-preorder-Large-Precategoryᵉ Hᵉ)
    ( Xᵉ)
    ( Yᵉ)
    ( Zᵉ) =
    comp-hom-Large-Precategoryᵉ Cᵉ
```

## Properties

### Small preorders from large preorders

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Preorderᵉ αᵉ βᵉ)
  where

  preorder-Large-Preorderᵉ : (lᵉ : Level) → Preorderᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  pr1ᵉ (preorder-Large-Preorderᵉ lᵉ) = type-Large-Preorderᵉ Pᵉ lᵉ
  pr1ᵉ (pr2ᵉ (preorder-Large-Preorderᵉ lᵉ)) = leq-prop-Large-Preorderᵉ Pᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (preorder-Large-Preorderᵉ lᵉ))) = refl-leq-Large-Preorderᵉ Pᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (preorder-Large-Preorderᵉ lᵉ))) = transitive-leq-Large-Preorderᵉ Pᵉ
```

### Large preorders are large precategories

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Preorderᵉ αᵉ βᵉ)
  where

  large-precategory-Large-Preorderᵉ : Large-Precategoryᵉ αᵉ βᵉ
  obj-Large-Precategoryᵉ large-precategory-Large-Preorderᵉ = type-Large-Preorderᵉ Pᵉ
  hom-set-Large-Precategoryᵉ large-precategory-Large-Preorderᵉ xᵉ yᵉ =
    set-Propᵉ (leq-prop-Large-Preorderᵉ Pᵉ xᵉ yᵉ)
  comp-hom-Large-Precategoryᵉ large-precategory-Large-Preorderᵉ {Xᵉ = xᵉ} {yᵉ} {zᵉ} =
    transitive-leq-Large-Preorderᵉ Pᵉ xᵉ yᵉ zᵉ
  id-hom-Large-Precategoryᵉ large-precategory-Large-Preorderᵉ {Xᵉ = xᵉ} =
    refl-leq-Large-Preorderᵉ Pᵉ xᵉ
  involutive-eq-associative-comp-hom-Large-Precategoryᵉ
    large-precategory-Large-Preorderᵉ
    {Xᵉ = xᵉ} {Wᵉ = wᵉ} hᵉ gᵉ fᵉ =
    involutive-eq-eqᵉ (eq-is-propᵉ (is-prop-leq-Large-Preorderᵉ Pᵉ xᵉ wᵉ))
  left-unit-law-comp-hom-Large-Precategoryᵉ large-precategory-Large-Preorderᵉ
    {Xᵉ = xᵉ} {yᵉ} fᵉ =
    eq-is-propᵉ (is-prop-leq-Large-Preorderᵉ Pᵉ xᵉ yᵉ)
  right-unit-law-comp-hom-Large-Precategoryᵉ large-precategory-Large-Preorderᵉ
    {Xᵉ = xᵉ} {yᵉ} fᵉ =
    eq-is-propᵉ (is-prop-leq-Large-Preorderᵉ Pᵉ xᵉ yᵉ)
```