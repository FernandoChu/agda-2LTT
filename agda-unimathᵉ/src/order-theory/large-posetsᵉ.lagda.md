# Large posets

```agda
module order-theory.large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-categoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-preordersᵉ
open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
```

</details>

## Idea

Aᵉ **largeᵉ poset**ᵉ isᵉ aᵉ [largeᵉ preorder](order-theory.large-preorders.mdᵉ) suchᵉ
thatᵉ theᵉ restrictionᵉ ofᵉ theᵉ orderingᵉ relationᵉ to anyᵉ particularᵉ universeᵉ levelᵉ
isᵉ antisymmetric.ᵉ

## Definition

### Large posets

```agda
record
  Large-Posetᵉ (αᵉ : Level → Level) (βᵉ : Level → Level → Level) : UUωᵉ where
  constructor
    make-Large-Posetᵉ
  field
    large-preorder-Large-Posetᵉ : Large-Preorderᵉ αᵉ βᵉ
    antisymmetric-leq-Large-Posetᵉ :
      is-antisymmetric-Large-Relationᵉ
        ( type-Large-Preorderᵉ large-preorder-Large-Posetᵉ)
        ( leq-Large-Preorderᵉ large-preorder-Large-Posetᵉ)

open Large-Posetᵉ public

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Xᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  type-Large-Posetᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)
  type-Large-Posetᵉ = type-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Xᵉ)

  leq-prop-Large-Posetᵉ : Large-Relation-Propᵉ βᵉ (type-Large-Posetᵉ)
  leq-prop-Large-Posetᵉ = leq-prop-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Xᵉ)

  leq-Large-Posetᵉ : Large-Relationᵉ βᵉ (type-Large-Posetᵉ)
  leq-Large-Posetᵉ = leq-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Xᵉ)

  is-prop-leq-Large-Posetᵉ :
    is-prop-Large-Relationᵉ (type-Large-Posetᵉ) (leq-Large-Posetᵉ)
  is-prop-leq-Large-Posetᵉ =
    is-prop-leq-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Xᵉ)

  leq-eq-Large-Posetᵉ :
    {l1ᵉ : Level} {xᵉ yᵉ : type-Large-Posetᵉ l1ᵉ} →
    (xᵉ ＝ᵉ yᵉ) → leq-Large-Posetᵉ xᵉ yᵉ
  leq-eq-Large-Posetᵉ =
    leq-eq-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Xᵉ)

  refl-leq-Large-Posetᵉ :
    is-reflexive-Large-Relationᵉ type-Large-Posetᵉ leq-Large-Posetᵉ
  refl-leq-Large-Posetᵉ =
    refl-leq-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Xᵉ)

  transitive-leq-Large-Posetᵉ :
    is-transitive-Large-Relationᵉ type-Large-Posetᵉ leq-Large-Posetᵉ
  transitive-leq-Large-Posetᵉ =
    transitive-leq-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Xᵉ)
```

### The predicate on large categories of being a large poset

Aᵉ [largeᵉ category](category-theory.large-categories.mdᵉ) isᵉ saidᵉ to beᵉ aᵉ **largeᵉ
poset**ᵉ ifᵉ `homᵉ Xᵉ Y`ᵉ isᵉ aᵉ propositionᵉ forᵉ everyᵉ twoᵉ objectsᵉ `X`ᵉ andᵉ `Y`.ᵉ

**Lemma**.ᵉ _Anyᵉ largeᵉ categoryᵉ ofᵉ whichᵉ theᵉ hom-[sets](foundation-core.sets.mdᵉ)
areᵉ [propositions](foundation-core.propositions.mdᵉ) isᵉ aᵉ largeᵉ poset.ᵉ_

**Proof:**ᵉ Theᵉ conditionᵉ thatᵉ `C`ᵉ isᵉ aᵉ largeᵉ posetᵉ immediatelyᵉ givesᵉ usᵉ aᵉ
[largeᵉ precategory](category-theory.large-precategories.md).ᵉ Theᵉ interestingᵉ
partᵉ ofᵉ theᵉ claimᵉ isᵉ thereforeᵉ thatᵉ thisᵉ largeᵉ preorderᵉ isᵉ antisymmetric.ᵉ

Considerᵉ twoᵉ objectsᵉ `X`ᵉ andᵉ `Y`ᵉ in `C`,ᵉ andᵉ twoᵉ morphismsᵉ `fᵉ : Xᵉ → Y`ᵉ andᵉ
`gᵉ : Yᵉ → X`.ᵉ Sinceᵉ thereᵉ isᵉ atᵉ mostᵉ oneᵉ morphismᵉ betweenᵉ anyᵉ twoᵉ objects,ᵉ itᵉ
followsᵉ immediatelyᵉ thatᵉ `fᵉ ∘ᵉ gᵉ ＝ᵉ id`ᵉ andᵉ `gᵉ ∘ᵉ fᵉ ＝ᵉ id`.ᵉ Thereforeᵉ weᵉ haveᵉ anᵉ
isomorphismᵉ `fᵉ : Xᵉ ≅ᵉ Y`.ᵉ Sinceᵉ `C`ᵉ wasᵉ assumedᵉ to beᵉ aᵉ category,ᵉ thisᵉ impliesᵉ
thatᵉ `Xᵉ ＝ᵉ Y`.ᵉ

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ)
  where

  is-large-poset-Large-Categoryᵉ : UUωᵉ
  is-large-poset-Large-Categoryᵉ =
    is-large-preorder-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ)

  is-antisymmetric-is-large-poset-Large-Categoryᵉ :
    is-large-poset-Large-Categoryᵉ →
    is-antisymmetric-Large-Relationᵉ
      ( obj-Large-Categoryᵉ Cᵉ)
      ( hom-Large-Categoryᵉ Cᵉ)
  is-antisymmetric-is-large-poset-Large-Categoryᵉ Hᵉ Xᵉ Yᵉ fᵉ gᵉ =
    eq-iso-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ
      ( fᵉ ,ᵉ gᵉ ,ᵉ eq-is-propᵉ (Hᵉ Yᵉ Yᵉ) ,ᵉ eq-is-propᵉ (Hᵉ Xᵉ Xᵉ))

  large-poset-Large-Categoryᵉ :
    is-large-poset-Large-Categoryᵉ → Large-Posetᵉ αᵉ βᵉ
  large-preorder-Large-Posetᵉ (large-poset-Large-Categoryᵉ Hᵉ) =
    large-preorder-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) Hᵉ
  antisymmetric-leq-Large-Posetᵉ (large-poset-Large-Categoryᵉ Hᵉ) =
    is-antisymmetric-is-large-poset-Large-Categoryᵉ Hᵉ
```

### Small posets from large posets

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Xᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  preorder-Large-Posetᵉ : (lᵉ : Level) → Preorderᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  preorder-Large-Posetᵉ = preorder-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Xᵉ)

  poset-Large-Posetᵉ : (lᵉ : Level) → Posetᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  pr1ᵉ (poset-Large-Posetᵉ lᵉ) = preorder-Large-Posetᵉ lᵉ
  pr2ᵉ (poset-Large-Posetᵉ lᵉ) = antisymmetric-leq-Large-Posetᵉ Xᵉ

  set-Large-Posetᵉ : (lᵉ : Level) → Setᵉ (αᵉ lᵉ)
  set-Large-Posetᵉ lᵉ = set-Posetᵉ (poset-Large-Posetᵉ lᵉ)

  is-set-type-Large-Posetᵉ : {lᵉ : Level} → is-setᵉ (type-Large-Posetᵉ Xᵉ lᵉ)
  is-set-type-Large-Posetᵉ {lᵉ} = is-set-type-Posetᵉ (poset-Large-Posetᵉ lᵉ)
```

## Properties

### Large posets are large categories

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  large-precategory-Large-Posetᵉ : Large-Precategoryᵉ αᵉ βᵉ
  large-precategory-Large-Posetᵉ =
    large-precategory-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Pᵉ)

  precategory-Large-Posetᵉ : (lᵉ : Level) → Precategoryᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  precategory-Large-Posetᵉ =
    precategory-Large-Precategoryᵉ large-precategory-Large-Posetᵉ

  is-large-category-Large-Posetᵉ :
    is-large-category-Large-Precategoryᵉ large-precategory-Large-Posetᵉ
  is-large-category-Large-Posetᵉ {lᵉ} xᵉ yᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-set-type-Large-Posetᵉ Pᵉ xᵉ yᵉ)
      ( is-prop-iso-is-prop-hom-Precategoryᵉ
        ( precategory-Large-Posetᵉ lᵉ)
        ( is-prop-leq-Large-Posetᵉ Pᵉ xᵉ yᵉ))
      ( λ fᵉ →
        antisymmetric-leq-Large-Posetᵉ Pᵉ xᵉ yᵉ
        ( hom-iso-Precategoryᵉ (precategory-Large-Posetᵉ lᵉ) fᵉ)
        ( hom-inv-iso-Precategoryᵉ (precategory-Large-Posetᵉ lᵉ) fᵉ))

  large-category-Large-Posetᵉ : Large-Categoryᵉ αᵉ βᵉ
  large-precategory-Large-Categoryᵉ large-category-Large-Posetᵉ =
    large-precategory-Large-Posetᵉ
  is-large-category-Large-Categoryᵉ large-category-Large-Posetᵉ =
    is-large-category-Large-Posetᵉ

  is-large-poset-large-category-Large-Posetᵉ :
    is-large-poset-Large-Categoryᵉ large-category-Large-Posetᵉ
  is-large-poset-large-category-Large-Posetᵉ =
    is-prop-leq-Large-Posetᵉ Pᵉ
```