# Posets

```agda
module order-theory.posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.binary-relationsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.preordersᵉ
```

</details>

## Idea

Aᵉ **poset**ᵉ isᵉ aᵉ [set](foundation-core.sets.mdᵉ)
[equipped](foundation.structure.mdᵉ) with aᵉ reflexive,ᵉ antisymmetric,ᵉ transitiveᵉ
[relation](foundation.binary-relations.mdᵉ) thatᵉ takesᵉ valuesᵉ in
[propositions](foundation-core.propositions.md).ᵉ

## Definition

```agda
is-antisymmetric-leq-Preorderᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Preorderᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-antisymmetric-leq-Preorderᵉ Pᵉ = is-antisymmetricᵉ (leq-Preorderᵉ Pᵉ)

Posetᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Posetᵉ l1ᵉ l2ᵉ =
  Σᵉ (Preorderᵉ l1ᵉ l2ᵉ) (is-antisymmetric-leq-Preorderᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  preorder-Posetᵉ : Preorderᵉ l1ᵉ l2ᵉ
  preorder-Posetᵉ = pr1ᵉ Xᵉ

  type-Posetᵉ : UUᵉ l1ᵉ
  type-Posetᵉ = type-Preorderᵉ preorder-Posetᵉ

  leq-Poset-Propᵉ : (xᵉ yᵉ : type-Posetᵉ) → Propᵉ l2ᵉ
  leq-Poset-Propᵉ = leq-Preorder-Propᵉ preorder-Posetᵉ

  leq-Posetᵉ : (xᵉ yᵉ : type-Posetᵉ) → UUᵉ l2ᵉ
  leq-Posetᵉ = leq-Preorderᵉ preorder-Posetᵉ

  is-prop-leq-Posetᵉ : (xᵉ yᵉ : type-Posetᵉ) → is-propᵉ (leq-Posetᵉ xᵉ yᵉ)
  is-prop-leq-Posetᵉ = is-prop-leq-Preorderᵉ preorder-Posetᵉ

  concatenate-eq-leq-Posetᵉ :
    {xᵉ yᵉ zᵉ : type-Posetᵉ} → xᵉ ＝ᵉ yᵉ → leq-Posetᵉ yᵉ zᵉ → leq-Posetᵉ xᵉ zᵉ
  concatenate-eq-leq-Posetᵉ = concatenate-eq-leq-Preorderᵉ preorder-Posetᵉ

  concatenate-leq-eq-Posetᵉ :
    {xᵉ yᵉ zᵉ : type-Posetᵉ} → leq-Posetᵉ xᵉ yᵉ → yᵉ ＝ᵉ zᵉ → leq-Posetᵉ xᵉ zᵉ
  concatenate-leq-eq-Posetᵉ = concatenate-leq-eq-Preorderᵉ preorder-Posetᵉ

  refl-leq-Posetᵉ : is-reflexiveᵉ leq-Posetᵉ
  refl-leq-Posetᵉ = refl-leq-Preorderᵉ preorder-Posetᵉ

  transitive-leq-Posetᵉ : is-transitiveᵉ leq-Posetᵉ
  transitive-leq-Posetᵉ = transitive-leq-Preorderᵉ preorder-Posetᵉ

  le-Poset-Propᵉ : (xᵉ yᵉ : type-Posetᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  le-Poset-Propᵉ = le-Preorder-Propᵉ preorder-Posetᵉ

  le-Posetᵉ : (xᵉ yᵉ : type-Posetᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  le-Posetᵉ = le-Preorderᵉ preorder-Posetᵉ

  is-prop-le-Posetᵉ :
    (xᵉ yᵉ : type-Posetᵉ) → is-propᵉ (le-Posetᵉ xᵉ yᵉ)
  is-prop-le-Posetᵉ = is-prop-le-Preorderᵉ preorder-Posetᵉ

  antisymmetric-leq-Posetᵉ : is-antisymmetricᵉ leq-Posetᵉ
  antisymmetric-leq-Posetᵉ = pr2ᵉ Xᵉ

  is-set-type-Posetᵉ : is-setᵉ type-Posetᵉ
  is-set-type-Posetᵉ =
    is-set-prop-in-idᵉ
      ( λ xᵉ yᵉ → leq-Posetᵉ xᵉ yᵉ ×ᵉ leq-Posetᵉ yᵉ xᵉ)
      ( λ xᵉ yᵉ → is-prop-productᵉ (is-prop-leq-Posetᵉ xᵉ yᵉ) (is-prop-leq-Posetᵉ yᵉ xᵉ))
      ( λ xᵉ → refl-leq-Posetᵉ xᵉ ,ᵉ refl-leq-Posetᵉ xᵉ)
      ( λ xᵉ yᵉ (Hᵉ ,ᵉ Kᵉ) → antisymmetric-leq-Posetᵉ xᵉ yᵉ Hᵉ Kᵉ)

  set-Posetᵉ : Setᵉ l1ᵉ
  pr1ᵉ set-Posetᵉ = type-Posetᵉ
  pr2ᵉ set-Posetᵉ = is-set-type-Posetᵉ
```

## Reasoning with inequalities in posets

Inequalitiesᵉ in preordersᵉ canᵉ beᵉ constructedᵉ byᵉ equationalᵉ reasoningᵉ asᵉ followsᵉ:

```text
calculate-in-Posetᵉ Xᵉ
  chain-of-inequalitiesᵉ
  xᵉ ≤ᵉ yᵉ
      byᵉ ineq-1ᵉ
      in-Posetᵉ Xᵉ
    ≤ᵉ zᵉ
      byᵉ ineq-2ᵉ
      in-Posetᵉ Xᵉ
    ≤ᵉ vᵉ
      byᵉ ineq-3ᵉ
      in-Posetᵉ Xᵉ
```

Note,ᵉ however,ᵉ thatᵉ in ourᵉ setupᵉ ofᵉ equationalᵉ reasoningᵉ with inequalitiesᵉ itᵉ isᵉ
notᵉ possibleᵉ to mixᵉ inequalitiesᵉ with equalitiesᵉ orᵉ strictᵉ inequalities.ᵉ

```agda
infixl 1 calculate-in-Poset_chain-of-inequalitiesᵉ_
infixl 0 step-calculate-in-Posetᵉ

calculate-in-Poset_chain-of-inequalitiesᵉ_ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ)
  (xᵉ : type-Posetᵉ Xᵉ) → leq-Posetᵉ Xᵉ xᵉ xᵉ
calculate-in-Poset_chain-of-inequalitiesᵉ_ = refl-leq-Posetᵉ

step-calculate-in-Posetᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : type-Posetᵉ Xᵉ} → leq-Posetᵉ Xᵉ xᵉ yᵉ →
  (zᵉ : type-Posetᵉ Xᵉ) → leq-Posetᵉ Xᵉ yᵉ zᵉ → leq-Posetᵉ Xᵉ xᵉ zᵉ
step-calculate-in-Posetᵉ Xᵉ {xᵉ} {yᵉ} uᵉ zᵉ vᵉ = transitive-leq-Posetᵉ Xᵉ xᵉ yᵉ zᵉ vᵉ uᵉ

syntax step-calculate-in-Posetᵉ Xᵉ uᵉ zᵉ vᵉ = uᵉ ≤ᵉ zᵉ byᵉ vᵉ in-Posetᵉ Xᵉ
```

## Properties

### Posets are categories whose underlying hom-sets are propositions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  precategory-Posetᵉ : Precategoryᵉ l1ᵉ l2ᵉ
  precategory-Posetᵉ = precategory-Preorderᵉ (preorder-Posetᵉ Xᵉ)

  is-category-precategory-Posetᵉ : is-category-Precategoryᵉ precategory-Posetᵉ
  is-category-precategory-Posetᵉ xᵉ yᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-set-type-Posetᵉ Xᵉ xᵉ yᵉ)
      ( is-prop-iso-is-prop-hom-Precategoryᵉ precategory-Posetᵉ
        ( is-prop-leq-Posetᵉ Xᵉ xᵉ yᵉ))
      ( λ fᵉ →
        antisymmetric-leq-Posetᵉ Xᵉ xᵉ yᵉ
          ( hom-iso-Precategoryᵉ precategory-Posetᵉ fᵉ)
          ( hom-inv-iso-Precategoryᵉ precategory-Posetᵉ fᵉ))

  category-Posetᵉ : Categoryᵉ l1ᵉ l2ᵉ
  pr1ᵉ category-Posetᵉ = precategory-Posetᵉ
  pr2ᵉ category-Posetᵉ = is-category-precategory-Posetᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (is-prop-hom-Cᵉ : (xᵉ yᵉ : obj-Categoryᵉ Cᵉ) → is-propᵉ (hom-Categoryᵉ Cᵉ xᵉ yᵉ))
  where

  preorder-is-prop-hom-Categoryᵉ : Preorderᵉ l1ᵉ l2ᵉ
  preorder-is-prop-hom-Categoryᵉ =
    preorder-is-prop-hom-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) (is-prop-hom-Cᵉ)

  poset-is-prop-hom-Categoryᵉ : Posetᵉ l1ᵉ l2ᵉ
  pr1ᵉ poset-is-prop-hom-Categoryᵉ = preorder-is-prop-hom-Categoryᵉ
  pr2ᵉ poset-is-prop-hom-Categoryᵉ xᵉ yᵉ fᵉ gᵉ =
    map-inv-is-equivᵉ
      ( is-category-Categoryᵉ Cᵉ xᵉ yᵉ)
      ( iso-is-prop-hom-Precategoryᵉ
        ( precategory-Categoryᵉ Cᵉ) is-prop-hom-Cᵉ fᵉ gᵉ)
```

Itᵉ remainsᵉ to showᵉ thatᵉ theseᵉ constructionsᵉ formᵉ inversesᵉ to eachother.ᵉ