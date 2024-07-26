# Preorders

```agda
module order-theory.preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ

open import foundation.binary-relationsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **preorder**ᵉ isᵉ aᵉ typeᵉ equippedᵉ with aᵉ reflexive,ᵉ transitiveᵉ relationᵉ thatᵉ isᵉ
valuedᵉ in propositions.ᵉ

## Definition

```agda
Preorderᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Preorderᵉ l1ᵉ l2ᵉ =
  Σᵉ ( UUᵉ l1ᵉ)
    ( λ Xᵉ →
      Σᵉ ( Relation-Propᵉ l2ᵉ Xᵉ)
        ( λ Rᵉ →
          ( is-reflexiveᵉ (type-Relation-Propᵉ Rᵉ)) ×ᵉ
          ( is-transitiveᵉ (type-Relation-Propᵉ Rᵉ))))

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  where

  type-Preorderᵉ : UUᵉ l1ᵉ
  type-Preorderᵉ = pr1ᵉ Xᵉ

  leq-Preorder-Propᵉ : Relation-Propᵉ l2ᵉ type-Preorderᵉ
  leq-Preorder-Propᵉ = pr1ᵉ (pr2ᵉ Xᵉ)

  leq-Preorderᵉ : (xᵉ yᵉ : type-Preorderᵉ) → UUᵉ l2ᵉ
  leq-Preorderᵉ xᵉ yᵉ = type-Propᵉ (leq-Preorder-Propᵉ xᵉ yᵉ)

  is-prop-leq-Preorderᵉ : (xᵉ yᵉ : type-Preorderᵉ) → is-propᵉ (leq-Preorderᵉ xᵉ yᵉ)
  is-prop-leq-Preorderᵉ = is-prop-type-Relation-Propᵉ leq-Preorder-Propᵉ

  concatenate-eq-leq-Preorderᵉ :
    {xᵉ yᵉ zᵉ : type-Preorderᵉ} → xᵉ ＝ᵉ yᵉ → leq-Preorderᵉ yᵉ zᵉ → leq-Preorderᵉ xᵉ zᵉ
  concatenate-eq-leq-Preorderᵉ reflᵉ = idᵉ

  concatenate-leq-eq-Preorderᵉ :
    {xᵉ yᵉ zᵉ : type-Preorderᵉ} → leq-Preorderᵉ xᵉ yᵉ → yᵉ ＝ᵉ zᵉ → leq-Preorderᵉ xᵉ zᵉ
  concatenate-leq-eq-Preorderᵉ Hᵉ reflᵉ = Hᵉ

  le-Preorder-Propᵉ : Relation-Propᵉ (l1ᵉ ⊔ l2ᵉ) type-Preorderᵉ
  le-Preorder-Propᵉ xᵉ yᵉ =
    product-Propᵉ (xᵉ ≠ᵉ yᵉ ,ᵉ is-prop-negᵉ) (leq-Preorder-Propᵉ xᵉ yᵉ)

  le-Preorderᵉ : Relationᵉ (l1ᵉ ⊔ l2ᵉ) type-Preorderᵉ
  le-Preorderᵉ xᵉ yᵉ = type-Propᵉ (le-Preorder-Propᵉ xᵉ yᵉ)

  is-prop-le-Preorderᵉ : (xᵉ yᵉ : type-Preorderᵉ) → is-propᵉ (le-Preorderᵉ xᵉ yᵉ)
  is-prop-le-Preorderᵉ = is-prop-type-Relation-Propᵉ le-Preorder-Propᵉ

  is-reflexive-leq-Preorderᵉ : is-reflexiveᵉ (leq-Preorderᵉ)
  is-reflexive-leq-Preorderᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Xᵉ))

  refl-leq-Preorderᵉ : is-reflexiveᵉ leq-Preorderᵉ
  refl-leq-Preorderᵉ = is-reflexive-leq-Preorderᵉ

  is-transitive-leq-Preorderᵉ : is-transitiveᵉ leq-Preorderᵉ
  is-transitive-leq-Preorderᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ Xᵉ))

  transitive-leq-Preorderᵉ : is-transitiveᵉ leq-Preorderᵉ
  transitive-leq-Preorderᵉ = is-transitive-leq-Preorderᵉ
```

## Reasoning with inequalities in preorders

Inequalitiesᵉ in preordersᵉ canᵉ beᵉ constructedᵉ byᵉ equationalᵉ reasoningᵉ asᵉ followsᵉ:

```text
calculate-in-Preorderᵉ Xᵉ
  chain-of-inequalitiesᵉ
  xᵉ ≤ᵉ yᵉ
      byᵉ ineq-1ᵉ
      in-Preorderᵉ Xᵉ
    ≤ᵉ zᵉ
      byᵉ ineq-2ᵉ
      in-Preorderᵉ Xᵉ
    ≤ᵉ vᵉ
      byᵉ ineq-3ᵉ
      in-Preorderᵉ Xᵉ
```

Note,ᵉ however,ᵉ thatᵉ in ourᵉ setupᵉ ofᵉ equationalᵉ reasoningᵉ with inequalitiesᵉ itᵉ isᵉ
notᵉ possibleᵉ to mixᵉ inequalitiesᵉ with equalitiesᵉ orᵉ strictᵉ inequalities.ᵉ

```agda
infixl 1 calculate-in-Preorder_chain-of-inequalitiesᵉ_
infixl 0 step-calculate-in-Preorderᵉ

calculate-in-Preorder_chain-of-inequalitiesᵉ_ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  (xᵉ : type-Preorderᵉ Xᵉ) → leq-Preorderᵉ Xᵉ xᵉ xᵉ
calculate-in-Preorder_chain-of-inequalitiesᵉ_ = refl-leq-Preorderᵉ

step-calculate-in-Preorderᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : type-Preorderᵉ Xᵉ} → leq-Preorderᵉ Xᵉ xᵉ yᵉ →
  (zᵉ : type-Preorderᵉ Xᵉ) → leq-Preorderᵉ Xᵉ yᵉ zᵉ → leq-Preorderᵉ Xᵉ xᵉ zᵉ
step-calculate-in-Preorderᵉ Xᵉ {xᵉ} {yᵉ} uᵉ zᵉ vᵉ =
  is-transitive-leq-Preorderᵉ Xᵉ xᵉ yᵉ zᵉ vᵉ uᵉ

syntax step-calculate-in-Preorderᵉ Xᵉ uᵉ zᵉ vᵉ = uᵉ ≤ᵉ zᵉ byᵉ vᵉ in-Preorderᵉ Xᵉ
```

## Properties

### Preorders are precategories whose hom-sets are propositions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  where

  precategory-Preorderᵉ : Precategoryᵉ l1ᵉ l2ᵉ
  precategory-Preorderᵉ =
    make-Precategoryᵉ
      ( type-Preorderᵉ Xᵉ)
      ( λ xᵉ yᵉ → set-Propᵉ (leq-Preorder-Propᵉ Xᵉ xᵉ yᵉ))
      ( λ {xᵉ} {yᵉ} {zᵉ} → is-transitive-leq-Preorderᵉ Xᵉ xᵉ yᵉ zᵉ)
      ( refl-leq-Preorderᵉ Xᵉ)
      ( λ {xᵉ} {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ fᵉ →
        eq-is-propᵉ (is-prop-type-Propᵉ (leq-Preorder-Propᵉ Xᵉ xᵉ wᵉ)))
      ( λ {xᵉ} {yᵉ} fᵉ → eq-is-propᵉ (is-prop-type-Propᵉ (leq-Preorder-Propᵉ Xᵉ xᵉ yᵉ)))
      ( λ {xᵉ} {yᵉ} fᵉ → eq-is-propᵉ (is-prop-type-Propᵉ (leq-Preorder-Propᵉ Xᵉ xᵉ yᵉ)))

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  ( is-prop-hom-Cᵉ : (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) → is-propᵉ (hom-Precategoryᵉ Cᵉ xᵉ yᵉ))
  where

  preorder-is-prop-hom-Precategoryᵉ : Preorderᵉ l1ᵉ l2ᵉ
  pr1ᵉ preorder-is-prop-hom-Precategoryᵉ =
    obj-Precategoryᵉ Cᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ preorder-is-prop-hom-Precategoryᵉ) xᵉ yᵉ) =
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ preorder-is-prop-hom-Precategoryᵉ) xᵉ yᵉ) =
    is-prop-hom-Cᵉ xᵉ yᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ preorder-is-prop-hom-Precategoryᵉ)) xᵉ =
    id-hom-Precategoryᵉ Cᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ preorder-is-prop-hom-Precategoryᵉ)) xᵉ yᵉ zᵉ =
    comp-hom-Precategoryᵉ Cᵉ
```

Itᵉ remainsᵉ to showᵉ thatᵉ theseᵉ constructionsᵉ formᵉ inversesᵉ to eachother.ᵉ