# Total orders

```agda
module order-theory.total-ordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
open import order-theory.total-preordersᵉ
```

</details>

## Idea

Aᵉ **totalᵉ order**,ᵉ orᵉ aᵉ **linearᵉ order**,ᵉ isᵉ aᵉ [poset](order-theory.posets.mdᵉ)
`P`ᵉ suchᵉ thatᵉ forᵉ everyᵉ twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ in `P`ᵉ theᵉ
[disjunction](foundation.disjunction.mdᵉ) `(xᵉ ≤ᵉ yᵉ) ∨ᵉ (yᵉ ≤ᵉ x)`ᵉ holds.ᵉ Inᵉ otherᵉ
words,ᵉ totalᵉ ordersᵉ areᵉ totallyᵉ orderedᵉ in theᵉ senseᵉ thatᵉ anyᵉ twoᵉ elementsᵉ areᵉ
comparable.ᵉ

## Definitions

### Being a totally ordered poset

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  incident-Poset-Propᵉ : (xᵉ yᵉ : type-Posetᵉ Xᵉ) → Propᵉ l2ᵉ
  incident-Poset-Propᵉ = incident-Preorder-Propᵉ (preorder-Posetᵉ Xᵉ)

  incident-Posetᵉ : (xᵉ yᵉ : type-Posetᵉ Xᵉ) → UUᵉ l2ᵉ
  incident-Posetᵉ = incident-Preorderᵉ (preorder-Posetᵉ Xᵉ)

  is-prop-incident-Posetᵉ :
    (xᵉ yᵉ : type-Posetᵉ Xᵉ) → is-propᵉ (incident-Posetᵉ xᵉ yᵉ)
  is-prop-incident-Posetᵉ = is-prop-incident-Preorderᵉ (preorder-Posetᵉ Xᵉ)

  is-total-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-total-Poset-Propᵉ = is-total-Preorder-Propᵉ (preorder-Posetᵉ Xᵉ)

  is-total-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-total-Posetᵉ = is-total-Preorderᵉ (preorder-Posetᵉ Xᵉ)

  is-prop-is-total-Posetᵉ : is-propᵉ is-total-Posetᵉ
  is-prop-is-total-Posetᵉ = is-prop-is-total-Preorderᵉ (preorder-Posetᵉ Xᵉ)
```

### The type of total orders

```agda
Total-Orderᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Total-Orderᵉ l1ᵉ l2ᵉ = Σᵉ (Posetᵉ l1ᵉ l2ᵉ) is-total-Posetᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Total-Orderᵉ l1ᵉ l2ᵉ)
  where

  poset-Total-Orderᵉ : Posetᵉ l1ᵉ l2ᵉ
  poset-Total-Orderᵉ = pr1ᵉ Xᵉ

  preorder-Total-Orderᵉ : Preorderᵉ l1ᵉ l2ᵉ
  preorder-Total-Orderᵉ = preorder-Posetᵉ poset-Total-Orderᵉ

  is-total-Total-Orderᵉ : is-total-Posetᵉ (poset-Total-Orderᵉ)
  is-total-Total-Orderᵉ = pr2ᵉ Xᵉ

  type-Total-Orderᵉ : UUᵉ l1ᵉ
  type-Total-Orderᵉ = type-Posetᵉ poset-Total-Orderᵉ

  leq-Total-Order-Propᵉ : (xᵉ yᵉ : type-Total-Orderᵉ) → Propᵉ l2ᵉ
  leq-Total-Order-Propᵉ = leq-Poset-Propᵉ poset-Total-Orderᵉ

  leq-Total-Orderᵉ : (xᵉ yᵉ : type-Total-Orderᵉ) → UUᵉ l2ᵉ
  leq-Total-Orderᵉ = leq-Posetᵉ poset-Total-Orderᵉ

  is-prop-leq-Total-Orderᵉ :
    (xᵉ yᵉ : type-Total-Orderᵉ) → is-propᵉ (leq-Total-Orderᵉ xᵉ yᵉ)
  is-prop-leq-Total-Orderᵉ = is-prop-leq-Posetᵉ poset-Total-Orderᵉ

  concatenate-eq-leq-Total-Orderᵉ :
    {xᵉ yᵉ zᵉ : type-Total-Orderᵉ} → xᵉ ＝ᵉ yᵉ →
    leq-Total-Orderᵉ yᵉ zᵉ → leq-Total-Orderᵉ xᵉ zᵉ
  concatenate-eq-leq-Total-Orderᵉ = concatenate-eq-leq-Posetᵉ poset-Total-Orderᵉ

  concatenate-leq-eq-Total-Orderᵉ :
    {xᵉ yᵉ zᵉ : type-Total-Orderᵉ} →
    leq-Total-Orderᵉ xᵉ yᵉ → yᵉ ＝ᵉ zᵉ → leq-Total-Orderᵉ xᵉ zᵉ
  concatenate-leq-eq-Total-Orderᵉ = concatenate-leq-eq-Posetᵉ poset-Total-Orderᵉ

  refl-leq-Total-Orderᵉ : is-reflexiveᵉ leq-Total-Orderᵉ
  refl-leq-Total-Orderᵉ = refl-leq-Posetᵉ poset-Total-Orderᵉ

  transitive-leq-Total-Orderᵉ : is-transitiveᵉ leq-Total-Orderᵉ
  transitive-leq-Total-Orderᵉ = transitive-leq-Posetᵉ poset-Total-Orderᵉ

  antisymmetric-leq-Total-Orderᵉ : is-antisymmetricᵉ leq-Total-Orderᵉ
  antisymmetric-leq-Total-Orderᵉ = antisymmetric-leq-Posetᵉ poset-Total-Orderᵉ

  is-set-type-Total-Orderᵉ : is-setᵉ type-Total-Orderᵉ
  is-set-type-Total-Orderᵉ = is-set-type-Posetᵉ poset-Total-Orderᵉ

  set-Total-Orderᵉ : Setᵉ l1ᵉ
  set-Total-Orderᵉ = set-Posetᵉ poset-Total-Orderᵉ
```