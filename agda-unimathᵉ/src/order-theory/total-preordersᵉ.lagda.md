# Total preorders

```agda
module order-theory.total-preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.disjunctionᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.preordersᵉ
```

</details>

## Idea

Aᵉ **totalᵉ preorder**ᵉ isᵉ aᵉ preorderᵉ `P`ᵉ suchᵉ thatᵉ forᵉ everyᵉ twoᵉ elementsᵉ
`xᵉ yᵉ : P`ᵉ theᵉ disjunctionᵉ `(xᵉ ≤ᵉ yᵉ) ∨ᵉ (yᵉ ≤ᵉ x)`ᵉ holds.ᵉ Inᵉ otherᵉ words,ᵉ totalᵉ
preordersᵉ areᵉ totallyᵉ orderedᵉ in theᵉ senseᵉ thatᵉ anyᵉ twoᵉ elementsᵉ canᵉ beᵉ
compared.ᵉ

## Definition

### Being a total preorder

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  where

  incident-Preorder-Propᵉ : (xᵉ yᵉ : type-Preorderᵉ Xᵉ) → Propᵉ l2ᵉ
  incident-Preorder-Propᵉ xᵉ yᵉ =
    (leq-Preorder-Propᵉ Xᵉ xᵉ yᵉ) ∨ᵉ (leq-Preorder-Propᵉ Xᵉ yᵉ xᵉ)

  incident-Preorderᵉ : (xᵉ yᵉ : type-Preorderᵉ Xᵉ) → UUᵉ l2ᵉ
  incident-Preorderᵉ xᵉ yᵉ = type-Propᵉ (incident-Preorder-Propᵉ xᵉ yᵉ)

  is-prop-incident-Preorderᵉ :
    (xᵉ yᵉ : type-Preorderᵉ Xᵉ) → is-propᵉ (incident-Preorderᵉ xᵉ yᵉ)
  is-prop-incident-Preorderᵉ xᵉ yᵉ = is-prop-type-Propᵉ (incident-Preorder-Propᵉ xᵉ yᵉ)

  is-total-Preorder-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-total-Preorder-Propᵉ =
    Π-Propᵉ
      ( type-Preorderᵉ Xᵉ)
      ( λ xᵉ → Π-Propᵉ ( type-Preorderᵉ Xᵉ) (λ yᵉ → incident-Preorder-Propᵉ xᵉ yᵉ))

  is-total-Preorderᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-total-Preorderᵉ = type-Propᵉ is-total-Preorder-Propᵉ

  is-prop-is-total-Preorderᵉ : is-propᵉ is-total-Preorderᵉ
  is-prop-is-total-Preorderᵉ = is-prop-type-Propᵉ is-total-Preorder-Propᵉ
```

### The type of total preorder

```agda
Total-Preorderᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Total-Preorderᵉ l1ᵉ l2ᵉ = Σᵉ (Preorderᵉ l1ᵉ l2ᵉ) is-total-Preorderᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Total-Preorderᵉ l1ᵉ l2ᵉ)
  where

  preorder-Total-Preorderᵉ : Preorderᵉ l1ᵉ l2ᵉ
  preorder-Total-Preorderᵉ = pr1ᵉ Xᵉ

  is-total-preorder-Total-Preorderᵉ : is-total-Preorderᵉ preorder-Total-Preorderᵉ
  is-total-preorder-Total-Preorderᵉ = pr2ᵉ Xᵉ

  type-Total-Preorderᵉ : UUᵉ l1ᵉ
  type-Total-Preorderᵉ = type-Preorderᵉ preorder-Total-Preorderᵉ

  leq-Total-Preorder-Propᵉ : (xᵉ yᵉ : type-Total-Preorderᵉ) → Propᵉ l2ᵉ
  leq-Total-Preorder-Propᵉ = leq-Preorder-Propᵉ preorder-Total-Preorderᵉ

  leq-Total-Preorderᵉ : (xᵉ yᵉ : type-Total-Preorderᵉ) → UUᵉ l2ᵉ
  leq-Total-Preorderᵉ = leq-Preorderᵉ preorder-Total-Preorderᵉ

  is-prop-leq-Total-Preorderᵉ :
    (xᵉ yᵉ : type-Total-Preorderᵉ) → is-propᵉ (leq-Total-Preorderᵉ xᵉ yᵉ)
  is-prop-leq-Total-Preorderᵉ = is-prop-leq-Preorderᵉ preorder-Total-Preorderᵉ

  refl-leq-Total-Preorderᵉ : is-reflexiveᵉ leq-Total-Preorderᵉ
  refl-leq-Total-Preorderᵉ = refl-leq-Preorderᵉ preorder-Total-Preorderᵉ

  transitive-leq-Total-Preorderᵉ : is-transitiveᵉ leq-Total-Preorderᵉ
  transitive-leq-Total-Preorderᵉ =
    transitive-leq-Preorderᵉ preorder-Total-Preorderᵉ
```