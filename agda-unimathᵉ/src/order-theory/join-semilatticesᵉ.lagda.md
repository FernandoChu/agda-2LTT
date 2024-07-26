# Join-semilattices

```agda
module order-theory.join-semilatticesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.semigroupsᵉ

open import order-theory.least-upper-bounds-posetsᵉ
open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
open import order-theory.upper-bounds-posetsᵉ
```

</details>

## Idea

Aᵉ **join-semilattice**ᵉ isᵉ aᵉ posetᵉ in whichᵉ everyᵉ pairᵉ ofᵉ elementsᵉ hasᵉ aᵉ leastᵉ
binaryᵉ upperᵉ bound.ᵉ Alternatively,ᵉ join-semilatticesᵉ canᵉ beᵉ definedᵉ
algebraicallyᵉ asᵉ aᵉ setᵉ `X`ᵉ equippedᵉ with aᵉ binaryᵉ operationᵉ `∧ᵉ : Xᵉ → Xᵉ → X`ᵉ
satisfyingᵉ

1.ᵉ Asociativityᵉ: `(xᵉ ∧ᵉ yᵉ) ∧ᵉ zᵉ ＝ᵉ xᵉ ∧ᵉ (yᵉ ∧ᵉ z)`,ᵉ
2.ᵉ Commutativityᵉ: `xᵉ ∧ᵉ yᵉ ＝ᵉ yᵉ ∧ᵉ x`,ᵉ
3.ᵉ Idempotencyᵉ: `xᵉ ∧ᵉ xᵉ ＝ᵉ x`.ᵉ

Noteᵉ thatᵉ thisᵉ definitionᵉ isᵉ identicalᵉ to theᵉ definitionᵉ ofᵉ
[meet-semilattices](order-theory.meet-semilattices.md).ᵉ Weᵉ willᵉ followᵉ theᵉ
algebraicᵉ approachᵉ forᵉ ourᵉ principalᵉ definitionᵉ ofᵉ join-semilattices,ᵉ sinceᵉ itᵉ
requiresᵉ onlyᵉ oneᵉ universeᵉ level.ᵉ Thisᵉ isᵉ necessaryᵉ in orderᵉ to considerᵉ theᵉ
[largeᵉ category](category-theory.large-categories.mdᵉ) ofᵉ join-semilattices.ᵉ

## Definitions

### The predicate on semigroups of being a join-semilattice

```agda
module _
  {lᵉ : Level} (Xᵉ : Semigroupᵉ lᵉ)
  where

  is-join-semilattice-prop-Semigroupᵉ : Propᵉ lᵉ
  is-join-semilattice-prop-Semigroupᵉ =
    product-Propᵉ
      ( Π-Propᵉ
        ( type-Semigroupᵉ Xᵉ)
        ( λ xᵉ →
          Π-Propᵉ
            ( type-Semigroupᵉ Xᵉ)
            ( λ yᵉ →
              Id-Propᵉ
                ( set-Semigroupᵉ Xᵉ)
                ( mul-Semigroupᵉ Xᵉ xᵉ yᵉ)
                ( mul-Semigroupᵉ Xᵉ yᵉ xᵉ))))
      ( Π-Propᵉ
        ( type-Semigroupᵉ Xᵉ)
        ( λ xᵉ →
          Id-Propᵉ
            ( set-Semigroupᵉ Xᵉ)
            ( mul-Semigroupᵉ Xᵉ xᵉ xᵉ)
            ( xᵉ)))

  is-join-semilattice-Semigroupᵉ : UUᵉ lᵉ
  is-join-semilattice-Semigroupᵉ =
    type-Propᵉ is-join-semilattice-prop-Semigroupᵉ

  is-prop-is-join-semilattice-Semigroupᵉ :
    is-propᵉ is-join-semilattice-Semigroupᵉ
  is-prop-is-join-semilattice-Semigroupᵉ =
    is-prop-type-Propᵉ is-join-semilattice-prop-Semigroupᵉ
```

### The algebraic definition of join-semilattices

```agda
Join-Semilatticeᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Join-Semilatticeᵉ lᵉ = type-subtypeᵉ is-join-semilattice-prop-Semigroupᵉ

module _
  {lᵉ : Level} (Xᵉ : Join-Semilatticeᵉ lᵉ)
  where

  semigroup-Join-Semilatticeᵉ : Semigroupᵉ lᵉ
  semigroup-Join-Semilatticeᵉ = pr1ᵉ Xᵉ

  set-Join-Semilatticeᵉ : Setᵉ lᵉ
  set-Join-Semilatticeᵉ = set-Semigroupᵉ semigroup-Join-Semilatticeᵉ

  type-Join-Semilatticeᵉ : UUᵉ lᵉ
  type-Join-Semilatticeᵉ = type-Semigroupᵉ semigroup-Join-Semilatticeᵉ

  is-set-type-Join-Semilatticeᵉ : is-setᵉ type-Join-Semilatticeᵉ
  is-set-type-Join-Semilatticeᵉ =
    is-set-type-Semigroupᵉ semigroup-Join-Semilatticeᵉ

  join-Join-Semilatticeᵉ : (xᵉ yᵉ : type-Join-Semilatticeᵉ) → type-Join-Semilatticeᵉ
  join-Join-Semilatticeᵉ = mul-Semigroupᵉ semigroup-Join-Semilatticeᵉ

  join-Join-Semilattice'ᵉ : (xᵉ yᵉ : type-Join-Semilatticeᵉ) → type-Join-Semilatticeᵉ
  join-Join-Semilattice'ᵉ xᵉ yᵉ = join-Join-Semilatticeᵉ yᵉ xᵉ

  private
    _∨ᵉ_ = join-Join-Semilatticeᵉ

  associative-join-Join-Semilatticeᵉ :
    (xᵉ yᵉ zᵉ : type-Join-Semilatticeᵉ) → ((xᵉ ∨ᵉ yᵉ) ∨ᵉ zᵉ) ＝ᵉ (xᵉ ∨ᵉ (yᵉ ∨ᵉ zᵉ))
  associative-join-Join-Semilatticeᵉ =
    associative-mul-Semigroupᵉ semigroup-Join-Semilatticeᵉ

  is-join-semilattice-Join-Semilatticeᵉ :
    is-join-semilattice-Semigroupᵉ semigroup-Join-Semilatticeᵉ
  is-join-semilattice-Join-Semilatticeᵉ = pr2ᵉ Xᵉ

  commutative-join-Join-Semilatticeᵉ :
    (xᵉ yᵉ : type-Join-Semilatticeᵉ) → (xᵉ ∨ᵉ yᵉ) ＝ᵉ (yᵉ ∨ᵉ xᵉ)
  commutative-join-Join-Semilatticeᵉ =
    pr1ᵉ is-join-semilattice-Join-Semilatticeᵉ

  idempotent-join-Join-Semilatticeᵉ :
    (xᵉ : type-Join-Semilatticeᵉ) → (xᵉ ∨ᵉ xᵉ) ＝ᵉ xᵉ
  idempotent-join-Join-Semilatticeᵉ =
    pr2ᵉ is-join-semilattice-Join-Semilatticeᵉ

  leq-Join-Semilattice-Propᵉ :
    (xᵉ yᵉ : type-Join-Semilatticeᵉ) → Propᵉ lᵉ
  leq-Join-Semilattice-Propᵉ xᵉ yᵉ =
    Id-Propᵉ set-Join-Semilatticeᵉ (xᵉ ∨ᵉ yᵉ) yᵉ

  leq-Join-Semilatticeᵉ :
    (xᵉ yᵉ : type-Join-Semilatticeᵉ) → UUᵉ lᵉ
  leq-Join-Semilatticeᵉ xᵉ yᵉ = type-Propᵉ (leq-Join-Semilattice-Propᵉ xᵉ yᵉ)

  is-prop-leq-Join-Semilatticeᵉ :
    (xᵉ yᵉ : type-Join-Semilatticeᵉ) → is-propᵉ (leq-Join-Semilatticeᵉ xᵉ yᵉ)
  is-prop-leq-Join-Semilatticeᵉ xᵉ yᵉ =
    is-prop-type-Propᵉ (leq-Join-Semilattice-Propᵉ xᵉ yᵉ)

  private
    _≤ᵉ_ = leq-Join-Semilatticeᵉ

  refl-leq-Join-Semilatticeᵉ : is-reflexiveᵉ leq-Join-Semilatticeᵉ
  refl-leq-Join-Semilatticeᵉ xᵉ = idempotent-join-Join-Semilatticeᵉ xᵉ

  transitive-leq-Join-Semilatticeᵉ : is-transitiveᵉ leq-Join-Semilatticeᵉ
  transitive-leq-Join-Semilatticeᵉ xᵉ yᵉ zᵉ Hᵉ Kᵉ =
    equational-reasoningᵉ
      xᵉ ∨ᵉ zᵉ
      ＝ᵉ xᵉ ∨ᵉ (yᵉ ∨ᵉ zᵉ)
        byᵉ apᵉ (join-Join-Semilatticeᵉ xᵉ) (invᵉ Hᵉ)
      ＝ᵉ (xᵉ ∨ᵉ yᵉ) ∨ᵉ zᵉ
        byᵉ invᵉ (associative-join-Join-Semilatticeᵉ xᵉ yᵉ zᵉ)
      ＝ᵉ yᵉ ∨ᵉ zᵉ
        byᵉ apᵉ (join-Join-Semilattice'ᵉ zᵉ) Kᵉ
      ＝ᵉ zᵉ
        byᵉ Hᵉ

  antisymmetric-leq-Join-Semilatticeᵉ : is-antisymmetricᵉ leq-Join-Semilatticeᵉ
  antisymmetric-leq-Join-Semilatticeᵉ xᵉ yᵉ Hᵉ Kᵉ =
    equational-reasoningᵉ
      xᵉ ＝ᵉ yᵉ ∨ᵉ xᵉ
          byᵉ invᵉ Kᵉ
        ＝ᵉ xᵉ ∨ᵉ yᵉ
          byᵉ commutative-join-Join-Semilatticeᵉ yᵉ xᵉ
        ＝ᵉ yᵉ
          byᵉ Hᵉ

  preorder-Join-Semilatticeᵉ : Preorderᵉ lᵉ lᵉ
  pr1ᵉ preorder-Join-Semilatticeᵉ = type-Join-Semilatticeᵉ
  pr1ᵉ (pr2ᵉ preorder-Join-Semilatticeᵉ) = leq-Join-Semilattice-Propᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ preorder-Join-Semilatticeᵉ)) = refl-leq-Join-Semilatticeᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ preorder-Join-Semilatticeᵉ)) = transitive-leq-Join-Semilatticeᵉ

  poset-Join-Semilatticeᵉ : Posetᵉ lᵉ lᵉ
  pr1ᵉ poset-Join-Semilatticeᵉ = preorder-Join-Semilatticeᵉ
  pr2ᵉ poset-Join-Semilatticeᵉ = antisymmetric-leq-Join-Semilatticeᵉ

  is-binary-upper-bound-join-Join-Semilatticeᵉ :
    (xᵉ yᵉ : type-Join-Semilatticeᵉ) →
    is-binary-upper-bound-Posetᵉ
      ( poset-Join-Semilatticeᵉ)
      ( xᵉ)
      ( yᵉ)
      ( join-Join-Semilatticeᵉ xᵉ yᵉ)
  pr1ᵉ (is-binary-upper-bound-join-Join-Semilatticeᵉ xᵉ yᵉ) =
    equational-reasoningᵉ
      xᵉ ∨ᵉ (xᵉ ∨ᵉ yᵉ)
      ＝ᵉ (xᵉ ∨ᵉ xᵉ) ∨ᵉ yᵉ
        byᵉ
        invᵉ (associative-join-Join-Semilatticeᵉ xᵉ xᵉ yᵉ)
      ＝ᵉ xᵉ ∨ᵉ yᵉ
        byᵉ
        apᵉ (join-Join-Semilattice'ᵉ yᵉ) (idempotent-join-Join-Semilatticeᵉ xᵉ)
  pr2ᵉ (is-binary-upper-bound-join-Join-Semilatticeᵉ xᵉ yᵉ) =
    equational-reasoningᵉ
      yᵉ ∨ᵉ (xᵉ ∨ᵉ yᵉ)
      ＝ᵉ (xᵉ ∨ᵉ yᵉ) ∨ᵉ yᵉ
        byᵉ commutative-join-Join-Semilatticeᵉ yᵉ (xᵉ ∨ᵉ yᵉ)
      ＝ᵉ xᵉ ∨ᵉ (yᵉ ∨ᵉ yᵉ)
        byᵉ
        associative-join-Join-Semilatticeᵉ xᵉ yᵉ yᵉ
      ＝ᵉ xᵉ ∨ᵉ yᵉ
        byᵉ
        apᵉ (join-Join-Semilatticeᵉ xᵉ) (idempotent-join-Join-Semilatticeᵉ yᵉ)

  is-least-binary-upper-bound-join-Join-Semilatticeᵉ :
    (xᵉ yᵉ : type-Join-Semilatticeᵉ) →
    is-least-binary-upper-bound-Posetᵉ
      ( poset-Join-Semilatticeᵉ)
      ( xᵉ)
      ( yᵉ)
      ( join-Join-Semilatticeᵉ xᵉ yᵉ)
  is-least-binary-upper-bound-join-Join-Semilatticeᵉ xᵉ yᵉ =
    prove-is-least-binary-upper-bound-Posetᵉ
      ( poset-Join-Semilatticeᵉ)
      ( is-binary-upper-bound-join-Join-Semilatticeᵉ xᵉ yᵉ)
      ( λ zᵉ (Hᵉ ,ᵉ Kᵉ) →
        equational-reasoningᵉ
          (xᵉ ∨ᵉ yᵉ) ∨ᵉ zᵉ
          ＝ᵉ xᵉ ∨ᵉ (yᵉ ∨ᵉ zᵉ)
            byᵉ associative-join-Join-Semilatticeᵉ xᵉ yᵉ zᵉ
          ＝ᵉ xᵉ ∨ᵉ zᵉ
            byᵉ apᵉ (join-Join-Semilatticeᵉ xᵉ) Kᵉ
          ＝ᵉ zᵉ
            byᵉ Hᵉ)
```

### The predicate on posets of being a join-semilattice

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  is-join-semilattice-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-join-semilattice-Poset-Propᵉ =
    Π-Propᵉ
      ( type-Posetᵉ Pᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( type-Posetᵉ Pᵉ)
          ( has-least-binary-upper-bound-Poset-Propᵉ Pᵉ xᵉ))

  is-join-semilattice-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-join-semilattice-Posetᵉ = type-Propᵉ is-join-semilattice-Poset-Propᵉ

  is-prop-is-join-semilattice-Posetᵉ :
    is-propᵉ is-join-semilattice-Posetᵉ
  is-prop-is-join-semilattice-Posetᵉ =
    is-prop-type-Propᵉ is-join-semilattice-Poset-Propᵉ

  module _
    (Hᵉ : is-join-semilattice-Posetᵉ)
    where

    join-is-join-semilattice-Posetᵉ :
      type-Posetᵉ Pᵉ → type-Posetᵉ Pᵉ → type-Posetᵉ Pᵉ
    join-is-join-semilattice-Posetᵉ xᵉ yᵉ = pr1ᵉ (Hᵉ xᵉ yᵉ)

    is-least-binary-upper-bound-join-is-join-semilattice-Posetᵉ :
      (xᵉ yᵉ : type-Posetᵉ Pᵉ) →
      is-least-binary-upper-bound-Posetᵉ Pᵉ xᵉ yᵉ
        ( join-is-join-semilattice-Posetᵉ xᵉ yᵉ)
    is-least-binary-upper-bound-join-is-join-semilattice-Posetᵉ xᵉ yᵉ =
      pr2ᵉ (Hᵉ xᵉ yᵉ)
```

### The order-theoretic definition of join semilattices

```agda
Order-Theoretic-Join-Semilatticeᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Order-Theoretic-Join-Semilatticeᵉ l1ᵉ l2ᵉ =
  Σᵉ (Posetᵉ l1ᵉ l2ᵉ) is-join-semilattice-Posetᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Order-Theoretic-Join-Semilatticeᵉ l1ᵉ l2ᵉ)
  where

  poset-Order-Theoretic-Join-Semilatticeᵉ : Posetᵉ l1ᵉ l2ᵉ
  poset-Order-Theoretic-Join-Semilatticeᵉ = pr1ᵉ Aᵉ

  type-Order-Theoretic-Join-Semilatticeᵉ : UUᵉ l1ᵉ
  type-Order-Theoretic-Join-Semilatticeᵉ =
    type-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ

  is-set-type-Order-Theoretic-Join-Semilatticeᵉ :
    is-setᵉ type-Order-Theoretic-Join-Semilatticeᵉ
  is-set-type-Order-Theoretic-Join-Semilatticeᵉ =
    is-set-type-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ

  set-Order-Theoretic-Join-Semilatticeᵉ : Setᵉ l1ᵉ
  set-Order-Theoretic-Join-Semilatticeᵉ =
    set-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ

  leq-Order-Theoretic-Join-Semilattice-Propᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Join-Semilatticeᵉ) → Propᵉ l2ᵉ
  leq-Order-Theoretic-Join-Semilattice-Propᵉ =
    leq-Poset-Propᵉ poset-Order-Theoretic-Join-Semilatticeᵉ

  leq-Order-Theoretic-Join-Semilatticeᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Join-Semilatticeᵉ) → UUᵉ l2ᵉ
  leq-Order-Theoretic-Join-Semilatticeᵉ =
    leq-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ

  is-prop-leq-Order-Theoretic-Join-Semilatticeᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Join-Semilatticeᵉ) →
    is-propᵉ (leq-Order-Theoretic-Join-Semilatticeᵉ xᵉ yᵉ)
  is-prop-leq-Order-Theoretic-Join-Semilatticeᵉ =
    is-prop-leq-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ

  refl-leq-Order-Theoretic-Join-Semilatticeᵉ :
    (xᵉ : type-Order-Theoretic-Join-Semilatticeᵉ) →
    leq-Order-Theoretic-Join-Semilatticeᵉ xᵉ xᵉ
  refl-leq-Order-Theoretic-Join-Semilatticeᵉ =
    refl-leq-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ

  antisymmetric-leq-Order-Theoretic-Join-Semilatticeᵉ :
    {xᵉ yᵉ : type-Order-Theoretic-Join-Semilatticeᵉ} →
    leq-Order-Theoretic-Join-Semilatticeᵉ xᵉ yᵉ →
    leq-Order-Theoretic-Join-Semilatticeᵉ yᵉ xᵉ →
    xᵉ ＝ᵉ yᵉ
  antisymmetric-leq-Order-Theoretic-Join-Semilatticeᵉ {xᵉ} {yᵉ} =
    antisymmetric-leq-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ xᵉ yᵉ

  transitive-leq-Order-Theoretic-Join-Semilatticeᵉ :
    (xᵉ yᵉ zᵉ : type-Order-Theoretic-Join-Semilatticeᵉ) →
    leq-Order-Theoretic-Join-Semilatticeᵉ yᵉ zᵉ →
    leq-Order-Theoretic-Join-Semilatticeᵉ xᵉ yᵉ →
    leq-Order-Theoretic-Join-Semilatticeᵉ xᵉ zᵉ
  transitive-leq-Order-Theoretic-Join-Semilatticeᵉ =
    transitive-leq-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ

  is-join-semilattice-Order-Theoretic-Join-Semilatticeᵉ :
    is-join-semilattice-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ
  is-join-semilattice-Order-Theoretic-Join-Semilatticeᵉ = pr2ᵉ Aᵉ

  join-Order-Theoretic-Join-Semilatticeᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Join-Semilatticeᵉ) →
    type-Order-Theoretic-Join-Semilatticeᵉ
  join-Order-Theoretic-Join-Semilatticeᵉ =
    join-is-join-semilattice-Posetᵉ
      poset-Order-Theoretic-Join-Semilatticeᵉ
      is-join-semilattice-Order-Theoretic-Join-Semilatticeᵉ

  private
    _∨ᵉ_ = join-Order-Theoretic-Join-Semilatticeᵉ

  is-least-binary-upper-bound-join-Order-Theoretic-Join-Semilatticeᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Join-Semilatticeᵉ) →
    is-least-binary-upper-bound-Posetᵉ
      ( poset-Order-Theoretic-Join-Semilatticeᵉ)
      ( xᵉ)
      ( yᵉ)
      ( xᵉ ∨ᵉ yᵉ)
  is-least-binary-upper-bound-join-Order-Theoretic-Join-Semilatticeᵉ =
    is-least-binary-upper-bound-join-is-join-semilattice-Posetᵉ
      poset-Order-Theoretic-Join-Semilatticeᵉ
      is-join-semilattice-Order-Theoretic-Join-Semilatticeᵉ

  is-binary-upper-bound-join-Order-Theoretic-Join-Semilatticeᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Join-Semilatticeᵉ) →
    is-binary-upper-bound-Posetᵉ
      ( poset-Order-Theoretic-Join-Semilatticeᵉ)
      ( xᵉ)
      ( yᵉ)
      ( xᵉ ∨ᵉ yᵉ)
  is-binary-upper-bound-join-Order-Theoretic-Join-Semilatticeᵉ xᵉ yᵉ =
    is-binary-upper-bound-is-least-binary-upper-bound-Posetᵉ
      ( poset-Order-Theoretic-Join-Semilatticeᵉ)
      ( is-least-binary-upper-bound-join-Order-Theoretic-Join-Semilatticeᵉ
        ( xᵉ)
        ( yᵉ))

  leq-left-join-Order-Theoretic-Join-Semilatticeᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Join-Semilatticeᵉ) →
    leq-Order-Theoretic-Join-Semilatticeᵉ xᵉ (xᵉ ∨ᵉ yᵉ)
  leq-left-join-Order-Theoretic-Join-Semilatticeᵉ xᵉ yᵉ =
    leq-left-is-binary-upper-bound-Posetᵉ
      ( poset-Order-Theoretic-Join-Semilatticeᵉ)
      ( is-binary-upper-bound-join-Order-Theoretic-Join-Semilatticeᵉ xᵉ yᵉ)

  leq-right-join-Order-Theoretic-Join-Semilatticeᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Join-Semilatticeᵉ) →
    leq-Order-Theoretic-Join-Semilatticeᵉ yᵉ (xᵉ ∨ᵉ yᵉ)
  leq-right-join-Order-Theoretic-Join-Semilatticeᵉ xᵉ yᵉ =
    leq-right-is-binary-upper-bound-Posetᵉ
      ( poset-Order-Theoretic-Join-Semilatticeᵉ)
      ( is-binary-upper-bound-join-Order-Theoretic-Join-Semilatticeᵉ xᵉ yᵉ)

  leq-join-Order-Theoretic-Join-Semilatticeᵉ :
    {xᵉ yᵉ zᵉ : type-Order-Theoretic-Join-Semilatticeᵉ} →
    leq-Order-Theoretic-Join-Semilatticeᵉ xᵉ zᵉ →
    leq-Order-Theoretic-Join-Semilatticeᵉ yᵉ zᵉ →
    leq-Order-Theoretic-Join-Semilatticeᵉ (xᵉ ∨ᵉ yᵉ) zᵉ
  leq-join-Order-Theoretic-Join-Semilatticeᵉ {xᵉ} {yᵉ} {zᵉ} Hᵉ Kᵉ =
    forward-implicationᵉ
      ( is-least-binary-upper-bound-join-Order-Theoretic-Join-Semilatticeᵉ
        ( xᵉ)
        ( yᵉ)
        ( zᵉ))
      ( Hᵉ ,ᵉ Kᵉ)
```

## Properties

### The join operation of order theoretic join-semilattices is associative

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Order-Theoretic-Join-Semilatticeᵉ l1ᵉ l2ᵉ)
  (xᵉ yᵉ zᵉ : type-Order-Theoretic-Join-Semilatticeᵉ Aᵉ)
  where

  private
    _∨ᵉ_ = join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
    _≤ᵉ_ = leq-Order-Theoretic-Join-Semilatticeᵉ Aᵉ

  leq-left-triple-join-Order-Theoretic-Join-Semilatticeᵉ :
    xᵉ ≤ᵉ ((xᵉ ∨ᵉ yᵉ) ∨ᵉ zᵉ)
  leq-left-triple-join-Order-Theoretic-Join-Semilatticeᵉ =
    calculate-in-Posetᵉ
      ( poset-Order-Theoretic-Join-Semilatticeᵉ Aᵉ)
      chain-of-inequalitiesᵉ
        xᵉ ≤ᵉ xᵉ ∨ᵉ yᵉ
            byᵉ leq-left-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ xᵉ yᵉ
            in-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
          ≤ᵉ (xᵉ ∨ᵉ yᵉ) ∨ᵉ zᵉ
            byᵉ leq-left-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ (xᵉ ∨ᵉ yᵉ) zᵉ
            in-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ Aᵉ

  leq-center-triple-join-Order-Theoretic-Join-Semilatticeᵉ :
    yᵉ ≤ᵉ ((xᵉ ∨ᵉ yᵉ) ∨ᵉ zᵉ)
  leq-center-triple-join-Order-Theoretic-Join-Semilatticeᵉ =
    calculate-in-Posetᵉ
      ( poset-Order-Theoretic-Join-Semilatticeᵉ Aᵉ)
      chain-of-inequalitiesᵉ
        yᵉ ≤ᵉ xᵉ ∨ᵉ yᵉ
            byᵉ leq-right-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ xᵉ yᵉ
            in-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
          ≤ᵉ (xᵉ ∨ᵉ yᵉ) ∨ᵉ zᵉ
            byᵉ leq-left-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ (xᵉ ∨ᵉ yᵉ) zᵉ
            in-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ Aᵉ

  leq-right-triple-join-Order-Theoretic-Join-Semilatticeᵉ :
    zᵉ ≤ᵉ ((xᵉ ∨ᵉ yᵉ) ∨ᵉ zᵉ)
  leq-right-triple-join-Order-Theoretic-Join-Semilatticeᵉ =
    leq-right-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ (xᵉ ∨ᵉ yᵉ) zᵉ

  leq-left-triple-join-Order-Theoretic-Join-Semilattice'ᵉ :
    xᵉ ≤ᵉ (xᵉ ∨ᵉ (yᵉ ∨ᵉ zᵉ))
  leq-left-triple-join-Order-Theoretic-Join-Semilattice'ᵉ =
    leq-left-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ xᵉ (yᵉ ∨ᵉ zᵉ)

  leq-center-triple-join-Order-Theoretic-Join-Semilattice'ᵉ :
    yᵉ ≤ᵉ (xᵉ ∨ᵉ (yᵉ ∨ᵉ zᵉ))
  leq-center-triple-join-Order-Theoretic-Join-Semilattice'ᵉ =
    calculate-in-Posetᵉ
      ( poset-Order-Theoretic-Join-Semilatticeᵉ Aᵉ)
      chain-of-inequalitiesᵉ
        yᵉ ≤ᵉ yᵉ ∨ᵉ zᵉ
            byᵉ leq-left-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ yᵉ zᵉ
            in-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
          ≤ᵉ xᵉ ∨ᵉ (yᵉ ∨ᵉ zᵉ)
            byᵉ leq-right-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ xᵉ (yᵉ ∨ᵉ zᵉ)
            in-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ Aᵉ

  leq-right-triple-join-Order-Theoretic-Join-Semilattice'ᵉ :
    zᵉ ≤ᵉ (xᵉ ∨ᵉ (yᵉ ∨ᵉ zᵉ))
  leq-right-triple-join-Order-Theoretic-Join-Semilattice'ᵉ =
    calculate-in-Posetᵉ
      ( poset-Order-Theoretic-Join-Semilatticeᵉ Aᵉ)
      chain-of-inequalitiesᵉ
        zᵉ ≤ᵉ yᵉ ∨ᵉ zᵉ
            byᵉ leq-right-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ yᵉ zᵉ
            in-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
          ≤ᵉ xᵉ ∨ᵉ (yᵉ ∨ᵉ zᵉ)
            byᵉ leq-right-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ xᵉ (yᵉ ∨ᵉ zᵉ)
            in-Posetᵉ poset-Order-Theoretic-Join-Semilatticeᵉ Aᵉ

  leq-associative-join-Order-Theoretic-Join-Semilatticeᵉ :
    ((xᵉ ∨ᵉ yᵉ) ∨ᵉ zᵉ) ≤ᵉ (xᵉ ∨ᵉ (yᵉ ∨ᵉ zᵉ))
  leq-associative-join-Order-Theoretic-Join-Semilatticeᵉ =
    leq-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
      ( leq-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
        ( leq-left-triple-join-Order-Theoretic-Join-Semilattice'ᵉ)
        ( leq-center-triple-join-Order-Theoretic-Join-Semilattice'ᵉ))
      ( leq-right-triple-join-Order-Theoretic-Join-Semilattice'ᵉ)

  leq-associative-join-Order-Theoretic-Join-Semilattice'ᵉ :
    (xᵉ ∨ᵉ (yᵉ ∨ᵉ zᵉ)) ≤ᵉ ((xᵉ ∨ᵉ yᵉ) ∨ᵉ zᵉ)
  leq-associative-join-Order-Theoretic-Join-Semilattice'ᵉ =
    leq-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
      ( leq-left-triple-join-Order-Theoretic-Join-Semilatticeᵉ)
      ( leq-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
        ( leq-center-triple-join-Order-Theoretic-Join-Semilatticeᵉ)
        ( leq-right-triple-join-Order-Theoretic-Join-Semilatticeᵉ))

  associative-join-Order-Theoretic-Join-Semilatticeᵉ :
    ((xᵉ ∨ᵉ yᵉ) ∨ᵉ zᵉ) ＝ᵉ (xᵉ ∨ᵉ (yᵉ ∨ᵉ zᵉ))
  associative-join-Order-Theoretic-Join-Semilatticeᵉ =
    antisymmetric-leq-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
      leq-associative-join-Order-Theoretic-Join-Semilatticeᵉ
      leq-associative-join-Order-Theoretic-Join-Semilattice'ᵉ
```

### The join operation of order theoretic join-semilattices is commutative

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Order-Theoretic-Join-Semilatticeᵉ l1ᵉ l2ᵉ)
  (xᵉ yᵉ : type-Order-Theoretic-Join-Semilatticeᵉ Aᵉ)
  where

  private
    _∨ᵉ_ = join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
    _≤ᵉ_ = leq-Order-Theoretic-Join-Semilatticeᵉ Aᵉ

  leq-commutative-join-Order-Theoretic-Join-Semilatticeᵉ :
    (xᵉ ∨ᵉ yᵉ) ≤ᵉ (yᵉ ∨ᵉ xᵉ)
  leq-commutative-join-Order-Theoretic-Join-Semilatticeᵉ =
    leq-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
      ( leq-right-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ yᵉ xᵉ)
      ( leq-left-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ yᵉ xᵉ)

  leq-commutative-join-Order-Theoretic-Join-Semilattice'ᵉ :
    (yᵉ ∨ᵉ xᵉ) ≤ᵉ (xᵉ ∨ᵉ yᵉ)
  leq-commutative-join-Order-Theoretic-Join-Semilattice'ᵉ =
    leq-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
      ( leq-right-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ xᵉ yᵉ)
      ( leq-left-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ xᵉ yᵉ)

  commutative-join-Order-Theoretic-Join-Semilatticeᵉ :
    (xᵉ ∨ᵉ yᵉ) ＝ᵉ (yᵉ ∨ᵉ xᵉ)
  commutative-join-Order-Theoretic-Join-Semilatticeᵉ =
    antisymmetric-leq-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
      leq-commutative-join-Order-Theoretic-Join-Semilatticeᵉ
      leq-commutative-join-Order-Theoretic-Join-Semilattice'ᵉ
```

### The join operation of order theoretic join-semilattices is idempotent

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Order-Theoretic-Join-Semilatticeᵉ l1ᵉ l2ᵉ)
  (xᵉ : type-Order-Theoretic-Join-Semilatticeᵉ Aᵉ)
  where

  private
    _∨ᵉ_ = join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
    _≤ᵉ_ = leq-Order-Theoretic-Join-Semilatticeᵉ Aᵉ

  idempotent-join-Order-Theoretic-Join-Semilatticeᵉ :
    (xᵉ ∨ᵉ xᵉ) ＝ᵉ xᵉ
  idempotent-join-Order-Theoretic-Join-Semilatticeᵉ =
    antisymmetric-leq-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
      ( leq-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
        ( refl-leq-Order-Theoretic-Join-Semilatticeᵉ Aᵉ xᵉ)
        ( refl-leq-Order-Theoretic-Join-Semilatticeᵉ Aᵉ xᵉ))
      ( leq-left-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ xᵉ xᵉ)
```

### Any order theoretic join-semilattice is an algebraic join semilattice

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Order-Theoretic-Join-Semilatticeᵉ l1ᵉ l2ᵉ)
  where

  semigroup-Order-Theoretic-Join-Semilatticeᵉ : Semigroupᵉ l1ᵉ
  pr1ᵉ semigroup-Order-Theoretic-Join-Semilatticeᵉ =
    set-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
  pr1ᵉ (pr2ᵉ semigroup-Order-Theoretic-Join-Semilatticeᵉ) =
    join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
  pr2ᵉ (pr2ᵉ semigroup-Order-Theoretic-Join-Semilatticeᵉ) =
    associative-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ

  join-semilattice-Order-Theoretic-Join-Semilatticeᵉ :
    Join-Semilatticeᵉ l1ᵉ
  pr1ᵉ join-semilattice-Order-Theoretic-Join-Semilatticeᵉ =
    semigroup-Order-Theoretic-Join-Semilatticeᵉ
  pr1ᵉ (pr2ᵉ join-semilattice-Order-Theoretic-Join-Semilatticeᵉ) =
    commutative-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
  pr2ᵉ (pr2ᵉ join-semilattice-Order-Theoretic-Join-Semilatticeᵉ) =
    idempotent-join-Order-Theoretic-Join-Semilatticeᵉ Aᵉ
```