# Meet-semilattices

```agda
module order-theory.meet-semilatticesᵉ where
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

open import group-theory.isomorphisms-semigroupsᵉ
open import group-theory.semigroupsᵉ

open import order-theory.greatest-lower-bounds-posetsᵉ
open import order-theory.lower-bounds-posetsᵉ
open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
```

</details>

## Idea

Aᵉ **meet-semilattice**ᵉ isᵉ aᵉ posetᵉ in whichᵉ everyᵉ pairᵉ ofᵉ elementsᵉ hasᵉ aᵉ greatestᵉ
binary-lowerᵉ bound.ᵉ Alternatively,ᵉ meet-semilatticesᵉ canᵉ beᵉ definedᵉ
algebraicallyᵉ asᵉ aᵉ setᵉ `X`ᵉ equippedᵉ with aᵉ binaryᵉ operationᵉ `∧ᵉ : Xᵉ → Xᵉ → X`ᵉ
satisfyingᵉ

1.ᵉ Asociativityᵉ: `(xᵉ ∧ᵉ yᵉ) ∧ᵉ zᵉ ＝ᵉ xᵉ ∧ᵉ (yᵉ ∧ᵉ z)`,ᵉ
2.ᵉ Commutativityᵉ: `xᵉ ∧ᵉ yᵉ ＝ᵉ yᵉ ∧ᵉ x`,ᵉ
3.ᵉ Idempotencyᵉ: `xᵉ ∧ᵉ xᵉ ＝ᵉ x`.ᵉ

Weᵉ willᵉ followᵉ theᵉ algebraicᵉ approachᵉ forᵉ ourᵉ principalᵉ definitionᵉ ofᵉ
meet-semilattices,ᵉ sinceᵉ itᵉ requiresᵉ onlyᵉ oneᵉ universeᵉ level.ᵉ Thisᵉ isᵉ necessaryᵉ
in orderᵉ to considerᵉ theᵉ [largeᵉ category](category-theory.large-categories.mdᵉ)
ofᵉ meet-semilattices.ᵉ

## Definitions

### The predicate on semigroups of being a meet-semilattice

```agda
module _
  {lᵉ : Level} (Xᵉ : Semigroupᵉ lᵉ)
  where

  is-meet-semilattice-prop-Semigroupᵉ : Propᵉ lᵉ
  is-meet-semilattice-prop-Semigroupᵉ =
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

  is-meet-semilattice-Semigroupᵉ : UUᵉ lᵉ
  is-meet-semilattice-Semigroupᵉ =
    type-Propᵉ is-meet-semilattice-prop-Semigroupᵉ

  is-prop-is-meet-semilattice-Semigroupᵉ :
    is-propᵉ is-meet-semilattice-Semigroupᵉ
  is-prop-is-meet-semilattice-Semigroupᵉ =
    is-prop-type-Propᵉ is-meet-semilattice-prop-Semigroupᵉ
```

### The algebraic definition of meet-semilattices

```agda
Meet-Semilatticeᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Meet-Semilatticeᵉ lᵉ = type-subtypeᵉ is-meet-semilattice-prop-Semigroupᵉ

module _
  {lᵉ : Level} (Xᵉ : Meet-Semilatticeᵉ lᵉ)
  where

  semigroup-Meet-Semilatticeᵉ : Semigroupᵉ lᵉ
  semigroup-Meet-Semilatticeᵉ = pr1ᵉ Xᵉ

  set-Meet-Semilatticeᵉ : Setᵉ lᵉ
  set-Meet-Semilatticeᵉ = set-Semigroupᵉ semigroup-Meet-Semilatticeᵉ

  type-Meet-Semilatticeᵉ : UUᵉ lᵉ
  type-Meet-Semilatticeᵉ = type-Semigroupᵉ semigroup-Meet-Semilatticeᵉ

  is-set-type-Meet-Semilatticeᵉ : is-setᵉ type-Meet-Semilatticeᵉ
  is-set-type-Meet-Semilatticeᵉ =
    is-set-type-Semigroupᵉ semigroup-Meet-Semilatticeᵉ

  meet-Meet-Semilatticeᵉ : (xᵉ yᵉ : type-Meet-Semilatticeᵉ) → type-Meet-Semilatticeᵉ
  meet-Meet-Semilatticeᵉ = mul-Semigroupᵉ semigroup-Meet-Semilatticeᵉ

  meet-Meet-Semilattice'ᵉ : (xᵉ yᵉ : type-Meet-Semilatticeᵉ) → type-Meet-Semilatticeᵉ
  meet-Meet-Semilattice'ᵉ xᵉ yᵉ = meet-Meet-Semilatticeᵉ yᵉ xᵉ

  private
    _∧ᵉ_ = meet-Meet-Semilatticeᵉ

  associative-meet-Meet-Semilatticeᵉ :
    (xᵉ yᵉ zᵉ : type-Meet-Semilatticeᵉ) → ((xᵉ ∧ᵉ yᵉ) ∧ᵉ zᵉ) ＝ᵉ (xᵉ ∧ᵉ (yᵉ ∧ᵉ zᵉ))
  associative-meet-Meet-Semilatticeᵉ =
    associative-mul-Semigroupᵉ semigroup-Meet-Semilatticeᵉ

  is-meet-semilattice-Meet-Semilatticeᵉ :
    is-meet-semilattice-Semigroupᵉ semigroup-Meet-Semilatticeᵉ
  is-meet-semilattice-Meet-Semilatticeᵉ = pr2ᵉ Xᵉ

  commutative-meet-Meet-Semilatticeᵉ :
    (xᵉ yᵉ : type-Meet-Semilatticeᵉ) → (xᵉ ∧ᵉ yᵉ) ＝ᵉ (yᵉ ∧ᵉ xᵉ)
  commutative-meet-Meet-Semilatticeᵉ =
    pr1ᵉ is-meet-semilattice-Meet-Semilatticeᵉ

  idempotent-meet-Meet-Semilatticeᵉ :
    (xᵉ : type-Meet-Semilatticeᵉ) → (xᵉ ∧ᵉ xᵉ) ＝ᵉ xᵉ
  idempotent-meet-Meet-Semilatticeᵉ =
    pr2ᵉ is-meet-semilattice-Meet-Semilatticeᵉ

  leq-Meet-Semilattice-Propᵉ :
    (xᵉ yᵉ : type-Meet-Semilatticeᵉ) → Propᵉ lᵉ
  leq-Meet-Semilattice-Propᵉ xᵉ yᵉ =
    Id-Propᵉ set-Meet-Semilatticeᵉ (xᵉ ∧ᵉ yᵉ) xᵉ

  leq-Meet-Semilatticeᵉ :
    (xᵉ yᵉ : type-Meet-Semilatticeᵉ) → UUᵉ lᵉ
  leq-Meet-Semilatticeᵉ xᵉ yᵉ = type-Propᵉ (leq-Meet-Semilattice-Propᵉ xᵉ yᵉ)

  is-prop-leq-Meet-Semilatticeᵉ :
    (xᵉ yᵉ : type-Meet-Semilatticeᵉ) → is-propᵉ (leq-Meet-Semilatticeᵉ xᵉ yᵉ)
  is-prop-leq-Meet-Semilatticeᵉ xᵉ yᵉ =
    is-prop-type-Propᵉ (leq-Meet-Semilattice-Propᵉ xᵉ yᵉ)

  private
    _≤ᵉ_ = leq-Meet-Semilatticeᵉ

  refl-leq-Meet-Semilatticeᵉ : is-reflexiveᵉ leq-Meet-Semilatticeᵉ
  refl-leq-Meet-Semilatticeᵉ xᵉ = idempotent-meet-Meet-Semilatticeᵉ xᵉ

  transitive-leq-Meet-Semilatticeᵉ : is-transitiveᵉ leq-Meet-Semilatticeᵉ
  transitive-leq-Meet-Semilatticeᵉ xᵉ yᵉ zᵉ Hᵉ Kᵉ =
    equational-reasoningᵉ
      xᵉ ∧ᵉ zᵉ
      ＝ᵉ (xᵉ ∧ᵉ yᵉ) ∧ᵉ zᵉ
        byᵉ apᵉ (meet-Meet-Semilattice'ᵉ zᵉ) (invᵉ Kᵉ)
      ＝ᵉ xᵉ ∧ᵉ (yᵉ ∧ᵉ zᵉ)
        byᵉ associative-meet-Meet-Semilatticeᵉ xᵉ yᵉ zᵉ
      ＝ᵉ xᵉ ∧ᵉ yᵉ
        byᵉ apᵉ (meet-Meet-Semilatticeᵉ xᵉ) Hᵉ
      ＝ᵉ xᵉ
        byᵉ Kᵉ

  antisymmetric-leq-Meet-Semilatticeᵉ : is-antisymmetricᵉ leq-Meet-Semilatticeᵉ
  antisymmetric-leq-Meet-Semilatticeᵉ xᵉ yᵉ Hᵉ Kᵉ =
    equational-reasoningᵉ
      xᵉ ＝ᵉ xᵉ ∧ᵉ yᵉ
          byᵉ invᵉ Hᵉ
        ＝ᵉ yᵉ ∧ᵉ xᵉ
          byᵉ commutative-meet-Meet-Semilatticeᵉ xᵉ yᵉ
        ＝ᵉ yᵉ
          byᵉ Kᵉ

  preorder-Meet-Semilatticeᵉ : Preorderᵉ lᵉ lᵉ
  pr1ᵉ preorder-Meet-Semilatticeᵉ = type-Meet-Semilatticeᵉ
  pr1ᵉ (pr2ᵉ preorder-Meet-Semilatticeᵉ) = leq-Meet-Semilattice-Propᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ preorder-Meet-Semilatticeᵉ)) = refl-leq-Meet-Semilatticeᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ preorder-Meet-Semilatticeᵉ)) = transitive-leq-Meet-Semilatticeᵉ

  poset-Meet-Semilatticeᵉ : Posetᵉ lᵉ lᵉ
  pr1ᵉ poset-Meet-Semilatticeᵉ = preorder-Meet-Semilatticeᵉ
  pr2ᵉ poset-Meet-Semilatticeᵉ = antisymmetric-leq-Meet-Semilatticeᵉ

  is-binary-lower-bound-meet-Meet-Semilatticeᵉ :
    (xᵉ yᵉ : type-Meet-Semilatticeᵉ) →
    is-binary-lower-bound-Posetᵉ
      ( poset-Meet-Semilatticeᵉ)
      ( xᵉ)
      ( yᵉ)
      ( meet-Meet-Semilatticeᵉ xᵉ yᵉ)
  pr1ᵉ (is-binary-lower-bound-meet-Meet-Semilatticeᵉ xᵉ yᵉ) =
    equational-reasoningᵉ
      (xᵉ ∧ᵉ yᵉ) ∧ᵉ xᵉ
      ＝ᵉ xᵉ ∧ᵉ (xᵉ ∧ᵉ yᵉ)
        byᵉ
        commutative-meet-Meet-Semilatticeᵉ (meet-Meet-Semilatticeᵉ xᵉ yᵉ) xᵉ
      ＝ᵉ (xᵉ ∧ᵉ xᵉ) ∧ᵉ yᵉ
        byᵉ
        invᵉ (associative-meet-Meet-Semilatticeᵉ xᵉ xᵉ yᵉ)
      ＝ᵉ xᵉ ∧ᵉ yᵉ
        byᵉ
        apᵉ (meet-Meet-Semilattice'ᵉ yᵉ) (idempotent-meet-Meet-Semilatticeᵉ xᵉ)
  pr2ᵉ (is-binary-lower-bound-meet-Meet-Semilatticeᵉ xᵉ yᵉ) =
    equational-reasoningᵉ
      (xᵉ ∧ᵉ yᵉ) ∧ᵉ yᵉ
      ＝ᵉ xᵉ ∧ᵉ (yᵉ ∧ᵉ yᵉ)
        byᵉ
        associative-meet-Meet-Semilatticeᵉ xᵉ yᵉ yᵉ
      ＝ᵉ xᵉ ∧ᵉ yᵉ
        byᵉ
        apᵉ (meet-Meet-Semilatticeᵉ xᵉ) (idempotent-meet-Meet-Semilatticeᵉ yᵉ)

  is-greatest-binary-lower-bound-meet-Meet-Semilatticeᵉ :
    (xᵉ yᵉ : type-Meet-Semilatticeᵉ) →
    is-greatest-binary-lower-bound-Posetᵉ
      ( poset-Meet-Semilatticeᵉ)
      ( xᵉ)
      ( yᵉ)
      ( meet-Meet-Semilatticeᵉ xᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-Meet-Semilatticeᵉ xᵉ yᵉ =
    prove-is-greatest-binary-lower-bound-Posetᵉ
      ( poset-Meet-Semilatticeᵉ)
      ( is-binary-lower-bound-meet-Meet-Semilatticeᵉ xᵉ yᵉ)
      ( λ zᵉ (Hᵉ ,ᵉ Kᵉ) →
        equational-reasoningᵉ
          zᵉ ∧ᵉ (xᵉ ∧ᵉ yᵉ)
          ＝ᵉ (zᵉ ∧ᵉ xᵉ) ∧ᵉ yᵉ
            byᵉ invᵉ (associative-meet-Meet-Semilatticeᵉ zᵉ xᵉ yᵉ)
          ＝ᵉ zᵉ ∧ᵉ yᵉ
            byᵉ apᵉ (meet-Meet-Semilattice'ᵉ yᵉ) Hᵉ
          ＝ᵉ zᵉ
            byᵉ Kᵉ)

  has-greatest-binary-lower-bound-Meet-Semilatticeᵉ :
    (xᵉ yᵉ : type-Meet-Semilatticeᵉ) →
    has-greatest-binary-lower-bound-Posetᵉ (poset-Meet-Semilatticeᵉ) xᵉ yᵉ
  pr1ᵉ (has-greatest-binary-lower-bound-Meet-Semilatticeᵉ xᵉ yᵉ) =
    meet-Meet-Semilatticeᵉ xᵉ yᵉ
  pr2ᵉ (has-greatest-binary-lower-bound-Meet-Semilatticeᵉ xᵉ yᵉ) =
    is-greatest-binary-lower-bound-meet-Meet-Semilatticeᵉ xᵉ yᵉ
```

### The predicate on posets of being a meet-semilattice

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  is-meet-semilattice-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-meet-semilattice-Poset-Propᵉ =
    Π-Propᵉ
      ( type-Posetᵉ Pᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( type-Posetᵉ Pᵉ)
          ( has-greatest-binary-lower-bound-Poset-Propᵉ Pᵉ xᵉ))

  is-meet-semilattice-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-meet-semilattice-Posetᵉ = type-Propᵉ is-meet-semilattice-Poset-Propᵉ

  is-prop-is-meet-semilattice-Posetᵉ :
    is-propᵉ is-meet-semilattice-Posetᵉ
  is-prop-is-meet-semilattice-Posetᵉ =
    is-prop-type-Propᵉ is-meet-semilattice-Poset-Propᵉ

  module _
    (Hᵉ : is-meet-semilattice-Posetᵉ)
    where

    meet-is-meet-semilattice-Posetᵉ :
      type-Posetᵉ Pᵉ → type-Posetᵉ Pᵉ → type-Posetᵉ Pᵉ
    meet-is-meet-semilattice-Posetᵉ xᵉ yᵉ = pr1ᵉ (Hᵉ xᵉ yᵉ)

    is-greatest-binary-lower-bound-meet-is-meet-semilattice-Posetᵉ :
      (xᵉ yᵉ : type-Posetᵉ Pᵉ) →
      is-greatest-binary-lower-bound-Posetᵉ Pᵉ xᵉ yᵉ
        ( meet-is-meet-semilattice-Posetᵉ xᵉ yᵉ)
    is-greatest-binary-lower-bound-meet-is-meet-semilattice-Posetᵉ xᵉ yᵉ =
      pr2ᵉ (Hᵉ xᵉ yᵉ)
```

### The order-theoretic definition of meet semilattices

```agda
Order-Theoretic-Meet-Semilatticeᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Order-Theoretic-Meet-Semilatticeᵉ l1ᵉ l2ᵉ =
  Σᵉ (Posetᵉ l1ᵉ l2ᵉ) is-meet-semilattice-Posetᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Order-Theoretic-Meet-Semilatticeᵉ l1ᵉ l2ᵉ)
  where

  poset-Order-Theoretic-Meet-Semilatticeᵉ : Posetᵉ l1ᵉ l2ᵉ
  poset-Order-Theoretic-Meet-Semilatticeᵉ = pr1ᵉ Aᵉ

  type-Order-Theoretic-Meet-Semilatticeᵉ : UUᵉ l1ᵉ
  type-Order-Theoretic-Meet-Semilatticeᵉ =
    type-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ

  is-set-type-Order-Theoretic-Meet-Semilatticeᵉ :
    is-setᵉ type-Order-Theoretic-Meet-Semilatticeᵉ
  is-set-type-Order-Theoretic-Meet-Semilatticeᵉ =
    is-set-type-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ

  set-Order-Theoretic-Meet-Semilatticeᵉ : Setᵉ l1ᵉ
  set-Order-Theoretic-Meet-Semilatticeᵉ =
    set-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ

  leq-Order-Theoretic-Meet-Semilattice-Propᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Meet-Semilatticeᵉ) → Propᵉ l2ᵉ
  leq-Order-Theoretic-Meet-Semilattice-Propᵉ =
    leq-Poset-Propᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ

  leq-Order-Theoretic-Meet-Semilatticeᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Meet-Semilatticeᵉ) → UUᵉ l2ᵉ
  leq-Order-Theoretic-Meet-Semilatticeᵉ =
    leq-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ

  is-prop-leq-Order-Theoretic-Meet-Semilatticeᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Meet-Semilatticeᵉ) →
    is-propᵉ (leq-Order-Theoretic-Meet-Semilatticeᵉ xᵉ yᵉ)
  is-prop-leq-Order-Theoretic-Meet-Semilatticeᵉ =
    is-prop-leq-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ

  refl-leq-Order-Theoretic-Meet-Semilatticeᵉ :
    (xᵉ : type-Order-Theoretic-Meet-Semilatticeᵉ) →
    leq-Order-Theoretic-Meet-Semilatticeᵉ xᵉ xᵉ
  refl-leq-Order-Theoretic-Meet-Semilatticeᵉ =
    refl-leq-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ

  antisymmetric-leq-Order-Theoretic-Meet-Semilatticeᵉ :
    {xᵉ yᵉ : type-Order-Theoretic-Meet-Semilatticeᵉ} →
    leq-Order-Theoretic-Meet-Semilatticeᵉ xᵉ yᵉ →
    leq-Order-Theoretic-Meet-Semilatticeᵉ yᵉ xᵉ →
    xᵉ ＝ᵉ yᵉ
  antisymmetric-leq-Order-Theoretic-Meet-Semilatticeᵉ {xᵉ} {yᵉ} =
    antisymmetric-leq-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ xᵉ yᵉ

  transitive-leq-Order-Theoretic-Meet-Semilatticeᵉ :
    (xᵉ yᵉ zᵉ : type-Order-Theoretic-Meet-Semilatticeᵉ) →
    leq-Order-Theoretic-Meet-Semilatticeᵉ yᵉ zᵉ →
    leq-Order-Theoretic-Meet-Semilatticeᵉ xᵉ yᵉ →
    leq-Order-Theoretic-Meet-Semilatticeᵉ xᵉ zᵉ
  transitive-leq-Order-Theoretic-Meet-Semilatticeᵉ =
    transitive-leq-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ

  is-meet-semilattice-Order-Theoretic-Meet-Semilatticeᵉ :
    is-meet-semilattice-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ
  is-meet-semilattice-Order-Theoretic-Meet-Semilatticeᵉ = pr2ᵉ Aᵉ

  meet-Order-Theoretic-Meet-Semilatticeᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Meet-Semilatticeᵉ) →
    type-Order-Theoretic-Meet-Semilatticeᵉ
  meet-Order-Theoretic-Meet-Semilatticeᵉ =
    meet-is-meet-semilattice-Posetᵉ
      poset-Order-Theoretic-Meet-Semilatticeᵉ
      is-meet-semilattice-Order-Theoretic-Meet-Semilatticeᵉ

  private
    _∧ᵉ_ = meet-Order-Theoretic-Meet-Semilatticeᵉ

  is-greatest-binary-lower-bound-meet-Order-Theoretic-Meet-Semilatticeᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Meet-Semilatticeᵉ) →
    is-greatest-binary-lower-bound-Posetᵉ
      ( poset-Order-Theoretic-Meet-Semilatticeᵉ)
      ( xᵉ)
      ( yᵉ)
      ( xᵉ ∧ᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-Order-Theoretic-Meet-Semilatticeᵉ =
    is-greatest-binary-lower-bound-meet-is-meet-semilattice-Posetᵉ
      poset-Order-Theoretic-Meet-Semilatticeᵉ
      is-meet-semilattice-Order-Theoretic-Meet-Semilatticeᵉ

  is-binary-lower-bound-meet-Order-Theoretic-Meet-Semilatticeᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Meet-Semilatticeᵉ) →
    is-binary-lower-bound-Posetᵉ
      ( poset-Order-Theoretic-Meet-Semilatticeᵉ)
      ( xᵉ)
      ( yᵉ)
      ( xᵉ ∧ᵉ yᵉ)
  is-binary-lower-bound-meet-Order-Theoretic-Meet-Semilatticeᵉ xᵉ yᵉ =
    is-binary-lower-bound-is-greatest-binary-lower-bound-Posetᵉ
      ( poset-Order-Theoretic-Meet-Semilatticeᵉ)
      ( is-greatest-binary-lower-bound-meet-Order-Theoretic-Meet-Semilatticeᵉ
        ( xᵉ)
        ( yᵉ))

  leq-left-meet-Order-Theoretic-Meet-Semilatticeᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Meet-Semilatticeᵉ) →
    leq-Order-Theoretic-Meet-Semilatticeᵉ (xᵉ ∧ᵉ yᵉ) xᵉ
  leq-left-meet-Order-Theoretic-Meet-Semilatticeᵉ xᵉ yᵉ =
    leq-left-is-binary-lower-bound-Posetᵉ
      ( poset-Order-Theoretic-Meet-Semilatticeᵉ)
      ( is-binary-lower-bound-meet-Order-Theoretic-Meet-Semilatticeᵉ xᵉ yᵉ)

  leq-right-meet-Order-Theoretic-Meet-Semilatticeᵉ :
    (xᵉ yᵉ : type-Order-Theoretic-Meet-Semilatticeᵉ) →
    leq-Order-Theoretic-Meet-Semilatticeᵉ (xᵉ ∧ᵉ yᵉ) yᵉ
  leq-right-meet-Order-Theoretic-Meet-Semilatticeᵉ xᵉ yᵉ =
    leq-right-is-binary-lower-bound-Posetᵉ
      ( poset-Order-Theoretic-Meet-Semilatticeᵉ)
      ( is-binary-lower-bound-meet-Order-Theoretic-Meet-Semilatticeᵉ xᵉ yᵉ)

  leq-meet-Order-Theoretic-Meet-Semilatticeᵉ :
    {xᵉ yᵉ zᵉ : type-Order-Theoretic-Meet-Semilatticeᵉ} →
    leq-Order-Theoretic-Meet-Semilatticeᵉ zᵉ xᵉ →
    leq-Order-Theoretic-Meet-Semilatticeᵉ zᵉ yᵉ →
    leq-Order-Theoretic-Meet-Semilatticeᵉ zᵉ (xᵉ ∧ᵉ yᵉ)
  leq-meet-Order-Theoretic-Meet-Semilatticeᵉ {xᵉ} {yᵉ} {zᵉ} Hᵉ Kᵉ =
    forward-implicationᵉ
      ( is-greatest-binary-lower-bound-meet-Order-Theoretic-Meet-Semilatticeᵉ
        ( xᵉ)
        ( yᵉ)
        ( zᵉ))
      ( Hᵉ ,ᵉ Kᵉ)
```

## Properties

### The meet operation of order theoretic meet-semilattices is associative

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Order-Theoretic-Meet-Semilatticeᵉ l1ᵉ l2ᵉ)
  (xᵉ yᵉ zᵉ : type-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ)
  where

  private
    _∧ᵉ_ = meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
    _≤ᵉ_ = leq-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ

  leq-left-triple-meet-Order-Theoretic-Meet-Semilatticeᵉ :
    ((xᵉ ∧ᵉ yᵉ) ∧ᵉ zᵉ) ≤ᵉ xᵉ
  leq-left-triple-meet-Order-Theoretic-Meet-Semilatticeᵉ =
    calculate-in-Posetᵉ
      ( poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ)
      chain-of-inequalitiesᵉ
        (xᵉ ∧ᵉ yᵉ) ∧ᵉ zᵉ
          ≤ᵉ xᵉ ∧ᵉ yᵉ
            byᵉ leq-left-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ (xᵉ ∧ᵉ yᵉ) zᵉ
            in-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
          ≤ᵉ xᵉ
            byᵉ leq-left-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ xᵉ yᵉ
            in-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ

  leq-center-triple-meet-Order-Theoretic-Meet-Semilatticeᵉ :
    ((xᵉ ∧ᵉ yᵉ) ∧ᵉ zᵉ) ≤ᵉ yᵉ
  leq-center-triple-meet-Order-Theoretic-Meet-Semilatticeᵉ =
    calculate-in-Posetᵉ
      ( poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ)
      chain-of-inequalitiesᵉ
        (xᵉ ∧ᵉ yᵉ) ∧ᵉ zᵉ
          ≤ᵉ xᵉ ∧ᵉ yᵉ
            byᵉ leq-left-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ (xᵉ ∧ᵉ yᵉ) zᵉ
            in-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
          ≤ᵉ yᵉ
            byᵉ leq-right-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ xᵉ yᵉ
            in-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ

  leq-right-triple-meet-Order-Theoretic-Meet-Semilatticeᵉ :
    ((xᵉ ∧ᵉ yᵉ) ∧ᵉ zᵉ) ≤ᵉ zᵉ
  leq-right-triple-meet-Order-Theoretic-Meet-Semilatticeᵉ =
    leq-right-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ (xᵉ ∧ᵉ yᵉ) zᵉ

  leq-left-triple-meet-Order-Theoretic-Meet-Semilattice'ᵉ :
    (xᵉ ∧ᵉ (yᵉ ∧ᵉ zᵉ)) ≤ᵉ xᵉ
  leq-left-triple-meet-Order-Theoretic-Meet-Semilattice'ᵉ =
    leq-left-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ xᵉ (yᵉ ∧ᵉ zᵉ)

  leq-center-triple-meet-Order-Theoretic-Meet-Semilattice'ᵉ :
    (xᵉ ∧ᵉ (yᵉ ∧ᵉ zᵉ)) ≤ᵉ yᵉ
  leq-center-triple-meet-Order-Theoretic-Meet-Semilattice'ᵉ =
    calculate-in-Posetᵉ
      ( poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ)
      chain-of-inequalitiesᵉ
        xᵉ ∧ᵉ (yᵉ ∧ᵉ zᵉ)
          ≤ᵉ yᵉ ∧ᵉ zᵉ
            byᵉ leq-right-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ xᵉ (yᵉ ∧ᵉ zᵉ)
            in-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
          ≤ᵉ yᵉ
            byᵉ leq-left-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ yᵉ zᵉ
            in-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ

  leq-right-triple-meet-Order-Theoretic-Meet-Semilattice'ᵉ :
    (xᵉ ∧ᵉ (yᵉ ∧ᵉ zᵉ)) ≤ᵉ zᵉ
  leq-right-triple-meet-Order-Theoretic-Meet-Semilattice'ᵉ =
    calculate-in-Posetᵉ
      ( poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ)
      chain-of-inequalitiesᵉ
        xᵉ ∧ᵉ (yᵉ ∧ᵉ zᵉ)
          ≤ᵉ yᵉ ∧ᵉ zᵉ
            byᵉ leq-right-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ xᵉ (yᵉ ∧ᵉ zᵉ)
            in-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
          ≤ᵉ zᵉ
            byᵉ leq-right-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ yᵉ zᵉ
            in-Posetᵉ poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ

  leq-associative-meet-Order-Theoretic-Meet-Semilatticeᵉ :
    ((xᵉ ∧ᵉ yᵉ) ∧ᵉ zᵉ) ≤ᵉ (xᵉ ∧ᵉ (yᵉ ∧ᵉ zᵉ))
  leq-associative-meet-Order-Theoretic-Meet-Semilatticeᵉ =
    leq-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
      ( leq-left-triple-meet-Order-Theoretic-Meet-Semilatticeᵉ)
      ( leq-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
        ( leq-center-triple-meet-Order-Theoretic-Meet-Semilatticeᵉ)
        ( leq-right-triple-meet-Order-Theoretic-Meet-Semilatticeᵉ))

  leq-associative-meet-Order-Theoretic-Meet-Semilattice'ᵉ :
    (xᵉ ∧ᵉ (yᵉ ∧ᵉ zᵉ)) ≤ᵉ ((xᵉ ∧ᵉ yᵉ) ∧ᵉ zᵉ)
  leq-associative-meet-Order-Theoretic-Meet-Semilattice'ᵉ =
    leq-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
      ( leq-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
        ( leq-left-triple-meet-Order-Theoretic-Meet-Semilattice'ᵉ)
        ( leq-center-triple-meet-Order-Theoretic-Meet-Semilattice'ᵉ))
      ( leq-right-triple-meet-Order-Theoretic-Meet-Semilattice'ᵉ)

  associative-meet-Order-Theoretic-Meet-Semilatticeᵉ :
    ((xᵉ ∧ᵉ yᵉ) ∧ᵉ zᵉ) ＝ᵉ (xᵉ ∧ᵉ (yᵉ ∧ᵉ zᵉ))
  associative-meet-Order-Theoretic-Meet-Semilatticeᵉ =
    antisymmetric-leq-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
      leq-associative-meet-Order-Theoretic-Meet-Semilatticeᵉ
      leq-associative-meet-Order-Theoretic-Meet-Semilattice'ᵉ
```

### The meet operation of order theoretic meet-semilattices is commutative

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Order-Theoretic-Meet-Semilatticeᵉ l1ᵉ l2ᵉ)
  (xᵉ yᵉ : type-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ)
  where

  private
    _∧ᵉ_ = meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
    _≤ᵉ_ = leq-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ

  leq-commutative-meet-Order-Theoretic-Meet-Semilatticeᵉ :
    (xᵉ ∧ᵉ yᵉ) ≤ᵉ (yᵉ ∧ᵉ xᵉ)
  leq-commutative-meet-Order-Theoretic-Meet-Semilatticeᵉ =
    leq-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
      ( leq-right-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ xᵉ yᵉ)
      ( leq-left-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ xᵉ yᵉ)

  leq-commutative-meet-Order-Theoretic-Meet-Semilattice'ᵉ :
    (yᵉ ∧ᵉ xᵉ) ≤ᵉ (xᵉ ∧ᵉ yᵉ)
  leq-commutative-meet-Order-Theoretic-Meet-Semilattice'ᵉ =
    leq-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
      ( leq-right-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ yᵉ xᵉ)
      ( leq-left-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ yᵉ xᵉ)

  commutative-meet-Order-Theoretic-Meet-Semilatticeᵉ :
    (xᵉ ∧ᵉ yᵉ) ＝ᵉ (yᵉ ∧ᵉ xᵉ)
  commutative-meet-Order-Theoretic-Meet-Semilatticeᵉ =
    antisymmetric-leq-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
      leq-commutative-meet-Order-Theoretic-Meet-Semilatticeᵉ
      leq-commutative-meet-Order-Theoretic-Meet-Semilattice'ᵉ
```

### The meet operation of order theoretic meet-semilattices is idempotent

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Order-Theoretic-Meet-Semilatticeᵉ l1ᵉ l2ᵉ)
  (xᵉ : type-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ)
  where

  private
    _∧ᵉ_ = meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
    _≤ᵉ_ = leq-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ

  idempotent-meet-Order-Theoretic-Meet-Semilatticeᵉ :
    (xᵉ ∧ᵉ xᵉ) ＝ᵉ xᵉ
  idempotent-meet-Order-Theoretic-Meet-Semilatticeᵉ =
    antisymmetric-leq-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
      ( leq-left-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ xᵉ xᵉ)
      ( leq-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
        ( refl-leq-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ xᵉ)
        ( refl-leq-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ xᵉ))
```

### Any order theoretic meet-semilattice is an algebraic meet semilattice

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Order-Theoretic-Meet-Semilatticeᵉ l1ᵉ l2ᵉ)
  where

  semigroup-Order-Theoretic-Meet-Semilatticeᵉ : Semigroupᵉ l1ᵉ
  pr1ᵉ semigroup-Order-Theoretic-Meet-Semilatticeᵉ =
    set-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
  pr1ᵉ (pr2ᵉ semigroup-Order-Theoretic-Meet-Semilatticeᵉ) =
    meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
  pr2ᵉ (pr2ᵉ semigroup-Order-Theoretic-Meet-Semilatticeᵉ) =
    associative-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ

  meet-semilattice-Order-Theoretic-Meet-Semilatticeᵉ :
    Meet-Semilatticeᵉ l1ᵉ
  pr1ᵉ meet-semilattice-Order-Theoretic-Meet-Semilatticeᵉ =
    semigroup-Order-Theoretic-Meet-Semilatticeᵉ
  pr1ᵉ (pr2ᵉ meet-semilattice-Order-Theoretic-Meet-Semilatticeᵉ) =
    commutative-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
  pr2ᵉ (pr2ᵉ meet-semilattice-Order-Theoretic-Meet-Semilatticeᵉ) =
    idempotent-meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ
```

### Any meet-semilattice `A` is isomorphic to the meet-semilattice obtained from the order theoretic meet-semilattice obtained from `A`

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Meet-Semilatticeᵉ l1ᵉ)
  where

  order-theoretic-meet-semilattice-Meet-Semilatticeᵉ :
    Order-Theoretic-Meet-Semilatticeᵉ l1ᵉ l1ᵉ
  pr1ᵉ order-theoretic-meet-semilattice-Meet-Semilatticeᵉ =
    poset-Meet-Semilatticeᵉ Aᵉ
  pr1ᵉ (pr2ᵉ order-theoretic-meet-semilattice-Meet-Semilatticeᵉ xᵉ yᵉ) =
    meet-Meet-Semilatticeᵉ Aᵉ xᵉ yᵉ
  pr2ᵉ (pr2ᵉ order-theoretic-meet-semilattice-Meet-Semilatticeᵉ xᵉ yᵉ) =
    is-greatest-binary-lower-bound-meet-Meet-Semilatticeᵉ Aᵉ xᵉ yᵉ

  compute-meet-order-theoretic-meet-semilattice-Meet-Semilatticeᵉ :
    (xᵉ yᵉ : type-Meet-Semilatticeᵉ Aᵉ) →
    meet-Meet-Semilatticeᵉ Aᵉ xᵉ yᵉ ＝ᵉ
    meet-Order-Theoretic-Meet-Semilatticeᵉ
      ( order-theoretic-meet-semilattice-Meet-Semilatticeᵉ)
      ( xᵉ)
      ( yᵉ)
  compute-meet-order-theoretic-meet-semilattice-Meet-Semilatticeᵉ xᵉ yᵉ = reflᵉ

  compute-order-theoretic-meet-semilattice-Meet-Semilatticeᵉ :
    iso-Semigroupᵉ
      ( semigroup-Meet-Semilatticeᵉ Aᵉ)
      ( semigroup-Meet-Semilatticeᵉ
        ( meet-semilattice-Order-Theoretic-Meet-Semilatticeᵉ
          ( order-theoretic-meet-semilattice-Meet-Semilatticeᵉ)))
  compute-order-theoretic-meet-semilattice-Meet-Semilatticeᵉ =
    id-iso-Semigroupᵉ (semigroup-Meet-Semilatticeᵉ Aᵉ)
```