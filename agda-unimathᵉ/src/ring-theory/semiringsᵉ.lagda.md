# Semirings

```agda
module ring-theory.semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Theᵉ conceptᵉ ofᵉ aᵉ _semiringᵉ_ vastlyᵉ generalizesᵉ theᵉ arithmeticalᵉ structureᵉ onᵉ theᵉ
[naturalᵉ numbers](elementary-number-theory.natural-numbers.md).ᵉ Aᵉ
{{#conceptᵉ "semiring"ᵉ Agda=Semiringᵉ}} consistsᵉ ofᵉ aᵉ
[set](foundation-core.sets.mdᵉ) equippedᵉ with additionᵉ andᵉ multiplication,ᵉ where
theᵉ additionᵉ operationᵉ givesᵉ theᵉ semiringᵉ theᵉ structureᵉ ofᵉ aᵉ
[commutativeᵉ monoid](group-theory.commutative-monoids.md),ᵉ andᵉ theᵉ
multiplicationᵉ isᵉ associative,ᵉ unital,ᵉ andᵉ distributiveᵉ overᵉ addition.ᵉ

## Definitions

### Semirings

```agda
has-mul-Commutative-Monoidᵉ :
  {lᵉ : Level} → Commutative-Monoidᵉ lᵉ → UUᵉ lᵉ
has-mul-Commutative-Monoidᵉ Mᵉ =
  Σᵉ ( has-associative-mul-Setᵉ (set-Commutative-Monoidᵉ Mᵉ))
    ( λ μᵉ →
      ( is-unitalᵉ (pr1ᵉ μᵉ)) ×ᵉ
      ( ( (aᵉ bᵉ cᵉ : type-Commutative-Monoidᵉ Mᵉ) →
          pr1ᵉ μᵉ aᵉ (mul-Commutative-Monoidᵉ Mᵉ bᵉ cᵉ) ＝ᵉ
          mul-Commutative-Monoidᵉ Mᵉ (pr1ᵉ μᵉ aᵉ bᵉ) (pr1ᵉ μᵉ aᵉ cᵉ)) ×ᵉ
        ( (aᵉ bᵉ cᵉ : type-Commutative-Monoidᵉ Mᵉ) →
          pr1ᵉ μᵉ (mul-Commutative-Monoidᵉ Mᵉ aᵉ bᵉ) cᵉ ＝ᵉ
          mul-Commutative-Monoidᵉ Mᵉ (pr1ᵉ μᵉ aᵉ cᵉ) (pr1ᵉ μᵉ bᵉ cᵉ))))

zero-laws-Commutative-Monoidᵉ :
  {lᵉ : Level} (Mᵉ : Commutative-Monoidᵉ lᵉ) → has-mul-Commutative-Monoidᵉ Mᵉ → UUᵉ lᵉ
zero-laws-Commutative-Monoidᵉ Mᵉ ((μᵉ ,ᵉ αᵉ) ,ᵉ lawsᵉ) =
  ( (xᵉ : type-Commutative-Monoidᵉ Mᵉ) →
    μᵉ (unit-Commutative-Monoidᵉ Mᵉ) xᵉ ＝ᵉ unit-Commutative-Monoidᵉ Mᵉ) ×ᵉ
  ((xᵉ : type-Commutative-Monoidᵉ Mᵉ) →
    μᵉ xᵉ (unit-Commutative-Monoidᵉ Mᵉ) ＝ᵉ unit-Commutative-Monoidᵉ Mᵉ)

Semiringᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Semiringᵉ l1ᵉ =
  Σᵉ ( Commutative-Monoidᵉ l1ᵉ)
    ( λ Mᵉ →
      Σᵉ (has-mul-Commutative-Monoidᵉ Mᵉ) (zero-laws-Commutative-Monoidᵉ Mᵉ))

module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  additive-commutative-monoid-Semiringᵉ : Commutative-Monoidᵉ lᵉ
  additive-commutative-monoid-Semiringᵉ = pr1ᵉ Rᵉ

  additive-monoid-Semiringᵉ : Monoidᵉ lᵉ
  additive-monoid-Semiringᵉ =
    monoid-Commutative-Monoidᵉ additive-commutative-monoid-Semiringᵉ

  additive-semigroup-Semiringᵉ : Semigroupᵉ lᵉ
  additive-semigroup-Semiringᵉ =
    semigroup-Commutative-Monoidᵉ additive-commutative-monoid-Semiringᵉ

  set-Semiringᵉ : Setᵉ lᵉ
  set-Semiringᵉ =
    set-Commutative-Monoidᵉ additive-commutative-monoid-Semiringᵉ

  type-Semiringᵉ : UUᵉ lᵉ
  type-Semiringᵉ =
    type-Commutative-Monoidᵉ additive-commutative-monoid-Semiringᵉ

  is-set-type-Semiringᵉ : is-setᵉ type-Semiringᵉ
  is-set-type-Semiringᵉ =
    is-set-type-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ)
```

### Addition in a semiring

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  has-associative-add-Semiringᵉ : has-associative-mul-Setᵉ (set-Semiringᵉ Rᵉ)
  has-associative-add-Semiringᵉ =
    has-associative-mul-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)

  add-Semiringᵉ : type-Semiringᵉ Rᵉ → type-Semiringᵉ Rᵉ → type-Semiringᵉ Rᵉ
  add-Semiringᵉ =
    mul-Commutative-Monoidᵉ (additive-commutative-monoid-Semiringᵉ Rᵉ)

  add-Semiring'ᵉ : type-Semiringᵉ Rᵉ → type-Semiringᵉ Rᵉ → type-Semiringᵉ Rᵉ
  add-Semiring'ᵉ =
    mul-Commutative-Monoid'ᵉ (additive-commutative-monoid-Semiringᵉ Rᵉ)

  ap-add-Semiringᵉ :
    {xᵉ yᵉ x'ᵉ y'ᵉ : type-Semiringᵉ Rᵉ} →
    xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → add-Semiringᵉ xᵉ yᵉ ＝ᵉ add-Semiringᵉ x'ᵉ y'ᵉ
  ap-add-Semiringᵉ =
    ap-mul-Commutative-Monoidᵉ (additive-commutative-monoid-Semiringᵉ Rᵉ)

  associative-add-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Semiringᵉ Rᵉ) →
    add-Semiringᵉ (add-Semiringᵉ xᵉ yᵉ) zᵉ ＝ᵉ add-Semiringᵉ xᵉ (add-Semiringᵉ yᵉ zᵉ)
  associative-add-Semiringᵉ =
    associative-mul-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)

  commutative-add-Semiringᵉ :
    (xᵉ yᵉ : type-Semiringᵉ Rᵉ) → add-Semiringᵉ xᵉ yᵉ ＝ᵉ add-Semiringᵉ yᵉ xᵉ
  commutative-add-Semiringᵉ =
    commutative-mul-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)

  interchange-add-add-Semiringᵉ :
    (xᵉ yᵉ x'ᵉ y'ᵉ : type-Semiringᵉ Rᵉ) →
    ( add-Semiringᵉ (add-Semiringᵉ xᵉ yᵉ) (add-Semiringᵉ x'ᵉ y'ᵉ)) ＝ᵉ
    ( add-Semiringᵉ (add-Semiringᵉ xᵉ x'ᵉ) (add-Semiringᵉ yᵉ y'ᵉ))
  interchange-add-add-Semiringᵉ =
    interchange-mul-mul-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)

  right-swap-add-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Semiringᵉ Rᵉ) →
    add-Semiringᵉ (add-Semiringᵉ xᵉ yᵉ) zᵉ ＝ᵉ add-Semiringᵉ (add-Semiringᵉ xᵉ zᵉ) yᵉ
  right-swap-add-Semiringᵉ =
    right-swap-mul-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)

  left-swap-add-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Semiringᵉ Rᵉ) →
    add-Semiringᵉ xᵉ (add-Semiringᵉ yᵉ zᵉ) ＝ᵉ add-Semiringᵉ yᵉ (add-Semiringᵉ xᵉ zᵉ)
  left-swap-add-Semiringᵉ =
    left-swap-mul-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)
```

### The zero element of a semiring

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  has-zero-Semiringᵉ : is-unitalᵉ (add-Semiringᵉ Rᵉ)
  has-zero-Semiringᵉ =
    has-unit-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)

  zero-Semiringᵉ : type-Semiringᵉ Rᵉ
  zero-Semiringᵉ =
    unit-Commutative-Monoidᵉ (additive-commutative-monoid-Semiringᵉ Rᵉ)

  is-zero-Semiringᵉ : type-Semiringᵉ Rᵉ → UUᵉ lᵉ
  is-zero-Semiringᵉ xᵉ = Idᵉ xᵉ zero-Semiringᵉ

  is-nonzero-Semiringᵉ : type-Semiringᵉ Rᵉ → UUᵉ lᵉ
  is-nonzero-Semiringᵉ xᵉ = ¬ᵉ (is-zero-Semiringᵉ xᵉ)

  is-zero-semiring-Propᵉ : type-Semiringᵉ Rᵉ → Propᵉ lᵉ
  is-zero-semiring-Propᵉ xᵉ = Id-Propᵉ (set-Semiringᵉ Rᵉ) xᵉ zero-Semiringᵉ

  left-unit-law-add-Semiringᵉ :
    (xᵉ : type-Semiringᵉ Rᵉ) → Idᵉ (add-Semiringᵉ Rᵉ zero-Semiringᵉ xᵉ) xᵉ
  left-unit-law-add-Semiringᵉ =
    left-unit-law-mul-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)

  right-unit-law-add-Semiringᵉ :
    (xᵉ : type-Semiringᵉ Rᵉ) → Idᵉ (add-Semiringᵉ Rᵉ xᵉ zero-Semiringᵉ) xᵉ
  right-unit-law-add-Semiringᵉ =
    right-unit-law-mul-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)
```

### Multiplication in a semiring

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  has-associative-mul-Semiringᵉ : has-associative-mul-Setᵉ (set-Semiringᵉ Rᵉ)
  has-associative-mul-Semiringᵉ = pr1ᵉ (pr1ᵉ (pr2ᵉ Rᵉ))

  mul-Semiringᵉ : type-Semiringᵉ Rᵉ → type-Semiringᵉ Rᵉ → type-Semiringᵉ Rᵉ
  mul-Semiringᵉ = pr1ᵉ has-associative-mul-Semiringᵉ

  mul-Semiring'ᵉ : type-Semiringᵉ Rᵉ → type-Semiringᵉ Rᵉ → type-Semiringᵉ Rᵉ
  mul-Semiring'ᵉ xᵉ yᵉ = mul-Semiringᵉ yᵉ xᵉ

  ap-mul-Semiringᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Semiringᵉ Rᵉ} (pᵉ : Idᵉ xᵉ x'ᵉ) (qᵉ : Idᵉ yᵉ y'ᵉ) →
    Idᵉ (mul-Semiringᵉ xᵉ yᵉ) (mul-Semiringᵉ x'ᵉ y'ᵉ)
  ap-mul-Semiringᵉ pᵉ qᵉ = ap-binaryᵉ mul-Semiringᵉ pᵉ qᵉ

  associative-mul-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Semiringᵉ Rᵉ) →
    Idᵉ (mul-Semiringᵉ (mul-Semiringᵉ xᵉ yᵉ) zᵉ) (mul-Semiringᵉ xᵉ (mul-Semiringᵉ yᵉ zᵉ))
  associative-mul-Semiringᵉ = pr2ᵉ has-associative-mul-Semiringᵉ

  multiplicative-semigroup-Semiringᵉ : Semigroupᵉ lᵉ
  pr1ᵉ multiplicative-semigroup-Semiringᵉ = set-Semiringᵉ Rᵉ
  pr2ᵉ multiplicative-semigroup-Semiringᵉ = has-associative-mul-Semiringᵉ

  left-distributive-mul-add-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Semiringᵉ Rᵉ) →
    mul-Semiringᵉ xᵉ (add-Semiringᵉ Rᵉ yᵉ zᵉ) ＝ᵉ
    add-Semiringᵉ Rᵉ (mul-Semiringᵉ xᵉ yᵉ) (mul-Semiringᵉ xᵉ zᵉ)
  left-distributive-mul-add-Semiringᵉ =
    pr1ᵉ (pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ Rᵉ))))

  right-distributive-mul-add-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Semiringᵉ Rᵉ) →
    mul-Semiringᵉ (add-Semiringᵉ Rᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    add-Semiringᵉ Rᵉ (mul-Semiringᵉ xᵉ zᵉ) (mul-Semiringᵉ yᵉ zᵉ)
  right-distributive-mul-add-Semiringᵉ =
    pr2ᵉ (pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ Rᵉ))))

  bidistributive-mul-add-Semiringᵉ :
    (uᵉ vᵉ xᵉ yᵉ : type-Semiringᵉ Rᵉ) →
    mul-Semiringᵉ (add-Semiringᵉ Rᵉ uᵉ vᵉ) (add-Semiringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
    add-Semiringᵉ Rᵉ
      ( add-Semiringᵉ Rᵉ (mul-Semiringᵉ uᵉ xᵉ) (mul-Semiringᵉ uᵉ yᵉ))
      ( add-Semiringᵉ Rᵉ (mul-Semiringᵉ vᵉ xᵉ) (mul-Semiringᵉ vᵉ yᵉ))
  bidistributive-mul-add-Semiringᵉ uᵉ vᵉ xᵉ yᵉ =
    ( right-distributive-mul-add-Semiringᵉ uᵉ vᵉ (add-Semiringᵉ Rᵉ xᵉ yᵉ)) ∙ᵉ
    ( ap-add-Semiringᵉ Rᵉ
      ( left-distributive-mul-add-Semiringᵉ uᵉ xᵉ yᵉ)
      ( left-distributive-mul-add-Semiringᵉ vᵉ xᵉ yᵉ))

  left-zero-law-mul-Semiringᵉ :
    (xᵉ : type-Semiringᵉ Rᵉ) → mul-Semiringᵉ (zero-Semiringᵉ Rᵉ) xᵉ ＝ᵉ zero-Semiringᵉ Rᵉ
  left-zero-law-mul-Semiringᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Rᵉ))

  right-zero-law-mul-Semiringᵉ :
    (xᵉ : type-Semiringᵉ Rᵉ) → mul-Semiringᵉ xᵉ (zero-Semiringᵉ Rᵉ) ＝ᵉ zero-Semiringᵉ Rᵉ
  right-zero-law-mul-Semiringᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ Rᵉ))
```

### Multiplicative units in a semiring

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  is-unital-Semiringᵉ : is-unitalᵉ (mul-Semiringᵉ Rᵉ)
  is-unital-Semiringᵉ = pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ Rᵉ)))

  multiplicative-monoid-Semiringᵉ : Monoidᵉ lᵉ
  pr1ᵉ multiplicative-monoid-Semiringᵉ = multiplicative-semigroup-Semiringᵉ Rᵉ
  pr2ᵉ multiplicative-monoid-Semiringᵉ = is-unital-Semiringᵉ

  one-Semiringᵉ : type-Semiringᵉ Rᵉ
  one-Semiringᵉ = unit-Monoidᵉ multiplicative-monoid-Semiringᵉ

  left-unit-law-mul-Semiringᵉ :
    (xᵉ : type-Semiringᵉ Rᵉ) → Idᵉ (mul-Semiringᵉ Rᵉ one-Semiringᵉ xᵉ) xᵉ
  left-unit-law-mul-Semiringᵉ =
    left-unit-law-mul-Monoidᵉ multiplicative-monoid-Semiringᵉ

  right-unit-law-mul-Semiringᵉ :
    (xᵉ : type-Semiringᵉ Rᵉ) → Idᵉ (mul-Semiringᵉ Rᵉ xᵉ one-Semiringᵉ) xᵉ
  right-unit-law-mul-Semiringᵉ =
    right-unit-law-mul-Monoidᵉ multiplicative-monoid-Semiringᵉ
```

### Scalar multiplication of semiring elements by natural numbers

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  mul-nat-scalar-Semiringᵉ : ℕᵉ → type-Semiringᵉ Rᵉ → type-Semiringᵉ Rᵉ
  mul-nat-scalar-Semiringᵉ zero-ℕᵉ xᵉ = zero-Semiringᵉ Rᵉ
  mul-nat-scalar-Semiringᵉ (succ-ℕᵉ nᵉ) xᵉ =
    add-Semiringᵉ Rᵉ (mul-nat-scalar-Semiringᵉ nᵉ xᵉ) xᵉ

  ap-mul-nat-scalar-Semiringᵉ :
    {mᵉ nᵉ : ℕᵉ} {xᵉ yᵉ : type-Semiringᵉ Rᵉ} →
    (mᵉ ＝ᵉ nᵉ) → (xᵉ ＝ᵉ yᵉ) →
    mul-nat-scalar-Semiringᵉ mᵉ xᵉ ＝ᵉ mul-nat-scalar-Semiringᵉ nᵉ yᵉ
  ap-mul-nat-scalar-Semiringᵉ pᵉ qᵉ = ap-binaryᵉ mul-nat-scalar-Semiringᵉ pᵉ qᵉ

  left-zero-law-mul-nat-scalar-Semiringᵉ :
    (xᵉ : type-Semiringᵉ Rᵉ) → mul-nat-scalar-Semiringᵉ 0 xᵉ ＝ᵉ zero-Semiringᵉ Rᵉ
  left-zero-law-mul-nat-scalar-Semiringᵉ xᵉ = reflᵉ

  right-zero-law-mul-nat-scalar-Semiringᵉ :
    (nᵉ : ℕᵉ) → mul-nat-scalar-Semiringᵉ nᵉ (zero-Semiringᵉ Rᵉ) ＝ᵉ zero-Semiringᵉ Rᵉ
  right-zero-law-mul-nat-scalar-Semiringᵉ zero-ℕᵉ = reflᵉ
  right-zero-law-mul-nat-scalar-Semiringᵉ (succ-ℕᵉ nᵉ) =
    ( right-unit-law-add-Semiringᵉ Rᵉ _) ∙ᵉ
    ( right-zero-law-mul-nat-scalar-Semiringᵉ nᵉ)

  left-unit-law-mul-nat-scalar-Semiringᵉ :
    (xᵉ : type-Semiringᵉ Rᵉ) → mul-nat-scalar-Semiringᵉ 1 xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-nat-scalar-Semiringᵉ xᵉ = left-unit-law-add-Semiringᵉ Rᵉ xᵉ

  left-nat-scalar-law-mul-Semiringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Semiringᵉ Rᵉ) →
    mul-Semiringᵉ Rᵉ (mul-nat-scalar-Semiringᵉ nᵉ xᵉ) yᵉ ＝ᵉ
    mul-nat-scalar-Semiringᵉ nᵉ (mul-Semiringᵉ Rᵉ xᵉ yᵉ)
  left-nat-scalar-law-mul-Semiringᵉ zero-ℕᵉ xᵉ yᵉ =
    left-zero-law-mul-Semiringᵉ Rᵉ yᵉ
  left-nat-scalar-law-mul-Semiringᵉ (succ-ℕᵉ nᵉ) xᵉ yᵉ =
    ( right-distributive-mul-add-Semiringᵉ Rᵉ
      ( mul-nat-scalar-Semiringᵉ nᵉ xᵉ)
      ( xᵉ)
      ( yᵉ)) ∙ᵉ
    ( apᵉ
      ( add-Semiring'ᵉ Rᵉ (mul-Semiringᵉ Rᵉ xᵉ yᵉ))
      ( left-nat-scalar-law-mul-Semiringᵉ nᵉ xᵉ yᵉ))

  right-nat-scalar-law-mul-Semiringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Semiringᵉ Rᵉ) →
    mul-Semiringᵉ Rᵉ xᵉ (mul-nat-scalar-Semiringᵉ nᵉ yᵉ) ＝ᵉ
    mul-nat-scalar-Semiringᵉ nᵉ (mul-Semiringᵉ Rᵉ xᵉ yᵉ)
  right-nat-scalar-law-mul-Semiringᵉ zero-ℕᵉ xᵉ yᵉ =
    right-zero-law-mul-Semiringᵉ Rᵉ xᵉ
  right-nat-scalar-law-mul-Semiringᵉ (succ-ℕᵉ nᵉ) xᵉ yᵉ =
    ( left-distributive-mul-add-Semiringᵉ Rᵉ xᵉ
      ( mul-nat-scalar-Semiringᵉ nᵉ yᵉ)
      ( yᵉ)) ∙ᵉ
    ( apᵉ
      ( add-Semiring'ᵉ Rᵉ (mul-Semiringᵉ Rᵉ xᵉ yᵉ))
      ( right-nat-scalar-law-mul-Semiringᵉ nᵉ xᵉ yᵉ))

  left-distributive-mul-nat-scalar-add-Semiringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Semiringᵉ Rᵉ) →
    mul-nat-scalar-Semiringᵉ nᵉ (add-Semiringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
    add-Semiringᵉ Rᵉ (mul-nat-scalar-Semiringᵉ nᵉ xᵉ) (mul-nat-scalar-Semiringᵉ nᵉ yᵉ)
  left-distributive-mul-nat-scalar-add-Semiringᵉ zero-ℕᵉ xᵉ yᵉ =
    invᵉ (left-unit-law-add-Semiringᵉ Rᵉ (zero-Semiringᵉ Rᵉ))
  left-distributive-mul-nat-scalar-add-Semiringᵉ (succ-ℕᵉ nᵉ) xᵉ yᵉ =
    ( apᵉ
      ( add-Semiring'ᵉ Rᵉ (add-Semiringᵉ Rᵉ xᵉ yᵉ))
      ( left-distributive-mul-nat-scalar-add-Semiringᵉ nᵉ xᵉ yᵉ)) ∙ᵉ
    ( interchange-add-add-Semiringᵉ Rᵉ
      ( mul-nat-scalar-Semiringᵉ nᵉ xᵉ)
      ( mul-nat-scalar-Semiringᵉ nᵉ yᵉ)
      ( xᵉ)
      ( yᵉ))

  right-distributive-mul-nat-scalar-add-Semiringᵉ :
    (mᵉ nᵉ : ℕᵉ) (xᵉ : type-Semiringᵉ Rᵉ) →
    mul-nat-scalar-Semiringᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    add-Semiringᵉ Rᵉ (mul-nat-scalar-Semiringᵉ mᵉ xᵉ) (mul-nat-scalar-Semiringᵉ nᵉ xᵉ)
  right-distributive-mul-nat-scalar-add-Semiringᵉ mᵉ zero-ℕᵉ xᵉ =
    invᵉ (right-unit-law-add-Semiringᵉ Rᵉ (mul-nat-scalar-Semiringᵉ mᵉ xᵉ))
  right-distributive-mul-nat-scalar-add-Semiringᵉ mᵉ (succ-ℕᵉ nᵉ) xᵉ =
    ( apᵉ
      ( add-Semiring'ᵉ Rᵉ xᵉ)
      ( right-distributive-mul-nat-scalar-add-Semiringᵉ mᵉ nᵉ xᵉ)) ∙ᵉ
    ( associative-add-Semiringᵉ Rᵉ
      ( mul-nat-scalar-Semiringᵉ mᵉ xᵉ)
      ( mul-nat-scalar-Semiringᵉ nᵉ xᵉ) xᵉ)
```