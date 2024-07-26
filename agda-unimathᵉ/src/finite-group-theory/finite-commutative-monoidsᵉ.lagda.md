# Finite Commutative monoids

```agda
module finite-group-theory.finite-commutative-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import finite-group-theory.finite-monoidsᵉ

open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ

open import univalent-combinatorics.dependent-function-typesᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ finiteᵉ commutativeᵉ monoidᵉ isᵉ aᵉ finiteᵉ monoidᵉ `M`ᵉ in whichᵉ `xyᵉ = yx`ᵉ holdsᵉ forᵉ
allᵉ `xᵉ yᵉ : M`.ᵉ

## Definition

### Finite commutative monoids

```agda
is-commutative-Monoid-𝔽ᵉ :
  {lᵉ : Level} (Mᵉ : Monoid-𝔽ᵉ lᵉ) → UUᵉ lᵉ
is-commutative-Monoid-𝔽ᵉ Mᵉ =
  is-commutative-Monoidᵉ (monoid-Monoid-𝔽ᵉ Mᵉ)

Commutative-Monoid-𝔽ᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Commutative-Monoid-𝔽ᵉ lᵉ = Σᵉ (Monoid-𝔽ᵉ lᵉ) is-commutative-Monoid-𝔽ᵉ

module _
  {lᵉ : Level} (Mᵉ : Commutative-Monoid-𝔽ᵉ lᵉ)
  where

  finite-monoid-Commutative-Monoid-𝔽ᵉ : Monoid-𝔽ᵉ lᵉ
  finite-monoid-Commutative-Monoid-𝔽ᵉ = pr1ᵉ Mᵉ

  monoid-Commutative-Monoid-𝔽ᵉ : Monoidᵉ lᵉ
  monoid-Commutative-Monoid-𝔽ᵉ =
    monoid-Monoid-𝔽ᵉ finite-monoid-Commutative-Monoid-𝔽ᵉ

  finite-type-Commutative-Monoid-𝔽ᵉ : 𝔽ᵉ lᵉ
  finite-type-Commutative-Monoid-𝔽ᵉ =
    finite-type-Monoid-𝔽ᵉ finite-monoid-Commutative-Monoid-𝔽ᵉ

  type-Commutative-Monoid-𝔽ᵉ : UUᵉ lᵉ
  type-Commutative-Monoid-𝔽ᵉ =
    type-Monoid-𝔽ᵉ finite-monoid-Commutative-Monoid-𝔽ᵉ

  is-finite-type-Commutative-Monoid-𝔽ᵉ : is-finiteᵉ type-Commutative-Monoid-𝔽ᵉ
  is-finite-type-Commutative-Monoid-𝔽ᵉ =
    is-finite-type-Monoid-𝔽ᵉ finite-monoid-Commutative-Monoid-𝔽ᵉ

  semigroup-Commutative-Monoid-𝔽ᵉ : Semigroupᵉ lᵉ
  semigroup-Commutative-Monoid-𝔽ᵉ =
    semigroup-Monoid-𝔽ᵉ finite-monoid-Commutative-Monoid-𝔽ᵉ

  set-Commutative-Monoid-𝔽ᵉ : Setᵉ lᵉ
  set-Commutative-Monoid-𝔽ᵉ =
    set-Monoid-𝔽ᵉ finite-monoid-Commutative-Monoid-𝔽ᵉ

  is-set-type-Commutative-Monoid-𝔽ᵉ : is-setᵉ type-Commutative-Monoid-𝔽ᵉ
  is-set-type-Commutative-Monoid-𝔽ᵉ =
    is-set-type-Monoid-𝔽ᵉ finite-monoid-Commutative-Monoid-𝔽ᵉ
```

### The multiplicative operation of a commutative monoid

```agda
  has-associative-mul-Commutative-Monoid-𝔽ᵉ :
    has-associative-mul-Setᵉ set-Commutative-Monoid-𝔽ᵉ
  has-associative-mul-Commutative-Monoid-𝔽ᵉ =
    has-associative-mul-Semigroupᵉ semigroup-Commutative-Monoid-𝔽ᵉ

  mul-Commutative-Monoid-𝔽ᵉ :
    (xᵉ yᵉ : type-Commutative-Monoid-𝔽ᵉ) → type-Commutative-Monoid-𝔽ᵉ
  mul-Commutative-Monoid-𝔽ᵉ = mul-Monoid-𝔽ᵉ finite-monoid-Commutative-Monoid-𝔽ᵉ

  mul-Commutative-Monoid-𝔽'ᵉ :
    (xᵉ yᵉ : type-Commutative-Monoid-𝔽ᵉ) → type-Commutative-Monoid-𝔽ᵉ
  mul-Commutative-Monoid-𝔽'ᵉ =
    mul-Monoid-𝔽'ᵉ finite-monoid-Commutative-Monoid-𝔽ᵉ

  ap-mul-Commutative-Monoid-𝔽ᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Commutative-Monoid-𝔽ᵉ} →
    xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ →
    mul-Commutative-Monoid-𝔽ᵉ xᵉ yᵉ ＝ᵉ mul-Commutative-Monoid-𝔽ᵉ x'ᵉ y'ᵉ
  ap-mul-Commutative-Monoid-𝔽ᵉ =
    ap-mul-Monoid-𝔽ᵉ finite-monoid-Commutative-Monoid-𝔽ᵉ

  associative-mul-Commutative-Monoid-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Monoid-𝔽ᵉ) →
    ( mul-Commutative-Monoid-𝔽ᵉ (mul-Commutative-Monoid-𝔽ᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( mul-Commutative-Monoid-𝔽ᵉ xᵉ (mul-Commutative-Monoid-𝔽ᵉ yᵉ zᵉ))
  associative-mul-Commutative-Monoid-𝔽ᵉ =
    associative-mul-Monoid-𝔽ᵉ finite-monoid-Commutative-Monoid-𝔽ᵉ

  commutative-mul-Commutative-Monoid-𝔽ᵉ :
    (xᵉ yᵉ : type-Commutative-Monoid-𝔽ᵉ) →
    mul-Commutative-Monoid-𝔽ᵉ xᵉ yᵉ ＝ᵉ mul-Commutative-Monoid-𝔽ᵉ yᵉ xᵉ
  commutative-mul-Commutative-Monoid-𝔽ᵉ = pr2ᵉ Mᵉ

  commutative-monoid-Commutative-Monoid-𝔽ᵉ : Commutative-Monoidᵉ lᵉ
  pr1ᵉ commutative-monoid-Commutative-Monoid-𝔽ᵉ = monoid-Commutative-Monoid-𝔽ᵉ
  pr2ᵉ commutative-monoid-Commutative-Monoid-𝔽ᵉ =
    commutative-mul-Commutative-Monoid-𝔽ᵉ

  interchange-mul-mul-Commutative-Monoid-𝔽ᵉ :
    (xᵉ yᵉ x'ᵉ y'ᵉ : type-Commutative-Monoid-𝔽ᵉ) →
    ( mul-Commutative-Monoid-𝔽ᵉ
      ( mul-Commutative-Monoid-𝔽ᵉ xᵉ yᵉ)
      ( mul-Commutative-Monoid-𝔽ᵉ x'ᵉ y'ᵉ)) ＝ᵉ
    ( mul-Commutative-Monoid-𝔽ᵉ
      ( mul-Commutative-Monoid-𝔽ᵉ xᵉ x'ᵉ)
      ( mul-Commutative-Monoid-𝔽ᵉ yᵉ y'ᵉ))
  interchange-mul-mul-Commutative-Monoid-𝔽ᵉ =
    interchange-mul-mul-Commutative-Monoidᵉ
      commutative-monoid-Commutative-Monoid-𝔽ᵉ

  right-swap-mul-Commutative-Monoid-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Monoid-𝔽ᵉ) →
    mul-Commutative-Monoid-𝔽ᵉ (mul-Commutative-Monoid-𝔽ᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Commutative-Monoid-𝔽ᵉ (mul-Commutative-Monoid-𝔽ᵉ xᵉ zᵉ) yᵉ
  right-swap-mul-Commutative-Monoid-𝔽ᵉ =
    right-swap-mul-Commutative-Monoidᵉ
      commutative-monoid-Commutative-Monoid-𝔽ᵉ

  left-swap-mul-Commutative-Monoid-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Monoid-𝔽ᵉ) →
    mul-Commutative-Monoid-𝔽ᵉ xᵉ (mul-Commutative-Monoid-𝔽ᵉ yᵉ zᵉ) ＝ᵉ
    mul-Commutative-Monoid-𝔽ᵉ yᵉ (mul-Commutative-Monoid-𝔽ᵉ xᵉ zᵉ)
  left-swap-mul-Commutative-Monoid-𝔽ᵉ =
    left-swap-mul-Commutative-Monoidᵉ
      commutative-monoid-Commutative-Monoid-𝔽ᵉ
```

### The unit element of a commutative monoid

```agda
module _
  {lᵉ : Level} (Mᵉ : Commutative-Monoid-𝔽ᵉ lᵉ)
  where

  has-unit-Commutative-Monoid-𝔽ᵉ : is-unitalᵉ (mul-Commutative-Monoid-𝔽ᵉ Mᵉ)
  has-unit-Commutative-Monoid-𝔽ᵉ =
    has-unit-Monoidᵉ (monoid-Commutative-Monoid-𝔽ᵉ Mᵉ)

  unit-Commutative-Monoid-𝔽ᵉ : type-Commutative-Monoid-𝔽ᵉ Mᵉ
  unit-Commutative-Monoid-𝔽ᵉ = unit-Monoidᵉ (monoid-Commutative-Monoid-𝔽ᵉ Mᵉ)

  left-unit-law-mul-Commutative-Monoid-𝔽ᵉ :
    (xᵉ : type-Commutative-Monoid-𝔽ᵉ Mᵉ) →
    mul-Commutative-Monoid-𝔽ᵉ Mᵉ unit-Commutative-Monoid-𝔽ᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Commutative-Monoid-𝔽ᵉ =
    left-unit-law-mul-Monoidᵉ (monoid-Commutative-Monoid-𝔽ᵉ Mᵉ)

  right-unit-law-mul-Commutative-Monoid-𝔽ᵉ :
    (xᵉ : type-Commutative-Monoid-𝔽ᵉ Mᵉ) →
    mul-Commutative-Monoid-𝔽ᵉ Mᵉ xᵉ unit-Commutative-Monoid-𝔽ᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Commutative-Monoid-𝔽ᵉ =
    right-unit-law-mul-Monoidᵉ (monoid-Commutative-Monoid-𝔽ᵉ Mᵉ)
```

## Properties

### There is a finite number of ways to equip a finite type with the structure of a finite commutative monoid

```agda
module _
  {lᵉ : Level}
  (Xᵉ : 𝔽ᵉ lᵉ)
  where

  structure-commutative-monoid-𝔽ᵉ : UUᵉ lᵉ
  structure-commutative-monoid-𝔽ᵉ =
    Σᵉ ( structure-monoid-𝔽ᵉ Xᵉ)
      ( λ mᵉ → is-commutative-Monoid-𝔽ᵉ (finite-monoid-structure-monoid-𝔽ᵉ Xᵉ mᵉ))

  finite-commutative-monoid-structure-commutative-monoid-𝔽ᵉ :
    structure-commutative-monoid-𝔽ᵉ → Commutative-Monoid-𝔽ᵉ lᵉ
  pr1ᵉ (finite-commutative-monoid-structure-commutative-monoid-𝔽ᵉ (mᵉ ,ᵉ cᵉ)) =
    finite-monoid-structure-monoid-𝔽ᵉ Xᵉ mᵉ
  pr2ᵉ (finite-commutative-monoid-structure-commutative-monoid-𝔽ᵉ (mᵉ ,ᵉ cᵉ)) = cᵉ

  is-finite-structure-commutative-monoid-𝔽ᵉ :
    is-finiteᵉ structure-commutative-monoid-𝔽ᵉ
  is-finite-structure-commutative-monoid-𝔽ᵉ =
    is-finite-Σᵉ
      ( is-finite-structure-monoid-𝔽ᵉ Xᵉ)
      ( λ mᵉ →
        is-finite-Πᵉ
          ( is-finite-type-𝔽ᵉ Xᵉ)
          ( λ xᵉ → is-finite-Πᵉ ( is-finite-type-𝔽ᵉ Xᵉ) ( λ yᵉ → is-finite-eq-𝔽ᵉ Xᵉ)))
```