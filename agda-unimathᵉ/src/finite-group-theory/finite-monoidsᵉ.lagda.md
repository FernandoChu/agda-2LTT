# Finite monoids

```agda
module finite-group-theory.finite-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.finite-semigroupsᵉ

open import foundation.decidable-propositionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.set-truncationsᵉ
open import foundation.setsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ

open import univalent-combinatorics.cartesian-product-typesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.decidable-dependent-function-typesᵉ
open import univalent-combinatorics.decidable-dependent-pair-typesᵉ
open import univalent-combinatorics.dependent-function-typesᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.pi-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ finiteᵉ monoidᵉ isᵉ aᵉ monoidᵉ ofᵉ whichᵉ theᵉ underlyingᵉ typeᵉ isᵉ finite.ᵉ

## Definition

### The type of finite monoids

```agda
is-unital-Semigroup-𝔽ᵉ :
  {lᵉ : Level} → Semigroup-𝔽ᵉ lᵉ → UUᵉ lᵉ
is-unital-Semigroup-𝔽ᵉ Gᵉ = is-unitalᵉ (mul-Semigroup-𝔽ᵉ Gᵉ)

Monoid-𝔽ᵉ :
  (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Monoid-𝔽ᵉ lᵉ = Σᵉ (Semigroup-𝔽ᵉ lᵉ) is-unital-Semigroup-𝔽ᵉ

module _
  {lᵉ : Level} (Mᵉ : Monoid-𝔽ᵉ lᵉ)
  where

  finite-semigroup-Monoid-𝔽ᵉ : Semigroup-𝔽ᵉ lᵉ
  finite-semigroup-Monoid-𝔽ᵉ = pr1ᵉ Mᵉ

  semigroup-Monoid-𝔽ᵉ : Semigroupᵉ lᵉ
  semigroup-Monoid-𝔽ᵉ = semigroup-Semigroup-𝔽ᵉ finite-semigroup-Monoid-𝔽ᵉ

  finite-type-Monoid-𝔽ᵉ : 𝔽ᵉ lᵉ
  finite-type-Monoid-𝔽ᵉ = finite-type-Semigroup-𝔽ᵉ finite-semigroup-Monoid-𝔽ᵉ

  type-Monoid-𝔽ᵉ : UUᵉ lᵉ
  type-Monoid-𝔽ᵉ = type-Semigroup-𝔽ᵉ finite-semigroup-Monoid-𝔽ᵉ

  is-finite-type-Monoid-𝔽ᵉ : is-finiteᵉ type-Monoid-𝔽ᵉ
  is-finite-type-Monoid-𝔽ᵉ = is-finite-type-Semigroup-𝔽ᵉ finite-semigroup-Monoid-𝔽ᵉ

  set-Monoid-𝔽ᵉ : Setᵉ lᵉ
  set-Monoid-𝔽ᵉ = set-Semigroupᵉ semigroup-Monoid-𝔽ᵉ

  is-set-type-Monoid-𝔽ᵉ : is-setᵉ type-Monoid-𝔽ᵉ
  is-set-type-Monoid-𝔽ᵉ = is-set-type-Semigroupᵉ semigroup-Monoid-𝔽ᵉ

  mul-Monoid-𝔽ᵉ : type-Monoid-𝔽ᵉ → type-Monoid-𝔽ᵉ → type-Monoid-𝔽ᵉ
  mul-Monoid-𝔽ᵉ = mul-Semigroupᵉ semigroup-Monoid-𝔽ᵉ

  mul-Monoid-𝔽'ᵉ : type-Monoid-𝔽ᵉ → type-Monoid-𝔽ᵉ → type-Monoid-𝔽ᵉ
  mul-Monoid-𝔽'ᵉ yᵉ xᵉ = mul-Monoid-𝔽ᵉ xᵉ yᵉ

  ap-mul-Monoid-𝔽ᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Monoid-𝔽ᵉ} →
    xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → mul-Monoid-𝔽ᵉ xᵉ yᵉ ＝ᵉ mul-Monoid-𝔽ᵉ x'ᵉ y'ᵉ
  ap-mul-Monoid-𝔽ᵉ = ap-mul-Semigroupᵉ semigroup-Monoid-𝔽ᵉ

  associative-mul-Monoid-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Monoid-𝔽ᵉ) →
    mul-Monoid-𝔽ᵉ (mul-Monoid-𝔽ᵉ xᵉ yᵉ) zᵉ ＝ᵉ mul-Monoid-𝔽ᵉ xᵉ (mul-Monoid-𝔽ᵉ yᵉ zᵉ)
  associative-mul-Monoid-𝔽ᵉ = associative-mul-Semigroupᵉ semigroup-Monoid-𝔽ᵉ

  has-unit-Monoid-𝔽ᵉ : is-unitalᵉ mul-Monoid-𝔽ᵉ
  has-unit-Monoid-𝔽ᵉ = pr2ᵉ Mᵉ

  monoid-Monoid-𝔽ᵉ : Monoidᵉ lᵉ
  pr1ᵉ monoid-Monoid-𝔽ᵉ = semigroup-Monoid-𝔽ᵉ
  pr2ᵉ monoid-Monoid-𝔽ᵉ = has-unit-Monoid-𝔽ᵉ

  unit-Monoid-𝔽ᵉ : type-Monoid-𝔽ᵉ
  unit-Monoid-𝔽ᵉ = unit-Monoidᵉ monoid-Monoid-𝔽ᵉ

  left-unit-law-mul-Monoid-𝔽ᵉ :
    (xᵉ : type-Monoid-𝔽ᵉ) → mul-Monoid-𝔽ᵉ unit-Monoid-𝔽ᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Monoid-𝔽ᵉ = left-unit-law-mul-Monoidᵉ monoid-Monoid-𝔽ᵉ

  right-unit-law-mul-Monoid-𝔽ᵉ :
    (xᵉ : type-Monoid-𝔽ᵉ) → mul-Monoid-𝔽ᵉ xᵉ unit-Monoid-𝔽ᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Monoid-𝔽ᵉ = right-unit-law-mul-Monoidᵉ monoid-Monoid-𝔽ᵉ
```

### Monoids of order `n`

```agda
Monoid-of-Orderᵉ : (lᵉ : Level) (nᵉ : ℕᵉ) → UUᵉ (lsuc lᵉ)
Monoid-of-Orderᵉ lᵉ nᵉ = Σᵉ (Monoidᵉ lᵉ) (λ Mᵉ → mere-equivᵉ (Finᵉ nᵉ) (type-Monoidᵉ Mᵉ))
```

## Properties

### For any semigroup of order `n`, the type of multiplicative units is finite

```agda
is-finite-is-unital-Semigroupᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Xᵉ : Semigroup-of-Orderᵉ lᵉ nᵉ) →
  is-finiteᵉ (is-unital-Semigroupᵉ (pr1ᵉ Xᵉ))
is-finite-is-unital-Semigroupᵉ {lᵉ} nᵉ Xᵉ =
  apply-universal-property-trunc-Propᵉ
    ( pr2ᵉ Xᵉ)
    ( is-finite-Propᵉ _)
    ( λ eᵉ →
      is-finite-is-decidable-Propᵉ
        ( is-unital-prop-Semigroupᵉ (pr1ᵉ Xᵉ))
        ( is-decidable-Σ-countᵉ
          ( pairᵉ nᵉ eᵉ)
          ( λ uᵉ →
            is-decidable-productᵉ
              ( is-decidable-Π-countᵉ
                ( pairᵉ nᵉ eᵉ)
                ( λ xᵉ →
                  has-decidable-equality-countᵉ
                    ( pairᵉ nᵉ eᵉ)
                    ( mul-Semigroupᵉ (pr1ᵉ Xᵉ) uᵉ xᵉ)
                    ( xᵉ)))
              ( is-decidable-Π-countᵉ
                ( pairᵉ nᵉ eᵉ)
                ( λ xᵉ →
                  has-decidable-equality-countᵉ
                    ( pairᵉ nᵉ eᵉ)
                    ( mul-Semigroupᵉ (pr1ᵉ Xᵉ) xᵉ uᵉ)
                    ( xᵉ))))))
```

### The type of monoids of order `n` is π-finite

```agda
is-π-finite-Monoid-of-Orderᵉ :
  {lᵉ : Level} (kᵉ nᵉ : ℕᵉ) → is-π-finiteᵉ kᵉ (Monoid-of-Orderᵉ lᵉ nᵉ)
is-π-finite-Monoid-of-Orderᵉ {lᵉ} kᵉ nᵉ =
  is-π-finite-equivᵉ kᵉ eᵉ
    ( is-π-finite-Σᵉ kᵉ
      ( is-π-finite-Semigroup-of-Orderᵉ (succ-ℕᵉ kᵉ) nᵉ)
      ( λ Xᵉ →
        is-π-finite-is-finiteᵉ kᵉ
          ( is-finite-is-unital-Semigroupᵉ nᵉ Xᵉ)))
  where
  eᵉ :
    Monoid-of-Orderᵉ lᵉ nᵉ ≃ᵉ
    Σᵉ (Semigroup-of-Orderᵉ lᵉ nᵉ) (λ Xᵉ → is-unital-Semigroupᵉ (pr1ᵉ Xᵉ))
  eᵉ = equiv-right-swap-Σᵉ
```

### The function that returns for any `n` the number of monoids of order `n` up to isomorphism

```agda
number-of-monoids-of-orderᵉ : ℕᵉ → ℕᵉ
number-of-monoids-of-orderᵉ nᵉ =
  number-of-connected-componentsᵉ
    ( is-π-finite-Monoid-of-Orderᵉ {lzeroᵉ} zero-ℕᵉ nᵉ)

mere-equiv-number-of-monoids-of-orderᵉ :
  (nᵉ : ℕᵉ) →
  mere-equivᵉ
    ( Finᵉ (number-of-monoids-of-orderᵉ nᵉ))
    ( type-trunc-Setᵉ (Monoid-of-Orderᵉ lzero nᵉ))
mere-equiv-number-of-monoids-of-orderᵉ nᵉ =
  mere-equiv-number-of-connected-componentsᵉ
    ( is-π-finite-Monoid-of-Orderᵉ {lzeroᵉ} zero-ℕᵉ nᵉ)
```

### For any finite semigroup `G`, being unital is a property

```agda
abstract
  is-prop-is-unital-Semigroup-𝔽ᵉ :
    {lᵉ : Level} (Gᵉ : Semigroup-𝔽ᵉ lᵉ) → is-propᵉ (is-unital-Semigroup-𝔽ᵉ Gᵉ)
  is-prop-is-unital-Semigroup-𝔽ᵉ Gᵉ =
    is-prop-is-unital-Semigroupᵉ (semigroup-Semigroup-𝔽ᵉ Gᵉ)

is-unital-Semigroup-𝔽-Propᵉ : {lᵉ : Level} (Gᵉ : Semigroup-𝔽ᵉ lᵉ) → Propᵉ lᵉ
pr1ᵉ (is-unital-Semigroup-𝔽-Propᵉ Gᵉ) = is-unital-Semigroup-𝔽ᵉ Gᵉ
pr2ᵉ (is-unital-Semigroup-𝔽-Propᵉ Gᵉ) = is-prop-is-unital-Semigroup-𝔽ᵉ Gᵉ
```

### For any finite semigroup `G`, being unital is finite

```agda
is-finite-is-unital-Semigroup-𝔽ᵉ :
  {lᵉ : Level} (Gᵉ : Semigroup-𝔽ᵉ lᵉ) → is-finiteᵉ (is-unital-Semigroup-𝔽ᵉ Gᵉ)
is-finite-is-unital-Semigroup-𝔽ᵉ Gᵉ =
  is-finite-Σᵉ
    ( is-finite-type-Semigroup-𝔽ᵉ Gᵉ)
    ( λ eᵉ →
      is-finite-productᵉ
        ( is-finite-Πᵉ
          ( is-finite-type-Semigroup-𝔽ᵉ Gᵉ)
          ( λ xᵉ → is-finite-eq-𝔽ᵉ (finite-type-Semigroup-𝔽ᵉ Gᵉ)))
        ( is-finite-Πᵉ
          ( is-finite-type-Semigroup-𝔽ᵉ Gᵉ)
          ( λ xᵉ → is-finite-eq-𝔽ᵉ (finite-type-Semigroup-𝔽ᵉ Gᵉ))))
```

### There is a finite number of ways to equip a finite type with the structure of a monoid

```agda
structure-monoid-𝔽ᵉ :
  {l1ᵉ : Level} → 𝔽ᵉ l1ᵉ → UUᵉ l1ᵉ
structure-monoid-𝔽ᵉ Xᵉ =
  Σᵉ (structure-semigroup-𝔽ᵉ Xᵉ) (λ pᵉ → is-unital-Semigroup-𝔽ᵉ (Xᵉ ,ᵉ pᵉ))

finite-monoid-structure-monoid-𝔽ᵉ :
  {lᵉ : Level} → (Xᵉ : 𝔽ᵉ lᵉ) → structure-monoid-𝔽ᵉ Xᵉ → Monoid-𝔽ᵉ lᵉ
pr1ᵉ (finite-monoid-structure-monoid-𝔽ᵉ Xᵉ (aᵉ ,ᵉ uᵉ)) = Xᵉ ,ᵉ aᵉ
pr2ᵉ (finite-monoid-structure-monoid-𝔽ᵉ Xᵉ (aᵉ ,ᵉ uᵉ)) = uᵉ

is-finite-structure-monoid-𝔽ᵉ :
  {lᵉ : Level} → (Xᵉ : 𝔽ᵉ lᵉ) → is-finiteᵉ (structure-monoid-𝔽ᵉ Xᵉ)
is-finite-structure-monoid-𝔽ᵉ Xᵉ =
  is-finite-Σᵉ
    ( is-finite-structure-semigroup-𝔽ᵉ Xᵉ)
    ( λ mᵉ → is-finite-is-unital-Semigroup-𝔽ᵉ (Xᵉ ,ᵉ mᵉ))
```