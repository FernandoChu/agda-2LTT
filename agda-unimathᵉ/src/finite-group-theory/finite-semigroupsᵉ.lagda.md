# Finite semigroups

```agda
module finite-group-theory.finite-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.decidable-propositionsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.set-truncationsᵉ
open import foundation.setsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.semigroupsᵉ

open import univalent-combinatorics.dependent-function-typesᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.function-typesᵉ
open import univalent-combinatorics.pi-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Finiteᵉ semigroupsᵉ areᵉ semigroupsᵉ ofᵉ whichᵉ theᵉ underlyingᵉ typeᵉ isᵉ finite.ᵉ

## Definitions

### The predicate of having an associative multiplication operation on finite types

```agda
has-associative-mul-𝔽ᵉ : {lᵉ : Level} (Xᵉ : 𝔽ᵉ lᵉ) → UUᵉ lᵉ
has-associative-mul-𝔽ᵉ Xᵉ = has-associative-mulᵉ (type-𝔽ᵉ Xᵉ)
```

### Finite semigroups

```agda
Semigroup-𝔽ᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Semigroup-𝔽ᵉ lᵉ = Σᵉ (𝔽ᵉ lᵉ) (has-associative-mul-𝔽ᵉ)

module _
  {lᵉ : Level} (Gᵉ : Semigroup-𝔽ᵉ lᵉ)
  where

  finite-type-Semigroup-𝔽ᵉ : 𝔽ᵉ lᵉ
  finite-type-Semigroup-𝔽ᵉ = pr1ᵉ Gᵉ

  set-Semigroup-𝔽ᵉ : Setᵉ lᵉ
  set-Semigroup-𝔽ᵉ = set-𝔽ᵉ finite-type-Semigroup-𝔽ᵉ

  type-Semigroup-𝔽ᵉ : UUᵉ lᵉ
  type-Semigroup-𝔽ᵉ = type-𝔽ᵉ finite-type-Semigroup-𝔽ᵉ

  is-finite-type-Semigroup-𝔽ᵉ : is-finiteᵉ type-Semigroup-𝔽ᵉ
  is-finite-type-Semigroup-𝔽ᵉ =
    is-finite-type-𝔽ᵉ finite-type-Semigroup-𝔽ᵉ

  is-set-type-Semigroup-𝔽ᵉ : is-setᵉ type-Semigroup-𝔽ᵉ
  is-set-type-Semigroup-𝔽ᵉ =
    is-set-type-𝔽ᵉ finite-type-Semigroup-𝔽ᵉ

  has-associative-mul-Semigroup-𝔽ᵉ :
    has-associative-mulᵉ type-Semigroup-𝔽ᵉ
  has-associative-mul-Semigroup-𝔽ᵉ = pr2ᵉ Gᵉ

  semigroup-Semigroup-𝔽ᵉ : Semigroupᵉ lᵉ
  pr1ᵉ semigroup-Semigroup-𝔽ᵉ = set-Semigroup-𝔽ᵉ
  pr2ᵉ semigroup-Semigroup-𝔽ᵉ = has-associative-mul-Semigroup-𝔽ᵉ

  mul-Semigroup-𝔽ᵉ :
    type-Semigroup-𝔽ᵉ → type-Semigroup-𝔽ᵉ → type-Semigroup-𝔽ᵉ
  mul-Semigroup-𝔽ᵉ = mul-Semigroupᵉ semigroup-Semigroup-𝔽ᵉ

  mul-Semigroup-𝔽'ᵉ :
    type-Semigroup-𝔽ᵉ → type-Semigroup-𝔽ᵉ → type-Semigroup-𝔽ᵉ
  mul-Semigroup-𝔽'ᵉ = mul-Semigroup'ᵉ semigroup-Semigroup-𝔽ᵉ

  associative-mul-Semigroup-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Semigroup-𝔽ᵉ) →
    ( mul-Semigroup-𝔽ᵉ (mul-Semigroup-𝔽ᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( mul-Semigroup-𝔽ᵉ xᵉ (mul-Semigroup-𝔽ᵉ yᵉ zᵉ))
  associative-mul-Semigroup-𝔽ᵉ =
    associative-mul-Semigroupᵉ semigroup-Semigroup-𝔽ᵉ

finite-semigroup-is-finite-Semigroupᵉ :
  {lᵉ : Level} → (Gᵉ : Semigroupᵉ lᵉ) → is-finiteᵉ (type-Semigroupᵉ Gᵉ) → Semigroup-𝔽ᵉ lᵉ
pr1ᵉ (pr1ᵉ (finite-semigroup-is-finite-Semigroupᵉ Gᵉ fᵉ)) = type-Semigroupᵉ Gᵉ
pr2ᵉ (pr1ᵉ (finite-semigroup-is-finite-Semigroupᵉ Gᵉ fᵉ)) = fᵉ
pr2ᵉ (finite-semigroup-is-finite-Semigroupᵉ Gᵉ fᵉ) = has-associative-mul-Semigroupᵉ Gᵉ

module _
  {lᵉ : Level} (Gᵉ : Semigroup-𝔽ᵉ lᵉ)
  where

  ap-mul-Semigroup-𝔽ᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Semigroup-𝔽ᵉ Gᵉ} →
    xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → mul-Semigroup-𝔽ᵉ Gᵉ xᵉ yᵉ ＝ᵉ mul-Semigroup-𝔽ᵉ Gᵉ x'ᵉ y'ᵉ
  ap-mul-Semigroup-𝔽ᵉ = ap-mul-Semigroupᵉ (semigroup-Semigroup-𝔽ᵉ Gᵉ)
```

### Semigroups of order `n`

```agda
Semigroup-of-Order'ᵉ : (lᵉ : Level) (nᵉ : ℕᵉ) → UUᵉ (lsuc lᵉ)
Semigroup-of-Order'ᵉ lᵉ nᵉ =
  Σᵉ ( UU-Finᵉ lᵉ nᵉ)
    ( λ Xᵉ → has-associative-mulᵉ (type-UU-Finᵉ nᵉ Xᵉ))

Semigroup-of-Orderᵉ : (lᵉ : Level) (nᵉ : ℕᵉ) → UUᵉ (lsuc lᵉ)
Semigroup-of-Orderᵉ lᵉ nᵉ =
  Σᵉ (Semigroupᵉ lᵉ) (λ Gᵉ → mere-equivᵉ (Finᵉ nᵉ) (type-Semigroupᵉ Gᵉ))
```

## Properties

### If `X` is finite, then there are finitely many associative operations on `X`

```agda
is-finite-has-associative-mulᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → is-finiteᵉ Xᵉ → is-finiteᵉ (has-associative-mulᵉ Xᵉ)
is-finite-has-associative-mulᵉ Hᵉ =
  is-finite-Σᵉ
    ( is-finite-function-typeᵉ Hᵉ (is-finite-function-typeᵉ Hᵉ Hᵉ))
    ( λ μᵉ →
      is-finite-Πᵉ Hᵉ
        ( λ xᵉ →
          is-finite-Πᵉ Hᵉ
            ( λ yᵉ →
              is-finite-Πᵉ Hᵉ
                ( λ zᵉ →
                  is-finite-eqᵉ (has-decidable-equality-is-finiteᵉ Hᵉ)))))
```

### The type of semigroups of order `n` is π-finite

```agda
is-π-finite-Semigroup-of-Order'ᵉ :
  {lᵉ : Level} (kᵉ nᵉ : ℕᵉ) → is-π-finiteᵉ kᵉ (Semigroup-of-Order'ᵉ lᵉ nᵉ)
is-π-finite-Semigroup-of-Order'ᵉ kᵉ nᵉ =
  is-π-finite-Σᵉ kᵉ
    ( is-π-finite-UU-Finᵉ (succ-ℕᵉ kᵉ) nᵉ)
    ( λ xᵉ →
      is-π-finite-is-finiteᵉ kᵉ
        ( is-finite-has-associative-mulᵉ
          ( is-finite-type-UU-Finᵉ nᵉ xᵉ)))

is-π-finite-Semigroup-of-Orderᵉ :
  {lᵉ : Level} (kᵉ nᵉ : ℕᵉ) → is-π-finiteᵉ kᵉ (Semigroup-of-Orderᵉ lᵉ nᵉ)
is-π-finite-Semigroup-of-Orderᵉ {lᵉ} kᵉ nᵉ =
  is-π-finite-equivᵉ kᵉ eᵉ
    ( is-π-finite-Semigroup-of-Order'ᵉ kᵉ nᵉ)
  where
  eᵉ : Semigroup-of-Orderᵉ lᵉ nᵉ ≃ᵉ Semigroup-of-Order'ᵉ lᵉ nᵉ
  eᵉ = ( equiv-Σᵉ
        ( has-associative-mulᵉ ∘ᵉ type-UU-Finᵉ nᵉ)
        ( ( right-unit-law-Σ-is-contrᵉ
            ( λ Xᵉ →
              is-proof-irrelevant-is-propᵉ
                ( is-prop-is-setᵉ _)
                ( is-set-is-finiteᵉ (is-finite-has-cardinalityᵉ nᵉ (pr2ᵉ Xᵉ))))) ∘eᵉ
          ( equiv-right-swap-Σᵉ))
        ( λ Xᵉ → id-equivᵉ)) ∘eᵉ
      ( equiv-right-swap-Σᵉ
        { Aᵉ = Setᵉ lᵉ}
        { Bᵉ = has-associative-mul-Setᵉ}
        { Cᵉ = mere-equivᵉ (Finᵉ nᵉ) ∘ᵉ type-Setᵉ})
```

### The function that returns for each `n` the number of semigroups of order `n` up to isomorphism

```agda
number-of-semi-groups-of-orderᵉ : ℕᵉ → ℕᵉ
number-of-semi-groups-of-orderᵉ nᵉ =
  number-of-connected-componentsᵉ
    ( is-π-finite-Semigroup-of-Orderᵉ {lzeroᵉ} zero-ℕᵉ nᵉ)

mere-equiv-number-of-semi-groups-of-orderᵉ :
  (nᵉ : ℕᵉ) →
  mere-equivᵉ
    ( Finᵉ (number-of-semi-groups-of-orderᵉ nᵉ))
    ( type-trunc-Setᵉ (Semigroup-of-Orderᵉ lzero nᵉ))
mere-equiv-number-of-semi-groups-of-orderᵉ nᵉ =
  mere-equiv-number-of-connected-componentsᵉ
    ( is-π-finite-Semigroup-of-Orderᵉ {lzeroᵉ} zero-ℕᵉ nᵉ)
```

### There is a finite number of ways to equip a finite type with the structure of a semigroup

```agda
structure-semigroup-𝔽ᵉ :
  {l1ᵉ : Level} → 𝔽ᵉ l1ᵉ → UUᵉ l1ᵉ
structure-semigroup-𝔽ᵉ = has-associative-mul-𝔽ᵉ

is-finite-structure-semigroup-𝔽ᵉ :
  {lᵉ : Level} → (Xᵉ : 𝔽ᵉ lᵉ) → is-finiteᵉ (structure-semigroup-𝔽ᵉ Xᵉ)
is-finite-structure-semigroup-𝔽ᵉ Xᵉ =
  is-finite-Σᵉ
    ( is-finite-Πᵉ
      ( is-finite-type-𝔽ᵉ Xᵉ)
      ( λ _ → is-finite-Πᵉ (is-finite-type-𝔽ᵉ Xᵉ) (λ _ → is-finite-type-𝔽ᵉ Xᵉ)))
    ( λ mᵉ →
      is-finite-Πᵉ
        ( is-finite-type-𝔽ᵉ Xᵉ)
        ( λ xᵉ →
          is-finite-Πᵉ
            ( is-finite-type-𝔽ᵉ Xᵉ)
            ( λ yᵉ →
              is-finite-Πᵉ
                ( is-finite-type-𝔽ᵉ Xᵉ)
                ( λ zᵉ →
                  is-finite-is-decidable-Propᵉ
                    ( (mᵉ (mᵉ xᵉ yᵉ) zᵉ ＝ᵉ mᵉ xᵉ (mᵉ yᵉ zᵉ)) ,ᵉ
                      is-set-is-finiteᵉ
                        ( is-finite-type-𝔽ᵉ Xᵉ)
                        ( mᵉ (mᵉ xᵉ yᵉ) zᵉ)
                        ( mᵉ xᵉ (mᵉ yᵉ zᵉ)))
                    ( has-decidable-equality-is-finiteᵉ
                      ( is-finite-type-𝔽ᵉ Xᵉ)
                      ( mᵉ (mᵉ xᵉ yᵉ) zᵉ)
                      ( mᵉ xᵉ (mᵉ yᵉ zᵉ)))))))
```