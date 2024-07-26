# Inverse semigroups

```agda
module group-theory.inverse-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.semigroupsᵉ
```

</details>

## Idea

Anᵉ inverseᵉ semigroupᵉ isᵉ anᵉ algebraicᵉ structureᵉ thatᵉ modelsᵉ partialᵉ bijections.ᵉ
Inᵉ anᵉ inverseᵉ semigroup,ᵉ elementsᵉ haveᵉ uniqueᵉ inversesᵉ in theᵉ senseᵉ thatᵉ forᵉ
eachᵉ `x`ᵉ thereᵉ isᵉ aᵉ uniqueᵉ `y`ᵉ suchᵉ thatᵉ `xyxᵉ = x`ᵉ andᵉ `yxyᵉ = y`.ᵉ

## Definition

```agda
is-inverse-Semigroupᵉ :
  {lᵉ : Level} (Sᵉ : Semigroupᵉ lᵉ) → UUᵉ lᵉ
is-inverse-Semigroupᵉ Sᵉ =
  (xᵉ : type-Semigroupᵉ Sᵉ) →
  is-contrᵉ
    ( Σᵉ ( type-Semigroupᵉ Sᵉ)
        ( λ yᵉ →
          Idᵉ (mul-Semigroupᵉ Sᵉ (mul-Semigroupᵉ Sᵉ xᵉ yᵉ) xᵉ) xᵉ ×ᵉ
          Idᵉ (mul-Semigroupᵉ Sᵉ (mul-Semigroupᵉ Sᵉ yᵉ xᵉ) yᵉ) yᵉ))

Inverse-Semigroupᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Inverse-Semigroupᵉ lᵉ = Σᵉ (Semigroupᵉ lᵉ) is-inverse-Semigroupᵉ

module _
  {lᵉ : Level} (Sᵉ : Inverse-Semigroupᵉ lᵉ)
  where

  semigroup-Inverse-Semigroupᵉ : Semigroupᵉ lᵉ
  semigroup-Inverse-Semigroupᵉ = pr1ᵉ Sᵉ

  set-Inverse-Semigroupᵉ : Setᵉ lᵉ
  set-Inverse-Semigroupᵉ = set-Semigroupᵉ semigroup-Inverse-Semigroupᵉ

  type-Inverse-Semigroupᵉ : UUᵉ lᵉ
  type-Inverse-Semigroupᵉ = type-Semigroupᵉ semigroup-Inverse-Semigroupᵉ

  is-set-type-Inverse-Semigroupᵉ : is-setᵉ type-Inverse-Semigroupᵉ
  is-set-type-Inverse-Semigroupᵉ =
    is-set-type-Semigroupᵉ semigroup-Inverse-Semigroupᵉ

  mul-Inverse-Semigroupᵉ :
    (xᵉ yᵉ : type-Inverse-Semigroupᵉ) → type-Inverse-Semigroupᵉ
  mul-Inverse-Semigroupᵉ = mul-Semigroupᵉ semigroup-Inverse-Semigroupᵉ

  mul-Inverse-Semigroup'ᵉ :
    (xᵉ yᵉ : type-Inverse-Semigroupᵉ) → type-Inverse-Semigroupᵉ
  mul-Inverse-Semigroup'ᵉ = mul-Semigroup'ᵉ semigroup-Inverse-Semigroupᵉ

  associative-mul-Inverse-Semigroupᵉ :
    (xᵉ yᵉ zᵉ : type-Inverse-Semigroupᵉ) →
    Idᵉ
      ( mul-Inverse-Semigroupᵉ (mul-Inverse-Semigroupᵉ xᵉ yᵉ) zᵉ)
      ( mul-Inverse-Semigroupᵉ xᵉ (mul-Inverse-Semigroupᵉ yᵉ zᵉ))
  associative-mul-Inverse-Semigroupᵉ =
    associative-mul-Semigroupᵉ semigroup-Inverse-Semigroupᵉ

  is-inverse-semigroup-Inverse-Semigroupᵉ :
    is-inverse-Semigroupᵉ semigroup-Inverse-Semigroupᵉ
  is-inverse-semigroup-Inverse-Semigroupᵉ = pr2ᵉ Sᵉ

  inv-Inverse-Semigroupᵉ : type-Inverse-Semigroupᵉ → type-Inverse-Semigroupᵉ
  inv-Inverse-Semigroupᵉ xᵉ =
    pr1ᵉ (centerᵉ (is-inverse-semigroup-Inverse-Semigroupᵉ xᵉ))

  inner-inverse-law-mul-Inverse-Semigroupᵉ :
    (xᵉ : type-Inverse-Semigroupᵉ) →
    Idᵉ
      ( mul-Inverse-Semigroupᵉ
        ( mul-Inverse-Semigroupᵉ xᵉ (inv-Inverse-Semigroupᵉ xᵉ))
        ( xᵉ))
      ( xᵉ)
  inner-inverse-law-mul-Inverse-Semigroupᵉ xᵉ =
    pr1ᵉ (pr2ᵉ (centerᵉ (is-inverse-semigroup-Inverse-Semigroupᵉ xᵉ)))

  outer-inverse-law-mul-Inverse-Semigroupᵉ :
    (xᵉ : type-Inverse-Semigroupᵉ) →
    Idᵉ
      ( mul-Inverse-Semigroupᵉ
        ( mul-Inverse-Semigroupᵉ (inv-Inverse-Semigroupᵉ xᵉ) xᵉ)
        ( inv-Inverse-Semigroupᵉ xᵉ))
      ( inv-Inverse-Semigroupᵉ xᵉ)
  outer-inverse-law-mul-Inverse-Semigroupᵉ xᵉ =
    pr2ᵉ (pr2ᵉ (centerᵉ (is-inverse-semigroup-Inverse-Semigroupᵉ xᵉ)))
```