# Commutative semirings

```agda
module commutative-algebra.commutative-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.monoidsᵉ

open import ring-theory.semiringsᵉ
```

</details>

## Idea

Aᵉ [semiring](ring-theory.semirings.mdᵉ) `A`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "commutative"ᵉ Disambiguation="semiring"ᵉ Agda=is-commutative-Semiringᵉ}}
ifᵉ itsᵉ multiplicativeᵉ operationᵉ isᵉ commutative,ᵉ i.e.,ᵉ ifᵉ `xyᵉ = yx`ᵉ forᵉ allᵉ
`x,ᵉ yᵉ ∈ᵉ A`.ᵉ

## Definitions

### The predicate on semirings of being commutative

```agda
module _
  {lᵉ : Level} (Aᵉ : Semiringᵉ lᵉ)
  where

  is-commutative-Semiringᵉ : UUᵉ lᵉ
  is-commutative-Semiringᵉ =
    (xᵉ yᵉ : type-Semiringᵉ Aᵉ) → mul-Semiringᵉ Aᵉ xᵉ yᵉ ＝ᵉ mul-Semiringᵉ Aᵉ yᵉ xᵉ

  is-prop-is-commutative-Semiringᵉ : is-propᵉ is-commutative-Semiringᵉ
  is-prop-is-commutative-Semiringᵉ =
    is-prop-iterated-Πᵉ 2
      ( λ xᵉ yᵉ →
        is-set-type-Semiringᵉ Aᵉ (mul-Semiringᵉ Aᵉ xᵉ yᵉ) (mul-Semiringᵉ Aᵉ yᵉ xᵉ))

  is-commutative-prop-Semiringᵉ : Propᵉ lᵉ
  is-commutative-prop-Semiringᵉ =
    ( is-commutative-Semiringᵉ ,ᵉ is-prop-is-commutative-Semiringᵉ)
```

### The type of commutative semirings

```agda
Commutative-Semiringᵉ :
  ( lᵉ : Level) → UUᵉ (lsuc lᵉ)
Commutative-Semiringᵉ lᵉ = Σᵉ (Semiringᵉ lᵉ) is-commutative-Semiringᵉ
```

### Immediate infrastructure for commutative semirings

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  semiring-Commutative-Semiringᵉ : Semiringᵉ lᵉ
  semiring-Commutative-Semiringᵉ = pr1ᵉ Aᵉ

  additive-commutative-monoid-Commutative-Semiringᵉ : Commutative-Monoidᵉ lᵉ
  additive-commutative-monoid-Commutative-Semiringᵉ =
    additive-commutative-monoid-Semiringᵉ semiring-Commutative-Semiringᵉ

  multiplicative-monoid-Commutative-Semiringᵉ : Monoidᵉ lᵉ
  multiplicative-monoid-Commutative-Semiringᵉ =
    multiplicative-monoid-Semiringᵉ semiring-Commutative-Semiringᵉ

  set-Commutative-Semiringᵉ : Setᵉ lᵉ
  set-Commutative-Semiringᵉ = set-Semiringᵉ semiring-Commutative-Semiringᵉ

  type-Commutative-Semiringᵉ : UUᵉ lᵉ
  type-Commutative-Semiringᵉ = type-Semiringᵉ semiring-Commutative-Semiringᵉ

  is-set-type-Commutative-Semiringᵉ : is-setᵉ type-Commutative-Semiringᵉ
  is-set-type-Commutative-Semiringᵉ =
    is-set-type-Semiringᵉ semiring-Commutative-Semiringᵉ

  zero-Commutative-Semiringᵉ : type-Commutative-Semiringᵉ
  zero-Commutative-Semiringᵉ = zero-Semiringᵉ semiring-Commutative-Semiringᵉ

  is-zero-Commutative-Semiringᵉ : type-Commutative-Semiringᵉ → UUᵉ lᵉ
  is-zero-Commutative-Semiringᵉ = is-zero-Semiringᵉ semiring-Commutative-Semiringᵉ

  is-nonzero-Commutative-Semiringᵉ : type-Commutative-Semiringᵉ → UUᵉ lᵉ
  is-nonzero-Commutative-Semiringᵉ =
    is-nonzero-Semiringᵉ semiring-Commutative-Semiringᵉ

  add-Commutative-Semiringᵉ :
    type-Commutative-Semiringᵉ → type-Commutative-Semiringᵉ →
    type-Commutative-Semiringᵉ
  add-Commutative-Semiringᵉ = add-Semiringᵉ semiring-Commutative-Semiringᵉ

  add-Commutative-Semiring'ᵉ :
    type-Commutative-Semiringᵉ → type-Commutative-Semiringᵉ →
    type-Commutative-Semiringᵉ
  add-Commutative-Semiring'ᵉ = add-Semiring'ᵉ semiring-Commutative-Semiringᵉ

  ap-add-Commutative-Semiringᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Commutative-Semiringᵉ} →
    (xᵉ ＝ᵉ x'ᵉ) → (yᵉ ＝ᵉ y'ᵉ) →
    add-Commutative-Semiringᵉ xᵉ yᵉ ＝ᵉ add-Commutative-Semiringᵉ x'ᵉ y'ᵉ
  ap-add-Commutative-Semiringᵉ = ap-add-Semiringᵉ semiring-Commutative-Semiringᵉ

  associative-add-Commutative-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Semiringᵉ) →
    ( add-Commutative-Semiringᵉ (add-Commutative-Semiringᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Commutative-Semiringᵉ xᵉ (add-Commutative-Semiringᵉ yᵉ zᵉ))
  associative-add-Commutative-Semiringᵉ =
    associative-add-Semiringᵉ semiring-Commutative-Semiringᵉ

  left-unit-law-add-Commutative-Semiringᵉ :
    (xᵉ : type-Commutative-Semiringᵉ) →
    add-Commutative-Semiringᵉ zero-Commutative-Semiringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Commutative-Semiringᵉ =
    left-unit-law-add-Semiringᵉ semiring-Commutative-Semiringᵉ

  right-unit-law-add-Commutative-Semiringᵉ :
    (xᵉ : type-Commutative-Semiringᵉ) →
    add-Commutative-Semiringᵉ xᵉ zero-Commutative-Semiringᵉ ＝ᵉ xᵉ
  right-unit-law-add-Commutative-Semiringᵉ =
    right-unit-law-add-Semiringᵉ semiring-Commutative-Semiringᵉ

  commutative-add-Commutative-Semiringᵉ :
    (xᵉ yᵉ : type-Commutative-Semiringᵉ) →
    add-Commutative-Semiringᵉ xᵉ yᵉ ＝ᵉ add-Commutative-Semiringᵉ yᵉ xᵉ
  commutative-add-Commutative-Semiringᵉ =
    commutative-add-Semiringᵉ semiring-Commutative-Semiringᵉ

  interchange-add-add-Commutative-Semiringᵉ :
    (xᵉ yᵉ x'ᵉ y'ᵉ : type-Commutative-Semiringᵉ) →
    ( add-Commutative-Semiringᵉ
      ( add-Commutative-Semiringᵉ xᵉ yᵉ)
      ( add-Commutative-Semiringᵉ x'ᵉ y'ᵉ)) ＝ᵉ
    ( add-Commutative-Semiringᵉ
      ( add-Commutative-Semiringᵉ xᵉ x'ᵉ)
      ( add-Commutative-Semiringᵉ yᵉ y'ᵉ))
  interchange-add-add-Commutative-Semiringᵉ =
    interchange-add-add-Semiringᵉ semiring-Commutative-Semiringᵉ

  right-swap-add-Commutative-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Semiringᵉ) →
    ( add-Commutative-Semiringᵉ (add-Commutative-Semiringᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Commutative-Semiringᵉ (add-Commutative-Semiringᵉ xᵉ zᵉ) yᵉ)
  right-swap-add-Commutative-Semiringᵉ =
    right-swap-add-Semiringᵉ semiring-Commutative-Semiringᵉ

  left-swap-add-Commutative-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Semiringᵉ) →
    ( add-Commutative-Semiringᵉ xᵉ (add-Commutative-Semiringᵉ yᵉ zᵉ)) ＝ᵉ
    ( add-Commutative-Semiringᵉ yᵉ (add-Commutative-Semiringᵉ xᵉ zᵉ))
  left-swap-add-Commutative-Semiringᵉ =
    left-swap-add-Semiringᵉ semiring-Commutative-Semiringᵉ

  mul-Commutative-Semiringᵉ :
    (xᵉ yᵉ : type-Commutative-Semiringᵉ) → type-Commutative-Semiringᵉ
  mul-Commutative-Semiringᵉ = mul-Semiringᵉ semiring-Commutative-Semiringᵉ

  mul-Commutative-Semiring'ᵉ :
    (xᵉ yᵉ : type-Commutative-Semiringᵉ) → type-Commutative-Semiringᵉ
  mul-Commutative-Semiring'ᵉ = mul-Semiring'ᵉ semiring-Commutative-Semiringᵉ

  one-Commutative-Semiringᵉ : type-Commutative-Semiringᵉ
  one-Commutative-Semiringᵉ = one-Semiringᵉ semiring-Commutative-Semiringᵉ

  left-unit-law-mul-Commutative-Semiringᵉ :
    (xᵉ : type-Commutative-Semiringᵉ) →
    mul-Commutative-Semiringᵉ one-Commutative-Semiringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Commutative-Semiringᵉ =
    left-unit-law-mul-Semiringᵉ semiring-Commutative-Semiringᵉ

  right-unit-law-mul-Commutative-Semiringᵉ :
    (xᵉ : type-Commutative-Semiringᵉ) →
    mul-Commutative-Semiringᵉ xᵉ one-Commutative-Semiringᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Commutative-Semiringᵉ =
    right-unit-law-mul-Semiringᵉ semiring-Commutative-Semiringᵉ

  associative-mul-Commutative-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Semiringᵉ) →
    mul-Commutative-Semiringᵉ (mul-Commutative-Semiringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Commutative-Semiringᵉ xᵉ (mul-Commutative-Semiringᵉ yᵉ zᵉ)
  associative-mul-Commutative-Semiringᵉ =
    associative-mul-Semiringᵉ semiring-Commutative-Semiringᵉ

  left-distributive-mul-add-Commutative-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Semiringᵉ) →
    ( mul-Commutative-Semiringᵉ xᵉ (add-Commutative-Semiringᵉ yᵉ zᵉ)) ＝ᵉ
    ( add-Commutative-Semiringᵉ
      ( mul-Commutative-Semiringᵉ xᵉ yᵉ)
      ( mul-Commutative-Semiringᵉ xᵉ zᵉ))
  left-distributive-mul-add-Commutative-Semiringᵉ =
    left-distributive-mul-add-Semiringᵉ semiring-Commutative-Semiringᵉ

  right-distributive-mul-add-Commutative-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Semiringᵉ) →
    ( mul-Commutative-Semiringᵉ (add-Commutative-Semiringᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Commutative-Semiringᵉ
      ( mul-Commutative-Semiringᵉ xᵉ zᵉ)
      ( mul-Commutative-Semiringᵉ yᵉ zᵉ))
  right-distributive-mul-add-Commutative-Semiringᵉ =
    right-distributive-mul-add-Semiringᵉ semiring-Commutative-Semiringᵉ

  commutative-mul-Commutative-Semiringᵉ :
    (xᵉ yᵉ : type-Commutative-Semiringᵉ) →
    mul-Commutative-Semiringᵉ xᵉ yᵉ ＝ᵉ mul-Commutative-Semiringᵉ yᵉ xᵉ
  commutative-mul-Commutative-Semiringᵉ = pr2ᵉ Aᵉ

  multiplicative-commutative-monoid-Commutative-Semiringᵉ :
    Commutative-Monoidᵉ lᵉ
  pr1ᵉ multiplicative-commutative-monoid-Commutative-Semiringᵉ =
    multiplicative-monoid-Commutative-Semiringᵉ
  pr2ᵉ multiplicative-commutative-monoid-Commutative-Semiringᵉ =
    commutative-mul-Commutative-Semiringᵉ

  left-zero-law-mul-Commutative-Semiringᵉ :
    (xᵉ : type-Commutative-Semiringᵉ) →
    mul-Commutative-Semiringᵉ zero-Commutative-Semiringᵉ xᵉ ＝ᵉ
    zero-Commutative-Semiringᵉ
  left-zero-law-mul-Commutative-Semiringᵉ =
    left-zero-law-mul-Semiringᵉ semiring-Commutative-Semiringᵉ

  right-zero-law-mul-Commutative-Semiringᵉ :
    (xᵉ : type-Commutative-Semiringᵉ) →
    mul-Commutative-Semiringᵉ xᵉ zero-Commutative-Semiringᵉ ＝ᵉ
    zero-Commutative-Semiringᵉ
  right-zero-law-mul-Commutative-Semiringᵉ =
    right-zero-law-mul-Semiringᵉ semiring-Commutative-Semiringᵉ

  right-swap-mul-Commutative-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Semiringᵉ) →
    mul-Commutative-Semiringᵉ (mul-Commutative-Semiringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Commutative-Semiringᵉ (mul-Commutative-Semiringᵉ xᵉ zᵉ) yᵉ
  right-swap-mul-Commutative-Semiringᵉ =
    right-swap-mul-Commutative-Monoidᵉ
      multiplicative-commutative-monoid-Commutative-Semiringᵉ

  left-swap-mul-Commutative-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Semiringᵉ) →
    mul-Commutative-Semiringᵉ xᵉ (mul-Commutative-Semiringᵉ yᵉ zᵉ) ＝ᵉ
    mul-Commutative-Semiringᵉ yᵉ (mul-Commutative-Semiringᵉ xᵉ zᵉ)
  left-swap-mul-Commutative-Semiringᵉ =
    left-swap-mul-Commutative-Monoidᵉ
      multiplicative-commutative-monoid-Commutative-Semiringᵉ
```

## Operations

### Scalar multiplication of elements of a commutative ring by natural numbers

```agda
  mul-nat-scalar-Commutative-Semiringᵉ :
    ℕᵉ → type-Commutative-Semiringᵉ → type-Commutative-Semiringᵉ
  mul-nat-scalar-Commutative-Semiringᵉ =
    mul-nat-scalar-Semiringᵉ semiring-Commutative-Semiringᵉ

  ap-mul-nat-scalar-Commutative-Semiringᵉ :
    {mᵉ nᵉ : ℕᵉ} {xᵉ yᵉ : type-Commutative-Semiringᵉ} →
    (mᵉ ＝ᵉ nᵉ) → (xᵉ ＝ᵉ yᵉ) →
    mul-nat-scalar-Commutative-Semiringᵉ mᵉ xᵉ ＝ᵉ
    mul-nat-scalar-Commutative-Semiringᵉ nᵉ yᵉ
  ap-mul-nat-scalar-Commutative-Semiringᵉ =
    ap-mul-nat-scalar-Semiringᵉ semiring-Commutative-Semiringᵉ

  left-zero-law-mul-nat-scalar-Commutative-Semiringᵉ :
    (xᵉ : type-Commutative-Semiringᵉ) →
    mul-nat-scalar-Commutative-Semiringᵉ 0 xᵉ ＝ᵉ zero-Commutative-Semiringᵉ
  left-zero-law-mul-nat-scalar-Commutative-Semiringᵉ =
    left-zero-law-mul-nat-scalar-Semiringᵉ semiring-Commutative-Semiringᵉ

  right-zero-law-mul-nat-scalar-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) →
    mul-nat-scalar-Commutative-Semiringᵉ nᵉ zero-Commutative-Semiringᵉ ＝ᵉ
    zero-Commutative-Semiringᵉ
  right-zero-law-mul-nat-scalar-Commutative-Semiringᵉ =
    right-zero-law-mul-nat-scalar-Semiringᵉ semiring-Commutative-Semiringᵉ

  left-unit-law-mul-nat-scalar-Commutative-Semiringᵉ :
    (xᵉ : type-Commutative-Semiringᵉ) →
    mul-nat-scalar-Commutative-Semiringᵉ 1 xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-nat-scalar-Commutative-Semiringᵉ =
    left-unit-law-mul-nat-scalar-Semiringᵉ semiring-Commutative-Semiringᵉ

  left-nat-scalar-law-mul-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Commutative-Semiringᵉ) →
    mul-Commutative-Semiringᵉ (mul-nat-scalar-Commutative-Semiringᵉ nᵉ xᵉ) yᵉ ＝ᵉ
    mul-nat-scalar-Commutative-Semiringᵉ nᵉ (mul-Commutative-Semiringᵉ xᵉ yᵉ)
  left-nat-scalar-law-mul-Commutative-Semiringᵉ =
    left-nat-scalar-law-mul-Semiringᵉ semiring-Commutative-Semiringᵉ

  right-nat-scalar-law-mul-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Commutative-Semiringᵉ) →
    mul-Commutative-Semiringᵉ xᵉ (mul-nat-scalar-Commutative-Semiringᵉ nᵉ yᵉ) ＝ᵉ
    mul-nat-scalar-Commutative-Semiringᵉ nᵉ (mul-Commutative-Semiringᵉ xᵉ yᵉ)
  right-nat-scalar-law-mul-Commutative-Semiringᵉ =
    right-nat-scalar-law-mul-Semiringᵉ semiring-Commutative-Semiringᵉ

  left-distributive-mul-nat-scalar-add-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Commutative-Semiringᵉ) →
    mul-nat-scalar-Commutative-Semiringᵉ nᵉ (add-Commutative-Semiringᵉ xᵉ yᵉ) ＝ᵉ
    add-Commutative-Semiringᵉ
      ( mul-nat-scalar-Commutative-Semiringᵉ nᵉ xᵉ)
      ( mul-nat-scalar-Commutative-Semiringᵉ nᵉ yᵉ)
  left-distributive-mul-nat-scalar-add-Commutative-Semiringᵉ =
    left-distributive-mul-nat-scalar-add-Semiringᵉ semiring-Commutative-Semiringᵉ

  right-distributive-mul-nat-scalar-add-Commutative-Semiringᵉ :
    (mᵉ nᵉ : ℕᵉ) (xᵉ : type-Commutative-Semiringᵉ) →
    mul-nat-scalar-Commutative-Semiringᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    add-Commutative-Semiringᵉ
      ( mul-nat-scalar-Commutative-Semiringᵉ mᵉ xᵉ)
      ( mul-nat-scalar-Commutative-Semiringᵉ nᵉ xᵉ)
  right-distributive-mul-nat-scalar-add-Commutative-Semiringᵉ =
    right-distributive-mul-nat-scalar-add-Semiringᵉ semiring-Commutative-Semiringᵉ
```