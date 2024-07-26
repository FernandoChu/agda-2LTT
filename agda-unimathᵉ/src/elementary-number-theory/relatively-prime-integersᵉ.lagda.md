# Relatively prime integers

```agda
module elementary-number-theory.relatively-prime-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integersᵉ
open import elementary-number-theory.greatest-common-divisor-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.relatively-prime-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Twoᵉ integersᵉ areᵉ saidᵉ to beᵉ relativelyᵉ primeᵉ ifᵉ theirᵉ greatestᵉ commonᵉ divisorᵉ
isᵉ 1.ᵉ

## Definition

```agda
is-relative-prime-ℤᵉ : ℤᵉ → ℤᵉ → UUᵉ lzero
is-relative-prime-ℤᵉ xᵉ yᵉ = is-one-ℤᵉ (gcd-ℤᵉ xᵉ yᵉ)
```

## Properties

### Being relatively prime is a proposition

```agda
is-prop-is-relative-prime-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → is-propᵉ (is-relative-prime-ℤᵉ xᵉ yᵉ)
is-prop-is-relative-prime-ℤᵉ xᵉ yᵉ = is-set-ℤᵉ (gcd-ℤᵉ xᵉ yᵉ) one-ℤᵉ
```

### Two integers are relatively prime if and only if their absolute values are relatively prime natural numbers

```agda
is-relatively-prime-abs-is-relatively-prime-ℤᵉ :
  {aᵉ bᵉ : ℤᵉ} → is-relative-prime-ℤᵉ aᵉ bᵉ →
  is-relatively-prime-ℕᵉ (abs-ℤᵉ aᵉ) (abs-ℤᵉ bᵉ)
is-relatively-prime-abs-is-relatively-prime-ℤᵉ {aᵉ} {bᵉ} Hᵉ = is-injective-int-ℕᵉ Hᵉ

is-relatively-prime-is-relatively-prime-abs-ℤᵉ :
  {aᵉ bᵉ : ℤᵉ} → is-relatively-prime-ℕᵉ (abs-ℤᵉ aᵉ) (abs-ℤᵉ bᵉ) →
  is-relative-prime-ℤᵉ aᵉ bᵉ
is-relatively-prime-is-relatively-prime-abs-ℤᵉ {aᵉ} {bᵉ} Hᵉ = apᵉ int-ℕᵉ Hᵉ
```

### For any two integers `a` and `b` that are not both `0`, the integers `a/gcd(a,b)` and `b/gcd(a,b)` are relatively prime

```agda
{-ᵉ
relatively-prime-quotient-div-ℤᵉ :
  {aᵉ bᵉ : ℤᵉ} → (is-nonzero-ℤᵉ aᵉ +ᵉ is-nonzero-ℤᵉ bᵉ) →
  is-relative-prime-ℤᵉ
    ( quotient-div-ℤᵉ (gcd-ℤᵉ aᵉ bᵉ) aᵉ (div-left-gcd-ℤᵉ aᵉ bᵉ))
    ( quotient-div-ℤᵉ (gcd-ℤᵉ aᵉ bᵉ) bᵉ (div-right-gcd-ℤᵉ aᵉ bᵉ))
relatively-prime-quotient-div-ℤᵉ Hᵉ =
  is-relatively-prime-is-relatively-prime-abs-ℤᵉ
    {!!ᵉ}
-ᵉ}
```