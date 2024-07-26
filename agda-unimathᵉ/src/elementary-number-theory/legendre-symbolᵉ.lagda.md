# The Legendre symbol

```agda
module elementary-number-theory.legendre-symbolᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.modular-arithmeticᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.prime-numbersᵉ
open import elementary-number-theory.squares-modular-arithmeticᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
```

</details>

## Idea

Theᵉ **Legendreᵉ symbol**ᵉ isᵉ aᵉ functionᵉ whichᵉ determinesᵉ whetherᵉ orᵉ notᵉ anᵉ
[integer](elementary-number-theory.integers.mdᵉ) isᵉ aᵉ perfectᵉ squareᵉ in theᵉ ringᵉ
`ℤₚ`ᵉ ofᵉ [integersᵉ moduloᵉ `p`](elementary-number-theory.modular-arithmetic.mdᵉ)
(i.e.ᵉ whetherᵉ orᵉ notᵉ itᵉ isᵉ aᵉ quadraticᵉ residue).ᵉ Specifically,ᵉ let `pᵉ : Prime-ℕ`ᵉ
beᵉ aᵉ [primeᵉ number](elementary-number-theory.prime-numbers.mdᵉ) andᵉ `aᵉ : ℤ`ᵉ beᵉ anᵉ
integer.ᵉ Ifᵉ `a`ᵉ isᵉ aᵉ squareᵉ in `ℤₚ`ᵉ thenᵉ `legendre(p,aᵉ) = 1`.ᵉ Similarlyᵉ ifᵉ `a`ᵉ
isᵉ notᵉ aᵉ squareᵉ in `ℤₚ`ᵉ thenᵉ `legendre(p,aᵉ) = -1`.ᵉ Finallyᵉ ifᵉ `a`ᵉ isᵉ congruentᵉ
to `0`ᵉ in `ℤₚ`ᵉ thenᵉ `legendre(p,aᵉ) = 0`.ᵉ

## Definition

```agda
int-is-square-ℤ-Modᵉ :
  {pᵉ : ℕᵉ} {kᵉ : ℤ-Modᵉ pᵉ} →
  is-decidableᵉ (is-zero-ℤ-Modᵉ pᵉ kᵉ) →
  is-decidableᵉ (is-square-ℤ-Modᵉ pᵉ kᵉ) →
  ℤᵉ
int-is-square-ℤ-Modᵉ (inlᵉ _) _ = zero-ℤᵉ
int-is-square-ℤ-Modᵉ (inrᵉ _) (inlᵉ _) = one-ℤᵉ
int-is-square-ℤ-Modᵉ (inrᵉ _) (inrᵉ _) = neg-one-ℤᵉ

legendre-symbol-ℤ-Modᵉ : (pᵉ : Prime-ℕᵉ) → ℤ-Modᵉ (nat-Prime-ℕᵉ pᵉ) → ℤᵉ
legendre-symbol-ℤ-Modᵉ (pᵉ ,ᵉ _) kᵉ =
  int-is-square-ℤ-Modᵉ
    ( has-decidable-equality-ℤ-Modᵉ pᵉ kᵉ (zero-ℤ-Modᵉ pᵉ))
    ( is-decidable-is-square-ℤ-Modᵉ pᵉ kᵉ)

legendre-symbolᵉ : Prime-ℕᵉ → ℤᵉ → ℤᵉ
legendre-symbolᵉ pᵉ aᵉ = legendre-symbol-ℤ-Modᵉ pᵉ (mod-ℤᵉ (nat-Prime-ℕᵉ pᵉ) aᵉ)

is-periodic-legendre-symbolᵉ :
  (pᵉ : Prime-ℕᵉ) (aᵉ bᵉ : ℤᵉ) →
  mod-ℤᵉ (nat-Prime-ℕᵉ pᵉ) aᵉ ＝ᵉ mod-ℤᵉ (nat-Prime-ℕᵉ pᵉ) bᵉ →
  legendre-symbolᵉ pᵉ aᵉ ＝ᵉ legendre-symbolᵉ pᵉ bᵉ
is-periodic-legendre-symbolᵉ pᵉ _ _ Hᵉ = apᵉ (legendre-symbol-ℤ-Modᵉ pᵉ) Hᵉ
```