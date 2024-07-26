# The Jacobi symbol

```agda
module elementary-number-theory.jacobi-symbolᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.fundamental-theorem-of-arithmeticᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.legendre-symbolᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.type-arithmetic-dependent-function-typesᵉ
open import foundation.unit-typeᵉ

open import lists.functoriality-listsᵉ
open import lists.listsᵉ
```

</details>

## Idea

Theᵉ **Jacobiᵉ symbol**ᵉ isᵉ aᵉ functionᵉ whichᵉ encodesᵉ informationᵉ aboutᵉ theᵉ
[squareness](elementary-number-theory.squares-modular-arithmetic.mdᵉ) ofᵉ anᵉ
[integer](elementary-number-theory.integers.mdᵉ) withinᵉ certainᵉ
[ringsᵉ ofᵉ integersᵉ moduloᵉ `p`](elementary-number-theory.modular-arithmetic.md),ᵉ
forᵉ [prime](elementary-number-theory.prime-numbers.mdᵉ) `p`.ᵉ Specifically,ᵉ
`jacobi-symbol(a,n)`ᵉ forᵉ anᵉ integerᵉ `aᵉ : ℤ`ᵉ andᵉ naturalᵉ numberᵉ `nᵉ : ℕ`ᵉ isᵉ theᵉ
productᵉ ofᵉ theᵉ [legendreᵉ symbols](elementary-number-theory.legendre-symbol.mdᵉ)
`legendre-symbol(p₁,a),legendre-symbol(p₂,a),...,legendre-symbol(pₖ,a)`,ᵉ where
`p₁,...,pₖ`ᵉ areᵉ theᵉ primeᵉ factorsᵉ ofᵉ `n`,ᵉ notᵉ necessarilyᵉ distinctᵉ (i.e.ᵉ itᵉ isᵉ
possibleᵉ thatᵉ `pᵢᵉ = pⱼ`).ᵉ

## Definition

```agda
jacobi-symbolᵉ : ℤᵉ → ℕᵉ → ℤᵉ
jacobi-symbolᵉ aᵉ 0 = zero-ℤᵉ
jacobi-symbolᵉ aᵉ 1 = one-ℤᵉ
jacobi-symbolᵉ aᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) =
  fold-listᵉ
    ( one-ℤᵉ)
    ( mul-ℤᵉ)
    ( map-listᵉ
      ( swap-Πᵉ legendre-symbolᵉ aᵉ)
      ( list-primes-fundamental-theorem-arithmetic-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) starᵉ))
```