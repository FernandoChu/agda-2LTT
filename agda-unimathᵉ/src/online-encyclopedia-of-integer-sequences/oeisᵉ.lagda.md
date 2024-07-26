# Sequences of the online encyclopedia of integer sequences

```agda
module online-encyclopedia-of-integer-sequences.oeisᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.ackermann-functionᵉ
open import elementary-number-theory.cofibonacciᵉ
open import elementary-number-theory.collatz-bijectionᵉ
open import elementary-number-theory.eulers-totient-functionᵉ
open import elementary-number-theory.exponentiation-natural-numbersᵉ
open import elementary-number-theory.factorialsᵉ
open import elementary-number-theory.fibonacci-sequenceᵉ
open import elementary-number-theory.infinitude-of-primesᵉ
open import elementary-number-theory.kolakoski-sequenceᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.pisano-periodsᵉ

open import finite-group-theory.finite-groupsᵉ

open import foundation.function-typesᵉ
```

</details>

## Sequences

### [A000001](https://oeis.org/A000001) The number of groups of order `n`

```agda
A000001ᵉ : ℕᵉ → ℕᵉ
A000001ᵉ = number-of-groups-of-orderᵉ
```

### [A000002](https://oeis.org/A000002) The Kolakoski sequence

```agda
A000002ᵉ : ℕᵉ → ℕᵉ
A000002ᵉ = kolakoskiᵉ
```

### [A000010](https://oeis.org/A000010) Euler's totient function

```agda
A000010ᵉ : ℕᵉ → ℕᵉ
A000010ᵉ = eulers-totient-function-relatively-primeᵉ
```

### [A000040](https://oeis.org/A000040) The prime numbers

```agda
A000040ᵉ : ℕᵉ → ℕᵉ
A000040ᵉ = prime-ℕᵉ
```

### [A000045](https://oeis.org/A000045) The Fibonacci sequence

```agda
A000045ᵉ : ℕᵉ → ℕᵉ
A000045ᵉ = Fibonacci-ℕᵉ
```

### [A000079](https://oeis.org/A000079) Powers of `2`

```agda
A000079ᵉ : ℕᵉ → ℕᵉ
A000079ᵉ = exp-ℕᵉ 2
```

### [A000142](https://oeis.org/A000142) Factorials

```agda
A000142ᵉ : ℕᵉ → ℕᵉ
A000142ᵉ = factorial-ℕᵉ
```

### [A000244](https://oeis.org/A000244) Powers of `3`

```agda
A000244ᵉ : ℕᵉ → ℕᵉ
A000244ᵉ = exp-ℕᵉ 3
```

### [A000720](https://oeis.org/A000720) The prime counting function

```agda
A000720ᵉ : ℕᵉ → ℕᵉ
A000720ᵉ = prime-counting-ℕᵉ
```

### [A001175](https://oeis.org/A001175) Pisano periods

```agda
A001175ᵉ : ℕᵉ → ℕᵉ
A001175ᵉ = pisano-periodᵉ
```

### [A001177](https://oeis.org/A001177) The cofibonacci sequence

```agda
A001177ᵉ : ℕᵉ → ℕᵉ
A001177ᵉ = cofibonacciᵉ
```

### [A001477](https://oeis.org/A001477) The natural numbers

```agda
A001477ᵉ : ℕᵉ → ℕᵉ
A001477ᵉ = idᵉ
```

### [A006369](https://oeis.org/A006369) Collatz' bijection

```agda
A006369ᵉ : ℕᵉ → ℕᵉ
A006369ᵉ = map-collatz-bijectionᵉ
```

### [A046859](https://oeis.org/A046859) The main diagonal of the Ackermann–Péter function

```agda
A046859ᵉ : ℕᵉ → ℕᵉ
A046859ᵉ nᵉ = ackermannᵉ nᵉ nᵉ
```