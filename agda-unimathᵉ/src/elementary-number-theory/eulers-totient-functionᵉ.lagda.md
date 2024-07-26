# Euler's totient function

```agda
{-# OPTIONSᵉ --allow-unsolved-metasᵉ #-}

module elementary-number-theory.eulers-totient-functionᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.relatively-prime-natural-numbersᵉ

open import univalent-combinatorics.decidable-subtypesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

**Euler'sᵉ totientᵉ function**ᵉ `φᵉ : ℕᵉ → ℕ`ᵉ isᵉ theᵉ functionᵉ thatᵉ mapsᵉ aᵉ
[naturalᵉ number](elementary-number-theory.natural-numbers.mdᵉ) `n`ᵉ to theᵉ numberᵉ
ofᵉ
[multiplicativeᵉ unitsᵉ moduloᵉ `n`](elementary-number-theory.multiplicative-units-standard-cyclic-rings.md).ᵉ
Inᵉ otherᵉ words,ᵉ theᵉ numberᵉ `φᵉ n`ᵉ isᵉ theᵉ cardinalityᵉ ofᵉ theᵉ
[groupᵉ ofᵉ units](ring-theory.groups-of-units-rings.mdᵉ) ofᵉ theᵉ
[ring](ring-theory.rings.mdᵉ) `ℤ-Modᵉ n`.ᵉ

Alternatively,ᵉ Euler'sᵉ totientᵉ functionᵉ canᵉ beᵉ definedᵉ asᵉ theᵉ functionᵉ `ℕᵉ → ℕ`ᵉ
thatᵉ returnsᵉ forᵉ eachᵉ `n`ᵉ theᵉ numberᵉ ofᵉ `xᵉ <ᵉ n`ᵉ thatᵉ areᵉ
[relativelyᵉ prime](elementary-number-theory.relatively-prime-natural-numbers.md).ᵉ
Theseᵉ twoᵉ definitionsᵉ ofᵉ Euler'sᵉ totientᵉ functionᵉ agreeᵉ onᵉ theᵉ _positiveᵉ_
naturalᵉ numbers.ᵉ However,ᵉ thereᵉ areᵉ twoᵉ multiplicativeᵉ unitsᵉ in theᵉ
[ringᵉ `ℤ`](elementary-number-theory.ring-of-integers.mdᵉ) ofᵉ
[integers](elementary-number-theory.integers.md),ᵉ whileᵉ thereᵉ areᵉ noᵉ naturalᵉ
numbersᵉ `xᵉ <ᵉ 0`ᵉ thatᵉ areᵉ relativelyᵉ primeᵉ to `0`.ᵉ

Ourᵉ reasonᵉ forᵉ preferringᵉ theᵉ firstᵉ definitionᵉ overᵉ theᵉ secondᵉ definitionᵉ isᵉ
thatᵉ theᵉ usualᵉ propertiesᵉ ofᵉ Euler'sᵉ totientᵉ function,ᵉ suchᵉ asᵉ multiplicativity,ᵉ
extendᵉ naturallyᵉ to theᵉ firstᵉ definition.ᵉ

## Definitions

### The definition of Euler's totient function using relatively prime natural numbers

```agda
eulers-totient-function-relatively-primeᵉ : ℕᵉ → ℕᵉ
eulers-totient-function-relatively-primeᵉ nᵉ =
  number-of-elements-subset-𝔽ᵉ
    ( Fin-𝔽ᵉ nᵉ)
    ( λ xᵉ → is-relatively-prime-ℕ-Decidable-Propᵉ (nat-Finᵉ nᵉ xᵉ) nᵉ)
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}