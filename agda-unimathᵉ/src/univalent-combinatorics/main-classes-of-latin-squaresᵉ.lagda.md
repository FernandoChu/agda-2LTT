# The groupoid of main classes of Latin squares

```agda
module univalent-combinatorics.main-classes-of-latin-squaresᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.mere-equivalencesᵉ
open import foundation.set-truncationsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.main-classes-of-latin-hypercubesᵉ
open import univalent-combinatorics.pi-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ groupoidᵉ ofᵉ mainᵉ classesᵉ ofᵉ latinᵉ squaresᵉ consistsᵉ ofᵉ unorderedᵉ triplesᵉ ofᵉ
inhabitedᵉ typesᵉ equippedᵉ with aᵉ ternaryᵉ 1-1ᵉ correspondence.ᵉ

## Definition

### Main classes of general latin squares

```agda
Main-Class-Latin-Squaresᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Main-Class-Latin-Squaresᵉ l1ᵉ l2ᵉ = Main-Class-Latin-Hypercubeᵉ l1ᵉ l2ᵉ 2
```

### Main classes of latin squares of fixed finite order

```agda
Main-Class-Latin-Square-of-Orderᵉ : (mᵉ : ℕᵉ) → UUᵉ (lsuc lzero)
Main-Class-Latin-Square-of-Orderᵉ mᵉ =
  Main-Class-Latin-Hypercube-of-Orderᵉ 2 mᵉ
```

## Properties

### The groupoid of main classes of latin squares of fixed order is π-finite

```agda
is-π-finite-Main-Class-Latin-Square-of-Orderᵉ :
  (kᵉ mᵉ : ℕᵉ) → is-π-finiteᵉ kᵉ (Main-Class-Latin-Square-of-Orderᵉ mᵉ)
is-π-finite-Main-Class-Latin-Square-of-Orderᵉ kᵉ mᵉ =
  is-π-finite-Main-Class-Latin-Hypercube-of-Orderᵉ kᵉ 2 mᵉ
```

### The sequence of the number of main classes of latin squares of finite order

Theᵉ followingᵉ sequenceᵉ definesᵉ [A003090](https://oeis.org/A003090ᵉ) in theᵉ OEIS.ᵉ

```agda
number-of-main-classes-of-Latin-squares-of-orderᵉ : ℕᵉ → ℕᵉ
number-of-main-classes-of-Latin-squares-of-orderᵉ =
  number-of-main-classes-of-Latin-hypercubes-of-orderᵉ 2

mere-equiv-number-of-main-classes-of-Latin-squares-of-orderᵉ :
  (mᵉ : ℕᵉ) →
  mere-equivᵉ
    ( Finᵉ (number-of-main-classes-of-Latin-squares-of-orderᵉ mᵉ))
    ( type-trunc-Setᵉ (Main-Class-Latin-Square-of-Orderᵉ mᵉ))
mere-equiv-number-of-main-classes-of-Latin-squares-of-orderᵉ =
  mere-equiv-number-of-main-classes-of-Latin-hypercubes-of-orderᵉ 2
```