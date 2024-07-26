# Integer multiples of elements of commutative rings

```agda
module commutative-algebra.integer-multiples-of-elements-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.homomorphisms-commutative-ringsᵉ
open import commutative-algebra.multiples-of-elements-commutative-ringsᵉ

open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-abelian-groupsᵉ

open import ring-theory.integer-multiples-of-elements-ringsᵉ
```

</details>

## Idea

Theᵉ **integerᵉ multipleᵉ operation**ᵉ onᵉ aᵉ
[commutativeᵉ ring](commutative-algebra.commutative-rings.mdᵉ) isᵉ theᵉ mapᵉ
`kᵉ xᵉ ↦ᵉ kx`,ᵉ whichᵉ isᵉ definedᵉ byᵉ
[iteratively](foundation.iterating-automorphisms.mdᵉ) addingᵉ `x`ᵉ with itselfᵉ anᵉ
[integer](elementary-number-theory.integers.mdᵉ) `k`ᵉ times.ᵉ

## Definitions

### Iteratively adding `g`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  iterative-addition-by-element-Commutative-Ringᵉ :
    type-Commutative-Ringᵉ Aᵉ →
    ℤᵉ → type-Commutative-Ringᵉ Aᵉ → type-Commutative-Ringᵉ Aᵉ
  iterative-addition-by-element-Commutative-Ringᵉ =
    iterative-addition-by-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Integer multiples of elements of commutative rings

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  integer-multiple-Commutative-Ringᵉ :
    ℤᵉ → type-Commutative-Ringᵉ Aᵉ → type-Commutative-Ringᵉ Aᵉ
  integer-multiple-Commutative-Ringᵉ =
    integer-multiple-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

## Properties

### Associativity of iterated addition by an element of a commutative ring

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) (aᵉ : type-Commutative-Ringᵉ Aᵉ)
  where

  associative-iterative-addition-by-element-Commutative-Ringᵉ :
    (kᵉ : ℤᵉ) (h1ᵉ h2ᵉ : type-Commutative-Ringᵉ Aᵉ) →
    iterative-addition-by-element-Commutative-Ringᵉ Aᵉ aᵉ kᵉ
      ( add-Commutative-Ringᵉ Aᵉ h1ᵉ h2ᵉ) ＝ᵉ
    add-Commutative-Ringᵉ Aᵉ
      ( iterative-addition-by-element-Commutative-Ringᵉ Aᵉ aᵉ kᵉ h1ᵉ)
      ( h2ᵉ)
  associative-iterative-addition-by-element-Commutative-Ringᵉ =
    associative-iterative-addition-by-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) aᵉ
```

### `integer-multiple-Commutative-Ring A (int-ℕ n) a ＝ multiple-Commutative-Ring A n a`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  integer-multiple-int-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (aᵉ : type-Commutative-Ringᵉ Aᵉ) →
    integer-multiple-Commutative-Ringᵉ Aᵉ (int-ℕᵉ nᵉ) aᵉ ＝ᵉ
    multiple-Commutative-Ringᵉ Aᵉ nᵉ aᵉ
  integer-multiple-int-Commutative-Ringᵉ =
    integer-multiple-int-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  integer-multiple-in-pos-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (aᵉ : type-Commutative-Ringᵉ Aᵉ) →
    integer-multiple-Commutative-Ringᵉ Aᵉ (in-pos-ℤᵉ nᵉ) aᵉ ＝ᵉ
    multiple-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ) aᵉ
  integer-multiple-in-pos-Commutative-Ringᵉ =
    integer-multiple-in-pos-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  integer-multiple-in-neg-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (aᵉ : type-Commutative-Ringᵉ Aᵉ) →
    integer-multiple-Commutative-Ringᵉ Aᵉ (in-neg-ℤᵉ nᵉ) aᵉ ＝ᵉ
    neg-Commutative-Ringᵉ Aᵉ (multiple-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ) aᵉ)
  integer-multiple-in-neg-Commutative-Ringᵉ =
    integer-multiple-in-neg-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### The integer multiple `0x` is `0`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) (aᵉ : type-Commutative-Ringᵉ Aᵉ)
  where

  integer-multiple-zero-Commutative-Ringᵉ :
    integer-multiple-Commutative-Ringᵉ Aᵉ zero-ℤᵉ aᵉ ＝ᵉ zero-Commutative-Ringᵉ Aᵉ
  integer-multiple-zero-Commutative-Ringᵉ =
    integer-multiple-zero-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) aᵉ
```

### `1x ＝ x`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) (aᵉ : type-Commutative-Ringᵉ Aᵉ)
  where

  integer-multiple-one-Commutative-Ringᵉ :
    integer-multiple-Commutative-Ringᵉ Aᵉ one-ℤᵉ aᵉ ＝ᵉ aᵉ
  integer-multiple-one-Commutative-Ringᵉ =
    integer-multiple-one-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) aᵉ
```

### The integer multiple `(-1)x` is the negative of `x`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) (aᵉ : type-Commutative-Ringᵉ Aᵉ)
  where

  integer-multiple-neg-one-Commutative-Ringᵉ :
    integer-multiple-Commutative-Ringᵉ Aᵉ neg-one-ℤᵉ aᵉ ＝ᵉ neg-Commutative-Ringᵉ Aᵉ aᵉ
  integer-multiple-neg-one-Commutative-Ringᵉ =
    integer-multiple-neg-one-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) aᵉ
```

### The integer multiple `(x + y)a` computes to `xa + ya`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) (aᵉ : type-Commutative-Ringᵉ Aᵉ)
  where

  distributive-integer-multiple-add-Commutative-Ringᵉ :
    (xᵉ yᵉ : ℤᵉ) →
    integer-multiple-Commutative-Ringᵉ Aᵉ (xᵉ +ℤᵉ yᵉ) aᵉ ＝ᵉ
    add-Commutative-Ringᵉ Aᵉ
      ( integer-multiple-Commutative-Ringᵉ Aᵉ xᵉ aᵉ)
      ( integer-multiple-Commutative-Ringᵉ Aᵉ yᵉ aᵉ)
  distributive-integer-multiple-add-Commutative-Ringᵉ =
    distributive-integer-multiple-add-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) aᵉ
```

### The integer multiple `(-k)x` is the negative of the integer multiple `kx`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  integer-multiple-neg-Commutative-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    integer-multiple-Commutative-Ringᵉ Aᵉ (neg-ℤᵉ kᵉ) xᵉ ＝ᵉ
    neg-Commutative-Ringᵉ Aᵉ (integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ xᵉ)
  integer-multiple-neg-Commutative-Ringᵉ =
    integer-multiple-neg-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### `(k + 1)x = kx + x` and `(k+1)x = x + kx`

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  integer-multiple-succ-Commutative-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    integer-multiple-Commutative-Ringᵉ Aᵉ (succ-ℤᵉ kᵉ) xᵉ ＝ᵉ
    add-Commutative-Ringᵉ Aᵉ (integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ xᵉ) xᵉ
  integer-multiple-succ-Commutative-Ringᵉ =
    integer-multiple-succ-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  integer-multiple-succ-Commutative-Ring'ᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    integer-multiple-Commutative-Ringᵉ Aᵉ (succ-ℤᵉ kᵉ) xᵉ ＝ᵉ
    add-Commutative-Ringᵉ Aᵉ xᵉ (integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ xᵉ)
  integer-multiple-succ-Commutative-Ring'ᵉ =
    integer-multiple-succ-Ring'ᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### `(k - 1)x = kx - x` and `(k - 1)x = -x + kx`

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  integer-multiple-pred-Commutative-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    integer-multiple-Commutative-Ringᵉ Aᵉ (pred-ℤᵉ kᵉ) xᵉ ＝ᵉ
    right-subtraction-Commutative-Ringᵉ Aᵉ
      ( integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ xᵉ)
      ( xᵉ)
  integer-multiple-pred-Commutative-Ringᵉ =
    integer-multiple-pred-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  integer-multiple-pred-Commutative-Ring'ᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    integer-multiple-Commutative-Ringᵉ Aᵉ (pred-ℤᵉ kᵉ) xᵉ ＝ᵉ
    left-subtraction-Commutative-Ringᵉ Aᵉ
      ( xᵉ)
      ( integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ xᵉ)
  integer-multiple-pred-Commutative-Ring'ᵉ =
    integer-multiple-pred-Ring'ᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### `k0 ＝ 0`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  right-zero-law-integer-multiple-Commutative-Ringᵉ :
    (kᵉ : ℤᵉ) →
    integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ (zero-Commutative-Ringᵉ Aᵉ) ＝ᵉ
    zero-Commutative-Ringᵉ Aᵉ
  right-zero-law-integer-multiple-Commutative-Ringᵉ =
    right-zero-law-integer-multiple-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Integer multiples distribute over the sum of `x` and `y`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  left-distributive-integer-multiple-add-Commutative-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ) →
    integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ (add-Commutative-Ringᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
    add-Commutative-Ringᵉ Aᵉ
      ( integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ xᵉ)
      ( integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ yᵉ)
  left-distributive-integer-multiple-add-Commutative-Ringᵉ =
    left-distributive-integer-multiple-add-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Left and right integer multiple laws for ring multiplication

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  left-integer-multiple-law-mul-Commutative-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ) →
    mul-Commutative-Ringᵉ Aᵉ (integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ xᵉ) yᵉ ＝ᵉ
    integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ (mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ)
  left-integer-multiple-law-mul-Commutative-Ringᵉ =
    left-integer-multiple-law-mul-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  right-integer-multiple-law-mul-Commutative-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ) →
    mul-Commutative-Ringᵉ Aᵉ xᵉ (integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ yᵉ) ＝ᵉ
    integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ (mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ)
  right-integer-multiple-law-mul-Commutative-Ringᵉ =
    right-integer-multiple-law-mul-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### For each integer `k`, the operation of taking `k`-multiples is a group homomorphism

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) (kᵉ : ℤᵉ)
  where

  hom-ab-integer-multiple-Commutative-Ringᵉ :
    hom-Abᵉ (ab-Commutative-Ringᵉ Aᵉ) (ab-Commutative-Ringᵉ Aᵉ)
  hom-ab-integer-multiple-Commutative-Ringᵉ =
    hom-ab-integer-multiple-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) kᵉ
```

### Multiples by products of integers are iterated integer multiples

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  integer-multiple-mul-Commutative-Ringᵉ :
    (kᵉ lᵉ : ℤᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    integer-multiple-Commutative-Ringᵉ Aᵉ (kᵉ *ℤᵉ lᵉ) xᵉ ＝ᵉ
    integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ
      ( integer-multiple-Commutative-Ringᵉ Aᵉ lᵉ xᵉ)
  integer-multiple-mul-Commutative-Ringᵉ =
    integer-multiple-mul-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Commutative ring homomorphisms preserve integer multiples

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Bᵉ : Commutative-Ringᵉ l2ᵉ)
  (fᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ)
  where

  preserves-integer-multiples-hom-Commutative-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    map-hom-Commutative-Ringᵉ Aᵉ Bᵉ fᵉ (integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ xᵉ) ＝ᵉ
    integer-multiple-Commutative-Ringᵉ Bᵉ kᵉ (map-hom-Commutative-Ringᵉ Aᵉ Bᵉ fᵉ xᵉ)
  preserves-integer-multiples-hom-Commutative-Ringᵉ =
    preserves-integer-multiples-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Bᵉ : Commutative-Ringᵉ l2ᵉ)
  (fᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ)
  where

  eq-integer-multiple-hom-Commutative-Ringᵉ :
    (gᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ) (kᵉ : ℤᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    ( map-hom-Commutative-Ringᵉ Aᵉ Bᵉ fᵉ xᵉ ＝ᵉ map-hom-Commutative-Ringᵉ Aᵉ Bᵉ gᵉ xᵉ) →
    map-hom-Commutative-Ringᵉ Aᵉ Bᵉ fᵉ (integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ xᵉ) ＝ᵉ
    map-hom-Commutative-Ringᵉ Aᵉ Bᵉ gᵉ (integer-multiple-Commutative-Ringᵉ Aᵉ kᵉ xᵉ)
  eq-integer-multiple-hom-Commutative-Ringᵉ gᵉ =
    eq-integer-multiple-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)
      ( gᵉ)
```