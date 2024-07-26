# Integer multiples of elements in abelian groups

```agda
module group-theory.integer-multiples-of-elements-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.homomorphisms-abelian-groupsᵉ
open import group-theory.integer-powers-of-elements-groupsᵉ
open import group-theory.multiples-of-elements-abelian-groupsᵉ
```

</details>

## Idea

Theᵉ **integerᵉ multipleᵉ operation**ᵉ onᵉ anᵉ
[abelianᵉ group](group-theory.abelian-groups.mdᵉ) isᵉ theᵉ mapᵉ `kᵉ xᵉ ↦ᵉ kx`,ᵉ whichᵉ isᵉ
definedᵉ byᵉ [iteratively](foundation.iterating-automorphisms.mdᵉ) addingᵉ `x`ᵉ with
itselfᵉ anᵉ [integer](elementary-number-theory.integers.mdᵉ) `k`ᵉ times.ᵉ

## Definitions

### Iteratively adding `g`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  iterative-addition-by-element-Abᵉ :
    type-Abᵉ Aᵉ → ℤᵉ → type-Abᵉ Aᵉ → type-Abᵉ Aᵉ
  iterative-addition-by-element-Abᵉ =
    iterative-multiplication-by-element-Groupᵉ (group-Abᵉ Aᵉ)
```

### Integer multiples of abelian group elements

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  integer-multiple-Abᵉ : ℤᵉ → type-Abᵉ Aᵉ → type-Abᵉ Aᵉ
  integer-multiple-Abᵉ = integer-power-Groupᵉ (group-Abᵉ Aᵉ)
```

### The predicate of being an integer multiple of an element in an abelian group

Weᵉ sayᵉ thatᵉ anᵉ elementᵉ `y`ᵉ **isᵉ anᵉ integerᵉ multiple**ᵉ ofᵉ anᵉ elementᵉ `x`ᵉ ifᵉ thereᵉ
[exists](foundation.existential-quantification.mdᵉ) anᵉ integerᵉ `k`ᵉ suchᵉ thatᵉ
`kxᵉ ＝ᵉ y`.ᵉ

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  is-integer-multiple-of-element-prop-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) → Propᵉ lᵉ
  is-integer-multiple-of-element-prop-Abᵉ =
    is-integer-power-of-element-prop-Groupᵉ (group-Abᵉ Aᵉ)

  is-integer-multiple-of-element-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) → UUᵉ lᵉ
  is-integer-multiple-of-element-Abᵉ =
    is-integer-power-of-element-Groupᵉ (group-Abᵉ Aᵉ)

  is-prop-is-integer-multiple-of-element-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    is-propᵉ (is-integer-multiple-of-element-Abᵉ xᵉ yᵉ)
  is-prop-is-integer-multiple-of-element-Abᵉ =
    is-prop-is-integer-power-of-element-Groupᵉ (group-Abᵉ Aᵉ)
```

## Properties

### Associativity of iterated addition by a group element

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ) (aᵉ : type-Abᵉ Aᵉ)
  where

  associative-iterative-addition-by-element-Abᵉ :
    (kᵉ : ℤᵉ) (h1ᵉ h2ᵉ : type-Abᵉ Aᵉ) →
    iterative-addition-by-element-Abᵉ Aᵉ aᵉ kᵉ (add-Abᵉ Aᵉ h1ᵉ h2ᵉ) ＝ᵉ
    add-Abᵉ Aᵉ (iterative-addition-by-element-Abᵉ Aᵉ aᵉ kᵉ h1ᵉ) h2ᵉ
  associative-iterative-addition-by-element-Abᵉ =
    associative-iterative-multiplication-by-element-Groupᵉ (group-Abᵉ Aᵉ) aᵉ
```

### `integer-multiple-Ab A (int-ℕ n) a ＝ multiple-Ab A n a`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  integer-multiple-int-Abᵉ :
    (nᵉ : ℕᵉ) (aᵉ : type-Abᵉ Aᵉ) →
    integer-multiple-Abᵉ Aᵉ (int-ℕᵉ nᵉ) aᵉ ＝ᵉ multiple-Abᵉ Aᵉ nᵉ aᵉ
  integer-multiple-int-Abᵉ = integer-power-int-Groupᵉ (group-Abᵉ Aᵉ)

  integer-multiple-in-pos-Abᵉ :
    (nᵉ : ℕᵉ) (aᵉ : type-Abᵉ Aᵉ) →
    integer-multiple-Abᵉ Aᵉ (in-pos-ℤᵉ nᵉ) aᵉ ＝ᵉ
    multiple-Abᵉ Aᵉ (succ-ℕᵉ nᵉ) aᵉ
  integer-multiple-in-pos-Abᵉ =
    integer-power-in-pos-Groupᵉ (group-Abᵉ Aᵉ)

  integer-multiple-in-neg-Abᵉ :
    (nᵉ : ℕᵉ) (aᵉ : type-Abᵉ Aᵉ) →
    integer-multiple-Abᵉ Aᵉ (in-neg-ℤᵉ nᵉ) aᵉ ＝ᵉ
    neg-Abᵉ Aᵉ (multiple-Abᵉ Aᵉ (succ-ℕᵉ nᵉ) aᵉ)
  integer-multiple-in-neg-Abᵉ =
    integer-power-in-neg-Groupᵉ (group-Abᵉ Aᵉ)
```

### The integer multiple `0x` is `0`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ) (aᵉ : type-Abᵉ Aᵉ)
  where

  integer-multiple-zero-Abᵉ :
    integer-multiple-Abᵉ Aᵉ zero-ℤᵉ aᵉ ＝ᵉ zero-Abᵉ Aᵉ
  integer-multiple-zero-Abᵉ =
    integer-power-zero-Groupᵉ (group-Abᵉ Aᵉ) aᵉ
```

### `1x ＝ x`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ) (aᵉ : type-Abᵉ Aᵉ)
  where

  integer-multiple-one-Abᵉ :
    integer-multiple-Abᵉ Aᵉ one-ℤᵉ aᵉ ＝ᵉ aᵉ
  integer-multiple-one-Abᵉ =
    integer-power-one-Groupᵉ (group-Abᵉ Aᵉ) aᵉ
```

### The integer multiple `(-1)x` is the negative of `x`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ) (aᵉ : type-Abᵉ Aᵉ)
  where

  integer-multiple-neg-one-Abᵉ :
    integer-multiple-Abᵉ Aᵉ neg-one-ℤᵉ aᵉ ＝ᵉ neg-Abᵉ Aᵉ aᵉ
  integer-multiple-neg-one-Abᵉ =
    integer-power-neg-one-Groupᵉ (group-Abᵉ Aᵉ) aᵉ
```

### The integer multiple `(x + y)a` computes to `xa + ya`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ) (aᵉ : type-Abᵉ Aᵉ)
  where

  distributive-integer-multiple-add-Abᵉ :
    (xᵉ yᵉ : ℤᵉ) →
    integer-multiple-Abᵉ Aᵉ (xᵉ +ℤᵉ yᵉ) aᵉ ＝ᵉ
    add-Abᵉ Aᵉ
      ( integer-multiple-Abᵉ Aᵉ xᵉ aᵉ)
      ( integer-multiple-Abᵉ Aᵉ yᵉ aᵉ)
  distributive-integer-multiple-add-Abᵉ =
    distributive-integer-power-add-Groupᵉ (group-Abᵉ Aᵉ) aᵉ
```

### The integer multiple `(-k)x` is the negative of the integer multiple `kx`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  integer-multiple-neg-Abᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Abᵉ Aᵉ) →
    integer-multiple-Abᵉ Aᵉ (neg-ℤᵉ kᵉ) xᵉ ＝ᵉ neg-Abᵉ Aᵉ (integer-multiple-Abᵉ Aᵉ kᵉ xᵉ)
  integer-multiple-neg-Abᵉ =
    integer-power-neg-Groupᵉ (group-Abᵉ Aᵉ)
```

### `(k + 1)x = kx + x` and `(k+1)x = x + kx`

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ)
  where

  integer-multiple-succ-Abᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Abᵉ Aᵉ) →
    integer-multiple-Abᵉ Aᵉ (succ-ℤᵉ kᵉ) xᵉ ＝ᵉ
    add-Abᵉ Aᵉ (integer-multiple-Abᵉ Aᵉ kᵉ xᵉ) xᵉ
  integer-multiple-succ-Abᵉ =
    integer-power-succ-Groupᵉ (group-Abᵉ Aᵉ)

  integer-multiple-succ-Ab'ᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Abᵉ Aᵉ) →
    integer-multiple-Abᵉ Aᵉ (succ-ℤᵉ kᵉ) xᵉ ＝ᵉ
    add-Abᵉ Aᵉ xᵉ (integer-multiple-Abᵉ Aᵉ kᵉ xᵉ)
  integer-multiple-succ-Ab'ᵉ =
    integer-power-succ-Group'ᵉ (group-Abᵉ Aᵉ)
```

### `(k - 1)x = kx - x` and `(k - 1)x = -x + kx`

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ)
  where

  integer-multiple-pred-Abᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Abᵉ Aᵉ) →
    integer-multiple-Abᵉ Aᵉ (pred-ℤᵉ kᵉ) xᵉ ＝ᵉ
    right-subtraction-Abᵉ Aᵉ (integer-multiple-Abᵉ Aᵉ kᵉ xᵉ) xᵉ
  integer-multiple-pred-Abᵉ =
    integer-power-pred-Groupᵉ (group-Abᵉ Aᵉ)

  integer-multiple-pred-Ab'ᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Abᵉ Aᵉ) →
    integer-multiple-Abᵉ Aᵉ (pred-ℤᵉ kᵉ) xᵉ ＝ᵉ
    left-subtraction-Abᵉ Aᵉ xᵉ (integer-multiple-Abᵉ Aᵉ kᵉ xᵉ)
  integer-multiple-pred-Ab'ᵉ =
    integer-power-pred-Group'ᵉ (group-Abᵉ Aᵉ)
```

### `k0 ＝ 0`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  right-zero-law-integer-multiple-Abᵉ :
    (kᵉ : ℤᵉ) → integer-multiple-Abᵉ Aᵉ kᵉ (zero-Abᵉ Aᵉ) ＝ᵉ zero-Abᵉ Aᵉ
  right-zero-law-integer-multiple-Abᵉ =
    integer-power-unit-Groupᵉ (group-Abᵉ Aᵉ)
```

### Integer multiples distribute over the sum of `x` and `y`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  left-distributive-integer-multiple-add-Abᵉ :
    (kᵉ : ℤᵉ) (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    integer-multiple-Abᵉ Aᵉ kᵉ (add-Abᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
    add-Abᵉ Aᵉ (integer-multiple-Abᵉ Aᵉ kᵉ xᵉ) (integer-multiple-Abᵉ Aᵉ kᵉ yᵉ)
  left-distributive-integer-multiple-add-Abᵉ kᵉ xᵉ yᵉ =
    distributive-integer-power-mul-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( kᵉ)
      ( xᵉ)
      ( yᵉ)
      ( commutative-add-Abᵉ Aᵉ xᵉ yᵉ)
```

### For each integer `k`, the operation of taking `k`-multiples is a group homomorphism

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ) (kᵉ : ℤᵉ)
  where

  hom-integer-multiple-Abᵉ : hom-Abᵉ Aᵉ Aᵉ
  pr1ᵉ hom-integer-multiple-Abᵉ =
    integer-multiple-Abᵉ Aᵉ kᵉ
  pr2ᵉ hom-integer-multiple-Abᵉ {xᵉ} {yᵉ} =
    left-distributive-integer-multiple-add-Abᵉ Aᵉ kᵉ xᵉ yᵉ
```

### Multiples by products of integers are iterated integer multiples

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  integer-multiple-mul-Abᵉ :
    (kᵉ lᵉ : ℤᵉ) (xᵉ : type-Abᵉ Aᵉ) →
    integer-multiple-Abᵉ Aᵉ (kᵉ *ℤᵉ lᵉ) xᵉ ＝ᵉ
    integer-multiple-Abᵉ Aᵉ kᵉ (integer-multiple-Abᵉ Aᵉ lᵉ xᵉ)
  integer-multiple-mul-Abᵉ kᵉ lᵉ xᵉ =
    ( apᵉ (λ uᵉ → integer-multiple-Abᵉ Aᵉ uᵉ xᵉ) (commutative-mul-ℤᵉ kᵉ lᵉ)) ∙ᵉ
    ( integer-power-mul-Groupᵉ (group-Abᵉ Aᵉ) lᵉ kᵉ xᵉ)

  swap-integer-multiple-Abᵉ :
    (kᵉ lᵉ : ℤᵉ) (xᵉ : type-Abᵉ Aᵉ) →
    integer-multiple-Abᵉ Aᵉ kᵉ (integer-multiple-Abᵉ Aᵉ lᵉ xᵉ) ＝ᵉ
    integer-multiple-Abᵉ Aᵉ lᵉ (integer-multiple-Abᵉ Aᵉ kᵉ xᵉ)
  swap-integer-multiple-Abᵉ kᵉ lᵉ xᵉ =
    ( invᵉ (integer-multiple-mul-Abᵉ kᵉ lᵉ xᵉ)) ∙ᵉ
    ( apᵉ (λ tᵉ → integer-multiple-Abᵉ Aᵉ tᵉ xᵉ) (commutative-mul-ℤᵉ kᵉ lᵉ)) ∙ᵉ
    ( integer-multiple-mul-Abᵉ lᵉ kᵉ xᵉ)
```

### Abelian group homomorphisms preserve integer multiples

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ) (fᵉ : hom-Abᵉ Aᵉ Bᵉ)
  where

  preserves-integer-multiples-hom-Abᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Abᵉ Aᵉ) →
    map-hom-Abᵉ Aᵉ Bᵉ fᵉ (integer-multiple-Abᵉ Aᵉ kᵉ xᵉ) ＝ᵉ
    integer-multiple-Abᵉ Bᵉ kᵉ (map-hom-Abᵉ Aᵉ Bᵉ fᵉ xᵉ)
  preserves-integer-multiples-hom-Abᵉ =
    preserves-integer-powers-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ) (fᵉ : hom-Abᵉ Aᵉ Bᵉ)
  where

  eq-integer-multiple-hom-Abᵉ :
    (gᵉ : hom-Abᵉ Aᵉ Bᵉ) (kᵉ : ℤᵉ) (xᵉ : type-Abᵉ Aᵉ) →
    ( map-hom-Abᵉ Aᵉ Bᵉ fᵉ xᵉ ＝ᵉ map-hom-Abᵉ Aᵉ Bᵉ gᵉ xᵉ) →
    ( map-hom-Abᵉ Aᵉ Bᵉ fᵉ (integer-multiple-Abᵉ Aᵉ kᵉ xᵉ) ＝ᵉ
      map-hom-Abᵉ Aᵉ Bᵉ gᵉ (integer-multiple-Abᵉ Aᵉ kᵉ xᵉ))
  eq-integer-multiple-hom-Abᵉ =
    eq-integer-power-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ
```