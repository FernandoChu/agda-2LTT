# Integer multiples of elements of rings

```agda
module ring-theory.integer-multiples-of-elements-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-abelian-groupsᵉ
open import group-theory.integer-multiples-of-elements-abelian-groupsᵉ

open import ring-theory.commuting-elements-ringsᵉ
open import ring-theory.homomorphisms-ringsᵉ
open import ring-theory.multiples-of-elements-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Theᵉ **integerᵉ multipleᵉ operation**ᵉ onᵉ aᵉ [ring](ring-theory.rings.mdᵉ) isᵉ theᵉ mapᵉ
`kᵉ xᵉ ↦ᵉ kx`,ᵉ whichᵉ isᵉ definedᵉ byᵉ
[iteratively](foundation.iterating-automorphisms.mdᵉ) addingᵉ `x`ᵉ with itselfᵉ anᵉ
[integer](elementary-number-theory.integers.mdᵉ) `k`ᵉ times.ᵉ

## Definitions

### Iteratively adding `g`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  iterative-addition-by-element-Ringᵉ :
    type-Ringᵉ Rᵉ → ℤᵉ → type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ
  iterative-addition-by-element-Ringᵉ =
    iterative-addition-by-element-Abᵉ (ab-Ringᵉ Rᵉ)
```

### Integer multiples of elements of rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  integer-multiple-Ringᵉ : ℤᵉ → type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ
  integer-multiple-Ringᵉ = integer-multiple-Abᵉ (ab-Ringᵉ Rᵉ)
```

### The predicate of being a natural multiple of an element in an ring

Weᵉ sayᵉ thatᵉ anᵉ elementᵉ `y`ᵉ **isᵉ anᵉ integerᵉ multiple**ᵉ ofᵉ anᵉ elementᵉ `x`ᵉ ifᵉ thereᵉ
[exists](foundation.existential-quantification.mdᵉ) anᵉ integerᵉ `k`ᵉ suchᵉ thatᵉ
`kxᵉ ＝ᵉ y`.ᵉ

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-integer-multiple-of-element-prop-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) → Propᵉ lᵉ
  is-integer-multiple-of-element-prop-Ringᵉ =
    is-integer-multiple-of-element-prop-Abᵉ (ab-Ringᵉ Rᵉ)

  is-integer-multiple-of-element-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) → UUᵉ lᵉ
  is-integer-multiple-of-element-Ringᵉ =
    is-integer-multiple-of-element-Abᵉ (ab-Ringᵉ Rᵉ)

  is-prop-is-integer-multiple-of-element-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    is-propᵉ (is-integer-multiple-of-element-Ringᵉ xᵉ yᵉ)
  is-prop-is-integer-multiple-of-element-Ringᵉ =
    is-prop-is-integer-multiple-of-element-Abᵉ (ab-Ringᵉ Rᵉ)
```

## Properties

### Associativity of iterated addition by a ring element

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (aᵉ : type-Ringᵉ Rᵉ)
  where

  associative-iterative-addition-by-element-Ringᵉ :
    (kᵉ : ℤᵉ) (h1ᵉ h2ᵉ : type-Ringᵉ Rᵉ) →
    iterative-addition-by-element-Ringᵉ Rᵉ aᵉ kᵉ (add-Ringᵉ Rᵉ h1ᵉ h2ᵉ) ＝ᵉ
    add-Ringᵉ Rᵉ (iterative-addition-by-element-Ringᵉ Rᵉ aᵉ kᵉ h1ᵉ) h2ᵉ
  associative-iterative-addition-by-element-Ringᵉ =
    associative-iterative-addition-by-element-Abᵉ (ab-Ringᵉ Rᵉ) aᵉ
```

### `integer-multiple-Ring R (int-ℕ n) a ＝ multiple-Ring R n a`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  integer-multiple-int-Ringᵉ :
    (nᵉ : ℕᵉ) (aᵉ : type-Ringᵉ Rᵉ) →
    integer-multiple-Ringᵉ Rᵉ (int-ℕᵉ nᵉ) aᵉ ＝ᵉ multiple-Ringᵉ Rᵉ nᵉ aᵉ
  integer-multiple-int-Ringᵉ = integer-multiple-int-Abᵉ (ab-Ringᵉ Rᵉ)

  integer-multiple-in-pos-Ringᵉ :
    (nᵉ : ℕᵉ) (aᵉ : type-Ringᵉ Rᵉ) →
    integer-multiple-Ringᵉ Rᵉ (in-pos-ℤᵉ nᵉ) aᵉ ＝ᵉ
    multiple-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ) aᵉ
  integer-multiple-in-pos-Ringᵉ =
    integer-multiple-in-pos-Abᵉ (ab-Ringᵉ Rᵉ)

  integer-multiple-in-neg-Ringᵉ :
    (nᵉ : ℕᵉ) (aᵉ : type-Ringᵉ Rᵉ) →
    integer-multiple-Ringᵉ Rᵉ (in-neg-ℤᵉ nᵉ) aᵉ ＝ᵉ
    neg-Ringᵉ Rᵉ (multiple-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ) aᵉ)
  integer-multiple-in-neg-Ringᵉ =
    integer-multiple-in-neg-Abᵉ (ab-Ringᵉ Rᵉ)
```

### The integer multiple `0x` is `0`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (aᵉ : type-Ringᵉ Rᵉ)
  where

  integer-multiple-zero-Ringᵉ :
    integer-multiple-Ringᵉ Rᵉ zero-ℤᵉ aᵉ ＝ᵉ zero-Ringᵉ Rᵉ
  integer-multiple-zero-Ringᵉ =
    integer-multiple-zero-Abᵉ (ab-Ringᵉ Rᵉ) aᵉ
```

### `1x ＝ x`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (aᵉ : type-Ringᵉ Rᵉ)
  where

  integer-multiple-one-Ringᵉ :
    integer-multiple-Ringᵉ Rᵉ one-ℤᵉ aᵉ ＝ᵉ aᵉ
  integer-multiple-one-Ringᵉ =
    integer-multiple-one-Abᵉ (ab-Ringᵉ Rᵉ) aᵉ
```

### The integer multiple `(-1)x` is the negative of `x`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (aᵉ : type-Ringᵉ Rᵉ)
  where

  integer-multiple-neg-one-Ringᵉ :
    integer-multiple-Ringᵉ Rᵉ neg-one-ℤᵉ aᵉ ＝ᵉ neg-Ringᵉ Rᵉ aᵉ
  integer-multiple-neg-one-Ringᵉ =
    integer-multiple-neg-one-Abᵉ (ab-Ringᵉ Rᵉ) aᵉ
```

### The integer multiple `(x + y)a` computes to `xa + ya`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (aᵉ : type-Ringᵉ Rᵉ)
  where

  distributive-integer-multiple-add-Ringᵉ :
    (xᵉ yᵉ : ℤᵉ) →
    integer-multiple-Ringᵉ Rᵉ (xᵉ +ℤᵉ yᵉ) aᵉ ＝ᵉ
    add-Ringᵉ Rᵉ
      ( integer-multiple-Ringᵉ Rᵉ xᵉ aᵉ)
      ( integer-multiple-Ringᵉ Rᵉ yᵉ aᵉ)
  distributive-integer-multiple-add-Ringᵉ =
    distributive-integer-multiple-add-Abᵉ (ab-Ringᵉ Rᵉ) aᵉ
```

### The integer multiple `(-k)x` is the negative of the integer multiple `kx`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  integer-multiple-neg-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    integer-multiple-Ringᵉ Rᵉ (neg-ℤᵉ kᵉ) xᵉ ＝ᵉ
    neg-Ringᵉ Rᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ xᵉ)
  integer-multiple-neg-Ringᵉ =
    integer-multiple-neg-Abᵉ (ab-Ringᵉ Rᵉ)
```

### `(k + 1)x = kx + x` and `(k + 1)x = x + kx`

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  integer-multiple-succ-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    integer-multiple-Ringᵉ Rᵉ (succ-ℤᵉ kᵉ) xᵉ ＝ᵉ
    add-Ringᵉ Rᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ xᵉ) xᵉ
  integer-multiple-succ-Ringᵉ =
    integer-multiple-succ-Abᵉ (ab-Ringᵉ Rᵉ)

  integer-multiple-succ-Ring'ᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    integer-multiple-Ringᵉ Rᵉ (succ-ℤᵉ kᵉ) xᵉ ＝ᵉ
    add-Ringᵉ Rᵉ xᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ xᵉ)
  integer-multiple-succ-Ring'ᵉ =
    integer-multiple-succ-Ab'ᵉ (ab-Ringᵉ Rᵉ)
```

### `(k - 1)x = kx - x` and `(k - 1)x = -x + kx`

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  integer-multiple-pred-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    integer-multiple-Ringᵉ Rᵉ (pred-ℤᵉ kᵉ) xᵉ ＝ᵉ
    right-subtraction-Ringᵉ Rᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ xᵉ) xᵉ
  integer-multiple-pred-Ringᵉ =
    integer-multiple-pred-Abᵉ (ab-Ringᵉ Rᵉ)

  integer-multiple-pred-Ring'ᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    integer-multiple-Ringᵉ Rᵉ (pred-ℤᵉ kᵉ) xᵉ ＝ᵉ
    left-subtraction-Ringᵉ Rᵉ xᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ xᵉ)
  integer-multiple-pred-Ring'ᵉ =
    integer-multiple-pred-Ab'ᵉ (ab-Ringᵉ Rᵉ)
```

### `k0 ＝ 0`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  right-zero-law-integer-multiple-Ringᵉ :
    (kᵉ : ℤᵉ) → integer-multiple-Ringᵉ Rᵉ kᵉ (zero-Ringᵉ Rᵉ) ＝ᵉ zero-Ringᵉ Rᵉ
  right-zero-law-integer-multiple-Ringᵉ =
    right-zero-law-integer-multiple-Abᵉ (ab-Ringᵉ Rᵉ)
```

### Integer multiples distribute over the sum of `x` and `y`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  left-distributive-integer-multiple-add-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    integer-multiple-Ringᵉ Rᵉ kᵉ (add-Ringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
    add-Ringᵉ Rᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ xᵉ) (integer-multiple-Ringᵉ Rᵉ kᵉ yᵉ)
  left-distributive-integer-multiple-add-Ringᵉ =
    left-distributive-integer-multiple-add-Abᵉ (ab-Ringᵉ Rᵉ)
```

### Left and right integer multiple laws for ring multiplication

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  left-integer-multiple-law-mul-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ xᵉ) yᵉ ＝ᵉ
    integer-multiple-Ringᵉ Rᵉ kᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)
  left-integer-multiple-law-mul-Ringᵉ (inlᵉ zero-ℕᵉ) xᵉ yᵉ =
    ( apᵉ (mul-Ring'ᵉ Rᵉ yᵉ) (integer-multiple-neg-one-Ringᵉ Rᵉ xᵉ)) ∙ᵉ
    ( ( left-negative-law-mul-Ringᵉ Rᵉ xᵉ yᵉ) ∙ᵉ
      ( invᵉ (integer-multiple-neg-one-Ringᵉ Rᵉ _)))
  left-integer-multiple-law-mul-Ringᵉ (inlᵉ (succ-ℕᵉ kᵉ)) xᵉ yᵉ =
    ( apᵉ (mul-Ring'ᵉ Rᵉ yᵉ) (integer-multiple-pred-Ringᵉ Rᵉ (inlᵉ kᵉ) xᵉ)) ∙ᵉ
    ( ( right-distributive-mul-right-subtraction-Ringᵉ Rᵉ _ _ _) ∙ᵉ
      ( ( apᵉ
          ( λ uᵉ → right-subtraction-Ringᵉ Rᵉ uᵉ _)
          ( left-integer-multiple-law-mul-Ringᵉ (inlᵉ kᵉ) _ _)) ∙ᵉ
        ( invᵉ (integer-multiple-pred-Ringᵉ Rᵉ (inlᵉ kᵉ) _))))
  left-integer-multiple-law-mul-Ringᵉ (inrᵉ (inlᵉ _)) xᵉ yᵉ =
    ( apᵉ (mul-Ring'ᵉ Rᵉ yᵉ) (integer-multiple-zero-Ringᵉ Rᵉ xᵉ)) ∙ᵉ
    ( left-zero-law-mul-Ringᵉ Rᵉ yᵉ)
  left-integer-multiple-law-mul-Ringᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) xᵉ yᵉ =
    ( apᵉ (mul-Ring'ᵉ Rᵉ yᵉ) (integer-multiple-one-Ringᵉ Rᵉ xᵉ)) ∙ᵉ
    ( invᵉ (integer-multiple-one-Ringᵉ Rᵉ _))
  left-integer-multiple-law-mul-Ringᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ))) xᵉ yᵉ =
    ( apᵉ (mul-Ring'ᵉ Rᵉ yᵉ) (integer-multiple-succ-Ringᵉ Rᵉ (inrᵉ (inrᵉ kᵉ)) xᵉ)) ∙ᵉ
    ( ( right-distributive-mul-add-Ringᵉ Rᵉ _ _ _) ∙ᵉ
      ( ( apᵉ
          ( add-Ring'ᵉ Rᵉ _)
          ( left-integer-multiple-law-mul-Ringᵉ (inrᵉ (inrᵉ kᵉ)) _ _)) ∙ᵉ
        ( invᵉ (integer-multiple-succ-Ringᵉ Rᵉ (inrᵉ (inrᵉ kᵉ)) _))))

  right-integer-multiple-law-mul-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ xᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ yᵉ) ＝ᵉ
    integer-multiple-Ringᵉ Rᵉ kᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)
  right-integer-multiple-law-mul-Ringᵉ (inlᵉ zero-ℕᵉ) xᵉ yᵉ =
    ( apᵉ (mul-Ringᵉ Rᵉ xᵉ) (integer-multiple-neg-one-Ringᵉ Rᵉ yᵉ)) ∙ᵉ
    ( ( right-negative-law-mul-Ringᵉ Rᵉ xᵉ yᵉ) ∙ᵉ
      ( invᵉ (integer-multiple-neg-one-Ringᵉ Rᵉ _)))
  right-integer-multiple-law-mul-Ringᵉ (inlᵉ (succ-ℕᵉ kᵉ)) xᵉ yᵉ =
    ( apᵉ (mul-Ringᵉ Rᵉ xᵉ) (integer-multiple-pred-Ringᵉ Rᵉ (inlᵉ kᵉ) yᵉ)) ∙ᵉ
    ( ( left-distributive-mul-right-subtraction-Ringᵉ Rᵉ _ _ _) ∙ᵉ
      ( ( apᵉ
          ( add-Ring'ᵉ Rᵉ _)
          ( right-integer-multiple-law-mul-Ringᵉ (inlᵉ kᵉ) xᵉ yᵉ)) ∙ᵉ
        ( invᵉ (integer-multiple-pred-Ringᵉ Rᵉ (inlᵉ kᵉ) _))))
  right-integer-multiple-law-mul-Ringᵉ (inrᵉ (inlᵉ _)) xᵉ yᵉ =
    ( apᵉ (mul-Ringᵉ Rᵉ xᵉ) (integer-multiple-zero-Ringᵉ Rᵉ yᵉ)) ∙ᵉ
    ( right-zero-law-mul-Ringᵉ Rᵉ xᵉ)
  right-integer-multiple-law-mul-Ringᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) xᵉ yᵉ =
    ( apᵉ (mul-Ringᵉ Rᵉ xᵉ) (integer-multiple-one-Ringᵉ Rᵉ yᵉ)) ∙ᵉ
    ( invᵉ (integer-multiple-one-Ringᵉ Rᵉ _))
  right-integer-multiple-law-mul-Ringᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ))) xᵉ yᵉ =
    ( apᵉ (mul-Ringᵉ Rᵉ xᵉ) (integer-multiple-succ-Ringᵉ Rᵉ (inrᵉ (inrᵉ kᵉ)) yᵉ)) ∙ᵉ
    ( ( left-distributive-mul-add-Ringᵉ Rᵉ xᵉ _ _) ∙ᵉ
      ( ( apᵉ
          ( add-Ring'ᵉ Rᵉ _)
          ( right-integer-multiple-law-mul-Ringᵉ (inrᵉ (inrᵉ kᵉ)) xᵉ yᵉ)) ∙ᵉ
        ( invᵉ (integer-multiple-succ-Ringᵉ Rᵉ (inrᵉ (inrᵉ kᵉ)) _))))
```

### If `x` and `y` commute, then integer multiples of `x` and `y` commute

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  commute-integer-multiple-Ringᵉ :
    (kᵉ : ℤᵉ) {xᵉ yᵉ : type-Ringᵉ Rᵉ} → commute-Ringᵉ Rᵉ xᵉ yᵉ →
    commute-Ringᵉ Rᵉ xᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ yᵉ)
  commute-integer-multiple-Ringᵉ (inlᵉ zero-ℕᵉ) Hᵉ =
    trᵉ
      ( commute-Ringᵉ Rᵉ _)
      ( invᵉ (integer-multiple-neg-one-Ringᵉ Rᵉ _))
      ( commute-neg-Ringᵉ Rᵉ Hᵉ)
  commute-integer-multiple-Ringᵉ (inlᵉ (succ-ℕᵉ kᵉ)) Hᵉ =
    trᵉ
      ( commute-Ringᵉ Rᵉ _)
      ( invᵉ (integer-multiple-pred-Ringᵉ Rᵉ (inlᵉ kᵉ) _))
      ( commute-right-subtraction-Ringᵉ Rᵉ
        ( commute-integer-multiple-Ringᵉ (inlᵉ kᵉ) Hᵉ)
        ( Hᵉ))
  commute-integer-multiple-Ringᵉ (inrᵉ (inlᵉ _)) {xᵉ} Hᵉ =
    trᵉ
      ( commute-Ringᵉ Rᵉ _)
      ( invᵉ (integer-multiple-zero-Ringᵉ Rᵉ xᵉ))
      ( invᵉ (commute-zero-Ringᵉ Rᵉ _))
  commute-integer-multiple-Ringᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) Hᵉ =
    trᵉ
      ( commute-Ringᵉ Rᵉ _)
      ( invᵉ (integer-multiple-one-Ringᵉ Rᵉ _))
      ( Hᵉ)
  commute-integer-multiple-Ringᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ))) Hᵉ =
    trᵉ
      ( commute-Ringᵉ Rᵉ _)
      ( invᵉ (integer-multiple-succ-Ringᵉ Rᵉ (inrᵉ (inrᵉ kᵉ)) _))
      ( commute-add-Ringᵉ Rᵉ
        ( commute-integer-multiple-Ringᵉ (inrᵉ (inrᵉ kᵉ)) Hᵉ)
        ( Hᵉ))

  commute-integer-multiples-Ringᵉ :
    (kᵉ lᵉ : ℤᵉ) {xᵉ yᵉ : type-Ringᵉ Rᵉ} → commute-Ringᵉ Rᵉ xᵉ yᵉ →
    commute-Ringᵉ Rᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ xᵉ) (integer-multiple-Ringᵉ Rᵉ lᵉ yᵉ)
  commute-integer-multiples-Ringᵉ (inlᵉ zero-ℕᵉ) lᵉ Hᵉ =
    trᵉ
      ( commute-Ring'ᵉ Rᵉ _)
      ( invᵉ (integer-multiple-neg-one-Ringᵉ Rᵉ _))
      ( invᵉ (commute-neg-Ringᵉ Rᵉ (invᵉ (commute-integer-multiple-Ringᵉ lᵉ Hᵉ))))
  commute-integer-multiples-Ringᵉ (inlᵉ (succ-ℕᵉ kᵉ)) lᵉ Hᵉ =
    trᵉ
      ( commute-Ring'ᵉ Rᵉ _)
      ( invᵉ (integer-multiple-pred-Ringᵉ Rᵉ (inlᵉ kᵉ) _))
      ( invᵉ
        ( commute-right-subtraction-Ringᵉ Rᵉ
          ( commute-integer-multiples-Ringᵉ lᵉ (inlᵉ kᵉ) (invᵉ Hᵉ))
          ( invᵉ (commute-integer-multiple-Ringᵉ lᵉ Hᵉ))))
  commute-integer-multiples-Ringᵉ (inrᵉ (inlᵉ _)) lᵉ {xᵉ} Hᵉ =
    trᵉ
      ( commute-Ring'ᵉ Rᵉ _)
      ( invᵉ (integer-multiple-zero-Ringᵉ Rᵉ xᵉ))
      ( commute-zero-Ringᵉ Rᵉ _)
  commute-integer-multiples-Ringᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) lᵉ Hᵉ =
    trᵉ
      ( commute-Ring'ᵉ Rᵉ _)
      ( invᵉ (integer-multiple-one-Ringᵉ Rᵉ _))
      ( commute-integer-multiple-Ringᵉ lᵉ Hᵉ)
  commute-integer-multiples-Ringᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ))) lᵉ Hᵉ =
    trᵉ
      ( commute-Ring'ᵉ Rᵉ _)
      ( invᵉ (integer-multiple-succ-Ringᵉ Rᵉ (inrᵉ (inrᵉ kᵉ)) _))
      ( invᵉ
        ( commute-add-Ringᵉ Rᵉ
          ( commute-integer-multiples-Ringᵉ lᵉ (inrᵉ (inrᵉ kᵉ)) (invᵉ Hᵉ))
          ( invᵉ (commute-integer-multiple-Ringᵉ lᵉ Hᵉ))))

  commute-integer-multiples-diagonal-Ringᵉ :
    (kᵉ lᵉ : ℤᵉ) {xᵉ : type-Ringᵉ Rᵉ} →
    commute-Ringᵉ Rᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ xᵉ) (integer-multiple-Ringᵉ Rᵉ lᵉ xᵉ)
  commute-integer-multiples-diagonal-Ringᵉ kᵉ lᵉ =
    commute-integer-multiples-Ringᵉ kᵉ lᵉ reflᵉ
```

### For each integer `k`, the operation of taking `k`-multiples is a group homomorphism

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (kᵉ : ℤᵉ)
  where

  hom-ab-integer-multiple-Ringᵉ : hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Rᵉ)
  hom-ab-integer-multiple-Ringᵉ = hom-integer-multiple-Abᵉ (ab-Ringᵉ Rᵉ) kᵉ
```

### Multiples by products of integers are iterated integer multiples

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  integer-multiple-mul-Ringᵉ :
    (kᵉ lᵉ : ℤᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    integer-multiple-Ringᵉ Rᵉ (kᵉ *ℤᵉ lᵉ) xᵉ ＝ᵉ
    integer-multiple-Ringᵉ Rᵉ kᵉ (integer-multiple-Ringᵉ Rᵉ lᵉ xᵉ)
  integer-multiple-mul-Ringᵉ =
    integer-multiple-mul-Abᵉ (ab-Ringᵉ Rᵉ)

  swap-integer-multiple-Ringᵉ :
    (kᵉ lᵉ : ℤᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    integer-multiple-Ringᵉ Rᵉ kᵉ (integer-multiple-Ringᵉ Rᵉ lᵉ xᵉ) ＝ᵉ
    integer-multiple-Ringᵉ Rᵉ lᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ xᵉ)
  swap-integer-multiple-Ringᵉ =
    swap-integer-multiple-Abᵉ (ab-Ringᵉ Rᵉ)
```

### Ring homomorphisms preserve integer multiples

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (fᵉ : hom-Ringᵉ Rᵉ Sᵉ)
  where

  preserves-integer-multiples-hom-Ringᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    map-hom-Ringᵉ Rᵉ Sᵉ fᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ xᵉ) ＝ᵉ
    integer-multiple-Ringᵉ Sᵉ kᵉ (map-hom-Ringᵉ Rᵉ Sᵉ fᵉ xᵉ)
  preserves-integer-multiples-hom-Ringᵉ =
    preserves-integer-multiples-hom-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( ab-Ringᵉ Sᵉ)
      ( hom-ab-hom-Ringᵉ Rᵉ Sᵉ fᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (fᵉ : hom-Ringᵉ Rᵉ Sᵉ)
  where

  eq-integer-multiple-hom-Ringᵉ :
    (gᵉ : hom-Ringᵉ Rᵉ Sᵉ) (kᵉ : ℤᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    ( map-hom-Ringᵉ Rᵉ Sᵉ fᵉ xᵉ ＝ᵉ map-hom-Ringᵉ Rᵉ Sᵉ gᵉ xᵉ) →
    map-hom-Ringᵉ Rᵉ Sᵉ fᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ xᵉ) ＝ᵉ
    map-hom-Ringᵉ Rᵉ Sᵉ gᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ xᵉ)
  eq-integer-multiple-hom-Ringᵉ gᵉ =
    eq-integer-multiple-hom-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( ab-Ringᵉ Sᵉ)
      ( hom-ab-hom-Ringᵉ Rᵉ Sᵉ fᵉ)
      ( hom-ab-hom-Ringᵉ Rᵉ Sᵉ gᵉ)
```

### Ring homomorphisms preserve integer multiples of `1`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (fᵉ : hom-Ringᵉ Rᵉ Sᵉ)
  where

  preserves-integer-multiple-one-hom-Ringᵉ :
    (kᵉ : ℤᵉ) →
    map-hom-Ringᵉ Rᵉ Sᵉ fᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ (one-Ringᵉ Rᵉ)) ＝ᵉ
    integer-multiple-Ringᵉ Sᵉ kᵉ (one-Ringᵉ Sᵉ)
  preserves-integer-multiple-one-hom-Ringᵉ kᵉ =
    ( preserves-integer-multiples-hom-Ringᵉ Rᵉ Sᵉ fᵉ kᵉ (one-Ringᵉ Rᵉ)) ∙ᵉ
    ( apᵉ (integer-multiple-Ringᵉ Sᵉ kᵉ) (preserves-one-hom-Ringᵉ Rᵉ Sᵉ fᵉ))
```