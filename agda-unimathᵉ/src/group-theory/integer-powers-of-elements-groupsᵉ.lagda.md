# Integer powers of elements of groups

```agda
module group-theory.integer-powers-of-elements-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.identity-typesᵉ
open import foundation.iterating-automorphismsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commuting-elements-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.powers-of-elements-groupsᵉ

open import structured-types.initial-pointed-type-equipped-with-automorphismᵉ
```

</details>

## Idea

Theᵉ **integerᵉ powerᵉ operation**ᵉ onᵉ aᵉ [group](group-theory.groups.mdᵉ) isᵉ theᵉ mapᵉ
`kᵉ xᵉ ↦ᵉ xᵏ`,ᵉ whichᵉ isᵉ definedᵉ byᵉ
[iteratively](foundation.iterating-automorphisms.mdᵉ) multiplyingᵉ `x`ᵉ with itselfᵉ
anᵉ [integer](elementary-number-theory.integers.mdᵉ) `k`ᵉ times.ᵉ

## Definitions

### Iteratively multiplication by `g`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  iterative-multiplication-by-element-Groupᵉ :
    type-Groupᵉ Gᵉ → ℤᵉ → type-Groupᵉ Gᵉ → type-Groupᵉ Gᵉ
  iterative-multiplication-by-element-Groupᵉ gᵉ kᵉ =
    map-iterate-automorphism-ℤᵉ kᵉ (equiv-mul-Groupᵉ Gᵉ gᵉ)
```

### Integer powers of group elements

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  integer-power-Groupᵉ : ℤᵉ → type-Groupᵉ Gᵉ → type-Groupᵉ Gᵉ
  integer-power-Groupᵉ kᵉ gᵉ =
    map-iterate-automorphism-ℤᵉ kᵉ (equiv-mul-Groupᵉ Gᵉ gᵉ) (unit-Groupᵉ Gᵉ)
```

### The predicate of being an integer power of an element in a group

Weᵉ sayᵉ thatᵉ anᵉ elementᵉ `y`ᵉ **isᵉ anᵉ integerᵉ power**ᵉ ofᵉ anᵉ elementᵉ `x`ᵉ ifᵉ thereᵉ
[exists](foundation.existential-quantification.mdᵉ) anᵉ integerᵉ `k`ᵉ suchᵉ thatᵉ
`xᵏᵉ ＝ᵉ y`.ᵉ

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  is-integer-power-of-element-prop-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → Propᵉ lᵉ
  is-integer-power-of-element-prop-Groupᵉ xᵉ yᵉ =
    exists-structure-Propᵉ ℤᵉ (λ kᵉ → integer-power-Groupᵉ Gᵉ kᵉ xᵉ ＝ᵉ yᵉ)

  is-integer-power-of-element-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → UUᵉ lᵉ
  is-integer-power-of-element-Groupᵉ xᵉ yᵉ =
    type-Propᵉ (is-integer-power-of-element-prop-Groupᵉ xᵉ yᵉ)

  is-prop-is-integer-power-of-element-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    is-propᵉ (is-integer-power-of-element-Groupᵉ xᵉ yᵉ)
  is-prop-is-integer-power-of-element-Groupᵉ xᵉ yᵉ =
    is-prop-type-Propᵉ (is-integer-power-of-element-prop-Groupᵉ xᵉ yᵉ)
```

## Properties

### Associativity of iterated multiplication by a group element

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) (gᵉ : type-Groupᵉ Gᵉ)
  where

  associative-iterative-multiplication-by-element-Groupᵉ :
    (kᵉ : ℤᵉ) (h1ᵉ h2ᵉ : type-Groupᵉ Gᵉ) →
    iterative-multiplication-by-element-Groupᵉ Gᵉ gᵉ kᵉ (mul-Groupᵉ Gᵉ h1ᵉ h2ᵉ) ＝ᵉ
    mul-Groupᵉ Gᵉ (iterative-multiplication-by-element-Groupᵉ Gᵉ gᵉ kᵉ h1ᵉ) h2ᵉ
  associative-iterative-multiplication-by-element-Groupᵉ
    ( inlᵉ zero-ℕᵉ) h1ᵉ h2ᵉ =
    invᵉ (associative-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ gᵉ) h1ᵉ h2ᵉ)
  associative-iterative-multiplication-by-element-Groupᵉ
    ( inlᵉ (succ-ℕᵉ xᵉ)) h1ᵉ h2ᵉ =
    ( apᵉ
      ( mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ gᵉ))
      ( associative-iterative-multiplication-by-element-Groupᵉ
        ( inlᵉ xᵉ)
        ( h1ᵉ)
        ( h2ᵉ))) ∙ᵉ
    ( invᵉ
      ( associative-mul-Groupᵉ Gᵉ
        ( inv-Groupᵉ Gᵉ gᵉ)
        ( iterative-multiplication-by-element-Groupᵉ Gᵉ gᵉ (inlᵉ xᵉ) h1ᵉ)
        ( h2ᵉ)))
  associative-iterative-multiplication-by-element-Groupᵉ
    ( inrᵉ (inlᵉ _)) h1ᵉ h2ᵉ =
    reflᵉ
  associative-iterative-multiplication-by-element-Groupᵉ
    ( inrᵉ (inrᵉ zero-ℕᵉ)) h1ᵉ h2ᵉ =
    invᵉ (associative-mul-Groupᵉ Gᵉ gᵉ h1ᵉ h2ᵉ)
  associative-iterative-multiplication-by-element-Groupᵉ
    ( inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) h1ᵉ h2ᵉ =
    ( apᵉ
      ( mul-Groupᵉ Gᵉ gᵉ)
      ( associative-iterative-multiplication-by-element-Groupᵉ
        ( inrᵉ (inrᵉ xᵉ))
        ( h1ᵉ)
        ( h2ᵉ))) ∙ᵉ
    ( invᵉ
      ( associative-mul-Groupᵉ Gᵉ gᵉ
        ( iterative-multiplication-by-element-Groupᵉ Gᵉ gᵉ (inrᵉ (inrᵉ xᵉ)) h1ᵉ)
        ( h2ᵉ)))
```

### `integer-power-Group G (int-ℕ n) g ＝ power-Group G n g`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  integer-power-int-Groupᵉ :
    (nᵉ : ℕᵉ) (gᵉ : type-Groupᵉ Gᵉ) →
    integer-power-Groupᵉ Gᵉ (int-ℕᵉ nᵉ) gᵉ ＝ᵉ power-Groupᵉ Gᵉ nᵉ gᵉ
  integer-power-int-Groupᵉ zero-ℕᵉ gᵉ = reflᵉ
  integer-power-int-Groupᵉ (succ-ℕᵉ zero-ℕᵉ) gᵉ = right-unit-law-mul-Groupᵉ Gᵉ gᵉ
  integer-power-int-Groupᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) gᵉ =
    ( apᵉ (mul-Groupᵉ Gᵉ gᵉ) (integer-power-int-Groupᵉ (succ-ℕᵉ nᵉ) gᵉ)) ∙ᵉ
    ( invᵉ (power-succ-Group'ᵉ Gᵉ (succ-ℕᵉ nᵉ) gᵉ))

  integer-power-in-pos-Groupᵉ :
    (nᵉ : ℕᵉ) (gᵉ : type-Groupᵉ Gᵉ) →
    integer-power-Groupᵉ Gᵉ (in-pos-ℤᵉ nᵉ) gᵉ ＝ᵉ
    power-Groupᵉ Gᵉ (succ-ℕᵉ nᵉ) gᵉ
  integer-power-in-pos-Groupᵉ nᵉ gᵉ = integer-power-int-Groupᵉ (succ-ℕᵉ nᵉ) gᵉ

  integer-power-in-neg-Groupᵉ :
    (nᵉ : ℕᵉ) (gᵉ : type-Groupᵉ Gᵉ) →
    integer-power-Groupᵉ Gᵉ (in-neg-ℤᵉ nᵉ) gᵉ ＝ᵉ
    inv-Groupᵉ Gᵉ (power-Groupᵉ Gᵉ (succ-ℕᵉ nᵉ) gᵉ)
  integer-power-in-neg-Groupᵉ zero-ℕᵉ gᵉ =
    right-unit-law-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ gᵉ)
  integer-power-in-neg-Groupᵉ (succ-ℕᵉ nᵉ) gᵉ =
    ( apᵉ (mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ gᵉ)) (integer-power-in-neg-Groupᵉ nᵉ gᵉ)) ∙ᵉ
    ( invᵉ (distributive-inv-mul-Groupᵉ Gᵉ)) ∙ᵉ
    ( apᵉ (inv-Groupᵉ Gᵉ) (power-succ-Groupᵉ Gᵉ (succ-ℕᵉ nᵉ) gᵉ))
```

### The integer power `x⁰` is the unit of the group

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) (gᵉ : type-Groupᵉ Gᵉ)
  where

  integer-power-zero-Groupᵉ :
    integer-power-Groupᵉ Gᵉ zero-ℤᵉ gᵉ ＝ᵉ unit-Groupᵉ Gᵉ
  integer-power-zero-Groupᵉ =
    preserves-point-map-ℤ-Pointed-Type-With-Autᵉ
      ( pointed-type-with-aut-Groupᵉ Gᵉ gᵉ)
```

### `x¹ ＝ x`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) (gᵉ : type-Groupᵉ Gᵉ)
  where

  integer-power-one-Groupᵉ :
    integer-power-Groupᵉ Gᵉ one-ℤᵉ gᵉ ＝ᵉ gᵉ
  integer-power-one-Groupᵉ = right-unit-law-mul-Groupᵉ Gᵉ gᵉ
```

### The integer power `x⁻¹` is the inverse of `x`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) (gᵉ : type-Groupᵉ Gᵉ)
  where

  integer-power-neg-one-Groupᵉ :
    integer-power-Groupᵉ Gᵉ neg-one-ℤᵉ gᵉ ＝ᵉ inv-Groupᵉ Gᵉ gᵉ
  integer-power-neg-one-Groupᵉ = right-unit-law-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ gᵉ)
```

### The integer power `gˣ⁺ʸ` computes to `gˣgʸ`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) (gᵉ : type-Groupᵉ Gᵉ)
  where

  distributive-integer-power-add-Groupᵉ :
    (xᵉ yᵉ : ℤᵉ) →
    integer-power-Groupᵉ Gᵉ (xᵉ +ℤᵉ yᵉ) gᵉ ＝ᵉ
    mul-Groupᵉ Gᵉ
      ( integer-power-Groupᵉ Gᵉ xᵉ gᵉ)
      ( integer-power-Groupᵉ Gᵉ yᵉ gᵉ)
  distributive-integer-power-add-Groupᵉ xᵉ yᵉ =
    ( iterate-automorphism-add-ℤᵉ xᵉ yᵉ (equiv-mul-Groupᵉ Gᵉ gᵉ) (unit-Groupᵉ Gᵉ)) ∙ᵉ
    ( apᵉ
      ( iterative-multiplication-by-element-Groupᵉ Gᵉ gᵉ xᵉ)
      ( invᵉ (left-unit-law-mul-Groupᵉ Gᵉ (integer-power-Groupᵉ Gᵉ yᵉ gᵉ)))) ∙ᵉ
    ( associative-iterative-multiplication-by-element-Groupᵉ Gᵉ gᵉ xᵉ
      ( unit-Groupᵉ Gᵉ)
      ( integer-power-Groupᵉ Gᵉ yᵉ gᵉ))
```

### The integer power `x⁻ᵏ` is the inverse of the integer power `xᵏ`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  integer-power-neg-Groupᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Groupᵉ Gᵉ) →
    integer-power-Groupᵉ Gᵉ (neg-ℤᵉ kᵉ) xᵉ ＝ᵉ inv-Groupᵉ Gᵉ (integer-power-Groupᵉ Gᵉ kᵉ xᵉ)
  integer-power-neg-Groupᵉ (inlᵉ kᵉ) xᵉ =
    transpose-eq-inv-Groupᵉ Gᵉ
      ( ( apᵉ (inv-Groupᵉ Gᵉ) (integer-power-in-pos-Groupᵉ Gᵉ kᵉ xᵉ)) ∙ᵉ
        ( invᵉ (integer-power-in-neg-Groupᵉ Gᵉ kᵉ xᵉ)))
  integer-power-neg-Groupᵉ (inrᵉ (inlᵉ _)) xᵉ =
    integer-power-zero-Groupᵉ Gᵉ xᵉ ∙ᵉ invᵉ (inv-unit-Groupᵉ Gᵉ)
  integer-power-neg-Groupᵉ (inrᵉ (inrᵉ kᵉ)) xᵉ =
    ( integer-power-in-neg-Groupᵉ Gᵉ kᵉ xᵉ) ∙ᵉ
    ( apᵉ (inv-Groupᵉ Gᵉ) (invᵉ (integer-power-in-pos-Groupᵉ Gᵉ kᵉ xᵉ)))
```

### `xᵏ⁺¹ = xᵏx` and `xᵏ⁺¹ = xxᵏ`

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  integer-power-succ-Groupᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Groupᵉ Gᵉ) →
    integer-power-Groupᵉ Gᵉ (succ-ℤᵉ kᵉ) xᵉ ＝ᵉ
    mul-Groupᵉ Gᵉ (integer-power-Groupᵉ Gᵉ kᵉ xᵉ) xᵉ
  integer-power-succ-Groupᵉ kᵉ xᵉ =
    ( apᵉ (λ tᵉ → integer-power-Groupᵉ Gᵉ tᵉ xᵉ) (is-right-add-one-succ-ℤᵉ kᵉ)) ∙ᵉ
    ( distributive-integer-power-add-Groupᵉ Gᵉ xᵉ kᵉ one-ℤᵉ) ∙ᵉ
    ( apᵉ (mul-Groupᵉ Gᵉ _) (integer-power-one-Groupᵉ Gᵉ xᵉ))

  integer-power-succ-Group'ᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Groupᵉ Gᵉ) →
    integer-power-Groupᵉ Gᵉ (succ-ℤᵉ kᵉ) xᵉ ＝ᵉ
    mul-Groupᵉ Gᵉ xᵉ (integer-power-Groupᵉ Gᵉ kᵉ xᵉ)
  integer-power-succ-Group'ᵉ kᵉ xᵉ =
    ( apᵉ (λ tᵉ → integer-power-Groupᵉ Gᵉ tᵉ xᵉ) (is-left-add-one-succ-ℤᵉ kᵉ)) ∙ᵉ
    ( distributive-integer-power-add-Groupᵉ Gᵉ xᵉ one-ℤᵉ kᵉ) ∙ᵉ
    ( apᵉ (mul-Group'ᵉ Gᵉ _) (integer-power-one-Groupᵉ Gᵉ xᵉ))
```

### `xᵏ⁻¹ = xᵏx⁻¹` and `xᵏ⁻¹ = x⁻¹xᵏ`

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  private

    infixl 45 _*ᵉ_
    _*ᵉ_ = mul-Groupᵉ Gᵉ

    pwrᵉ = integer-power-Groupᵉ Gᵉ

    infixr 50 _^ᵉ_
    _^ᵉ_ : (xᵉ : type-Groupᵉ Gᵉ) (kᵉ : ℤᵉ) → type-Groupᵉ Gᵉ
    _^ᵉ_ xᵉ kᵉ = integer-power-Groupᵉ Gᵉ kᵉ xᵉ

    infix 55 _⁻¹ᵉ
    _⁻¹ᵉ = inv-Groupᵉ Gᵉ

  integer-power-pred-Groupᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Groupᵉ Gᵉ) → xᵉ ^ᵉ (pred-ℤᵉ kᵉ) ＝ᵉ xᵉ ^ᵉ kᵉ *ᵉ xᵉ ⁻¹ᵉ
  integer-power-pred-Groupᵉ kᵉ xᵉ =
    ( apᵉ (xᵉ ^ᵉ_) (is-right-add-neg-one-pred-ℤᵉ kᵉ)) ∙ᵉ
    ( distributive-integer-power-add-Groupᵉ Gᵉ xᵉ kᵉ neg-one-ℤᵉ) ∙ᵉ
    ( apᵉ ((xᵉ ^ᵉ kᵉ) *ᵉ_) (integer-power-neg-one-Groupᵉ Gᵉ xᵉ))

  integer-power-pred-Group'ᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Groupᵉ Gᵉ) → xᵉ ^ᵉ (pred-ℤᵉ kᵉ) ＝ᵉ xᵉ ⁻¹ᵉ *ᵉ xᵉ ^ᵉ kᵉ
  integer-power-pred-Group'ᵉ kᵉ xᵉ =
    ( apᵉ (xᵉ ^ᵉ_) (is-left-add-neg-one-pred-ℤᵉ kᵉ)) ∙ᵉ
    ( distributive-integer-power-add-Groupᵉ Gᵉ xᵉ neg-one-ℤᵉ kᵉ) ∙ᵉ
    ( apᵉ (_*ᵉ (xᵉ ^ᵉ kᵉ)) (integer-power-neg-one-Groupᵉ Gᵉ xᵉ))
```

### `1ᵏ ＝ 1`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  integer-power-unit-Groupᵉ :
    (kᵉ : ℤᵉ) → integer-power-Groupᵉ Gᵉ kᵉ (unit-Groupᵉ Gᵉ) ＝ᵉ unit-Groupᵉ Gᵉ
  integer-power-unit-Groupᵉ (inlᵉ zero-ℕᵉ) =
    integer-power-neg-one-Groupᵉ Gᵉ (unit-Groupᵉ Gᵉ) ∙ᵉ inv-unit-Groupᵉ Gᵉ
  integer-power-unit-Groupᵉ (inlᵉ (succ-ℕᵉ kᵉ)) =
    ( ap-mul-Groupᵉ Gᵉ (inv-unit-Groupᵉ Gᵉ) (integer-power-unit-Groupᵉ (inlᵉ kᵉ))) ∙ᵉ
    ( left-unit-law-mul-Groupᵉ Gᵉ (unit-Groupᵉ Gᵉ))
  integer-power-unit-Groupᵉ (inrᵉ (inlᵉ _)) = reflᵉ
  integer-power-unit-Groupᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) =
    integer-power-one-Groupᵉ Gᵉ (unit-Groupᵉ Gᵉ)
  integer-power-unit-Groupᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ))) =
    left-unit-law-mul-Groupᵉ Gᵉ _ ∙ᵉ integer-power-unit-Groupᵉ (inrᵉ (inrᵉ kᵉ))
```

### If `x` commutes with `y` then so do their integer powers

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  private

    infixl 45 _*ᵉ_
    _*ᵉ_ = mul-Groupᵉ Gᵉ

    pwrᵉ = integer-power-Groupᵉ Gᵉ

    infixr 50 _^ᵉ_
    _^ᵉ_ : (xᵉ : type-Groupᵉ Gᵉ) (kᵉ : ℤᵉ) → type-Groupᵉ Gᵉ
    _^ᵉ_ xᵉ kᵉ = integer-power-Groupᵉ Gᵉ kᵉ xᵉ

    infix 55 _⁻¹ᵉ
    _⁻¹ᵉ = inv-Groupᵉ Gᵉ

  commute-integer-powers-Group'ᵉ :
    (kᵉ : ℤᵉ) {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    commute-Groupᵉ Gᵉ xᵉ yᵉ → commute-Groupᵉ Gᵉ xᵉ (yᵉ ^ᵉ kᵉ)
  commute-integer-powers-Group'ᵉ (inlᵉ zero-ℕᵉ) {xᵉ} {yᵉ} Hᵉ =
    ( apᵉ (xᵉ *ᵉ_) (integer-power-neg-one-Groupᵉ Gᵉ yᵉ)) ∙ᵉ
    ( commute-inv-Groupᵉ Gᵉ xᵉ yᵉ Hᵉ) ∙ᵉ
    ( apᵉ (_*ᵉ xᵉ) (invᵉ (integer-power-neg-one-Groupᵉ Gᵉ yᵉ)))
  commute-integer-powers-Group'ᵉ (inlᵉ (succ-ℕᵉ kᵉ)) {xᵉ} {yᵉ} Hᵉ =
    commute-mul-Groupᵉ Gᵉ xᵉ
      ( inv-Groupᵉ Gᵉ yᵉ)
      ( integer-power-Groupᵉ Gᵉ (inlᵉ kᵉ) yᵉ)
      ( commute-inv-Groupᵉ Gᵉ xᵉ yᵉ Hᵉ)
      ( commute-integer-powers-Group'ᵉ (inlᵉ kᵉ) Hᵉ)
  commute-integer-powers-Group'ᵉ (inrᵉ (inlᵉ _)) {xᵉ} {yᵉ} Hᵉ =
    commute-unit-Groupᵉ Gᵉ xᵉ
  commute-integer-powers-Group'ᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) {xᵉ} {yᵉ} Hᵉ =
    ( apᵉ (xᵉ *ᵉ_) (integer-power-one-Groupᵉ Gᵉ yᵉ)) ∙ᵉ
    ( Hᵉ) ∙ᵉ
    ( apᵉ (_*ᵉ xᵉ) (invᵉ (integer-power-one-Groupᵉ Gᵉ yᵉ)))
  commute-integer-powers-Group'ᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ))) {xᵉ} {yᵉ} Hᵉ =
    commute-mul-Groupᵉ Gᵉ xᵉ yᵉ
      ( integer-power-Groupᵉ Gᵉ (inrᵉ (inrᵉ kᵉ)) yᵉ)
      ( Hᵉ)
      ( commute-integer-powers-Group'ᵉ (inrᵉ (inrᵉ kᵉ)) Hᵉ)

  commute-integer-powers-Groupᵉ :
    (kᵉ lᵉ : ℤᵉ) {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    commute-Groupᵉ Gᵉ xᵉ yᵉ → commute-Groupᵉ Gᵉ (xᵉ ^ᵉ kᵉ) (yᵉ ^ᵉ lᵉ)
  commute-integer-powers-Groupᵉ (inlᵉ zero-ℕᵉ) lᵉ {xᵉ} {yᵉ} Hᵉ =
    ( apᵉ (_*ᵉ (yᵉ ^ᵉ lᵉ)) (integer-power-neg-one-Groupᵉ Gᵉ xᵉ)) ∙ᵉ
    ( invᵉ
      ( commute-inv-Groupᵉ Gᵉ
        ( yᵉ ^ᵉ lᵉ)
        ( xᵉ)
        ( invᵉ (commute-integer-powers-Group'ᵉ lᵉ Hᵉ)))) ∙ᵉ
    ( apᵉ ((yᵉ ^ᵉ lᵉ) *ᵉ_) (invᵉ (integer-power-neg-one-Groupᵉ Gᵉ xᵉ)))
  commute-integer-powers-Groupᵉ (inlᵉ (succ-ℕᵉ kᵉ)) lᵉ {xᵉ} {yᵉ} Hᵉ =
    invᵉ
      ( commute-mul-Groupᵉ Gᵉ
        ( yᵉ ^ᵉ lᵉ)
        ( inv-Groupᵉ Gᵉ xᵉ)
        ( xᵉ ^ᵉ inlᵉ kᵉ)
        ( commute-inv-Groupᵉ Gᵉ (yᵉ ^ᵉ lᵉ) xᵉ
          ( invᵉ (commute-integer-powers-Group'ᵉ lᵉ Hᵉ)))
        ( invᵉ (commute-integer-powers-Groupᵉ (inlᵉ kᵉ) lᵉ Hᵉ)))
  commute-integer-powers-Groupᵉ (inrᵉ (inlᵉ _)) lᵉ {xᵉ} {yᵉ} Hᵉ =
    invᵉ (commute-unit-Groupᵉ Gᵉ (yᵉ ^ᵉ lᵉ))
  commute-integer-powers-Groupᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) lᵉ {xᵉ} {yᵉ} Hᵉ =
    ( apᵉ (_*ᵉ (yᵉ ^ᵉ lᵉ)) (integer-power-one-Groupᵉ Gᵉ xᵉ)) ∙ᵉ
    ( commute-integer-powers-Group'ᵉ lᵉ Hᵉ) ∙ᵉ
    ( apᵉ ((yᵉ ^ᵉ lᵉ) *ᵉ_) (invᵉ (integer-power-one-Groupᵉ Gᵉ xᵉ)))
  commute-integer-powers-Groupᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ))) lᵉ {xᵉ} {yᵉ} Hᵉ =
    invᵉ
      ( commute-mul-Groupᵉ Gᵉ
        ( yᵉ ^ᵉ lᵉ)
        ( xᵉ)
        ( xᵉ ^ᵉ inrᵉ (inrᵉ kᵉ))
        ( invᵉ (commute-integer-powers-Group'ᵉ lᵉ Hᵉ))
        ( invᵉ (commute-integer-powers-Groupᵉ (inrᵉ (inrᵉ kᵉ)) lᵉ Hᵉ)))
```

### If `x` commutes with `y`, then integer powers distribute over the product of `x` and `y`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  private

    infixl 45 _*ᵉ_
    _*ᵉ_ = mul-Groupᵉ Gᵉ

    pwrᵉ = integer-power-Groupᵉ Gᵉ

    infixr 50 _^ᵉ_
    _^ᵉ_ : (xᵉ : type-Groupᵉ Gᵉ) (kᵉ : ℤᵉ) → type-Groupᵉ Gᵉ
    _^ᵉ_ xᵉ kᵉ = integer-power-Groupᵉ Gᵉ kᵉ xᵉ

    infix 55 _⁻¹ᵉ
    _⁻¹ᵉ = inv-Groupᵉ Gᵉ

  distributive-integer-power-mul-Groupᵉ :
    (kᵉ : ℤᵉ) (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    commute-Groupᵉ Gᵉ xᵉ yᵉ → (xᵉ *ᵉ yᵉ) ^ᵉ kᵉ ＝ᵉ xᵉ ^ᵉ kᵉ *ᵉ yᵉ ^ᵉ kᵉ
  distributive-integer-power-mul-Groupᵉ (inlᵉ zero-ℕᵉ) xᵉ yᵉ Hᵉ =
    equational-reasoningᵉ
      (xᵉ *ᵉ yᵉ) ^ᵉ neg-one-ℤᵉ
      ＝ᵉ (xᵉ *ᵉ yᵉ) ⁻¹ᵉ
        byᵉ integer-power-neg-one-Groupᵉ Gᵉ (xᵉ *ᵉ yᵉ)
      ＝ᵉ xᵉ ⁻¹ᵉ *ᵉ yᵉ ⁻¹ᵉ
        byᵉ distributive-inv-mul-Group'ᵉ Gᵉ xᵉ yᵉ Hᵉ
      ＝ᵉ xᵉ ^ᵉ neg-one-ℤᵉ *ᵉ yᵉ ^ᵉ neg-one-ℤᵉ
        byᵉ
        invᵉ
          ( ap-mul-Groupᵉ Gᵉ
            ( integer-power-neg-one-Groupᵉ Gᵉ xᵉ)
            ( integer-power-neg-one-Groupᵉ Gᵉ yᵉ))
  distributive-integer-power-mul-Groupᵉ (inlᵉ (succ-ℕᵉ kᵉ)) xᵉ yᵉ Hᵉ =
    equational-reasoningᵉ
      (xᵉ *ᵉ yᵉ) ^ᵉ (pred-ℤᵉ (inlᵉ kᵉ))
      ＝ᵉ (xᵉ *ᵉ yᵉ) ^ᵉ (inlᵉ kᵉ) *ᵉ (xᵉ *ᵉ yᵉ) ⁻¹ᵉ
        byᵉ integer-power-pred-Groupᵉ Gᵉ (inlᵉ kᵉ) (xᵉ *ᵉ yᵉ)
      ＝ᵉ (xᵉ ^ᵉ (inlᵉ kᵉ) *ᵉ yᵉ ^ᵉ (inlᵉ kᵉ)) *ᵉ (xᵉ ⁻¹ᵉ *ᵉ yᵉ ⁻¹ᵉ)
        byᵉ
        ap-mul-Groupᵉ Gᵉ
          ( distributive-integer-power-mul-Groupᵉ (inlᵉ kᵉ) xᵉ yᵉ Hᵉ)
          ( distributive-inv-mul-Group'ᵉ Gᵉ xᵉ yᵉ Hᵉ)
      ＝ᵉ (xᵉ ^ᵉ (inlᵉ kᵉ) *ᵉ xᵉ ⁻¹ᵉ) *ᵉ (yᵉ ^ᵉ (inlᵉ kᵉ) *ᵉ yᵉ ⁻¹ᵉ)
        byᵉ
        interchange-mul-mul-Groupᵉ Gᵉ
          ( double-transpose-eq-mul-Group'ᵉ Gᵉ
            ( commute-integer-powers-Group'ᵉ Gᵉ (inlᵉ kᵉ) Hᵉ))
      ＝ᵉ (xᵉ ^ᵉ (pred-ℤᵉ (inlᵉ kᵉ))) *ᵉ (yᵉ ^ᵉ (pred-ℤᵉ (inlᵉ kᵉ)))
        byᵉ
        ap-mul-Groupᵉ Gᵉ
          ( invᵉ (integer-power-pred-Groupᵉ Gᵉ (inlᵉ kᵉ) xᵉ))
          ( invᵉ (integer-power-pred-Groupᵉ Gᵉ (inlᵉ kᵉ) yᵉ))
  distributive-integer-power-mul-Groupᵉ (inrᵉ (inlᵉ _)) xᵉ yᵉ Hᵉ =
    invᵉ (left-unit-law-mul-Groupᵉ Gᵉ (unit-Groupᵉ Gᵉ))
  distributive-integer-power-mul-Groupᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) xᵉ yᵉ Hᵉ =
    ( integer-power-one-Groupᵉ Gᵉ (xᵉ *ᵉ yᵉ)) ∙ᵉ
    ( invᵉ
      ( ap-mul-Groupᵉ Gᵉ
        ( integer-power-one-Groupᵉ Gᵉ xᵉ)
        ( integer-power-one-Groupᵉ Gᵉ yᵉ)))
  distributive-integer-power-mul-Groupᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ))) xᵉ yᵉ Hᵉ =
    equational-reasoningᵉ
      (xᵉ *ᵉ yᵉ) ^ᵉ (succ-ℤᵉ (in-pos-ℤᵉ kᵉ))
      ＝ᵉ (xᵉ *ᵉ yᵉ) ^ᵉ (in-pos-ℤᵉ kᵉ) *ᵉ (xᵉ *ᵉ yᵉ)
        byᵉ integer-power-succ-Groupᵉ Gᵉ (in-pos-ℤᵉ kᵉ) (xᵉ *ᵉ yᵉ)
      ＝ᵉ (xᵉ ^ᵉ (in-pos-ℤᵉ kᵉ) *ᵉ yᵉ ^ᵉ (in-pos-ℤᵉ kᵉ)) *ᵉ (xᵉ *ᵉ yᵉ)
        byᵉ
        apᵉ
          ( _*ᵉ (xᵉ *ᵉ yᵉ))
          ( distributive-integer-power-mul-Groupᵉ (inrᵉ (inrᵉ kᵉ)) xᵉ yᵉ Hᵉ)
      ＝ᵉ (xᵉ ^ᵉ (in-pos-ℤᵉ kᵉ) *ᵉ xᵉ) *ᵉ (yᵉ ^ᵉ (in-pos-ℤᵉ kᵉ) *ᵉ yᵉ)
        byᵉ
        interchange-mul-mul-Groupᵉ Gᵉ
          ( invᵉ (commute-integer-powers-Group'ᵉ Gᵉ (in-pos-ℤᵉ kᵉ) Hᵉ))
      ＝ᵉ xᵉ ^ᵉ (succ-ℤᵉ (in-pos-ℤᵉ kᵉ)) *ᵉ yᵉ ^ᵉ (succ-ℤᵉ (in-pos-ℤᵉ kᵉ))
        byᵉ
        ap-mul-Groupᵉ Gᵉ
          ( invᵉ (integer-power-succ-Groupᵉ Gᵉ (in-pos-ℤᵉ kᵉ) xᵉ))
          ( invᵉ (integer-power-succ-Groupᵉ Gᵉ (in-pos-ℤᵉ kᵉ) yᵉ))
```

### Powers by products of integers are iterated integer powers

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  private

    infixl 45 _*ᵉ_
    _*ᵉ_ = mul-ℤᵉ

    pwrᵉ = integer-power-Groupᵉ Gᵉ

    infixr 50 _^ᵉ_
    _^ᵉ_ : (xᵉ : type-Groupᵉ Gᵉ) (kᵉ : ℤᵉ) → type-Groupᵉ Gᵉ
    _^ᵉ_ xᵉ kᵉ = integer-power-Groupᵉ Gᵉ kᵉ xᵉ

  integer-power-mul-Groupᵉ :
    (kᵉ lᵉ : ℤᵉ) (xᵉ : type-Groupᵉ Gᵉ) → xᵉ ^ᵉ (kᵉ *ᵉ lᵉ) ＝ᵉ (xᵉ ^ᵉ kᵉ) ^ᵉ lᵉ
  integer-power-mul-Groupᵉ kᵉ (inlᵉ zero-ℕᵉ) xᵉ =
    ( apᵉ (xᵉ ^ᵉ_) (right-neg-unit-law-mul-ℤᵉ kᵉ)) ∙ᵉ
    ( integer-power-neg-Groupᵉ Gᵉ kᵉ xᵉ) ∙ᵉ
    ( invᵉ (integer-power-neg-one-Groupᵉ Gᵉ _))
  integer-power-mul-Groupᵉ kᵉ (inlᵉ (succ-ℕᵉ lᵉ)) xᵉ =
    equational-reasoningᵉ
      (xᵉ ^ᵉ (kᵉ *ᵉ inlᵉ (succ-ℕᵉ lᵉ)))
      ＝ᵉ xᵉ ^ᵉ (neg-ℤᵉ kᵉ +ℤᵉ (kᵉ *ℤᵉ inlᵉ lᵉ))
        byᵉ apᵉ (xᵉ ^ᵉ_) (right-predecessor-law-mul-ℤᵉ kᵉ (inlᵉ lᵉ))
      ＝ᵉ mul-Groupᵉ Gᵉ (xᵉ ^ᵉ neg-ℤᵉ kᵉ) (xᵉ ^ᵉ (kᵉ *ᵉ (inlᵉ lᵉ)))
        byᵉ distributive-integer-power-add-Groupᵉ Gᵉ xᵉ (neg-ℤᵉ kᵉ) _
      ＝ᵉ mul-Groupᵉ Gᵉ ((xᵉ ^ᵉ kᵉ) ^ᵉ neg-one-ℤᵉ) ((xᵉ ^ᵉ kᵉ) ^ᵉ (inlᵉ lᵉ))
        byᵉ
        ap-mul-Groupᵉ Gᵉ
          ( ( integer-power-neg-Groupᵉ Gᵉ kᵉ xᵉ) ∙ᵉ
            ( invᵉ (integer-power-neg-one-Groupᵉ Gᵉ (xᵉ ^ᵉ kᵉ))))
          ( integer-power-mul-Groupᵉ kᵉ (inlᵉ lᵉ) xᵉ)
      ＝ᵉ (xᵉ ^ᵉ kᵉ) ^ᵉ (neg-one-ℤᵉ +ℤᵉ (inlᵉ lᵉ))
        byᵉ
        invᵉ (distributive-integer-power-add-Groupᵉ Gᵉ (xᵉ ^ᵉ kᵉ) neg-one-ℤᵉ (inlᵉ lᵉ))
      ＝ᵉ (xᵉ ^ᵉ kᵉ) ^ᵉ (inlᵉ (succ-ℕᵉ lᵉ))
        byᵉ apᵉ ((xᵉ ^ᵉ kᵉ) ^ᵉ_) (is-left-add-neg-one-pred-ℤᵉ (inlᵉ lᵉ))
  integer-power-mul-Groupᵉ kᵉ (inrᵉ (inlᵉ _)) xᵉ =
    apᵉ (xᵉ ^ᵉ_) (right-zero-law-mul-ℤᵉ kᵉ)
  integer-power-mul-Groupᵉ kᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) xᵉ =
    ( apᵉ (xᵉ ^ᵉ_) (right-unit-law-mul-ℤᵉ kᵉ)) ∙ᵉ
    ( invᵉ (integer-power-one-Groupᵉ Gᵉ _))
  integer-power-mul-Groupᵉ kᵉ (inrᵉ (inrᵉ (succ-ℕᵉ lᵉ))) xᵉ =
    equational-reasoningᵉ
      (xᵉ ^ᵉ (kᵉ *ᵉ succ-ℤᵉ (in-pos-ℤᵉ lᵉ)))
      ＝ᵉ xᵉ ^ᵉ (kᵉ +ℤᵉ kᵉ *ᵉ (in-pos-ℤᵉ lᵉ))
        byᵉ apᵉ (xᵉ ^ᵉ_) (right-successor-law-mul-ℤᵉ kᵉ (in-pos-ℤᵉ lᵉ))
      ＝ᵉ mul-Groupᵉ Gᵉ (xᵉ ^ᵉ kᵉ) (xᵉ ^ᵉ (kᵉ *ᵉ in-pos-ℤᵉ lᵉ))
        byᵉ
        distributive-integer-power-add-Groupᵉ Gᵉ xᵉ kᵉ (kᵉ *ᵉ in-pos-ℤᵉ lᵉ)
      ＝ᵉ mul-Groupᵉ Gᵉ (xᵉ ^ᵉ kᵉ) ((xᵉ ^ᵉ kᵉ) ^ᵉ (in-pos-ℤᵉ lᵉ))
        byᵉ
        apᵉ (mul-Groupᵉ Gᵉ _) (integer-power-mul-Groupᵉ kᵉ (inrᵉ (inrᵉ lᵉ)) xᵉ)
      ＝ᵉ (xᵉ ^ᵉ kᵉ) ^ᵉ (succ-ℤᵉ (in-pos-ℤᵉ lᵉ))
        byᵉ
        invᵉ (integer-power-succ-Group'ᵉ Gᵉ (in-pos-ℤᵉ lᵉ) (xᵉ ^ᵉ kᵉ))

  swap-integer-power-Groupᵉ :
    (kᵉ lᵉ : ℤᵉ) (xᵉ : type-Groupᵉ Gᵉ) →
    integer-power-Groupᵉ Gᵉ kᵉ (integer-power-Groupᵉ Gᵉ lᵉ xᵉ) ＝ᵉ
    integer-power-Groupᵉ Gᵉ lᵉ (integer-power-Groupᵉ Gᵉ kᵉ xᵉ)
  swap-integer-power-Groupᵉ kᵉ lᵉ xᵉ =
    ( invᵉ (integer-power-mul-Groupᵉ lᵉ kᵉ xᵉ)) ∙ᵉ
    ( apᵉ (λ tᵉ → integer-power-Groupᵉ Gᵉ tᵉ xᵉ) (commutative-mul-ℤᵉ lᵉ kᵉ)) ∙ᵉ
    ( integer-power-mul-Groupᵉ kᵉ lᵉ xᵉ)
```

### Group homomorphisms preserve integer powers

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  preserves-integer-powers-hom-Groupᵉ :
    (kᵉ : ℤᵉ) (xᵉ : type-Groupᵉ Gᵉ) →
    map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (integer-power-Groupᵉ Gᵉ kᵉ xᵉ) ＝ᵉ
    integer-power-Groupᵉ Hᵉ kᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ)
  preserves-integer-powers-hom-Groupᵉ (inlᵉ zero-ℕᵉ) xᵉ =
    ( preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ) ∙ᵉ
    ( ap-mul-Groupᵉ Hᵉ
      ( preserves-inv-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
      ( preserves-unit-hom-Groupᵉ Gᵉ Hᵉ fᵉ))
  preserves-integer-powers-hom-Groupᵉ (inlᵉ (succ-ℕᵉ kᵉ)) xᵉ =
    ( preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ) ∙ᵉ
    ( ap-mul-Groupᵉ Hᵉ
      ( preserves-inv-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
      ( preserves-integer-powers-hom-Groupᵉ (inlᵉ kᵉ) xᵉ))
  preserves-integer-powers-hom-Groupᵉ (inrᵉ (inlᵉ _)) xᵉ =
    preserves-unit-hom-Groupᵉ Gᵉ Hᵉ fᵉ
  preserves-integer-powers-hom-Groupᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) xᵉ =
    ( preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ) ∙ᵉ
    ( apᵉ (mul-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ)) (preserves-unit-hom-Groupᵉ Gᵉ Hᵉ fᵉ))
  preserves-integer-powers-hom-Groupᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ))) xᵉ =
    ( preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ) ∙ᵉ
    ( apᵉ
      ( mul-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ))
      ( preserves-integer-powers-hom-Groupᵉ (inrᵉ (inrᵉ kᵉ)) xᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  eq-integer-power-hom-Groupᵉ :
    (gᵉ : hom-Groupᵉ Gᵉ Hᵉ) (kᵉ : ℤᵉ) (xᵉ : type-Groupᵉ Gᵉ) →
    ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ ＝ᵉ map-hom-Groupᵉ Gᵉ Hᵉ gᵉ xᵉ) →
    ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (integer-power-Groupᵉ Gᵉ kᵉ xᵉ) ＝ᵉ
      map-hom-Groupᵉ Gᵉ Hᵉ gᵉ (integer-power-Groupᵉ Gᵉ kᵉ xᵉ))
  eq-integer-power-hom-Groupᵉ gᵉ kᵉ xᵉ pᵉ =
    ( preserves-integer-powers-hom-Groupᵉ Gᵉ Hᵉ fᵉ kᵉ xᵉ) ∙ᵉ
    ( apᵉ (integer-power-Groupᵉ Hᵉ kᵉ) pᵉ) ∙ᵉ
    ( invᵉ (preserves-integer-powers-hom-Groupᵉ Gᵉ Hᵉ gᵉ kᵉ xᵉ))
```