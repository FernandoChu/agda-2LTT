# Addition on integer fractions

```agda
module elementary-number-theory.addition-integer-fractionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.integer-fractionsᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.multiplication-positive-and-negative-integersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
```

</details>

## Idea

Weᵉ introduceᵉ additionᵉ onᵉ integerᵉ fractionsᵉ andᵉ deriveᵉ itsᵉ basicᵉ properties.ᵉ Noteᵉ
thatᵉ theᵉ propertiesᵉ onlyᵉ holdᵉ upᵉ to fractionᵉ similarity.ᵉ

## Definition

```agda
add-fraction-ℤᵉ : fraction-ℤᵉ → fraction-ℤᵉ → fraction-ℤᵉ
pr1ᵉ (add-fraction-ℤᵉ (mᵉ ,ᵉ nᵉ ,ᵉ n-posᵉ) (m'ᵉ ,ᵉ n'ᵉ ,ᵉ n'-posᵉ)) =
  (mᵉ *ℤᵉ n'ᵉ) +ℤᵉ (m'ᵉ *ℤᵉ nᵉ)
pr1ᵉ (pr2ᵉ (add-fraction-ℤᵉ (mᵉ ,ᵉ nᵉ ,ᵉ n-posᵉ) (m'ᵉ ,ᵉ n'ᵉ ,ᵉ n'-posᵉ))) =
  nᵉ *ℤᵉ n'ᵉ
pr2ᵉ (pr2ᵉ (add-fraction-ℤᵉ (mᵉ ,ᵉ nᵉ ,ᵉ n-posᵉ) (m'ᵉ ,ᵉ n'ᵉ ,ᵉ n'-posᵉ))) =
  is-positive-mul-ℤᵉ n-posᵉ n'-posᵉ

add-fraction-ℤ'ᵉ : fraction-ℤᵉ → fraction-ℤᵉ → fraction-ℤᵉ
add-fraction-ℤ'ᵉ xᵉ yᵉ = add-fraction-ℤᵉ yᵉ xᵉ

infixl 35 _+fraction-ℤᵉ_
_+fraction-ℤᵉ_ = add-fraction-ℤᵉ

ap-add-fraction-ℤᵉ :
  {xᵉ yᵉ x'ᵉ y'ᵉ : fraction-ℤᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ →
  xᵉ +fraction-ℤᵉ yᵉ ＝ᵉ x'ᵉ +fraction-ℤᵉ y'ᵉ
ap-add-fraction-ℤᵉ pᵉ qᵉ = ap-binaryᵉ add-fraction-ℤᵉ pᵉ qᵉ
```

## Properties

### Addition respects the similarity relation

```agda
abstract
  sim-fraction-add-fraction-ℤᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : fraction-ℤᵉ} →
    sim-fraction-ℤᵉ xᵉ x'ᵉ →
    sim-fraction-ℤᵉ yᵉ y'ᵉ →
    sim-fraction-ℤᵉ (xᵉ +fraction-ℤᵉ yᵉ) (x'ᵉ +fraction-ℤᵉ y'ᵉ)
  sim-fraction-add-fraction-ℤᵉ
    {(nxᵉ ,ᵉ dxᵉ ,ᵉ dxpᵉ)} {(nx'ᵉ ,ᵉ dx'ᵉ ,ᵉ dx'pᵉ)}
    {(nyᵉ ,ᵉ dyᵉ ,ᵉ dypᵉ)} {(ny'ᵉ ,ᵉ dy'ᵉ ,ᵉ dy'pᵉ)} pᵉ qᵉ =
    equational-reasoningᵉ
      ((nxᵉ *ℤᵉ dyᵉ) +ℤᵉ (nyᵉ *ℤᵉ dxᵉ)) *ℤᵉ (dx'ᵉ *ℤᵉ dy'ᵉ)
      ＝ᵉ ((nxᵉ *ℤᵉ dyᵉ) *ℤᵉ (dx'ᵉ *ℤᵉ dy'ᵉ)) +ℤᵉ ((nyᵉ *ℤᵉ dxᵉ) *ℤᵉ (dx'ᵉ *ℤᵉ dy'ᵉ))
        byᵉ right-distributive-mul-add-ℤᵉ (nxᵉ *ℤᵉ dyᵉ) (nyᵉ *ℤᵉ dxᵉ) (dx'ᵉ *ℤᵉ dy'ᵉ)
      ＝ᵉ ((dyᵉ *ℤᵉ nxᵉ) *ℤᵉ (dx'ᵉ *ℤᵉ dy'ᵉ)) +ℤᵉ ((dxᵉ *ℤᵉ nyᵉ) *ℤᵉ (dy'ᵉ *ℤᵉ dx'ᵉ))
        byᵉ ap-add-ℤᵉ (ap-mul-ℤᵉ (commutative-mul-ℤᵉ nxᵉ dyᵉ) reflᵉ)
          (ap-mul-ℤᵉ (commutative-mul-ℤᵉ nyᵉ dxᵉ) (commutative-mul-ℤᵉ dx'ᵉ dy'ᵉ))
      ＝ᵉ (((dyᵉ *ℤᵉ nxᵉ) *ℤᵉ dx'ᵉ) *ℤᵉ dy'ᵉ) +ℤᵉ (((dxᵉ *ℤᵉ nyᵉ) *ℤᵉ dy'ᵉ) *ℤᵉ dx'ᵉ)
        byᵉ ap-add-ℤᵉ (invᵉ (associative-mul-ℤᵉ (dyᵉ *ℤᵉ nxᵉ) dx'ᵉ dy'ᵉ))
          (invᵉ (associative-mul-ℤᵉ (dxᵉ *ℤᵉ nyᵉ) dy'ᵉ dx'ᵉ))
      ＝ᵉ ((dyᵉ *ℤᵉ (nxᵉ *ℤᵉ dx'ᵉ)) *ℤᵉ dy'ᵉ) +ℤᵉ ((dxᵉ *ℤᵉ (nyᵉ *ℤᵉ dy'ᵉ)) *ℤᵉ dx'ᵉ)
        byᵉ ap-add-ℤᵉ (ap-mul-ℤᵉ (associative-mul-ℤᵉ dyᵉ nxᵉ dx'ᵉ) reflᵉ)
          (ap-mul-ℤᵉ (associative-mul-ℤᵉ dxᵉ nyᵉ dy'ᵉ) reflᵉ)
      ＝ᵉ ((dyᵉ *ℤᵉ (dxᵉ *ℤᵉ nx'ᵉ)) *ℤᵉ dy'ᵉ) +ℤᵉ ((dxᵉ *ℤᵉ (dyᵉ *ℤᵉ ny'ᵉ)) *ℤᵉ dx'ᵉ)
        byᵉ ap-add-ℤᵉ
          (ap-mul-ℤᵉ (ap-mul-ℤᵉ (reflᵉ {xᵉ = dyᵉ}) (pᵉ ∙ᵉ commutative-mul-ℤᵉ nx'ᵉ dxᵉ))
            (reflᵉ {xᵉ = dy'ᵉ}))
          (ap-mul-ℤᵉ (ap-mul-ℤᵉ (reflᵉ {xᵉ = dxᵉ}) (qᵉ ∙ᵉ commutative-mul-ℤᵉ ny'ᵉ dyᵉ))
            (reflᵉ {xᵉ = dx'ᵉ}))
      ＝ᵉ (((dyᵉ *ℤᵉ dxᵉ) *ℤᵉ nx'ᵉ) *ℤᵉ dy'ᵉ) +ℤᵉ (((dxᵉ *ℤᵉ dyᵉ) *ℤᵉ ny'ᵉ) *ℤᵉ dx'ᵉ)
        byᵉ ap-add-ℤᵉ (ap-mul-ℤᵉ (invᵉ (associative-mul-ℤᵉ dyᵉ dxᵉ nx'ᵉ)) reflᵉ)
          (ap-mul-ℤᵉ (invᵉ (associative-mul-ℤᵉ dxᵉ dyᵉ ny'ᵉ)) reflᵉ)
      ＝ᵉ ((nx'ᵉ *ℤᵉ (dyᵉ *ℤᵉ dxᵉ)) *ℤᵉ dy'ᵉ) +ℤᵉ ((ny'ᵉ *ℤᵉ (dxᵉ *ℤᵉ dyᵉ)) *ℤᵉ dx'ᵉ)
        byᵉ ap-add-ℤᵉ (ap-mul-ℤᵉ (commutative-mul-ℤᵉ (dyᵉ *ℤᵉ dxᵉ) nx'ᵉ) reflᵉ)
          (ap-mul-ℤᵉ (commutative-mul-ℤᵉ (dxᵉ *ℤᵉ dyᵉ) ny'ᵉ) reflᵉ)
      ＝ᵉ (nx'ᵉ *ℤᵉ ((dyᵉ *ℤᵉ dxᵉ) *ℤᵉ dy'ᵉ)) +ℤᵉ (ny'ᵉ *ℤᵉ ((dxᵉ *ℤᵉ dyᵉ) *ℤᵉ dx'ᵉ))
        byᵉ ap-add-ℤᵉ (associative-mul-ℤᵉ nx'ᵉ (dyᵉ *ℤᵉ dxᵉ) dy'ᵉ)
          (associative-mul-ℤᵉ ny'ᵉ (dxᵉ *ℤᵉ dyᵉ) dx'ᵉ)
      ＝ᵉ (nx'ᵉ *ℤᵉ (dy'ᵉ *ℤᵉ (dyᵉ *ℤᵉ dxᵉ))) +ℤᵉ (ny'ᵉ *ℤᵉ (dx'ᵉ *ℤᵉ (dxᵉ *ℤᵉ dyᵉ)))
        byᵉ ap-add-ℤᵉ
          (ap-mul-ℤᵉ (reflᵉ {xᵉ = nx'ᵉ}) (commutative-mul-ℤᵉ (dyᵉ *ℤᵉ dxᵉ) dy'ᵉ))
          (ap-mul-ℤᵉ (reflᵉ {xᵉ = ny'ᵉ}) (commutative-mul-ℤᵉ (dxᵉ *ℤᵉ dyᵉ) dx'ᵉ))
      ＝ᵉ ((nx'ᵉ *ℤᵉ dy'ᵉ) *ℤᵉ (dyᵉ *ℤᵉ dxᵉ)) +ℤᵉ ((ny'ᵉ *ℤᵉ dx'ᵉ) *ℤᵉ (dxᵉ *ℤᵉ dyᵉ))
        byᵉ ap-add-ℤᵉ (invᵉ (associative-mul-ℤᵉ nx'ᵉ dy'ᵉ (dyᵉ *ℤᵉ dxᵉ)))
          (invᵉ (associative-mul-ℤᵉ ny'ᵉ dx'ᵉ (dxᵉ *ℤᵉ dyᵉ)))
      ＝ᵉ ((nx'ᵉ *ℤᵉ dy'ᵉ) *ℤᵉ (dxᵉ *ℤᵉ dyᵉ)) +ℤᵉ ((ny'ᵉ *ℤᵉ dx'ᵉ) *ℤᵉ (dxᵉ *ℤᵉ dyᵉ))
        byᵉ ap-add-ℤᵉ
          (ap-mul-ℤᵉ (reflᵉ {xᵉ = nx'ᵉ *ℤᵉ dy'ᵉ}) (commutative-mul-ℤᵉ dyᵉ dxᵉ)) reflᵉ
      ＝ᵉ ((nx'ᵉ *ℤᵉ dy'ᵉ) +ℤᵉ (ny'ᵉ *ℤᵉ dx'ᵉ)) *ℤᵉ (dxᵉ *ℤᵉ dyᵉ)
        byᵉ invᵉ (right-distributive-mul-add-ℤᵉ (nx'ᵉ *ℤᵉ dy'ᵉ) _ (dxᵉ *ℤᵉ dyᵉ))
```

### Unit laws

```agda
abstract
  left-unit-law-add-fraction-ℤᵉ :
    (kᵉ : fraction-ℤᵉ) →
    sim-fraction-ℤᵉ (zero-fraction-ℤᵉ +fraction-ℤᵉ kᵉ) kᵉ
  left-unit-law-add-fraction-ℤᵉ (mᵉ ,ᵉ nᵉ ,ᵉ pᵉ) =
    ap-mul-ℤᵉ (right-unit-law-mul-ℤᵉ mᵉ) reflᵉ

  right-unit-law-add-fraction-ℤᵉ :
    (kᵉ : fraction-ℤᵉ) →
    sim-fraction-ℤᵉ (kᵉ +fraction-ℤᵉ zero-fraction-ℤᵉ) kᵉ
  right-unit-law-add-fraction-ℤᵉ (mᵉ ,ᵉ nᵉ ,ᵉ pᵉ) =
    ap-mul-ℤᵉ
      ( ap-add-ℤᵉ (right-unit-law-mul-ℤᵉ mᵉ) reflᵉ ∙ᵉ right-unit-law-add-ℤᵉ mᵉ)
      ( invᵉ (right-unit-law-mul-ℤᵉ nᵉ))
```

### Addition is associative

```agda
abstract
  associative-add-fraction-ℤᵉ :
    (xᵉ yᵉ zᵉ : fraction-ℤᵉ) →
    sim-fraction-ℤᵉ
      ((xᵉ +fraction-ℤᵉ yᵉ) +fraction-ℤᵉ zᵉ)
      (xᵉ +fraction-ℤᵉ (yᵉ +fraction-ℤᵉ zᵉ))
  associative-add-fraction-ℤᵉ (nxᵉ ,ᵉ dxᵉ ,ᵉ dxpᵉ) (nyᵉ ,ᵉ dyᵉ ,ᵉ dypᵉ) (nzᵉ ,ᵉ dzᵉ ,ᵉ dzpᵉ) =
    ap-mul-ℤᵉ (eq-numᵉ) (invᵉ (associative-mul-ℤᵉ dxᵉ dyᵉ dzᵉ))
    where
    eq-numᵉ :
      ( ((nxᵉ *ℤᵉ dyᵉ) +ℤᵉ (nyᵉ *ℤᵉ dxᵉ)) *ℤᵉ dzᵉ) +ℤᵉ (nzᵉ *ℤᵉ (dxᵉ *ℤᵉ dyᵉ)) ＝ᵉ
      ( (nxᵉ *ℤᵉ (dyᵉ *ℤᵉ dzᵉ)) +ℤᵉ (((nyᵉ *ℤᵉ dzᵉ) +ℤᵉ (nzᵉ *ℤᵉ dyᵉ)) *ℤᵉ dxᵉ))
    eq-numᵉ =
      equational-reasoningᵉ
        (((nxᵉ *ℤᵉ dyᵉ) +ℤᵉ (nyᵉ *ℤᵉ dxᵉ)) *ℤᵉ dzᵉ) +ℤᵉ (nzᵉ *ℤᵉ (dxᵉ *ℤᵉ dyᵉ))
        ＝ᵉ (((nxᵉ *ℤᵉ dyᵉ) *ℤᵉ dzᵉ) +ℤᵉ ((nyᵉ *ℤᵉ dxᵉ) *ℤᵉ dzᵉ)) +ℤᵉ
            (nzᵉ *ℤᵉ (dxᵉ *ℤᵉ dyᵉ))
          byᵉ ap-add-ℤᵉ
            (right-distributive-mul-add-ℤᵉ (nxᵉ *ℤᵉ dyᵉ) (nyᵉ *ℤᵉ dxᵉ) dzᵉ) reflᵉ
        ＝ᵉ ((nxᵉ *ℤᵉ dyᵉ) *ℤᵉ dzᵉ) +ℤᵉ
            (((nyᵉ *ℤᵉ dxᵉ) *ℤᵉ dzᵉ) +ℤᵉ (nzᵉ *ℤᵉ (dxᵉ *ℤᵉ dyᵉ)))
          byᵉ associative-add-ℤᵉ
            ((nxᵉ *ℤᵉ dyᵉ) *ℤᵉ dzᵉ) ((nyᵉ *ℤᵉ dxᵉ) *ℤᵉ dzᵉ) _
        ＝ᵉ (nxᵉ *ℤᵉ (dyᵉ *ℤᵉ dzᵉ)) +ℤᵉ
            (((nyᵉ *ℤᵉ dxᵉ) *ℤᵉ dzᵉ) +ℤᵉ (nzᵉ *ℤᵉ (dxᵉ *ℤᵉ dyᵉ)))
          byᵉ ap-add-ℤᵉ (associative-mul-ℤᵉ nxᵉ dyᵉ dzᵉ) reflᵉ
        ＝ᵉ (nxᵉ *ℤᵉ (dyᵉ *ℤᵉ dzᵉ)) +ℤᵉ
            ((nyᵉ *ℤᵉ (dzᵉ *ℤᵉ dxᵉ)) +ℤᵉ (nzᵉ *ℤᵉ (dyᵉ *ℤᵉ dxᵉ)))
          byᵉ ap-add-ℤᵉ
            (reflᵉ {xᵉ = nxᵉ *ℤᵉ (dyᵉ *ℤᵉ dzᵉ)})
            (ap-add-ℤᵉ
              (associative-mul-ℤᵉ nyᵉ dxᵉ dzᵉ ∙ᵉ ap-mul-ℤᵉ (reflᵉ {xᵉ = nyᵉ})
                (commutative-mul-ℤᵉ dxᵉ dzᵉ))
              (ap-mul-ℤᵉ (reflᵉ {xᵉ = nzᵉ}) (commutative-mul-ℤᵉ dxᵉ dyᵉ)))
        ＝ᵉ (nxᵉ *ℤᵉ (dyᵉ *ℤᵉ dzᵉ)) +ℤᵉ
            (((nyᵉ *ℤᵉ dzᵉ) *ℤᵉ dxᵉ) +ℤᵉ ((nzᵉ *ℤᵉ dyᵉ) *ℤᵉ dxᵉ))
          byᵉ ap-add-ℤᵉ
            (reflᵉ {xᵉ = nxᵉ *ℤᵉ (dyᵉ *ℤᵉ dzᵉ)})
            (invᵉ
              (ap-add-ℤᵉ
                ( associative-mul-ℤᵉ nyᵉ dzᵉ dxᵉ)
                ( associative-mul-ℤᵉ nzᵉ dyᵉ dxᵉ)))
        ＝ᵉ (nxᵉ *ℤᵉ (dyᵉ *ℤᵉ dzᵉ)) +ℤᵉ (((nyᵉ *ℤᵉ dzᵉ) +ℤᵉ (nzᵉ *ℤᵉ dyᵉ)) *ℤᵉ dxᵉ)
          byᵉ ap-add-ℤᵉ
            (reflᵉ {xᵉ = nxᵉ *ℤᵉ (dyᵉ *ℤᵉ dzᵉ)})
            (invᵉ (right-distributive-mul-add-ℤᵉ (nyᵉ *ℤᵉ dzᵉ) (nzᵉ *ℤᵉ dyᵉ) dxᵉ))
```

### Addition is commutative

```agda
abstract
  commutative-add-fraction-ℤᵉ :
    (xᵉ yᵉ : fraction-ℤᵉ) →
    sim-fraction-ℤᵉ
      (xᵉ +fraction-ℤᵉ yᵉ)
      (yᵉ +fraction-ℤᵉ xᵉ)
  commutative-add-fraction-ℤᵉ (nxᵉ ,ᵉ dxᵉ ,ᵉ dxpᵉ) (nyᵉ ,ᵉ dyᵉ ,ᵉ dypᵉ) =
    ap-mul-ℤᵉ
      ( commutative-add-ℤᵉ (nxᵉ *ℤᵉ dyᵉ) (nyᵉ *ℤᵉ dxᵉ))
      ( commutative-mul-ℤᵉ dyᵉ dxᵉ)
```

### The numerator of the sum of an integer fraction and its negative is zero

```agda
abstract
  is-zero-numerator-add-left-neg-fraction-ℤᵉ :
    (xᵉ : fraction-ℤᵉ) →
    is-zero-ℤᵉ (numerator-fraction-ℤᵉ (add-fraction-ℤᵉ (neg-fraction-ℤᵉ xᵉ) xᵉ))
  is-zero-numerator-add-left-neg-fraction-ℤᵉ (pᵉ ,ᵉ qᵉ ,ᵉ Hᵉ) =
    apᵉ (_+ℤᵉ (pᵉ *ℤᵉ qᵉ)) (left-negative-law-mul-ℤᵉ pᵉ qᵉ) ∙ᵉ
    left-inverse-law-add-ℤᵉ (pᵉ *ℤᵉ qᵉ)

  is-zero-numerator-add-right-neg-fraction-ℤᵉ :
    (xᵉ : fraction-ℤᵉ) →
    is-zero-ℤᵉ (numerator-fraction-ℤᵉ (add-fraction-ℤᵉ xᵉ (neg-fraction-ℤᵉ xᵉ)))
  is-zero-numerator-add-right-neg-fraction-ℤᵉ (pᵉ ,ᵉ qᵉ ,ᵉ Hᵉ) =
    apᵉ ((pᵉ *ℤᵉ qᵉ) +ℤᵉ_) (left-negative-law-mul-ℤᵉ pᵉ qᵉ) ∙ᵉ
    right-inverse-law-add-ℤᵉ (pᵉ *ℤᵉ qᵉ)
```

### Distributivity of negatives over addition on the integer fractions

```agda
abstract
  distributive-neg-add-fraction-ℤᵉ :
    (xᵉ yᵉ : fraction-ℤᵉ) →
    sim-fraction-ℤᵉ
      (neg-fraction-ℤᵉ (xᵉ +fraction-ℤᵉ yᵉ))
      (neg-fraction-ℤᵉ xᵉ +fraction-ℤᵉ neg-fraction-ℤᵉ yᵉ)
  distributive-neg-add-fraction-ℤᵉ (nxᵉ ,ᵉ dxᵉ ,ᵉ dxpᵉ) (nyᵉ ,ᵉ dyᵉ ,ᵉ dypᵉ) =
    apᵉ
      ( _*ℤᵉ (dxᵉ *ℤᵉ dyᵉ))
      ( ( distributive-neg-add-ℤᵉ (nxᵉ *ℤᵉ dyᵉ) (nyᵉ *ℤᵉ dxᵉ)) ∙ᵉ
        ( ap-add-ℤᵉ
          ( invᵉ (left-negative-law-mul-ℤᵉ nxᵉ dyᵉ))
          ( invᵉ (left-negative-law-mul-ℤᵉ nyᵉ dxᵉ))))
```