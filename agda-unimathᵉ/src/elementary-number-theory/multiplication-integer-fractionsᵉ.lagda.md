# Multiplication on integer fractions

```agda
module elementary-number-theory.multiplication-integer-fractionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractionsᵉ
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

**Multiplicationᵉ onᵉ integerᵉ fractions**ᵉ isᵉ anᵉ extensionᵉ ofᵉ theᵉ
[multiplicativeᵉ operation](elementary-number-theory.multiplication-integers.mdᵉ)
onᵉ theᵉ [integers](elementary-number-theory.integers.mdᵉ) to
[integerᵉ fractions](elementary-number-theory.integer-fractions.md).ᵉ Noteᵉ thatᵉ
theᵉ basicᵉ propertiesᵉ ofᵉ multiplicationᵉ onᵉ integerᵉ fractionᵉ onlyᵉ holdᵉ upᵉ to
fractionᵉ similarity.ᵉ

## Definition

```agda
mul-fraction-ℤᵉ : fraction-ℤᵉ → fraction-ℤᵉ → fraction-ℤᵉ
pr1ᵉ (mul-fraction-ℤᵉ (mᵉ ,ᵉ nᵉ ,ᵉ n-posᵉ) (m'ᵉ ,ᵉ n'ᵉ ,ᵉ n'-posᵉ)) =
  mᵉ *ℤᵉ m'ᵉ
pr1ᵉ (pr2ᵉ (mul-fraction-ℤᵉ (mᵉ ,ᵉ nᵉ ,ᵉ n-posᵉ) (m'ᵉ ,ᵉ n'ᵉ ,ᵉ n'-posᵉ))) =
  nᵉ *ℤᵉ n'ᵉ
pr2ᵉ (pr2ᵉ (mul-fraction-ℤᵉ (mᵉ ,ᵉ nᵉ ,ᵉ n-posᵉ) (m'ᵉ ,ᵉ n'ᵉ ,ᵉ n'-posᵉ))) =
  is-positive-mul-ℤᵉ n-posᵉ n'-posᵉ

mul-fraction-ℤ'ᵉ : fraction-ℤᵉ → fraction-ℤᵉ → fraction-ℤᵉ
mul-fraction-ℤ'ᵉ xᵉ yᵉ = mul-fraction-ℤᵉ yᵉ xᵉ

infixl 40 _*fraction-ℤᵉ_
_*fraction-ℤᵉ_ = mul-fraction-ℤᵉ

ap-mul-fraction-ℤᵉ :
  {xᵉ yᵉ x'ᵉ y'ᵉ : fraction-ℤᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ →
  xᵉ *fraction-ℤᵉ yᵉ ＝ᵉ x'ᵉ *fraction-ℤᵉ y'ᵉ
ap-mul-fraction-ℤᵉ pᵉ qᵉ = ap-binaryᵉ mul-fraction-ℤᵉ pᵉ qᵉ
```

## Properties

### Multiplication on integer fractions respects the similarity relation

```agda
sim-fraction-mul-fraction-ℤᵉ :
  {xᵉ x'ᵉ yᵉ y'ᵉ : fraction-ℤᵉ} →
  sim-fraction-ℤᵉ xᵉ x'ᵉ →
  sim-fraction-ℤᵉ yᵉ y'ᵉ →
  sim-fraction-ℤᵉ (xᵉ *fraction-ℤᵉ yᵉ) (x'ᵉ *fraction-ℤᵉ y'ᵉ)
sim-fraction-mul-fraction-ℤᵉ
  {(nxᵉ ,ᵉ dxᵉ ,ᵉ dxpᵉ)} {(nx'ᵉ ,ᵉ dx'ᵉ ,ᵉ dx'pᵉ)}
  {(nyᵉ ,ᵉ dyᵉ ,ᵉ dypᵉ)} {(ny'ᵉ ,ᵉ dy'ᵉ ,ᵉ dy'pᵉ)} pᵉ qᵉ =
  equational-reasoningᵉ
    (nxᵉ *ℤᵉ nyᵉ) *ℤᵉ (dx'ᵉ *ℤᵉ dy'ᵉ)
    ＝ᵉ (nxᵉ *ℤᵉ dx'ᵉ) *ℤᵉ (nyᵉ *ℤᵉ dy'ᵉ)
      byᵉ interchange-law-mul-mul-ℤᵉ nxᵉ nyᵉ dx'ᵉ dy'ᵉ
    ＝ᵉ (nx'ᵉ *ℤᵉ dxᵉ) *ℤᵉ (ny'ᵉ *ℤᵉ dyᵉ)
      byᵉ ap-mul-ℤᵉ pᵉ qᵉ
    ＝ᵉ (nx'ᵉ *ℤᵉ ny'ᵉ) *ℤᵉ (dxᵉ *ℤᵉ dyᵉ)
      byᵉ interchange-law-mul-mul-ℤᵉ nx'ᵉ dxᵉ ny'ᵉ dyᵉ
```

### Unit laws for multiplication on integer fractions

```agda
left-unit-law-mul-fraction-ℤᵉ :
  (kᵉ : fraction-ℤᵉ) →
  sim-fraction-ℤᵉ (mul-fraction-ℤᵉ one-fraction-ℤᵉ kᵉ) kᵉ
left-unit-law-mul-fraction-ℤᵉ kᵉ = reflᵉ

right-unit-law-mul-fraction-ℤᵉ :
  (kᵉ : fraction-ℤᵉ) →
  sim-fraction-ℤᵉ (mul-fraction-ℤᵉ kᵉ one-fraction-ℤᵉ) kᵉ
right-unit-law-mul-fraction-ℤᵉ (nᵉ ,ᵉ dᵉ ,ᵉ pᵉ) =
  ap-mul-ℤᵉ (right-unit-law-mul-ℤᵉ nᵉ) (invᵉ (right-unit-law-mul-ℤᵉ dᵉ))
```

### Multiplication on integer fractions is associative

```agda
associative-mul-fraction-ℤᵉ :
  (xᵉ yᵉ zᵉ : fraction-ℤᵉ) →
  sim-fraction-ℤᵉ
    (mul-fraction-ℤᵉ (mul-fraction-ℤᵉ xᵉ yᵉ) zᵉ)
    (mul-fraction-ℤᵉ xᵉ (mul-fraction-ℤᵉ yᵉ zᵉ))
associative-mul-fraction-ℤᵉ (nxᵉ ,ᵉ dxᵉ ,ᵉ dxpᵉ) (nyᵉ ,ᵉ dyᵉ ,ᵉ dypᵉ) (nzᵉ ,ᵉ dzᵉ ,ᵉ dzpᵉ) =
  ap-mul-ℤᵉ (associative-mul-ℤᵉ nxᵉ nyᵉ nzᵉ) (invᵉ (associative-mul-ℤᵉ dxᵉ dyᵉ dzᵉ))
```

### Multiplication on integer fractions is commutative

```agda
commutative-mul-fraction-ℤᵉ :
  (xᵉ yᵉ : fraction-ℤᵉ) → sim-fraction-ℤᵉ (xᵉ *fraction-ℤᵉ yᵉ) (yᵉ *fraction-ℤᵉ xᵉ)
commutative-mul-fraction-ℤᵉ (nxᵉ ,ᵉ dxᵉ ,ᵉ dxpᵉ) (nyᵉ ,ᵉ dyᵉ ,ᵉ dypᵉ) =
  ap-mul-ℤᵉ (commutative-mul-ℤᵉ nxᵉ nyᵉ) (commutative-mul-ℤᵉ dyᵉ dxᵉ)
```

### Multiplication on integer fractions distributes on the left over addition

```agda
left-distributive-mul-add-fraction-ℤᵉ :
  (xᵉ yᵉ zᵉ : fraction-ℤᵉ) →
  sim-fraction-ℤᵉ
    (mul-fraction-ℤᵉ xᵉ (add-fraction-ℤᵉ yᵉ zᵉ))
    (add-fraction-ℤᵉ (mul-fraction-ℤᵉ xᵉ yᵉ) (mul-fraction-ℤᵉ xᵉ zᵉ))
left-distributive-mul-add-fraction-ℤᵉ
  (nxᵉ ,ᵉ dxᵉ ,ᵉ dxpᵉ) (nyᵉ ,ᵉ dyᵉ ,ᵉ dypᵉ) (nzᵉ ,ᵉ dzᵉ ,ᵉ dzpᵉ) =
    ( apᵉ
      ( ( nxᵉ *ℤᵉ (nyᵉ *ℤᵉ dzᵉ +ℤᵉ nzᵉ *ℤᵉ dyᵉ)) *ℤᵉ_)
      ( ( interchange-law-mul-mul-ℤᵉ dxᵉ dyᵉ dxᵉ dzᵉ) ∙ᵉ
        ( associative-mul-ℤᵉ dxᵉ dxᵉ (dyᵉ *ℤᵉ dzᵉ)))) ∙ᵉ
    ( interchange-law-mul-mul-ℤᵉ
      ( nxᵉ)
      ( nyᵉ *ℤᵉ dzᵉ +ℤᵉ nzᵉ *ℤᵉ dyᵉ)
      ( dxᵉ)
      ( dxᵉ *ℤᵉ (dyᵉ *ℤᵉ dzᵉ))) ∙ᵉ
    ( invᵉ
      ( associative-mul-ℤᵉ
        ( nxᵉ *ℤᵉ dxᵉ)
        ( nyᵉ *ℤᵉ dzᵉ +ℤᵉ nzᵉ *ℤᵉ dyᵉ)
        ( dxᵉ *ℤᵉ (dyᵉ *ℤᵉ dzᵉ)))) ∙ᵉ
    ( apᵉ
      ( _*ℤᵉ (dxᵉ *ℤᵉ (dyᵉ *ℤᵉ dzᵉ)))
      ( ( left-distributive-mul-add-ℤᵉ
          ( nxᵉ *ℤᵉ dxᵉ)
          ( nyᵉ *ℤᵉ dzᵉ)
          ( nzᵉ *ℤᵉ dyᵉ)) ∙ᵉ
        ( ap-add-ℤᵉ
          ( interchange-law-mul-mul-ℤᵉ nxᵉ dxᵉ nyᵉ dzᵉ))
          ( interchange-law-mul-mul-ℤᵉ nxᵉ dxᵉ nzᵉ dyᵉ)))
```