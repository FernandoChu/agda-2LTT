# Divisibility of integers

```agda
module elementary-number-theory.divisibility-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integersᵉ
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.equality-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.multiplication-positive-and-negative-integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.nonpositive-integersᵉ
open import elementary-number-theory.nonzero-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositional-mapsᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ integerᵉ `m`ᵉ isᵉ saidᵉ to **divide**ᵉ anᵉ integerᵉ `n`ᵉ ifᵉ thereᵉ existsᵉ anᵉ integerᵉ
`k`ᵉ equippedᵉ with anᵉ identificationᵉ `kmᵉ ＝ᵉ n`.ᵉ Usingᵉ theᵉ Curry-Howardᵉ
interpretationᵉ ofᵉ logicᵉ intoᵉ typeᵉ theory,ᵉ weᵉ expressᵉ divisibilityᵉ asᵉ followsᵉ:

```text
  div-ℤᵉ mᵉ nᵉ :=ᵉ Σᵉ (kᵉ : ℤ),ᵉ kᵉ *ℤᵉ mᵉ ＝ᵉ n.ᵉ
```

Ifᵉ `n`ᵉ isᵉ aᵉ nonzeroᵉ integer,ᵉ thenᵉ `div-ℤᵉ mᵉ n`ᵉ isᵉ alwaysᵉ aᵉ propositionᵉ in theᵉ
senseᵉ thatᵉ theᵉ typeᵉ `div-ℤᵉ mᵉ n`ᵉ containsᵉ atᵉ mostᵉ oneᵉ element.ᵉ

Weᵉ alsoᵉ introduceᵉ **unitᵉ integers**,ᵉ whichᵉ areᵉ integersᵉ thatᵉ divideᵉ theᵉ integerᵉ
`1`,ᵉ andᵉ anᵉ equivalenceᵉ relationᵉ `sim-unit-ℤ`ᵉ onᵉ theᵉ integersᵉ in whichᵉ twoᵉ
integersᵉ `x`ᵉ andᵉ `y`ᵉ areᵉ equivalentᵉ ifᵉ thereᵉ existsᵉ aᵉ unitᵉ integerᵉ `u`ᵉ suchᵉ thatᵉ
`uxᵉ ＝ᵉ y`.ᵉ Theseᵉ twoᵉ conceptsᵉ helpᵉ establishᵉ furtherᵉ propertiesᵉ ofᵉ theᵉ
divisibilityᵉ relationᵉ onᵉ theᵉ integers.ᵉ

## Definitions

```agda
div-ℤᵉ : ℤᵉ → ℤᵉ → UUᵉ lzero
div-ℤᵉ dᵉ xᵉ = Σᵉ ℤᵉ (λ kᵉ → kᵉ *ℤᵉ dᵉ ＝ᵉ xᵉ)

quotient-div-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → div-ℤᵉ xᵉ yᵉ → ℤᵉ
quotient-div-ℤᵉ xᵉ yᵉ Hᵉ = pr1ᵉ Hᵉ

eq-quotient-div-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) (Hᵉ : div-ℤᵉ xᵉ yᵉ) → (quotient-div-ℤᵉ xᵉ yᵉ Hᵉ) *ℤᵉ xᵉ ＝ᵉ yᵉ
eq-quotient-div-ℤᵉ xᵉ yᵉ Hᵉ = pr2ᵉ Hᵉ

eq-quotient-div-ℤ'ᵉ :
  (xᵉ yᵉ : ℤᵉ) (Hᵉ : div-ℤᵉ xᵉ yᵉ) → xᵉ *ℤᵉ (quotient-div-ℤᵉ xᵉ yᵉ Hᵉ) ＝ᵉ yᵉ
eq-quotient-div-ℤ'ᵉ xᵉ yᵉ Hᵉ =
  commutative-mul-ℤᵉ xᵉ (quotient-div-ℤᵉ xᵉ yᵉ Hᵉ) ∙ᵉ eq-quotient-div-ℤᵉ xᵉ yᵉ Hᵉ

div-quotient-div-ℤᵉ :
  (dᵉ xᵉ : ℤᵉ) (Hᵉ : div-ℤᵉ dᵉ xᵉ) → div-ℤᵉ (quotient-div-ℤᵉ dᵉ xᵉ Hᵉ) xᵉ
pr1ᵉ (div-quotient-div-ℤᵉ dᵉ xᵉ (uᵉ ,ᵉ pᵉ)) = dᵉ
pr2ᵉ (div-quotient-div-ℤᵉ dᵉ xᵉ (uᵉ ,ᵉ pᵉ)) = commutative-mul-ℤᵉ dᵉ uᵉ ∙ᵉ pᵉ

concatenate-eq-div-ℤᵉ :
  {xᵉ yᵉ zᵉ : ℤᵉ} → xᵉ ＝ᵉ yᵉ → div-ℤᵉ yᵉ zᵉ → div-ℤᵉ xᵉ zᵉ
concatenate-eq-div-ℤᵉ reflᵉ pᵉ = pᵉ

concatenate-div-eq-ℤᵉ :
  {xᵉ yᵉ zᵉ : ℤᵉ} → div-ℤᵉ xᵉ yᵉ → yᵉ ＝ᵉ zᵉ → div-ℤᵉ xᵉ zᵉ
concatenate-div-eq-ℤᵉ pᵉ reflᵉ = pᵉ

concatenate-eq-div-eq-ℤᵉ :
  {xᵉ yᵉ zᵉ wᵉ : ℤᵉ} → xᵉ ＝ᵉ yᵉ → div-ℤᵉ yᵉ zᵉ → zᵉ ＝ᵉ wᵉ → div-ℤᵉ xᵉ wᵉ
concatenate-eq-div-eq-ℤᵉ reflᵉ pᵉ reflᵉ = pᵉ
```

### Unit integers

```agda
is-unit-ℤᵉ : ℤᵉ → UUᵉ lzero
is-unit-ℤᵉ xᵉ = div-ℤᵉ xᵉ one-ℤᵉ

unit-ℤᵉ : UUᵉ lzero
unit-ℤᵉ = Σᵉ ℤᵉ is-unit-ℤᵉ

int-unit-ℤᵉ : unit-ℤᵉ → ℤᵉ
int-unit-ℤᵉ = pr1ᵉ

is-unit-int-unit-ℤᵉ : (xᵉ : unit-ℤᵉ) → is-unit-ℤᵉ (int-unit-ℤᵉ xᵉ)
is-unit-int-unit-ℤᵉ = pr2ᵉ

div-is-unit-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → is-unit-ℤᵉ xᵉ → div-ℤᵉ xᵉ yᵉ
pr1ᵉ (div-is-unit-ℤᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) = yᵉ *ℤᵉ dᵉ
pr2ᵉ (div-is-unit-ℤᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) =
  associative-mul-ℤᵉ yᵉ dᵉ xᵉ ∙ᵉ (apᵉ (yᵉ *ℤᵉ_) pᵉ ∙ᵉ right-unit-law-mul-ℤᵉ yᵉ)
```

### The equivalence relation `sim-unit-ℤ`

Weᵉ defineᵉ theᵉ equivalenceᵉ relationᵉ `sim-unit-ℤ`ᵉ in suchᵉ aᵉ wayᵉ thatᵉ
`sim-unit-ℤᵉ xᵉ y`ᵉ isᵉ alwaysᵉ aᵉ proposition.ᵉ

```agda
presim-unit-ℤᵉ : ℤᵉ → ℤᵉ → UUᵉ lzero
presim-unit-ℤᵉ xᵉ yᵉ = Σᵉ unit-ℤᵉ (λ uᵉ → (pr1ᵉ uᵉ) *ℤᵉ xᵉ ＝ᵉ yᵉ)

sim-unit-ℤᵉ : ℤᵉ → ℤᵉ → UUᵉ lzero
sim-unit-ℤᵉ xᵉ yᵉ = ¬ᵉ (is-zero-ℤᵉ xᵉ ×ᵉ is-zero-ℤᵉ yᵉ) → presim-unit-ℤᵉ xᵉ yᵉ
```

## Properties

### Divisibility by a nonzero integer is a property

```agda
is-prop-div-ℤᵉ : (dᵉ xᵉ : ℤᵉ) → is-nonzero-ℤᵉ dᵉ → is-propᵉ (div-ℤᵉ dᵉ xᵉ)
is-prop-div-ℤᵉ dᵉ xᵉ fᵉ = is-prop-map-is-embᵉ (is-emb-right-mul-ℤᵉ dᵉ fᵉ) xᵉ
```

### The divisibility relation is a preorder

Noteᵉ thatᵉ theᵉ divisibilityᵉ relationᵉ onᵉ theᵉ integersᵉ isᵉ notᵉ antisymmetric.ᵉ

```agda
refl-div-ℤᵉ : is-reflexiveᵉ div-ℤᵉ
pr1ᵉ (refl-div-ℤᵉ xᵉ) = one-ℤᵉ
pr2ᵉ (refl-div-ℤᵉ xᵉ) = left-unit-law-mul-ℤᵉ xᵉ

transitive-div-ℤᵉ : is-transitiveᵉ div-ℤᵉ
pr1ᵉ (transitive-div-ℤᵉ xᵉ yᵉ zᵉ (pairᵉ eᵉ qᵉ) (pairᵉ dᵉ pᵉ)) = eᵉ *ℤᵉ dᵉ
pr2ᵉ (transitive-div-ℤᵉ xᵉ yᵉ zᵉ (pairᵉ eᵉ qᵉ) (pairᵉ dᵉ pᵉ)) =
  ( associative-mul-ℤᵉ eᵉ dᵉ xᵉ) ∙ᵉ
    ( ( apᵉ (eᵉ *ℤᵉ_) pᵉ) ∙ᵉ
      ( qᵉ))
```

### Every integer is divisible by `1`

```agda
div-one-ℤᵉ : (xᵉ : ℤᵉ) → div-ℤᵉ one-ℤᵉ xᵉ
pr1ᵉ (div-one-ℤᵉ xᵉ) = xᵉ
pr2ᵉ (div-one-ℤᵉ xᵉ) = right-unit-law-mul-ℤᵉ xᵉ
```

### Every integer divides `0`

```agda
div-zero-ℤᵉ : (xᵉ : ℤᵉ) → div-ℤᵉ xᵉ zero-ℤᵉ
pr1ᵉ (div-zero-ℤᵉ xᵉ) = zero-ℤᵉ
pr2ᵉ (div-zero-ℤᵉ xᵉ) = left-zero-law-mul-ℤᵉ xᵉ
```

### Every integer that is divisible by `0` is `0`

```agda
is-zero-div-zero-ℤᵉ :
  (xᵉ : ℤᵉ) → div-ℤᵉ zero-ℤᵉ xᵉ → is-zero-ℤᵉ xᵉ
is-zero-div-zero-ℤᵉ xᵉ (pairᵉ dᵉ pᵉ) = invᵉ pᵉ ∙ᵉ right-zero-law-mul-ℤᵉ dᵉ
```

### The quotient of `x` by one is `x`

```agda
eq-quotient-div-is-one-ℤᵉ :
  (kᵉ xᵉ : ℤᵉ) → is-one-ℤᵉ kᵉ → (Hᵉ : div-ℤᵉ kᵉ xᵉ) → quotient-div-ℤᵉ kᵉ xᵉ Hᵉ ＝ᵉ xᵉ
eq-quotient-div-is-one-ℤᵉ .one-ℤᵉ xᵉ reflᵉ Hᵉ =
  apᵉ
    ( quotient-div-ℤᵉ one-ℤᵉ xᵉ)
    ( invᵉ
      ( eq-is-prop'ᵉ
        ( is-prop-div-ℤᵉ one-ℤᵉ xᵉ (λ ()))
        ( div-one-ℤᵉ xᵉ)
        ( Hᵉ)))
```

### If `k` divides `x` and `k` is `0` then `x` is `0`

```agda
is-zero-is-zero-div-ℤᵉ : (xᵉ kᵉ : ℤᵉ) → div-ℤᵉ kᵉ xᵉ → is-zero-ℤᵉ kᵉ → is-zero-ℤᵉ xᵉ
is-zero-is-zero-div-ℤᵉ xᵉ .zero-ℤᵉ k-div-xᵉ reflᵉ = is-zero-div-zero-ℤᵉ xᵉ k-div-xᵉ
```

### If `x` divides both `y` and `z`, then it divides `y + z`

```agda
div-add-ℤᵉ : (xᵉ yᵉ zᵉ : ℤᵉ) → div-ℤᵉ xᵉ yᵉ → div-ℤᵉ xᵉ zᵉ → div-ℤᵉ xᵉ (yᵉ +ℤᵉ zᵉ)
pr1ᵉ (div-add-ℤᵉ xᵉ yᵉ zᵉ (pairᵉ dᵉ pᵉ) (pairᵉ eᵉ qᵉ)) = dᵉ +ℤᵉ eᵉ
pr2ᵉ (div-add-ℤᵉ xᵉ yᵉ zᵉ (pairᵉ dᵉ pᵉ) (pairᵉ eᵉ qᵉ)) =
  ( right-distributive-mul-add-ℤᵉ dᵉ eᵉ xᵉ) ∙ᵉ
  ( ap-add-ℤᵉ pᵉ qᵉ)
```

### If `x` divides `y` then `x` divides any multiple of `y`

```agda
div-mul-ℤᵉ :
  (kᵉ xᵉ yᵉ : ℤᵉ) → div-ℤᵉ xᵉ yᵉ → div-ℤᵉ xᵉ (kᵉ *ℤᵉ yᵉ)
div-mul-ℤᵉ kᵉ xᵉ yᵉ = transitive-div-ℤᵉ xᵉ yᵉ (kᵉ *ℤᵉ yᵉ) (kᵉ ,ᵉ reflᵉ)
```

### If `x` divides `y` then it divides `-y`

```agda
div-neg-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → div-ℤᵉ xᵉ yᵉ → div-ℤᵉ xᵉ (neg-ℤᵉ yᵉ)
pr1ᵉ (div-neg-ℤᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) = neg-ℤᵉ dᵉ
pr2ᵉ (div-neg-ℤᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) = left-negative-law-mul-ℤᵉ dᵉ xᵉ ∙ᵉ apᵉ neg-ℤᵉ pᵉ
```

### If `x` divides `y` then `-x` divides `y`

```agda
neg-div-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → div-ℤᵉ xᵉ yᵉ → div-ℤᵉ (neg-ℤᵉ xᵉ) yᵉ
pr1ᵉ (neg-div-ℤᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) = neg-ℤᵉ dᵉ
pr2ᵉ (neg-div-ℤᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) =
  equational-reasoningᵉ
    (neg-ℤᵉ dᵉ) *ℤᵉ (neg-ℤᵉ xᵉ)
    ＝ᵉ neg-ℤᵉ (dᵉ *ℤᵉ (neg-ℤᵉ xᵉ))
      byᵉ left-negative-law-mul-ℤᵉ dᵉ (neg-ℤᵉ xᵉ)
    ＝ᵉ neg-ℤᵉ (neg-ℤᵉ (dᵉ *ℤᵉ xᵉ))
      byᵉ apᵉ neg-ℤᵉ (right-negative-law-mul-ℤᵉ dᵉ xᵉ)
    ＝ᵉ (dᵉ *ℤᵉ xᵉ)
      byᵉ neg-neg-ℤᵉ (dᵉ *ℤᵉ xᵉ)
    ＝ᵉ yᵉ
      byᵉ pᵉ
```

### Multiplication preserves divisibility

```agda
preserves-div-mul-ℤᵉ :
  (kᵉ xᵉ yᵉ : ℤᵉ) → div-ℤᵉ xᵉ yᵉ → div-ℤᵉ (kᵉ *ℤᵉ xᵉ) (kᵉ *ℤᵉ yᵉ)
pr1ᵉ (preserves-div-mul-ℤᵉ kᵉ xᵉ yᵉ (pairᵉ qᵉ pᵉ)) = qᵉ
pr2ᵉ (preserves-div-mul-ℤᵉ kᵉ xᵉ yᵉ (pairᵉ qᵉ pᵉ)) =
  ( invᵉ (associative-mul-ℤᵉ qᵉ kᵉ xᵉ)) ∙ᵉ
    ( ( apᵉ (_*ℤᵉ xᵉ) (commutative-mul-ℤᵉ qᵉ kᵉ)) ∙ᵉ
      ( ( associative-mul-ℤᵉ kᵉ qᵉ xᵉ) ∙ᵉ
        ( apᵉ (kᵉ *ℤᵉ_) pᵉ)))
```

### Multiplication by a nonzero number reflects divisibility

```agda
reflects-div-mul-ℤᵉ :
  (kᵉ xᵉ yᵉ : ℤᵉ) → is-nonzero-ℤᵉ kᵉ → div-ℤᵉ (kᵉ *ℤᵉ xᵉ) (kᵉ *ℤᵉ yᵉ) → div-ℤᵉ xᵉ yᵉ
pr1ᵉ (reflects-div-mul-ℤᵉ kᵉ xᵉ yᵉ Hᵉ (pairᵉ qᵉ pᵉ)) = qᵉ
pr2ᵉ (reflects-div-mul-ℤᵉ kᵉ xᵉ yᵉ Hᵉ (pairᵉ qᵉ pᵉ)) =
  is-injective-left-mul-ℤᵉ kᵉ Hᵉ
    ( ( invᵉ (associative-mul-ℤᵉ kᵉ qᵉ xᵉ)) ∙ᵉ
      ( ( apᵉ (_*ℤᵉ xᵉ) (commutative-mul-ℤᵉ kᵉ qᵉ)) ∙ᵉ
        ( ( associative-mul-ℤᵉ qᵉ kᵉ xᵉ) ∙ᵉ
          ( pᵉ))))
```

### If a nonzero number `d` divides `y`, then `dx` divides `y` if and only if `x` divides the quotient `y/d`

```agda
div-quotient-div-div-ℤᵉ :
  (xᵉ yᵉ dᵉ : ℤᵉ) (Hᵉ : div-ℤᵉ dᵉ yᵉ) → is-nonzero-ℤᵉ dᵉ →
  div-ℤᵉ (dᵉ *ℤᵉ xᵉ) yᵉ → div-ℤᵉ xᵉ (quotient-div-ℤᵉ dᵉ yᵉ Hᵉ)
div-quotient-div-div-ℤᵉ xᵉ yᵉ dᵉ Hᵉ fᵉ Kᵉ =
  reflects-div-mul-ℤᵉ dᵉ xᵉ
    ( quotient-div-ℤᵉ dᵉ yᵉ Hᵉ)
    ( fᵉ)
    ( trᵉ (div-ℤᵉ (dᵉ *ℤᵉ xᵉ)) (invᵉ (eq-quotient-div-ℤ'ᵉ dᵉ yᵉ Hᵉ)) Kᵉ)

div-div-quotient-div-ℤᵉ :
  (xᵉ yᵉ dᵉ : ℤᵉ) (Hᵉ : div-ℤᵉ dᵉ yᵉ) →
  div-ℤᵉ xᵉ (quotient-div-ℤᵉ dᵉ yᵉ Hᵉ) → div-ℤᵉ (dᵉ *ℤᵉ xᵉ) yᵉ
div-div-quotient-div-ℤᵉ xᵉ yᵉ dᵉ Hᵉ Kᵉ =
  trᵉ
    ( div-ℤᵉ (dᵉ *ℤᵉ xᵉ))
    ( eq-quotient-div-ℤ'ᵉ dᵉ yᵉ Hᵉ)
    ( preserves-div-mul-ℤᵉ dᵉ xᵉ (quotient-div-ℤᵉ dᵉ yᵉ Hᵉ) Kᵉ)
```

### Comparison of divisibility on `ℕ` and on `ℤ`

```agda
div-int-div-ℕᵉ :
  {xᵉ yᵉ : ℕᵉ} → div-ℕᵉ xᵉ yᵉ → div-ℤᵉ (int-ℕᵉ xᵉ) (int-ℕᵉ yᵉ)
pr1ᵉ (div-int-div-ℕᵉ {xᵉ} {yᵉ} (pairᵉ dᵉ pᵉ)) = int-ℕᵉ dᵉ
pr2ᵉ (div-int-div-ℕᵉ {xᵉ} {yᵉ} (pairᵉ dᵉ pᵉ)) = mul-int-ℕᵉ dᵉ xᵉ ∙ᵉ apᵉ int-ℕᵉ pᵉ

div-div-int-ℕᵉ :
  {xᵉ yᵉ : ℕᵉ} → div-ℤᵉ (int-ℕᵉ xᵉ) (int-ℕᵉ yᵉ) → div-ℕᵉ xᵉ yᵉ
div-div-int-ℕᵉ {zero-ℕᵉ} {yᵉ} (pairᵉ dᵉ pᵉ) =
  div-eq-ℕᵉ zero-ℕᵉ yᵉ
    ( invᵉ (is-injective-int-ℕᵉ (is-zero-div-zero-ℤᵉ (int-ℕᵉ yᵉ) (pairᵉ dᵉ pᵉ))))
pr1ᵉ (div-div-int-ℕᵉ {succ-ℕᵉ xᵉ} {yᵉ} (pairᵉ dᵉ pᵉ)) = abs-ℤᵉ dᵉ
pr2ᵉ (div-div-int-ℕᵉ {succ-ℕᵉ xᵉ} {yᵉ} (pairᵉ dᵉ pᵉ)) =
  is-injective-int-ℕᵉ
    ( ( invᵉ (mul-int-ℕᵉ (abs-ℤᵉ dᵉ) (succ-ℕᵉ xᵉ))) ∙ᵉ
      ( ( apᵉ
          ( _*ℤᵉ (inrᵉ (inrᵉ xᵉ)))
          { int-abs-ℤᵉ dᵉ}
          { dᵉ}
          ( int-abs-is-nonnegative-ℤᵉ dᵉ
            ( is-nonnegative-left-factor-mul-ℤᵉ
              { dᵉ}
              { inrᵉ (inrᵉ xᵉ)}
              ( is-nonnegative-eq-ℤᵉ (invᵉ pᵉ) (is-nonnegative-int-ℕᵉ yᵉ))
              ( starᵉ)))) ∙ᵉ
        ( pᵉ)))
```

### An integer is a unit if and only if it is `1` or `-1`

```agda
is-one-or-neg-one-ℤᵉ : ℤᵉ → UUᵉ lzero
is-one-or-neg-one-ℤᵉ xᵉ = (is-one-ℤᵉ xᵉ) +ᵉ (is-neg-one-ℤᵉ xᵉ)

is-unit-one-ℤᵉ : is-unit-ℤᵉ one-ℤᵉ
is-unit-one-ℤᵉ = refl-div-ℤᵉ one-ℤᵉ

one-unit-ℤᵉ : unit-ℤᵉ
pr1ᵉ one-unit-ℤᵉ = one-ℤᵉ
pr2ᵉ one-unit-ℤᵉ = is-unit-one-ℤᵉ

is-unit-is-one-ℤᵉ :
  (xᵉ : ℤᵉ) → is-one-ℤᵉ xᵉ → is-unit-ℤᵉ xᵉ
is-unit-is-one-ℤᵉ .one-ℤᵉ reflᵉ = is-unit-one-ℤᵉ

is-unit-neg-one-ℤᵉ : is-unit-ℤᵉ neg-one-ℤᵉ
pr1ᵉ is-unit-neg-one-ℤᵉ = neg-one-ℤᵉ
pr2ᵉ is-unit-neg-one-ℤᵉ = reflᵉ

neg-one-unit-ℤᵉ : unit-ℤᵉ
pr1ᵉ neg-one-unit-ℤᵉ = neg-one-ℤᵉ
pr2ᵉ neg-one-unit-ℤᵉ = is-unit-neg-one-ℤᵉ

is-unit-is-neg-one-ℤᵉ :
  (xᵉ : ℤᵉ) → is-neg-one-ℤᵉ xᵉ → is-unit-ℤᵉ xᵉ
is-unit-is-neg-one-ℤᵉ .neg-one-ℤᵉ reflᵉ = is-unit-neg-one-ℤᵉ

is-unit-is-one-or-neg-one-ℤᵉ :
  (xᵉ : ℤᵉ) → is-one-or-neg-one-ℤᵉ xᵉ → is-unit-ℤᵉ xᵉ
is-unit-is-one-or-neg-one-ℤᵉ xᵉ (inlᵉ pᵉ) = is-unit-is-one-ℤᵉ xᵉ pᵉ
is-unit-is-one-or-neg-one-ℤᵉ xᵉ (inrᵉ pᵉ) = is-unit-is-neg-one-ℤᵉ xᵉ pᵉ

is-one-or-neg-one-is-unit-ℤᵉ :
  (xᵉ : ℤᵉ) → is-unit-ℤᵉ xᵉ → is-one-or-neg-one-ℤᵉ xᵉ
is-one-or-neg-one-is-unit-ℤᵉ (inlᵉ zero-ℕᵉ) (pairᵉ dᵉ pᵉ) = inrᵉ reflᵉ
is-one-or-neg-one-is-unit-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) (pairᵉ (inlᵉ zero-ℕᵉ) pᵉ) =
  ex-falsoᵉ (Eq-eq-ℤᵉ (invᵉ pᵉ ∙ᵉ compute-mul-ℤᵉ neg-one-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ))))
is-one-or-neg-one-is-unit-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) (pairᵉ (inlᵉ (succ-ℕᵉ dᵉ)) pᵉ) =
  ex-falsoᵉ (Eq-eq-ℤᵉ (invᵉ pᵉ ∙ᵉ compute-mul-ℤᵉ (inlᵉ (succ-ℕᵉ dᵉ)) (inlᵉ (succ-ℕᵉ xᵉ))))
is-one-or-neg-one-is-unit-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) (pairᵉ (inrᵉ (inlᵉ starᵉ)) pᵉ) =
  ex-falsoᵉ (Eq-eq-ℤᵉ (invᵉ pᵉ ∙ᵉ compute-mul-ℤᵉ zero-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ))))
is-one-or-neg-one-is-unit-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) (pairᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) pᵉ) =
  ex-falsoᵉ (Eq-eq-ℤᵉ (invᵉ pᵉ ∙ᵉ compute-mul-ℤᵉ one-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ))))
is-one-or-neg-one-is-unit-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) (pairᵉ (inrᵉ (inrᵉ (succ-ℕᵉ dᵉ))) pᵉ) =
  ex-falsoᵉ
    ( Eq-eq-ℤᵉ (invᵉ pᵉ ∙ᵉ compute-mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ dᵉ))) (inlᵉ (succ-ℕᵉ xᵉ))))
is-one-or-neg-one-is-unit-ℤᵉ (inrᵉ (inlᵉ starᵉ)) (pairᵉ dᵉ pᵉ) =
  ex-falsoᵉ (Eq-eq-ℤᵉ (invᵉ (right-zero-law-mul-ℤᵉ dᵉ) ∙ᵉ pᵉ))
is-one-or-neg-one-is-unit-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) (pairᵉ dᵉ pᵉ) = inlᵉ reflᵉ
is-one-or-neg-one-is-unit-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) (pairᵉ (inlᵉ zero-ℕᵉ) pᵉ) =
  ex-falsoᵉ (Eq-eq-ℤᵉ (invᵉ pᵉ ∙ᵉ compute-mul-ℤᵉ neg-one-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ)))))
is-one-or-neg-one-is-unit-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) (pairᵉ (inlᵉ (succ-ℕᵉ dᵉ)) pᵉ) =
  ex-falsoᵉ
    ( Eq-eq-ℤᵉ (invᵉ pᵉ ∙ᵉ compute-mul-ℤᵉ (inlᵉ (succ-ℕᵉ dᵉ)) (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ)))))
is-one-or-neg-one-is-unit-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) (pairᵉ (inrᵉ (inlᵉ starᵉ)) pᵉ) =
  ex-falsoᵉ (Eq-eq-ℤᵉ (invᵉ pᵉ ∙ᵉ compute-mul-ℤᵉ zero-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ)))))
is-one-or-neg-one-is-unit-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) (pairᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) pᵉ) =
  ex-falsoᵉ (Eq-eq-ℤᵉ (invᵉ pᵉ ∙ᵉ compute-mul-ℤᵉ one-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ)))))
is-one-or-neg-one-is-unit-ℤᵉ
  (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) (pairᵉ (inrᵉ (inrᵉ (succ-ℕᵉ dᵉ))) pᵉ) =
  ex-falsoᵉ
    ( Eq-eq-ℤᵉ
      ( invᵉ pᵉ ∙ᵉ compute-mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ dᵉ))) (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ)))))
```

### Units are idempotent

```agda
idempotent-is-unit-ℤᵉ : {xᵉ : ℤᵉ} → is-unit-ℤᵉ xᵉ → xᵉ *ℤᵉ xᵉ ＝ᵉ one-ℤᵉ
idempotent-is-unit-ℤᵉ {xᵉ} Hᵉ =
  fᵉ (is-one-or-neg-one-is-unit-ℤᵉ xᵉ Hᵉ)
  where
  fᵉ : is-one-or-neg-one-ℤᵉ xᵉ → xᵉ *ℤᵉ xᵉ ＝ᵉ one-ℤᵉ
  fᵉ (inlᵉ reflᵉ) = reflᵉ
  fᵉ (inrᵉ reflᵉ) = reflᵉ

abstract
  is-one-is-unit-int-ℕᵉ : (xᵉ : ℕᵉ) → is-unit-ℤᵉ (int-ℕᵉ xᵉ) → is-one-ℕᵉ xᵉ
  is-one-is-unit-int-ℕᵉ xᵉ Hᵉ with is-one-or-neg-one-is-unit-ℤᵉ (int-ℕᵉ xᵉ) Hᵉ
  ... | inlᵉ pᵉ = is-injective-int-ℕᵉ pᵉ
  ... | inrᵉ pᵉ = ex-falsoᵉ (trᵉ is-nonnegative-ℤᵉ pᵉ (is-nonnegative-int-ℕᵉ xᵉ))
```

### The product `xy` is a unit if and only if both `x` and `y` are units

```agda
is-unit-mul-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → is-unit-ℤᵉ xᵉ → is-unit-ℤᵉ yᵉ → is-unit-ℤᵉ (xᵉ *ℤᵉ yᵉ)
pr1ᵉ (is-unit-mul-ℤᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ) (pairᵉ eᵉ qᵉ)) = eᵉ *ℤᵉ dᵉ
pr2ᵉ (is-unit-mul-ℤᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ) (pairᵉ eᵉ qᵉ)) =
  ( associative-mul-ℤᵉ eᵉ dᵉ (xᵉ *ℤᵉ yᵉ)) ∙ᵉ
    ( ( apᵉ
        ( eᵉ *ℤᵉ_)
        ( ( invᵉ (associative-mul-ℤᵉ dᵉ xᵉ yᵉ)) ∙ᵉ
          ( apᵉ (_*ℤᵉ yᵉ) pᵉ))) ∙ᵉ
      ( qᵉ))

mul-unit-ℤᵉ : unit-ℤᵉ → unit-ℤᵉ → unit-ℤᵉ
pr1ᵉ (mul-unit-ℤᵉ (pairᵉ xᵉ Hᵉ) (pairᵉ yᵉ Kᵉ)) = xᵉ *ℤᵉ yᵉ
pr2ᵉ (mul-unit-ℤᵉ (pairᵉ xᵉ Hᵉ) (pairᵉ yᵉ Kᵉ)) = is-unit-mul-ℤᵉ xᵉ yᵉ Hᵉ Kᵉ

is-unit-left-factor-mul-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → is-unit-ℤᵉ (xᵉ *ℤᵉ yᵉ) → is-unit-ℤᵉ xᵉ
pr1ᵉ (is-unit-left-factor-mul-ℤᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) = dᵉ *ℤᵉ yᵉ
pr2ᵉ (is-unit-left-factor-mul-ℤᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) =
  associative-mul-ℤᵉ dᵉ yᵉ xᵉ ∙ᵉ (apᵉ (dᵉ *ℤᵉ_) (commutative-mul-ℤᵉ yᵉ xᵉ) ∙ᵉ pᵉ)

is-unit-right-factor-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → is-unit-ℤᵉ (xᵉ *ℤᵉ yᵉ) → is-unit-ℤᵉ yᵉ
is-unit-right-factor-ℤᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ) =
  is-unit-left-factor-mul-ℤᵉ yᵉ xᵉ
    ( pairᵉ dᵉ (apᵉ (dᵉ *ℤᵉ_) (commutative-mul-ℤᵉ yᵉ xᵉ) ∙ᵉ pᵉ))
```

### The relations `presim-unit-ℤ` and `sim-unit-ℤ` are logically equivalent

```agda
sim-unit-presim-unit-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → presim-unit-ℤᵉ xᵉ yᵉ → sim-unit-ℤᵉ xᵉ yᵉ
sim-unit-presim-unit-ℤᵉ {xᵉ} {yᵉ} Hᵉ fᵉ = Hᵉ

presim-unit-sim-unit-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → sim-unit-ℤᵉ xᵉ yᵉ → presim-unit-ℤᵉ xᵉ yᵉ
presim-unit-sim-unit-ℤᵉ {inlᵉ xᵉ} {inlᵉ yᵉ} Hᵉ = Hᵉ (λ tᵉ → Eq-eq-ℤᵉ (pr1ᵉ tᵉ))
presim-unit-sim-unit-ℤᵉ {inlᵉ xᵉ} {inrᵉ yᵉ} Hᵉ = Hᵉ (λ tᵉ → Eq-eq-ℤᵉ (pr1ᵉ tᵉ))
presim-unit-sim-unit-ℤᵉ {inrᵉ xᵉ} {inlᵉ yᵉ} Hᵉ = Hᵉ (λ tᵉ → Eq-eq-ℤᵉ (pr2ᵉ tᵉ))
pr1ᵉ (presim-unit-sim-unit-ℤᵉ {inrᵉ (inlᵉ starᵉ)} {inrᵉ (inlᵉ starᵉ)} Hᵉ) = one-unit-ℤᵉ
pr2ᵉ (presim-unit-sim-unit-ℤᵉ {inrᵉ (inlᵉ starᵉ)} {inrᵉ (inlᵉ starᵉ)} Hᵉ) = reflᵉ
presim-unit-sim-unit-ℤᵉ {inrᵉ (inlᵉ starᵉ)} {inrᵉ (inrᵉ yᵉ)} Hᵉ =
  Hᵉ (λ tᵉ → Eq-eq-ℤᵉ (pr2ᵉ tᵉ))
presim-unit-sim-unit-ℤᵉ {inrᵉ (inrᵉ xᵉ)} {inrᵉ (inlᵉ starᵉ)} Hᵉ =
  Hᵉ (λ tᵉ → Eq-eq-ℤᵉ (pr1ᵉ tᵉ))
presim-unit-sim-unit-ℤᵉ {inrᵉ (inrᵉ xᵉ)} {inrᵉ (inrᵉ yᵉ)} Hᵉ =
  Hᵉ (λ tᵉ → Eq-eq-ℤᵉ (pr1ᵉ tᵉ))
```

### The relations `presim-unit-ℤ` and `sim-unit-ℤ` relate `zero-ℤ` only to itself

```agda
is-nonzero-presim-unit-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → presim-unit-ℤᵉ xᵉ yᵉ → is-nonzero-ℤᵉ xᵉ → is-nonzero-ℤᵉ yᵉ
is-nonzero-presim-unit-ℤᵉ {xᵉ} {yᵉ} (pairᵉ (pairᵉ vᵉ (pairᵉ uᵉ αᵉ)) βᵉ) fᵉ pᵉ =
  Eq-eq-ℤᵉ (apᵉ (_*ℤᵉ uᵉ) (invᵉ qᵉ) ∙ᵉ (commutative-mul-ℤᵉ vᵉ uᵉ ∙ᵉ αᵉ))
  where
  qᵉ : is-zero-ℤᵉ vᵉ
  qᵉ = is-injective-right-mul-ℤᵉ xᵉ fᵉ {vᵉ} {zero-ℤᵉ} (βᵉ ∙ᵉ pᵉ)

is-nonzero-sim-unit-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → sim-unit-ℤᵉ xᵉ yᵉ → is-nonzero-ℤᵉ xᵉ → is-nonzero-ℤᵉ yᵉ
is-nonzero-sim-unit-ℤᵉ Hᵉ fᵉ =
  is-nonzero-presim-unit-ℤᵉ (Hᵉ (fᵉ ∘ᵉ pr1ᵉ)) fᵉ

is-zero-sim-unit-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → sim-unit-ℤᵉ xᵉ yᵉ → is-zero-ℤᵉ xᵉ → is-zero-ℤᵉ yᵉ
is-zero-sim-unit-ℤᵉ {xᵉ} {yᵉ} Hᵉ pᵉ =
  double-negation-elim-is-decidableᵉ
    ( has-decidable-equality-ℤᵉ yᵉ zero-ℤᵉ)
    ( λ gᵉ → gᵉ (invᵉ (βᵉ gᵉ) ∙ᵉ (apᵉ ((uᵉ gᵉ) *ℤᵉ_) pᵉ ∙ᵉ right-zero-law-mul-ℤᵉ (uᵉ gᵉ))))
  where
  Kᵉ : is-nonzero-ℤᵉ yᵉ → presim-unit-ℤᵉ xᵉ yᵉ
  Kᵉ gᵉ = Hᵉ (λ (uᵉ ,ᵉ vᵉ) → gᵉ vᵉ)
  uᵉ : is-nonzero-ℤᵉ yᵉ → ℤᵉ
  uᵉ gᵉ = pr1ᵉ (pr1ᵉ (Kᵉ gᵉ))
  vᵉ : is-nonzero-ℤᵉ yᵉ → ℤᵉ
  vᵉ gᵉ = pr1ᵉ (pr2ᵉ (pr1ᵉ (Kᵉ gᵉ)))
  βᵉ : (gᵉ : is-nonzero-ℤᵉ yᵉ) → (uᵉ gᵉ) *ℤᵉ xᵉ ＝ᵉ yᵉ
  βᵉ gᵉ = pr2ᵉ (Kᵉ gᵉ)
```

### The relations `presim-unit-ℤ` and `sim-unit-ℤ` are equivalence relations

```agda
refl-presim-unit-ℤᵉ : is-reflexiveᵉ presim-unit-ℤᵉ
pr1ᵉ (refl-presim-unit-ℤᵉ xᵉ) = one-unit-ℤᵉ
pr2ᵉ (refl-presim-unit-ℤᵉ xᵉ) = left-unit-law-mul-ℤᵉ xᵉ

refl-sim-unit-ℤᵉ : is-reflexiveᵉ sim-unit-ℤᵉ
refl-sim-unit-ℤᵉ xᵉ fᵉ = refl-presim-unit-ℤᵉ xᵉ

presim-unit-eq-ℤᵉ : {xᵉ yᵉ : ℤᵉ} → xᵉ ＝ᵉ yᵉ → presim-unit-ℤᵉ xᵉ yᵉ
presim-unit-eq-ℤᵉ {xᵉ} reflᵉ = refl-presim-unit-ℤᵉ xᵉ

sim-unit-eq-ℤᵉ : {xᵉ yᵉ : ℤᵉ} → xᵉ ＝ᵉ yᵉ → sim-unit-ℤᵉ xᵉ yᵉ
sim-unit-eq-ℤᵉ {xᵉ} reflᵉ = refl-sim-unit-ℤᵉ xᵉ

symmetric-presim-unit-ℤᵉ : is-symmetricᵉ presim-unit-ℤᵉ
symmetric-presim-unit-ℤᵉ xᵉ yᵉ (pairᵉ (pairᵉ uᵉ Hᵉ) pᵉ) =
  fᵉ (is-one-or-neg-one-is-unit-ℤᵉ uᵉ Hᵉ)
  where
  fᵉ : is-one-or-neg-one-ℤᵉ uᵉ → presim-unit-ℤᵉ yᵉ xᵉ
  pr1ᵉ (fᵉ (inlᵉ reflᵉ)) = one-unit-ℤᵉ
  pr2ᵉ (fᵉ (inlᵉ reflᵉ)) = invᵉ pᵉ
  pr1ᵉ (fᵉ (inrᵉ reflᵉ)) = neg-one-unit-ℤᵉ
  pr2ᵉ (fᵉ (inrᵉ reflᵉ)) = invᵉ (invᵉ (neg-neg-ℤᵉ xᵉ) ∙ᵉ apᵉ (neg-one-ℤᵉ *ℤᵉ_) pᵉ)

symmetric-sim-unit-ℤᵉ : is-symmetricᵉ sim-unit-ℤᵉ
symmetric-sim-unit-ℤᵉ xᵉ yᵉ Hᵉ fᵉ =
  symmetric-presim-unit-ℤᵉ xᵉ yᵉ (Hᵉ (λ pᵉ → fᵉ (pairᵉ (pr2ᵉ pᵉ) (pr1ᵉ pᵉ))))

is-nonzero-sim-unit-ℤ'ᵉ :
  {xᵉ yᵉ : ℤᵉ} → sim-unit-ℤᵉ xᵉ yᵉ → is-nonzero-ℤᵉ yᵉ → is-nonzero-ℤᵉ xᵉ
is-nonzero-sim-unit-ℤ'ᵉ {xᵉ} {yᵉ} Hᵉ =
  is-nonzero-sim-unit-ℤᵉ (symmetric-sim-unit-ℤᵉ xᵉ yᵉ Hᵉ)

is-zero-sim-unit-ℤ'ᵉ :
  {xᵉ yᵉ : ℤᵉ} → sim-unit-ℤᵉ xᵉ yᵉ → is-zero-ℤᵉ yᵉ → is-zero-ℤᵉ xᵉ
is-zero-sim-unit-ℤ'ᵉ {xᵉ} {yᵉ} Hᵉ = is-zero-sim-unit-ℤᵉ (symmetric-sim-unit-ℤᵉ xᵉ yᵉ Hᵉ)

transitive-presim-unit-ℤᵉ : is-transitiveᵉ presim-unit-ℤᵉ
transitive-presim-unit-ℤᵉ xᵉ yᵉ zᵉ (pairᵉ (pairᵉ vᵉ Kᵉ) qᵉ) (pairᵉ (pairᵉ uᵉ Hᵉ) pᵉ) =
  fᵉ (is-one-or-neg-one-is-unit-ℤᵉ uᵉ Hᵉ) (is-one-or-neg-one-is-unit-ℤᵉ vᵉ Kᵉ)
  where
  fᵉ : is-one-or-neg-one-ℤᵉ uᵉ → is-one-or-neg-one-ℤᵉ vᵉ → presim-unit-ℤᵉ xᵉ zᵉ
  pr1ᵉ (fᵉ (inlᵉ reflᵉ) (inlᵉ reflᵉ)) = one-unit-ℤᵉ
  pr2ᵉ (fᵉ (inlᵉ reflᵉ) (inlᵉ reflᵉ)) = pᵉ ∙ᵉ qᵉ
  pr1ᵉ (fᵉ (inlᵉ reflᵉ) (inrᵉ reflᵉ)) = neg-one-unit-ℤᵉ
  pr2ᵉ (fᵉ (inlᵉ reflᵉ) (inrᵉ reflᵉ)) = apᵉ neg-ℤᵉ pᵉ ∙ᵉ qᵉ
  pr1ᵉ (fᵉ (inrᵉ reflᵉ) (inlᵉ reflᵉ)) = neg-one-unit-ℤᵉ
  pr2ᵉ (fᵉ (inrᵉ reflᵉ) (inlᵉ reflᵉ)) = pᵉ ∙ᵉ qᵉ
  pr1ᵉ (fᵉ (inrᵉ reflᵉ) (inrᵉ reflᵉ)) = one-unit-ℤᵉ
  pr2ᵉ (fᵉ (inrᵉ reflᵉ) (inrᵉ reflᵉ)) = invᵉ (neg-neg-ℤᵉ xᵉ) ∙ᵉ (apᵉ neg-ℤᵉ pᵉ ∙ᵉ qᵉ)

transitive-sim-unit-ℤᵉ : is-transitiveᵉ sim-unit-ℤᵉ
transitive-sim-unit-ℤᵉ xᵉ yᵉ zᵉ Kᵉ Hᵉ fᵉ =
  transitive-presim-unit-ℤᵉ xᵉ yᵉ zᵉ
    ( Kᵉ (λ (pᵉ ,ᵉ qᵉ) → fᵉ (is-zero-sim-unit-ℤ'ᵉ Hᵉ pᵉ ,ᵉ qᵉ)))
    ( Hᵉ (λ (pᵉ ,ᵉ qᵉ) → fᵉ (pᵉ ,ᵉ is-zero-sim-unit-ℤᵉ Kᵉ qᵉ)))
```

### `sim-unit-ℤ x y` holds if and only if `x|y` and `y|x`

```agda
antisymmetric-div-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → div-ℤᵉ xᵉ yᵉ → div-ℤᵉ yᵉ xᵉ → sim-unit-ℤᵉ xᵉ yᵉ
antisymmetric-div-ℤᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ) (pairᵉ eᵉ qᵉ) Hᵉ =
  fᵉ (is-decidable-is-zero-ℤᵉ xᵉ)
  where
  fᵉ : is-decidableᵉ (is-zero-ℤᵉ xᵉ) → presim-unit-ℤᵉ xᵉ yᵉ
  fᵉ (inlᵉ reflᵉ) = presim-unit-eq-ℤᵉ (invᵉ (right-zero-law-mul-ℤᵉ dᵉ) ∙ᵉ pᵉ)
  pr1ᵉ (pr1ᵉ (fᵉ (inrᵉ gᵉ))) = dᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (fᵉ (inrᵉ gᵉ)))) = eᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (fᵉ (inrᵉ gᵉ)))) =
    is-injective-left-mul-ℤᵉ xᵉ gᵉ
      ( ( commutative-mul-ℤᵉ xᵉ (eᵉ *ℤᵉ dᵉ)) ∙ᵉ
        ( ( associative-mul-ℤᵉ eᵉ dᵉ xᵉ) ∙ᵉ
          ( ( apᵉ (eᵉ *ℤᵉ_) pᵉ) ∙ᵉ
            ( qᵉ ∙ᵉ invᵉ (right-unit-law-mul-ℤᵉ xᵉ)))))
  pr2ᵉ (fᵉ (inrᵉ gᵉ)) = pᵉ
```

### `sim-unit-ℤ |x| x` holds

```agda
sim-unit-abs-ℤᵉ : (xᵉ : ℤᵉ) → sim-unit-ℤᵉ (int-abs-ℤᵉ xᵉ) xᵉ
pr1ᵉ (sim-unit-abs-ℤᵉ (inlᵉ xᵉ) fᵉ) = neg-one-unit-ℤᵉ
pr2ᵉ (sim-unit-abs-ℤᵉ (inlᵉ xᵉ) fᵉ) = reflᵉ
sim-unit-abs-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = refl-sim-unit-ℤᵉ zero-ℤᵉ
sim-unit-abs-ℤᵉ (inrᵉ (inrᵉ xᵉ)) = refl-sim-unit-ℤᵉ (inrᵉ (inrᵉ xᵉ))

div-presim-unit-ℤᵉ :
  {xᵉ yᵉ x'ᵉ y'ᵉ : ℤᵉ} → presim-unit-ℤᵉ xᵉ x'ᵉ → presim-unit-ℤᵉ yᵉ y'ᵉ →
  div-ℤᵉ xᵉ yᵉ → div-ℤᵉ x'ᵉ y'ᵉ
pr1ᵉ (div-presim-unit-ℤᵉ {xᵉ} {yᵉ} {x'ᵉ} {y'ᵉ} (pairᵉ uᵉ qᵉ) (pairᵉ vᵉ rᵉ) (pairᵉ dᵉ pᵉ)) =
  ((int-unit-ℤᵉ vᵉ) *ℤᵉ dᵉ) *ℤᵉ (int-unit-ℤᵉ uᵉ)
pr2ᵉ (div-presim-unit-ℤᵉ {xᵉ} {yᵉ} {x'ᵉ} {y'ᵉ} (pairᵉ uᵉ qᵉ) (pairᵉ vᵉ rᵉ) (pairᵉ dᵉ pᵉ)) =
  ( apᵉ ((((int-unit-ℤᵉ vᵉ) *ℤᵉ dᵉ) *ℤᵉ (int-unit-ℤᵉ uᵉ)) *ℤᵉ_) (invᵉ qᵉ)) ∙ᵉ
  ( ( associative-mul-ℤᵉ
      ( (int-unit-ℤᵉ vᵉ) *ℤᵉ dᵉ)
      ( int-unit-ℤᵉ uᵉ)
      ( (int-unit-ℤᵉ uᵉ) *ℤᵉ xᵉ)) ∙ᵉ
    ( ( apᵉ
        ( ((int-unit-ℤᵉ vᵉ) *ℤᵉ dᵉ) *ℤᵉ_)
        ( ( invᵉ (associative-mul-ℤᵉ (int-unit-ℤᵉ uᵉ) (int-unit-ℤᵉ uᵉ) xᵉ)) ∙ᵉ
          ( apᵉ (_*ℤᵉ xᵉ) (idempotent-is-unit-ℤᵉ (is-unit-int-unit-ℤᵉ uᵉ))))) ∙ᵉ
      ( ( associative-mul-ℤᵉ (int-unit-ℤᵉ vᵉ) dᵉ xᵉ) ∙ᵉ
        ( ( apᵉ ((int-unit-ℤᵉ vᵉ) *ℤᵉ_) pᵉ) ∙ᵉ
          ( rᵉ)))))

div-sim-unit-ℤᵉ :
  {xᵉ yᵉ x'ᵉ y'ᵉ : ℤᵉ} → sim-unit-ℤᵉ xᵉ x'ᵉ → sim-unit-ℤᵉ yᵉ y'ᵉ →
  div-ℤᵉ xᵉ yᵉ → div-ℤᵉ x'ᵉ y'ᵉ
div-sim-unit-ℤᵉ {xᵉ} {yᵉ} {x'ᵉ} {y'ᵉ} Hᵉ Kᵉ =
  div-presim-unit-ℤᵉ (presim-unit-sim-unit-ℤᵉ Hᵉ) (presim-unit-sim-unit-ℤᵉ Kᵉ)

div-int-abs-div-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → div-ℤᵉ xᵉ yᵉ → div-ℤᵉ (int-abs-ℤᵉ xᵉ) yᵉ
div-int-abs-div-ℤᵉ {xᵉ} {yᵉ} =
  div-sim-unit-ℤᵉ
    ( symmetric-sim-unit-ℤᵉ (int-abs-ℤᵉ xᵉ) xᵉ (sim-unit-abs-ℤᵉ xᵉ))
    ( refl-sim-unit-ℤᵉ yᵉ)

div-div-int-abs-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → div-ℤᵉ (int-abs-ℤᵉ xᵉ) yᵉ → div-ℤᵉ xᵉ yᵉ
div-div-int-abs-ℤᵉ {xᵉ} {yᵉ} =
  div-sim-unit-ℤᵉ (sim-unit-abs-ℤᵉ xᵉ) (refl-sim-unit-ℤᵉ yᵉ)
```

### If we have that `sim-unit-ℤ x y`, then they must differ only by sign

```agda
is-plus-or-minus-sim-unit-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → sim-unit-ℤᵉ xᵉ yᵉ → is-plus-or-minus-ℤᵉ xᵉ yᵉ
is-plus-or-minus-sim-unit-ℤᵉ {xᵉ} {yᵉ} Hᵉ with ( is-decidable-is-zero-ℤᵉ xᵉ)
is-plus-or-minus-sim-unit-ℤᵉ {xᵉ} {yᵉ} Hᵉ | inlᵉ zᵉ =
  inlᵉ (zᵉ ∙ᵉ invᵉ (is-zero-sim-unit-ℤᵉ Hᵉ zᵉ))
is-plus-or-minus-sim-unit-ℤᵉ {xᵉ} {yᵉ} Hᵉ | inrᵉ nzᵉ
  with
  ( is-one-or-neg-one-is-unit-ℤᵉ
    ( int-unit-ℤᵉ (pr1ᵉ (Hᵉ (λ uᵉ → nzᵉ (pr1ᵉ uᵉ)))))
    ( is-unit-int-unit-ℤᵉ (pr1ᵉ (Hᵉ (λ uᵉ → nzᵉ (pr1ᵉ uᵉ))))))
is-plus-or-minus-sim-unit-ℤᵉ {xᵉ} {yᵉ} Hᵉ | inrᵉ nzᵉ | inlᵉ posᵉ =
  inlᵉ
    ( equational-reasoningᵉ
      xᵉ
      ＝ᵉ one-ℤᵉ *ℤᵉ xᵉ
        byᵉ (invᵉ (left-unit-law-mul-ℤᵉ xᵉ))
      ＝ᵉ (int-unit-ℤᵉ (pr1ᵉ (Hᵉ (λ uᵉ → nzᵉ (pr1ᵉ uᵉ))))) *ℤᵉ xᵉ
        byᵉ invᵉ (apᵉ (_*ℤᵉ xᵉ) posᵉ)
      ＝ᵉ yᵉ
        byᵉ pr2ᵉ (Hᵉ (λ uᵉ → nzᵉ (pr1ᵉ uᵉ))))
is-plus-or-minus-sim-unit-ℤᵉ {xᵉ} {yᵉ} Hᵉ | inrᵉ nzᵉ | inrᵉ pᵉ =
  inrᵉ
    ( equational-reasoningᵉ
      neg-ℤᵉ xᵉ
      ＝ᵉ (int-unit-ℤᵉ (pr1ᵉ (Hᵉ (λ uᵉ → nzᵉ (pr1ᵉ uᵉ))))) *ℤᵉ xᵉ
        byᵉ apᵉ (_*ℤᵉ xᵉ) (invᵉ pᵉ)
      ＝ᵉ yᵉ
        byᵉ pr2ᵉ (Hᵉ (λ uᵉ → nzᵉ (pr1ᵉ uᵉ))))
```

### If `sim-unit-ℤ x y` holds and both `x` and `y` have the same sign, then `x ＝ y`

```agda
eq-sim-unit-is-nonnegative-ℤᵉ :
  {aᵉ bᵉ : ℤᵉ} → is-nonnegative-ℤᵉ aᵉ → is-nonnegative-ℤᵉ bᵉ → sim-unit-ℤᵉ aᵉ bᵉ → aᵉ ＝ᵉ bᵉ
eq-sim-unit-is-nonnegative-ℤᵉ {aᵉ} {bᵉ} Hᵉ H'ᵉ Kᵉ =
  rec-coproductᵉ
    ( idᵉ)
    ( λ K'ᵉ →
      eq-is-zero-ℤᵉ
        ( is-zero-is-nonnegative-neg-is-nonnegative-ℤᵉ Hᵉ
          ( is-nonnegative-eq-ℤᵉ (invᵉ K'ᵉ) H'ᵉ))
        ( is-zero-is-nonnegative-neg-is-nonnegative-ℤᵉ H'ᵉ
          ( is-nonnegative-eq-ℤᵉ (invᵉ (neg-neg-ℤᵉ aᵉ) ∙ᵉ apᵉ neg-ℤᵉ K'ᵉ) Hᵉ)))
    ( is-plus-or-minus-sim-unit-ℤᵉ Kᵉ)
```