# Minimum on the natural numbers

```agda
module elementary-number-theory.minimum-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ

open import order-theory.greatest-lower-bounds-posetsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Weᵉ defineᵉ theᵉ operationᵉ ofᵉ minimumᵉ (greatestᵉ lowerᵉ boundᵉ) forᵉ theᵉ naturalᵉ
numbers.ᵉ

## Definition

```agda
min-ℕᵉ : ℕᵉ → (ℕᵉ → ℕᵉ)
min-ℕᵉ 0 nᵉ = 0
min-ℕᵉ (succ-ℕᵉ mᵉ) 0 = 0
min-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) = succ-ℕᵉ (min-ℕᵉ mᵉ nᵉ)

ap-min-ℕᵉ : {xᵉ x'ᵉ yᵉ y'ᵉ : ℕᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → min-ℕᵉ xᵉ yᵉ ＝ᵉ min-ℕᵉ x'ᵉ y'ᵉ
ap-min-ℕᵉ pᵉ qᵉ = ap-binaryᵉ min-ℕᵉ pᵉ qᵉ

min-Fin-ℕᵉ : (nᵉ : ℕᵉ) → (Finᵉ (succ-ℕᵉ nᵉ) → ℕᵉ) → ℕᵉ
min-Fin-ℕᵉ zero-ℕᵉ fᵉ = fᵉ (inrᵉ starᵉ)
min-Fin-ℕᵉ (succ-ℕᵉ nᵉ) fᵉ = min-ℕᵉ (fᵉ (inrᵉ starᵉ)) (min-Fin-ℕᵉ nᵉ (λ kᵉ → fᵉ (inlᵉ kᵉ)))
```

## Properties

### The minimum of two natural numbers is a greatest lower bound

```agda
leq-min-ℕᵉ :
  (kᵉ mᵉ nᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ mᵉ → kᵉ ≤-ℕᵉ nᵉ → kᵉ ≤-ℕᵉ (min-ℕᵉ mᵉ nᵉ)
leq-min-ℕᵉ zero-ℕᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ Kᵉ = starᵉ
leq-min-ℕᵉ zero-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) Hᵉ Kᵉ = starᵉ
leq-min-ℕᵉ zero-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ Hᵉ Kᵉ = starᵉ
leq-min-ℕᵉ zero-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) Hᵉ Kᵉ = starᵉ
leq-min-ℕᵉ (succ-ℕᵉ kᵉ) (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) Hᵉ Kᵉ = leq-min-ℕᵉ kᵉ mᵉ nᵉ Hᵉ Kᵉ

leq-left-leq-min-ℕᵉ :
  (kᵉ mᵉ nᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ (min-ℕᵉ mᵉ nᵉ) → kᵉ ≤-ℕᵉ mᵉ
leq-left-leq-min-ℕᵉ zero-ℕᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ = starᵉ
leq-left-leq-min-ℕᵉ zero-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) Hᵉ = starᵉ
leq-left-leq-min-ℕᵉ zero-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ Hᵉ = starᵉ
leq-left-leq-min-ℕᵉ zero-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) Hᵉ = starᵉ
leq-left-leq-min-ℕᵉ (succ-ℕᵉ kᵉ) (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) Hᵉ =
  leq-left-leq-min-ℕᵉ kᵉ mᵉ nᵉ Hᵉ

leq-right-leq-min-ℕᵉ :
  (kᵉ mᵉ nᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ (min-ℕᵉ mᵉ nᵉ) → kᵉ ≤-ℕᵉ nᵉ
leq-right-leq-min-ℕᵉ zero-ℕᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ = starᵉ
leq-right-leq-min-ℕᵉ zero-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) Hᵉ = starᵉ
leq-right-leq-min-ℕᵉ zero-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ Hᵉ = starᵉ
leq-right-leq-min-ℕᵉ zero-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) Hᵉ = starᵉ
leq-right-leq-min-ℕᵉ (succ-ℕᵉ kᵉ) (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) Hᵉ =
  leq-right-leq-min-ℕᵉ kᵉ mᵉ nᵉ Hᵉ

is-greatest-lower-bound-min-ℕᵉ :
  (lᵉ mᵉ : ℕᵉ) → is-greatest-binary-lower-bound-Posetᵉ ℕ-Posetᵉ lᵉ mᵉ (min-ℕᵉ lᵉ mᵉ)
is-greatest-lower-bound-min-ℕᵉ lᵉ mᵉ =
  prove-is-greatest-binary-lower-bound-Posetᵉ
    ( ℕ-Posetᵉ)
    ( leq-left-leq-min-ℕᵉ (min-ℕᵉ lᵉ mᵉ) lᵉ mᵉ (refl-leq-ℕᵉ (min-ℕᵉ lᵉ mᵉ)) ,ᵉ
      leq-right-leq-min-ℕᵉ (min-ℕᵉ lᵉ mᵉ) lᵉ mᵉ (refl-leq-ℕᵉ (min-ℕᵉ lᵉ mᵉ)))
    ( λ xᵉ (Hᵉ ,ᵉ Kᵉ) → leq-min-ℕᵉ xᵉ lᵉ mᵉ Hᵉ Kᵉ)
```

### Associativity of `min-ℕ`

```agda
associative-min-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → min-ℕᵉ (min-ℕᵉ xᵉ yᵉ) zᵉ ＝ᵉ min-ℕᵉ xᵉ (min-ℕᵉ yᵉ zᵉ)
associative-min-ℕᵉ zero-ℕᵉ yᵉ zᵉ = reflᵉ
associative-min-ℕᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ zero-ℕᵉ = reflᵉ
associative-min-ℕᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ (succ-ℕᵉ zᵉ) = reflᵉ
associative-min-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) zero-ℕᵉ = reflᵉ
associative-min-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) (succ-ℕᵉ zᵉ) =
  apᵉ succ-ℕᵉ (associative-min-ℕᵉ xᵉ yᵉ zᵉ)
```

### Zero laws for `min-ℕ`

```agda
left-zero-law-min-ℕᵉ : (xᵉ : ℕᵉ) → min-ℕᵉ 0 xᵉ ＝ᵉ 0
left-zero-law-min-ℕᵉ xᵉ = reflᵉ

right-zero-law-min-ℕᵉ : (xᵉ : ℕᵉ) → min-ℕᵉ xᵉ 0 ＝ᵉ 0
right-zero-law-min-ℕᵉ zero-ℕᵉ = reflᵉ
right-zero-law-min-ℕᵉ (succ-ℕᵉ xᵉ) = reflᵉ
```

### Commutativity of `min-ℕ`

```agda
commutative-min-ℕᵉ : (xᵉ yᵉ : ℕᵉ) → min-ℕᵉ xᵉ yᵉ ＝ᵉ min-ℕᵉ yᵉ xᵉ
commutative-min-ℕᵉ zero-ℕᵉ zero-ℕᵉ = reflᵉ
commutative-min-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) = reflᵉ
commutative-min-ℕᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ = reflᵉ
commutative-min-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) = apᵉ succ-ℕᵉ (commutative-min-ℕᵉ xᵉ yᵉ)
```

### `min-ℕ` is idempotent

```agda
idempotent-min-ℕᵉ : (xᵉ : ℕᵉ) → min-ℕᵉ xᵉ xᵉ ＝ᵉ xᵉ
idempotent-min-ℕᵉ zero-ℕᵉ = reflᵉ
idempotent-min-ℕᵉ (succ-ℕᵉ xᵉ) = apᵉ succ-ℕᵉ (idempotent-min-ℕᵉ xᵉ)
```

### Addition distributes over `min-ℕ`

```agda
left-distributive-add-min-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → xᵉ +ℕᵉ (min-ℕᵉ yᵉ zᵉ) ＝ᵉ min-ℕᵉ (xᵉ +ℕᵉ yᵉ) (xᵉ +ℕᵉ zᵉ)
left-distributive-add-min-ℕᵉ zero-ℕᵉ yᵉ zᵉ =
  ( left-unit-law-add-ℕᵉ (min-ℕᵉ yᵉ zᵉ)) ∙ᵉ
  ( ap-min-ℕᵉ (invᵉ (left-unit-law-add-ℕᵉ yᵉ)) (invᵉ (left-unit-law-add-ℕᵉ zᵉ)))
left-distributive-add-min-ℕᵉ (succ-ℕᵉ xᵉ) yᵉ zᵉ =
  ( left-successor-law-add-ℕᵉ xᵉ (min-ℕᵉ yᵉ zᵉ)) ∙ᵉ
  ( ( apᵉ succ-ℕᵉ (left-distributive-add-min-ℕᵉ xᵉ yᵉ zᵉ)) ∙ᵉ
    ( ap-min-ℕᵉ
      ( invᵉ (left-successor-law-add-ℕᵉ xᵉ yᵉ))
      ( invᵉ (left-successor-law-add-ℕᵉ xᵉ zᵉ))))

right-distributive-add-min-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → (min-ℕᵉ xᵉ yᵉ) +ℕᵉ zᵉ ＝ᵉ min-ℕᵉ (xᵉ +ℕᵉ zᵉ) (yᵉ +ℕᵉ zᵉ)
right-distributive-add-min-ℕᵉ xᵉ yᵉ zᵉ =
  ( commutative-add-ℕᵉ (min-ℕᵉ xᵉ yᵉ) zᵉ) ∙ᵉ
  ( ( left-distributive-add-min-ℕᵉ zᵉ xᵉ yᵉ) ∙ᵉ
    ( ap-min-ℕᵉ (commutative-add-ℕᵉ zᵉ xᵉ) (commutative-add-ℕᵉ zᵉ yᵉ)))
```