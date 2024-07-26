# Maximum on the natural numbers

```agda
module elementary-number-theory.maximum-natural-numbersᵉ where
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

open import order-theory.least-upper-bounds-posetsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Weᵉ defineᵉ theᵉ operationᵉ ofᵉ maximumᵉ (leastᵉ upperᵉ boundᵉ) forᵉ theᵉ naturalᵉ numbers.ᵉ

## Definition

### Maximum of natural numbers

```agda
max-ℕᵉ : ℕᵉ → (ℕᵉ → ℕᵉ)
max-ℕᵉ 0 nᵉ = nᵉ
max-ℕᵉ (succ-ℕᵉ mᵉ) 0 = succ-ℕᵉ mᵉ
max-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) = succ-ℕᵉ (max-ℕᵉ mᵉ nᵉ)

ap-max-ℕᵉ : {xᵉ x'ᵉ yᵉ y'ᵉ : ℕᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → max-ℕᵉ xᵉ yᵉ ＝ᵉ max-ℕᵉ x'ᵉ y'ᵉ
ap-max-ℕᵉ pᵉ qᵉ = ap-binaryᵉ max-ℕᵉ pᵉ qᵉ

max-ℕ'ᵉ : ℕᵉ → (ℕᵉ → ℕᵉ)
max-ℕ'ᵉ xᵉ yᵉ = max-ℕᵉ yᵉ xᵉ
```

### Maximum of elements of standard finite types

```agda
max-Fin-ℕᵉ : (nᵉ : ℕᵉ) → (Finᵉ nᵉ → ℕᵉ) → ℕᵉ
max-Fin-ℕᵉ zero-ℕᵉ fᵉ = zero-ℕᵉ
max-Fin-ℕᵉ (succ-ℕᵉ nᵉ) fᵉ = max-ℕᵉ (fᵉ (inrᵉ starᵉ)) (max-Fin-ℕᵉ nᵉ (λ kᵉ → fᵉ (inlᵉ kᵉ)))
```

## Properties

### Maximum is a least upper bound

```agda
leq-max-ℕᵉ :
  (kᵉ mᵉ nᵉ : ℕᵉ) → mᵉ ≤-ℕᵉ kᵉ → nᵉ ≤-ℕᵉ kᵉ → (max-ℕᵉ mᵉ nᵉ) ≤-ℕᵉ kᵉ
leq-max-ℕᵉ zero-ℕᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ Kᵉ = starᵉ
leq-max-ℕᵉ (succ-ℕᵉ kᵉ) zero-ℕᵉ zero-ℕᵉ Hᵉ Kᵉ = starᵉ
leq-max-ℕᵉ (succ-ℕᵉ kᵉ) zero-ℕᵉ (succ-ℕᵉ nᵉ) Hᵉ Kᵉ = Kᵉ
leq-max-ℕᵉ (succ-ℕᵉ kᵉ) (succ-ℕᵉ mᵉ) zero-ℕᵉ Hᵉ Kᵉ = Hᵉ
leq-max-ℕᵉ (succ-ℕᵉ kᵉ) (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) Hᵉ Kᵉ = leq-max-ℕᵉ kᵉ mᵉ nᵉ Hᵉ Kᵉ

leq-left-leq-max-ℕᵉ :
  (kᵉ mᵉ nᵉ : ℕᵉ) → (max-ℕᵉ mᵉ nᵉ) ≤-ℕᵉ kᵉ → mᵉ ≤-ℕᵉ kᵉ
leq-left-leq-max-ℕᵉ kᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ = starᵉ
leq-left-leq-max-ℕᵉ kᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) Hᵉ = starᵉ
leq-left-leq-max-ℕᵉ kᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ Hᵉ = Hᵉ
leq-left-leq-max-ℕᵉ (succ-ℕᵉ kᵉ) (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) Hᵉ =
  leq-left-leq-max-ℕᵉ kᵉ mᵉ nᵉ Hᵉ

leq-right-leq-max-ℕᵉ :
  (kᵉ mᵉ nᵉ : ℕᵉ) → (max-ℕᵉ mᵉ nᵉ) ≤-ℕᵉ kᵉ → nᵉ ≤-ℕᵉ kᵉ
leq-right-leq-max-ℕᵉ kᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ = starᵉ
leq-right-leq-max-ℕᵉ kᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) Hᵉ = Hᵉ
leq-right-leq-max-ℕᵉ kᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ Hᵉ = starᵉ
leq-right-leq-max-ℕᵉ (succ-ℕᵉ kᵉ) (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) Hᵉ =
  leq-right-leq-max-ℕᵉ kᵉ mᵉ nᵉ Hᵉ

is-least-upper-bound-max-ℕᵉ :
  (mᵉ nᵉ : ℕᵉ) → is-least-binary-upper-bound-Posetᵉ ℕ-Posetᵉ mᵉ nᵉ (max-ℕᵉ mᵉ nᵉ)
is-least-upper-bound-max-ℕᵉ mᵉ nᵉ =
  prove-is-least-binary-upper-bound-Posetᵉ
    ( ℕ-Posetᵉ)
    { mᵉ}
    { nᵉ}
    { max-ℕᵉ mᵉ nᵉ}
    ( leq-left-leq-max-ℕᵉ (max-ℕᵉ mᵉ nᵉ) mᵉ nᵉ (refl-leq-ℕᵉ (max-ℕᵉ mᵉ nᵉ)) ,ᵉ
      leq-right-leq-max-ℕᵉ (max-ℕᵉ mᵉ nᵉ) mᵉ nᵉ (refl-leq-ℕᵉ (max-ℕᵉ mᵉ nᵉ)))
    ( λ xᵉ (Hᵉ ,ᵉ Kᵉ) → leq-max-ℕᵉ xᵉ mᵉ nᵉ Hᵉ Kᵉ)
```

### Associativity of `max-ℕ`

```agda
associative-max-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → max-ℕᵉ (max-ℕᵉ xᵉ yᵉ) zᵉ ＝ᵉ max-ℕᵉ xᵉ (max-ℕᵉ yᵉ zᵉ)
associative-max-ℕᵉ zero-ℕᵉ yᵉ zᵉ = reflᵉ
associative-max-ℕᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ zero-ℕᵉ = reflᵉ
associative-max-ℕᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ (succ-ℕᵉ zᵉ) = reflᵉ
associative-max-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) zero-ℕᵉ = reflᵉ
associative-max-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) (succ-ℕᵉ zᵉ) =
  apᵉ succ-ℕᵉ (associative-max-ℕᵉ xᵉ yᵉ zᵉ)
```

### Unit laws for `max-ℕ`

```agda
left-unit-law-max-ℕᵉ : (xᵉ : ℕᵉ) → max-ℕᵉ 0 xᵉ ＝ᵉ xᵉ
left-unit-law-max-ℕᵉ xᵉ = reflᵉ

right-unit-law-max-ℕᵉ : (xᵉ : ℕᵉ) → max-ℕᵉ xᵉ 0 ＝ᵉ xᵉ
right-unit-law-max-ℕᵉ zero-ℕᵉ = reflᵉ
right-unit-law-max-ℕᵉ (succ-ℕᵉ xᵉ) = reflᵉ
```

### Commutativity of `max-ℕ`

```agda
commutative-max-ℕᵉ : (xᵉ yᵉ : ℕᵉ) → max-ℕᵉ xᵉ yᵉ ＝ᵉ max-ℕᵉ yᵉ xᵉ
commutative-max-ℕᵉ zero-ℕᵉ zero-ℕᵉ = reflᵉ
commutative-max-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) = reflᵉ
commutative-max-ℕᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ = reflᵉ
commutative-max-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) = apᵉ succ-ℕᵉ (commutative-max-ℕᵉ xᵉ yᵉ)
```

### `max-ℕ` is idempotent

```agda
idempotent-max-ℕᵉ : (xᵉ : ℕᵉ) → max-ℕᵉ xᵉ xᵉ ＝ᵉ xᵉ
idempotent-max-ℕᵉ zero-ℕᵉ = reflᵉ
idempotent-max-ℕᵉ (succ-ℕᵉ xᵉ) = apᵉ succ-ℕᵉ (idempotent-max-ℕᵉ xᵉ)
```

### Successor diagonal laws for `max-ℕ`

```agda
left-successor-diagonal-law-max-ℕᵉ : (xᵉ : ℕᵉ) → max-ℕᵉ (succ-ℕᵉ xᵉ) xᵉ ＝ᵉ succ-ℕᵉ xᵉ
left-successor-diagonal-law-max-ℕᵉ zero-ℕᵉ = reflᵉ
left-successor-diagonal-law-max-ℕᵉ (succ-ℕᵉ xᵉ) =
  apᵉ succ-ℕᵉ (left-successor-diagonal-law-max-ℕᵉ xᵉ)

right-successor-diagonal-law-max-ℕᵉ : (xᵉ : ℕᵉ) → max-ℕᵉ xᵉ (succ-ℕᵉ xᵉ) ＝ᵉ succ-ℕᵉ xᵉ
right-successor-diagonal-law-max-ℕᵉ zero-ℕᵉ = reflᵉ
right-successor-diagonal-law-max-ℕᵉ (succ-ℕᵉ xᵉ) =
  apᵉ succ-ℕᵉ (right-successor-diagonal-law-max-ℕᵉ xᵉ)
```

### Addition distributes over `max-ℕ`

```agda
left-distributive-add-max-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → xᵉ +ℕᵉ (max-ℕᵉ yᵉ zᵉ) ＝ᵉ max-ℕᵉ (xᵉ +ℕᵉ yᵉ) (xᵉ +ℕᵉ zᵉ)
left-distributive-add-max-ℕᵉ zero-ℕᵉ yᵉ zᵉ =
  ( left-unit-law-add-ℕᵉ (max-ℕᵉ yᵉ zᵉ)) ∙ᵉ
  ( ap-max-ℕᵉ (invᵉ (left-unit-law-add-ℕᵉ yᵉ)) (invᵉ (left-unit-law-add-ℕᵉ zᵉ)))
left-distributive-add-max-ℕᵉ (succ-ℕᵉ xᵉ) yᵉ zᵉ =
  ( left-successor-law-add-ℕᵉ xᵉ (max-ℕᵉ yᵉ zᵉ)) ∙ᵉ
  ( ( apᵉ succ-ℕᵉ (left-distributive-add-max-ℕᵉ xᵉ yᵉ zᵉ)) ∙ᵉ
    ( ap-max-ℕᵉ
      ( invᵉ (left-successor-law-add-ℕᵉ xᵉ yᵉ))
      ( invᵉ (left-successor-law-add-ℕᵉ xᵉ zᵉ))))

right-distributive-add-max-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → (max-ℕᵉ xᵉ yᵉ) +ℕᵉ zᵉ ＝ᵉ max-ℕᵉ (xᵉ +ℕᵉ zᵉ) (yᵉ +ℕᵉ zᵉ)
right-distributive-add-max-ℕᵉ xᵉ yᵉ zᵉ =
  ( commutative-add-ℕᵉ (max-ℕᵉ xᵉ yᵉ) zᵉ) ∙ᵉ
  ( ( left-distributive-add-max-ℕᵉ zᵉ xᵉ yᵉ) ∙ᵉ
    ( ap-max-ℕᵉ (commutative-add-ℕᵉ zᵉ xᵉ) (commutative-add-ℕᵉ zᵉ yᵉ)))
```