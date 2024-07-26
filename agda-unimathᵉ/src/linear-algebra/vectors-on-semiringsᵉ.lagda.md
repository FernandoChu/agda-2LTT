# Vectors on semirings

```agda
module linear-algebra.vectors-on-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ

open import linear-algebra.constant-vectorsᵉ
open import linear-algebra.functoriality-vectorsᵉ
open import linear-algebra.vectorsᵉ

open import ring-theory.semiringsᵉ
```

</details>

## Idea

Givenᵉ aᵉ ringᵉ `R`,ᵉ theᵉ typeᵉ `vecᵉ nᵉ R`ᵉ ofᵉ `R`-vectorsᵉ isᵉ anᵉ `R`-moduleᵉ

## Definitions

### Listed vectors on semirings

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  vec-Semiringᵉ : ℕᵉ → UUᵉ lᵉ
  vec-Semiringᵉ = vecᵉ (type-Semiringᵉ Rᵉ)

  head-vec-Semiringᵉ : {nᵉ : ℕᵉ} → vec-Semiringᵉ (succ-ℕᵉ nᵉ) → type-Semiringᵉ Rᵉ
  head-vec-Semiringᵉ vᵉ = head-vecᵉ vᵉ

  tail-vec-Semiringᵉ : {nᵉ : ℕᵉ} → vec-Semiringᵉ (succ-ℕᵉ nᵉ) → vec-Semiringᵉ nᵉ
  tail-vec-Semiringᵉ vᵉ = tail-vecᵉ vᵉ

  snoc-vec-Semiringᵉ :
    {nᵉ : ℕᵉ} → vec-Semiringᵉ nᵉ → type-Semiringᵉ Rᵉ → vec-Semiringᵉ (succ-ℕᵉ nᵉ)
  snoc-vec-Semiringᵉ vᵉ rᵉ = snoc-vecᵉ vᵉ rᵉ
```

### Functional vectors on rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  functional-vec-Semiringᵉ : ℕᵉ → UUᵉ lᵉ
  functional-vec-Semiringᵉ = functional-vecᵉ (type-Semiringᵉ Rᵉ)

  head-functional-vec-Semiringᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Semiringᵉ (succ-ℕᵉ nᵉ) → type-Semiringᵉ Rᵉ
  head-functional-vec-Semiringᵉ nᵉ vᵉ = head-functional-vecᵉ nᵉ vᵉ

  tail-functional-vec-Semiringᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Semiringᵉ (succ-ℕᵉ nᵉ) → functional-vec-Semiringᵉ nᵉ
  tail-functional-vec-Semiringᵉ = tail-functional-vecᵉ

  cons-functional-vec-Semiringᵉ :
    (nᵉ : ℕᵉ) → type-Semiringᵉ Rᵉ →
    functional-vec-Semiringᵉ nᵉ → functional-vec-Semiringᵉ (succ-ℕᵉ nᵉ)
  cons-functional-vec-Semiringᵉ = cons-functional-vecᵉ

  snoc-functional-vec-Semiringᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Semiringᵉ nᵉ → type-Semiringᵉ Rᵉ →
    functional-vec-Semiringᵉ (succ-ℕᵉ nᵉ)
  snoc-functional-vec-Semiringᵉ = snoc-functional-vecᵉ
```

### Zero vector on a ring

#### The zero listed vector

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  zero-vec-Semiringᵉ : {nᵉ : ℕᵉ} → vec-Semiringᵉ Rᵉ nᵉ
  zero-vec-Semiringᵉ = constant-vecᵉ (zero-Semiringᵉ Rᵉ)
```

#### The zero functional vector

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  zero-functional-vec-Semiringᵉ : (nᵉ : ℕᵉ) → functional-vec-Semiringᵉ Rᵉ nᵉ
  zero-functional-vec-Semiringᵉ nᵉ iᵉ = zero-Semiringᵉ Rᵉ
```

### Pointwise addition of vectors on a ring

#### Pointwise addition of listed vectors on a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  add-vec-Semiringᵉ :
    {nᵉ : ℕᵉ} → vec-Semiringᵉ Rᵉ nᵉ → vec-Semiringᵉ Rᵉ nᵉ → vec-Semiringᵉ Rᵉ nᵉ
  add-vec-Semiringᵉ = binary-map-vecᵉ (add-Semiringᵉ Rᵉ)

  associative-add-vec-Semiringᵉ :
    {nᵉ : ℕᵉ} (v1ᵉ v2ᵉ v3ᵉ : vec-Semiringᵉ Rᵉ nᵉ) →
    add-vec-Semiringᵉ (add-vec-Semiringᵉ v1ᵉ v2ᵉ) v3ᵉ ＝ᵉ
    add-vec-Semiringᵉ v1ᵉ (add-vec-Semiringᵉ v2ᵉ v3ᵉ)
  associative-add-vec-Semiringᵉ empty-vecᵉ empty-vecᵉ empty-vecᵉ = reflᵉ
  associative-add-vec-Semiringᵉ (xᵉ ∷ᵉ v1ᵉ) (yᵉ ∷ᵉ v2ᵉ) (zᵉ ∷ᵉ v3ᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( associative-add-Semiringᵉ Rᵉ xᵉ yᵉ zᵉ)
      ( associative-add-vec-Semiringᵉ v1ᵉ v2ᵉ v3ᵉ)

  vec-Semiring-Semigroupᵉ : ℕᵉ → Semigroupᵉ lᵉ
  pr1ᵉ (vec-Semiring-Semigroupᵉ nᵉ) = vec-Setᵉ (set-Semiringᵉ Rᵉ) nᵉ
  pr1ᵉ (pr2ᵉ (vec-Semiring-Semigroupᵉ nᵉ)) = add-vec-Semiringᵉ
  pr2ᵉ (pr2ᵉ (vec-Semiring-Semigroupᵉ nᵉ)) = associative-add-vec-Semiringᵉ

  left-unit-law-add-vec-Semiringᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vec-Semiringᵉ Rᵉ nᵉ) →
    add-vec-Semiringᵉ (zero-vec-Semiringᵉ Rᵉ) vᵉ ＝ᵉ vᵉ
  left-unit-law-add-vec-Semiringᵉ empty-vecᵉ = reflᵉ
  left-unit-law-add-vec-Semiringᵉ (xᵉ ∷ᵉ vᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( left-unit-law-add-Semiringᵉ Rᵉ xᵉ)
      ( left-unit-law-add-vec-Semiringᵉ vᵉ)

  right-unit-law-add-vec-Semiringᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vec-Semiringᵉ Rᵉ nᵉ) →
    add-vec-Semiringᵉ vᵉ (zero-vec-Semiringᵉ Rᵉ) ＝ᵉ vᵉ
  right-unit-law-add-vec-Semiringᵉ empty-vecᵉ = reflᵉ
  right-unit-law-add-vec-Semiringᵉ (xᵉ ∷ᵉ vᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( right-unit-law-add-Semiringᵉ Rᵉ xᵉ)
      ( right-unit-law-add-vec-Semiringᵉ vᵉ)

  vec-Semiring-Monoidᵉ : ℕᵉ → Monoidᵉ lᵉ
  pr1ᵉ (vec-Semiring-Monoidᵉ nᵉ) = vec-Semiring-Semigroupᵉ nᵉ
  pr1ᵉ (pr2ᵉ (vec-Semiring-Monoidᵉ nᵉ)) = zero-vec-Semiringᵉ Rᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (vec-Semiring-Monoidᵉ nᵉ))) = left-unit-law-add-vec-Semiringᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (vec-Semiring-Monoidᵉ nᵉ))) = right-unit-law-add-vec-Semiringᵉ

  commutative-add-vec-Semiringᵉ :
    {nᵉ : ℕᵉ} (vᵉ wᵉ : vec-Semiringᵉ Rᵉ nᵉ) →
    add-vec-Semiringᵉ vᵉ wᵉ ＝ᵉ add-vec-Semiringᵉ wᵉ vᵉ
  commutative-add-vec-Semiringᵉ empty-vecᵉ empty-vecᵉ = reflᵉ
  commutative-add-vec-Semiringᵉ (xᵉ ∷ᵉ vᵉ) (yᵉ ∷ᵉ wᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( commutative-add-Semiringᵉ Rᵉ xᵉ yᵉ)
      ( commutative-add-vec-Semiringᵉ vᵉ wᵉ)

  vec-Semiring-Commutative-Monoidᵉ : ℕᵉ → Commutative-Monoidᵉ lᵉ
  pr1ᵉ (vec-Semiring-Commutative-Monoidᵉ nᵉ) = vec-Semiring-Monoidᵉ nᵉ
  pr2ᵉ (vec-Semiring-Commutative-Monoidᵉ nᵉ) = commutative-add-vec-Semiringᵉ
```

#### Pointwise addition of functional vectors on a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  add-functional-vec-Semiringᵉ :
    (nᵉ : ℕᵉ) (vᵉ wᵉ : functional-vec-Semiringᵉ Rᵉ nᵉ) → functional-vec-Semiringᵉ Rᵉ nᵉ
  add-functional-vec-Semiringᵉ nᵉ = binary-map-functional-vecᵉ nᵉ (add-Semiringᵉ Rᵉ)

  associative-add-functional-vec-Semiringᵉ :
    (nᵉ : ℕᵉ) (v1ᵉ v2ᵉ v3ᵉ : functional-vec-Semiringᵉ Rᵉ nᵉ) →
    ( add-functional-vec-Semiringᵉ nᵉ (add-functional-vec-Semiringᵉ nᵉ v1ᵉ v2ᵉ) v3ᵉ) ＝ᵉ
    ( add-functional-vec-Semiringᵉ nᵉ v1ᵉ (add-functional-vec-Semiringᵉ nᵉ v2ᵉ v3ᵉ))
  associative-add-functional-vec-Semiringᵉ nᵉ v1ᵉ v2ᵉ v3ᵉ =
    eq-htpyᵉ (λ iᵉ → associative-add-Semiringᵉ Rᵉ (v1ᵉ iᵉ) (v2ᵉ iᵉ) (v3ᵉ iᵉ))

  functional-vec-Semiring-Semigroupᵉ : ℕᵉ → Semigroupᵉ lᵉ
  pr1ᵉ (functional-vec-Semiring-Semigroupᵉ nᵉ) =
    functional-vec-Setᵉ (set-Semiringᵉ Rᵉ) nᵉ
  pr1ᵉ (pr2ᵉ (functional-vec-Semiring-Semigroupᵉ nᵉ)) =
    add-functional-vec-Semiringᵉ nᵉ
  pr2ᵉ (pr2ᵉ (functional-vec-Semiring-Semigroupᵉ nᵉ)) =
    associative-add-functional-vec-Semiringᵉ nᵉ

  left-unit-law-add-functional-vec-Semiringᵉ :
    (nᵉ : ℕᵉ) (vᵉ : functional-vec-Semiringᵉ Rᵉ nᵉ) →
    add-functional-vec-Semiringᵉ nᵉ (zero-functional-vec-Semiringᵉ Rᵉ nᵉ) vᵉ ＝ᵉ vᵉ
  left-unit-law-add-functional-vec-Semiringᵉ nᵉ vᵉ =
    eq-htpyᵉ (λ iᵉ → left-unit-law-add-Semiringᵉ Rᵉ (vᵉ iᵉ))

  right-unit-law-add-functional-vec-Semiringᵉ :
    (nᵉ : ℕᵉ) (vᵉ : functional-vec-Semiringᵉ Rᵉ nᵉ) →
    add-functional-vec-Semiringᵉ nᵉ vᵉ (zero-functional-vec-Semiringᵉ Rᵉ nᵉ) ＝ᵉ vᵉ
  right-unit-law-add-functional-vec-Semiringᵉ nᵉ vᵉ =
    eq-htpyᵉ (λ iᵉ → right-unit-law-add-Semiringᵉ Rᵉ (vᵉ iᵉ))

  functional-vec-Semiring-Monoidᵉ : ℕᵉ → Monoidᵉ lᵉ
  pr1ᵉ (functional-vec-Semiring-Monoidᵉ nᵉ) =
    functional-vec-Semiring-Semigroupᵉ nᵉ
  pr1ᵉ (pr2ᵉ (functional-vec-Semiring-Monoidᵉ nᵉ)) =
    zero-functional-vec-Semiringᵉ Rᵉ nᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (functional-vec-Semiring-Monoidᵉ nᵉ))) =
    left-unit-law-add-functional-vec-Semiringᵉ nᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (functional-vec-Semiring-Monoidᵉ nᵉ))) =
    right-unit-law-add-functional-vec-Semiringᵉ nᵉ

  commutative-add-functional-vec-Semiringᵉ :
    (nᵉ : ℕᵉ) (vᵉ wᵉ : functional-vec-Semiringᵉ Rᵉ nᵉ) →
    add-functional-vec-Semiringᵉ nᵉ vᵉ wᵉ ＝ᵉ add-functional-vec-Semiringᵉ nᵉ wᵉ vᵉ
  commutative-add-functional-vec-Semiringᵉ nᵉ vᵉ wᵉ =
    eq-htpyᵉ (λ iᵉ → commutative-add-Semiringᵉ Rᵉ (vᵉ iᵉ) (wᵉ iᵉ))

  functional-vec-Semiring-Commutative-Monoidᵉ : ℕᵉ → Commutative-Monoidᵉ lᵉ
  pr1ᵉ (functional-vec-Semiring-Commutative-Monoidᵉ nᵉ) =
    functional-vec-Semiring-Monoidᵉ nᵉ
  pr2ᵉ (functional-vec-Semiring-Commutative-Monoidᵉ nᵉ) =
    commutative-add-functional-vec-Semiringᵉ nᵉ
```