# Vectors on rings

```agda
module linear-algebra.vectors-on-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.commutative-monoidsᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ

open import linear-algebra.constant-vectorsᵉ
open import linear-algebra.functoriality-vectorsᵉ
open import linear-algebra.vectorsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Idea

Givenᵉ aᵉ ringᵉ `R`,ᵉ theᵉ typeᵉ `vecᵉ nᵉ R`ᵉ ofᵉ `R`-vectorsᵉ isᵉ anᵉ `R`-module.ᵉ

## Definitions

### Listed vectors on rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  vec-Ringᵉ : ℕᵉ → UUᵉ lᵉ
  vec-Ringᵉ = vecᵉ (type-Ringᵉ Rᵉ)

  head-vec-Ringᵉ : {nᵉ : ℕᵉ} → vec-Ringᵉ (succ-ℕᵉ nᵉ) → type-Ringᵉ Rᵉ
  head-vec-Ringᵉ vᵉ = head-vecᵉ vᵉ

  tail-vec-Ringᵉ : {nᵉ : ℕᵉ} → vec-Ringᵉ (succ-ℕᵉ nᵉ) → vec-Ringᵉ nᵉ
  tail-vec-Ringᵉ vᵉ = tail-vecᵉ vᵉ

  snoc-vec-Ringᵉ : {nᵉ : ℕᵉ} → vec-Ringᵉ nᵉ → type-Ringᵉ Rᵉ → vec-Ringᵉ (succ-ℕᵉ nᵉ)
  snoc-vec-Ringᵉ vᵉ rᵉ = snoc-vecᵉ vᵉ rᵉ
```

### Functional vectors on rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  functional-vec-Ringᵉ : ℕᵉ → UUᵉ lᵉ
  functional-vec-Ringᵉ = functional-vecᵉ (type-Ringᵉ Rᵉ)

  head-functional-vec-Ringᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Ringᵉ (succ-ℕᵉ nᵉ) → type-Ringᵉ Rᵉ
  head-functional-vec-Ringᵉ nᵉ vᵉ = head-functional-vecᵉ nᵉ vᵉ

  tail-functional-vec-Ringᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Ringᵉ (succ-ℕᵉ nᵉ) → functional-vec-Ringᵉ nᵉ
  tail-functional-vec-Ringᵉ = tail-functional-vecᵉ

  cons-functional-vec-Ringᵉ :
    (nᵉ : ℕᵉ) → type-Ringᵉ Rᵉ →
    functional-vec-Ringᵉ nᵉ → functional-vec-Ringᵉ (succ-ℕᵉ nᵉ)
  cons-functional-vec-Ringᵉ = cons-functional-vecᵉ

  snoc-functional-vec-Ringᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Ringᵉ nᵉ → type-Ringᵉ Rᵉ →
    functional-vec-Ringᵉ (succ-ℕᵉ nᵉ)
  snoc-functional-vec-Ringᵉ = snoc-functional-vecᵉ
```

### Zero vector on a ring

#### The zero listed vector

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  zero-vec-Ringᵉ : {nᵉ : ℕᵉ} → vec-Ringᵉ Rᵉ nᵉ
  zero-vec-Ringᵉ = constant-vecᵉ (zero-Ringᵉ Rᵉ)
```

#### The zero functional vector

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  zero-functional-vec-Ringᵉ : (nᵉ : ℕᵉ) → functional-vec-Ringᵉ Rᵉ nᵉ
  zero-functional-vec-Ringᵉ nᵉ iᵉ = zero-Ringᵉ Rᵉ
```

### Pointwise addition of vectors on a ring

#### Pointwise addition of listed vectors on a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  add-vec-Ringᵉ : {nᵉ : ℕᵉ} → vec-Ringᵉ Rᵉ nᵉ → vec-Ringᵉ Rᵉ nᵉ → vec-Ringᵉ Rᵉ nᵉ
  add-vec-Ringᵉ = binary-map-vecᵉ (add-Ringᵉ Rᵉ)

  associative-add-vec-Ringᵉ :
    {nᵉ : ℕᵉ} (v1ᵉ v2ᵉ v3ᵉ : vec-Ringᵉ Rᵉ nᵉ) →
    Idᵉ
      ( add-vec-Ringᵉ (add-vec-Ringᵉ v1ᵉ v2ᵉ) v3ᵉ)
      ( add-vec-Ringᵉ v1ᵉ (add-vec-Ringᵉ v2ᵉ v3ᵉ))
  associative-add-vec-Ringᵉ empty-vecᵉ empty-vecᵉ empty-vecᵉ = reflᵉ
  associative-add-vec-Ringᵉ (xᵉ ∷ᵉ v1ᵉ) (yᵉ ∷ᵉ v2ᵉ) (zᵉ ∷ᵉ v3ᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( associative-add-Ringᵉ Rᵉ xᵉ yᵉ zᵉ)
      ( associative-add-vec-Ringᵉ v1ᵉ v2ᵉ v3ᵉ)

  vec-Ring-Semigroupᵉ : ℕᵉ → Semigroupᵉ lᵉ
  pr1ᵉ (vec-Ring-Semigroupᵉ nᵉ) = vec-Setᵉ (set-Ringᵉ Rᵉ) nᵉ
  pr1ᵉ (pr2ᵉ (vec-Ring-Semigroupᵉ nᵉ)) = add-vec-Ringᵉ
  pr2ᵉ (pr2ᵉ (vec-Ring-Semigroupᵉ nᵉ)) = associative-add-vec-Ringᵉ

  left-unit-law-add-vec-Ringᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vec-Ringᵉ Rᵉ nᵉ) → Idᵉ (add-vec-Ringᵉ (zero-vec-Ringᵉ Rᵉ) vᵉ) vᵉ
  left-unit-law-add-vec-Ringᵉ empty-vecᵉ = reflᵉ
  left-unit-law-add-vec-Ringᵉ (xᵉ ∷ᵉ vᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( left-unit-law-add-Ringᵉ Rᵉ xᵉ)
      ( left-unit-law-add-vec-Ringᵉ vᵉ)

  right-unit-law-add-vec-Ringᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vec-Ringᵉ Rᵉ nᵉ) → Idᵉ (add-vec-Ringᵉ vᵉ (zero-vec-Ringᵉ Rᵉ)) vᵉ
  right-unit-law-add-vec-Ringᵉ empty-vecᵉ = reflᵉ
  right-unit-law-add-vec-Ringᵉ (xᵉ ∷ᵉ vᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( right-unit-law-add-Ringᵉ Rᵉ xᵉ)
      ( right-unit-law-add-vec-Ringᵉ vᵉ)

  vec-Ring-Monoidᵉ : ℕᵉ → Monoidᵉ lᵉ
  pr1ᵉ (vec-Ring-Monoidᵉ nᵉ) = vec-Ring-Semigroupᵉ nᵉ
  pr1ᵉ (pr2ᵉ (vec-Ring-Monoidᵉ nᵉ)) = zero-vec-Ringᵉ Rᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (vec-Ring-Monoidᵉ nᵉ))) = left-unit-law-add-vec-Ringᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (vec-Ring-Monoidᵉ nᵉ))) = right-unit-law-add-vec-Ringᵉ

  commutative-add-vec-Ringᵉ :
    {nᵉ : ℕᵉ} (vᵉ wᵉ : vec-Ringᵉ Rᵉ nᵉ) → Idᵉ (add-vec-Ringᵉ vᵉ wᵉ) (add-vec-Ringᵉ wᵉ vᵉ)
  commutative-add-vec-Ringᵉ empty-vecᵉ empty-vecᵉ = reflᵉ
  commutative-add-vec-Ringᵉ (xᵉ ∷ᵉ vᵉ) (yᵉ ∷ᵉ wᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( commutative-add-Ringᵉ Rᵉ xᵉ yᵉ)
      ( commutative-add-vec-Ringᵉ vᵉ wᵉ)

  vec-Ring-Commutative-Monoidᵉ : ℕᵉ → Commutative-Monoidᵉ lᵉ
  pr1ᵉ (vec-Ring-Commutative-Monoidᵉ nᵉ) = vec-Ring-Monoidᵉ nᵉ
  pr2ᵉ (vec-Ring-Commutative-Monoidᵉ nᵉ) = commutative-add-vec-Ringᵉ
```

#### Pointwise addition of functional vectors on a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  add-functional-vec-Ringᵉ :
    (nᵉ : ℕᵉ) (vᵉ wᵉ : functional-vec-Ringᵉ Rᵉ nᵉ) → functional-vec-Ringᵉ Rᵉ nᵉ
  add-functional-vec-Ringᵉ nᵉ = binary-map-functional-vecᵉ nᵉ (add-Ringᵉ Rᵉ)

  associative-add-functional-vec-Ringᵉ :
    (nᵉ : ℕᵉ) (v1ᵉ v2ᵉ v3ᵉ : functional-vec-Ringᵉ Rᵉ nᵉ) →
    ( add-functional-vec-Ringᵉ nᵉ (add-functional-vec-Ringᵉ nᵉ v1ᵉ v2ᵉ) v3ᵉ) ＝ᵉ
    ( add-functional-vec-Ringᵉ nᵉ v1ᵉ (add-functional-vec-Ringᵉ nᵉ v2ᵉ v3ᵉ))
  associative-add-functional-vec-Ringᵉ nᵉ v1ᵉ v2ᵉ v3ᵉ =
    eq-htpyᵉ (λ iᵉ → associative-add-Ringᵉ Rᵉ (v1ᵉ iᵉ) (v2ᵉ iᵉ) (v3ᵉ iᵉ))

  functional-vec-Ring-Semigroupᵉ : ℕᵉ → Semigroupᵉ lᵉ
  pr1ᵉ (functional-vec-Ring-Semigroupᵉ nᵉ) = functional-vec-Setᵉ (set-Ringᵉ Rᵉ) nᵉ
  pr1ᵉ (pr2ᵉ (functional-vec-Ring-Semigroupᵉ nᵉ)) = add-functional-vec-Ringᵉ nᵉ
  pr2ᵉ (pr2ᵉ (functional-vec-Ring-Semigroupᵉ nᵉ)) =
    associative-add-functional-vec-Ringᵉ nᵉ

  left-unit-law-add-functional-vec-Ringᵉ :
    (nᵉ : ℕᵉ) (vᵉ : functional-vec-Ringᵉ Rᵉ nᵉ) →
    add-functional-vec-Ringᵉ nᵉ (zero-functional-vec-Ringᵉ Rᵉ nᵉ) vᵉ ＝ᵉ vᵉ
  left-unit-law-add-functional-vec-Ringᵉ nᵉ vᵉ =
    eq-htpyᵉ (λ iᵉ → left-unit-law-add-Ringᵉ Rᵉ (vᵉ iᵉ))

  right-unit-law-add-functional-vec-Ringᵉ :
    (nᵉ : ℕᵉ) (vᵉ : functional-vec-Ringᵉ Rᵉ nᵉ) →
    add-functional-vec-Ringᵉ nᵉ vᵉ (zero-functional-vec-Ringᵉ Rᵉ nᵉ) ＝ᵉ vᵉ
  right-unit-law-add-functional-vec-Ringᵉ nᵉ vᵉ =
    eq-htpyᵉ (λ iᵉ → right-unit-law-add-Ringᵉ Rᵉ (vᵉ iᵉ))

  functional-vec-Ring-Monoidᵉ : ℕᵉ → Monoidᵉ lᵉ
  pr1ᵉ (functional-vec-Ring-Monoidᵉ nᵉ) =
    functional-vec-Ring-Semigroupᵉ nᵉ
  pr1ᵉ (pr2ᵉ (functional-vec-Ring-Monoidᵉ nᵉ)) =
    zero-functional-vec-Ringᵉ Rᵉ nᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (functional-vec-Ring-Monoidᵉ nᵉ))) =
    left-unit-law-add-functional-vec-Ringᵉ nᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (functional-vec-Ring-Monoidᵉ nᵉ))) =
    right-unit-law-add-functional-vec-Ringᵉ nᵉ

  commutative-add-functional-vec-Ringᵉ :
    (nᵉ : ℕᵉ) (vᵉ wᵉ : functional-vec-Ringᵉ Rᵉ nᵉ) →
    add-functional-vec-Ringᵉ nᵉ vᵉ wᵉ ＝ᵉ add-functional-vec-Ringᵉ nᵉ wᵉ vᵉ
  commutative-add-functional-vec-Ringᵉ nᵉ vᵉ wᵉ =
    eq-htpyᵉ (λ iᵉ → commutative-add-Ringᵉ Rᵉ (vᵉ iᵉ) (wᵉ iᵉ))

  functional-vec-Ring-Commutative-Monoidᵉ : ℕᵉ → Commutative-Monoidᵉ lᵉ
  pr1ᵉ (functional-vec-Ring-Commutative-Monoidᵉ nᵉ) =
    functional-vec-Ring-Monoidᵉ nᵉ
  pr2ᵉ (functional-vec-Ring-Commutative-Monoidᵉ nᵉ) =
    commutative-add-functional-vec-Ringᵉ nᵉ
```

### The negative of a vector on a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  neg-vec-Ringᵉ : {nᵉ : ℕᵉ} → vec-Ringᵉ Rᵉ nᵉ → vec-Ringᵉ Rᵉ nᵉ
  neg-vec-Ringᵉ = map-vecᵉ (neg-Ringᵉ Rᵉ)

  left-inverse-law-add-vec-Ringᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vec-Ringᵉ Rᵉ nᵉ) →
    Idᵉ (add-vec-Ringᵉ Rᵉ (neg-vec-Ringᵉ vᵉ) vᵉ) (zero-vec-Ringᵉ Rᵉ)
  left-inverse-law-add-vec-Ringᵉ empty-vecᵉ = reflᵉ
  left-inverse-law-add-vec-Ringᵉ (xᵉ ∷ᵉ vᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( left-inverse-law-add-Ringᵉ Rᵉ xᵉ)
      ( left-inverse-law-add-vec-Ringᵉ vᵉ)

  right-inverse-law-add-vec-Ringᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vec-Ringᵉ Rᵉ nᵉ) →
    Idᵉ (add-vec-Ringᵉ Rᵉ vᵉ (neg-vec-Ringᵉ vᵉ)) (zero-vec-Ringᵉ Rᵉ)
  right-inverse-law-add-vec-Ringᵉ empty-vecᵉ = reflᵉ
  right-inverse-law-add-vec-Ringᵉ (xᵉ ∷ᵉ vᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( right-inverse-law-add-Ringᵉ Rᵉ xᵉ)
      ( right-inverse-law-add-vec-Ringᵉ vᵉ)

  is-unital-vec-Ringᵉ : (nᵉ : ℕᵉ) → is-unitalᵉ (add-vec-Ringᵉ Rᵉ {nᵉ})
  pr1ᵉ (is-unital-vec-Ringᵉ nᵉ) = zero-vec-Ringᵉ Rᵉ
  pr1ᵉ (pr2ᵉ (is-unital-vec-Ringᵉ nᵉ)) = left-unit-law-add-vec-Ringᵉ Rᵉ
  pr2ᵉ (pr2ᵉ (is-unital-vec-Ringᵉ nᵉ)) = right-unit-law-add-vec-Ringᵉ Rᵉ

  is-group-vec-Ringᵉ : (nᵉ : ℕᵉ) → is-group-Semigroupᵉ (vec-Ring-Semigroupᵉ Rᵉ nᵉ)
  pr1ᵉ (is-group-vec-Ringᵉ nᵉ) = is-unital-vec-Ringᵉ nᵉ
  pr1ᵉ (pr2ᵉ (is-group-vec-Ringᵉ nᵉ)) = neg-vec-Ringᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (is-group-vec-Ringᵉ nᵉ))) = left-inverse-law-add-vec-Ringᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (is-group-vec-Ringᵉ nᵉ))) = right-inverse-law-add-vec-Ringᵉ

  vec-Ring-Groupᵉ : ℕᵉ → Groupᵉ lᵉ
  pr1ᵉ (vec-Ring-Groupᵉ nᵉ) = vec-Ring-Semigroupᵉ Rᵉ nᵉ
  pr2ᵉ (vec-Ring-Groupᵉ nᵉ) = is-group-vec-Ringᵉ nᵉ

  vec-Ring-Abᵉ : ℕᵉ → Abᵉ lᵉ
  pr1ᵉ (vec-Ring-Abᵉ nᵉ) = vec-Ring-Groupᵉ nᵉ
  pr2ᵉ (vec-Ring-Abᵉ nᵉ) = commutative-add-vec-Ringᵉ Rᵉ
```