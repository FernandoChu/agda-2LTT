# Vectors on euclidean domains

```agda
module linear-algebra.vectors-on-euclidean-domainsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.euclidean-domainsᵉ

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
```

</details>

## Idea

Givenᵉ anᵉ euclideanᵉ domainᵉ `R`,ᵉ theᵉ typeᵉ `vecᵉ nᵉ R`ᵉ ofᵉ `R`-vectorsᵉ isᵉ anᵉ
`R`-module.ᵉ

## Definitions

### Listed vectors on euclidean domains

```agda
module _
  {lᵉ : Level} (Rᵉ : Euclidean-Domainᵉ lᵉ)
  where

  vec-Euclidean-Domainᵉ : ℕᵉ → UUᵉ lᵉ
  vec-Euclidean-Domainᵉ = vecᵉ (type-Euclidean-Domainᵉ Rᵉ)

  head-vec-Euclidean-Domainᵉ :
    {nᵉ : ℕᵉ} → vec-Euclidean-Domainᵉ (succ-ℕᵉ nᵉ) → type-Euclidean-Domainᵉ Rᵉ
  head-vec-Euclidean-Domainᵉ vᵉ = head-vecᵉ vᵉ

  tail-vec-Euclidean-Domainᵉ :
    {nᵉ : ℕᵉ} → vec-Euclidean-Domainᵉ (succ-ℕᵉ nᵉ) → vec-Euclidean-Domainᵉ nᵉ
  tail-vec-Euclidean-Domainᵉ vᵉ = tail-vecᵉ vᵉ

  snoc-vec-Euclidean-Domainᵉ :
    {nᵉ : ℕᵉ} → vec-Euclidean-Domainᵉ nᵉ →
    type-Euclidean-Domainᵉ Rᵉ → vec-Euclidean-Domainᵉ (succ-ℕᵉ nᵉ)
  snoc-vec-Euclidean-Domainᵉ vᵉ rᵉ = snoc-vecᵉ vᵉ rᵉ
```

### Functional vectors on euclidean domains

```agda
module _
  {lᵉ : Level} (Rᵉ : Euclidean-Domainᵉ lᵉ)
  where

  functional-vec-Euclidean-Domainᵉ : ℕᵉ → UUᵉ lᵉ
  functional-vec-Euclidean-Domainᵉ = functional-vecᵉ (type-Euclidean-Domainᵉ Rᵉ)

  head-functional-vec-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) →
    functional-vec-Euclidean-Domainᵉ (succ-ℕᵉ nᵉ) →
    type-Euclidean-Domainᵉ Rᵉ
  head-functional-vec-Euclidean-Domainᵉ nᵉ vᵉ = head-functional-vecᵉ nᵉ vᵉ

  tail-functional-vec-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) →
    functional-vec-Euclidean-Domainᵉ (succ-ℕᵉ nᵉ) →
    functional-vec-Euclidean-Domainᵉ nᵉ
  tail-functional-vec-Euclidean-Domainᵉ = tail-functional-vecᵉ

  cons-functional-vec-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) → type-Euclidean-Domainᵉ Rᵉ →
    functional-vec-Euclidean-Domainᵉ nᵉ →
    functional-vec-Euclidean-Domainᵉ (succ-ℕᵉ nᵉ)
  cons-functional-vec-Euclidean-Domainᵉ = cons-functional-vecᵉ

  snoc-functional-vec-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Euclidean-Domainᵉ nᵉ → type-Euclidean-Domainᵉ Rᵉ →
    functional-vec-Euclidean-Domainᵉ (succ-ℕᵉ nᵉ)
  snoc-functional-vec-Euclidean-Domainᵉ = snoc-functional-vecᵉ
```

### Zero vector on a euclidean domain

#### The zero listed vector

```agda
module _
  {lᵉ : Level} (Rᵉ : Euclidean-Domainᵉ lᵉ)
  where

  zero-vec-Euclidean-Domainᵉ : {nᵉ : ℕᵉ} → vec-Euclidean-Domainᵉ Rᵉ nᵉ
  zero-vec-Euclidean-Domainᵉ = constant-vecᵉ (zero-Euclidean-Domainᵉ Rᵉ)
```

#### The zero functional vector

```agda
module _
  {lᵉ : Level} (Rᵉ : Euclidean-Domainᵉ lᵉ)
  where

  zero-functional-vec-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Euclidean-Domainᵉ Rᵉ nᵉ
  zero-functional-vec-Euclidean-Domainᵉ nᵉ iᵉ = zero-Euclidean-Domainᵉ Rᵉ
```

### Pointwise addition of vectors on a euclidean domain

#### Pointwise addition of listed vectors on a euclidean domain

```agda
module _
  {lᵉ : Level} (Rᵉ : Euclidean-Domainᵉ lᵉ)
  where

  add-vec-Euclidean-Domainᵉ :
    {nᵉ : ℕᵉ} →
    vec-Euclidean-Domainᵉ Rᵉ nᵉ →
    vec-Euclidean-Domainᵉ Rᵉ nᵉ →
    vec-Euclidean-Domainᵉ Rᵉ nᵉ
  add-vec-Euclidean-Domainᵉ = binary-map-vecᵉ (add-Euclidean-Domainᵉ Rᵉ)

  associative-add-vec-Euclidean-Domainᵉ :
    {nᵉ : ℕᵉ} (v1ᵉ v2ᵉ v3ᵉ : vec-Euclidean-Domainᵉ Rᵉ nᵉ) →
    Idᵉ
      ( add-vec-Euclidean-Domainᵉ (add-vec-Euclidean-Domainᵉ v1ᵉ v2ᵉ) v3ᵉ)
      ( add-vec-Euclidean-Domainᵉ v1ᵉ (add-vec-Euclidean-Domainᵉ v2ᵉ v3ᵉ))
  associative-add-vec-Euclidean-Domainᵉ empty-vecᵉ empty-vecᵉ empty-vecᵉ = reflᵉ
  associative-add-vec-Euclidean-Domainᵉ (xᵉ ∷ᵉ v1ᵉ) (yᵉ ∷ᵉ v2ᵉ) (zᵉ ∷ᵉ v3ᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( associative-add-Euclidean-Domainᵉ Rᵉ xᵉ yᵉ zᵉ)
      ( associative-add-vec-Euclidean-Domainᵉ v1ᵉ v2ᵉ v3ᵉ)

  vec-Euclidean-Domain-Semigroupᵉ : ℕᵉ → Semigroupᵉ lᵉ
  pr1ᵉ (vec-Euclidean-Domain-Semigroupᵉ nᵉ) = vec-Setᵉ (set-Euclidean-Domainᵉ Rᵉ) nᵉ
  pr1ᵉ (pr2ᵉ (vec-Euclidean-Domain-Semigroupᵉ nᵉ)) = add-vec-Euclidean-Domainᵉ
  pr2ᵉ (pr2ᵉ (vec-Euclidean-Domain-Semigroupᵉ nᵉ)) =
    associative-add-vec-Euclidean-Domainᵉ

  left-unit-law-add-vec-Euclidean-Domainᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vec-Euclidean-Domainᵉ Rᵉ nᵉ) →
    Idᵉ (add-vec-Euclidean-Domainᵉ (zero-vec-Euclidean-Domainᵉ Rᵉ) vᵉ) vᵉ
  left-unit-law-add-vec-Euclidean-Domainᵉ empty-vecᵉ = reflᵉ
  left-unit-law-add-vec-Euclidean-Domainᵉ (xᵉ ∷ᵉ vᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( left-unit-law-add-Euclidean-Domainᵉ Rᵉ xᵉ)
      ( left-unit-law-add-vec-Euclidean-Domainᵉ vᵉ)

  right-unit-law-add-vec-Euclidean-Domainᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vec-Euclidean-Domainᵉ Rᵉ nᵉ) →
    Idᵉ (add-vec-Euclidean-Domainᵉ vᵉ (zero-vec-Euclidean-Domainᵉ Rᵉ)) vᵉ
  right-unit-law-add-vec-Euclidean-Domainᵉ empty-vecᵉ = reflᵉ
  right-unit-law-add-vec-Euclidean-Domainᵉ (xᵉ ∷ᵉ vᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( right-unit-law-add-Euclidean-Domainᵉ Rᵉ xᵉ)
      ( right-unit-law-add-vec-Euclidean-Domainᵉ vᵉ)

  vec-Euclidean-Domain-Monoidᵉ : ℕᵉ → Monoidᵉ lᵉ
  pr1ᵉ (vec-Euclidean-Domain-Monoidᵉ nᵉ) = vec-Euclidean-Domain-Semigroupᵉ nᵉ
  pr1ᵉ (pr2ᵉ (vec-Euclidean-Domain-Monoidᵉ nᵉ)) = zero-vec-Euclidean-Domainᵉ Rᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (vec-Euclidean-Domain-Monoidᵉ nᵉ))) =
    left-unit-law-add-vec-Euclidean-Domainᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (vec-Euclidean-Domain-Monoidᵉ nᵉ))) =
    right-unit-law-add-vec-Euclidean-Domainᵉ

  commutative-add-vec-Euclidean-Domainᵉ :
    {nᵉ : ℕᵉ} (vᵉ wᵉ : vec-Euclidean-Domainᵉ Rᵉ nᵉ) →
    Idᵉ (add-vec-Euclidean-Domainᵉ vᵉ wᵉ) (add-vec-Euclidean-Domainᵉ wᵉ vᵉ)
  commutative-add-vec-Euclidean-Domainᵉ empty-vecᵉ empty-vecᵉ = reflᵉ
  commutative-add-vec-Euclidean-Domainᵉ (xᵉ ∷ᵉ vᵉ) (yᵉ ∷ᵉ wᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( commutative-add-Euclidean-Domainᵉ Rᵉ xᵉ yᵉ)
      ( commutative-add-vec-Euclidean-Domainᵉ vᵉ wᵉ)

  vec-Euclidean-Domain-Commutative-Monoidᵉ : ℕᵉ → Commutative-Monoidᵉ lᵉ
  pr1ᵉ (vec-Euclidean-Domain-Commutative-Monoidᵉ nᵉ) =
    vec-Euclidean-Domain-Monoidᵉ nᵉ
  pr2ᵉ (vec-Euclidean-Domain-Commutative-Monoidᵉ nᵉ) =
    commutative-add-vec-Euclidean-Domainᵉ
```

#### Pointwise addition of functional vectors on a euclidean domain

```agda
module _
  {lᵉ : Level} (Rᵉ : Euclidean-Domainᵉ lᵉ)
  where

  add-functional-vec-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) (vᵉ wᵉ : functional-vec-Euclidean-Domainᵉ Rᵉ nᵉ) →
    functional-vec-Euclidean-Domainᵉ Rᵉ nᵉ
  add-functional-vec-Euclidean-Domainᵉ nᵉ =
    binary-map-functional-vecᵉ nᵉ (add-Euclidean-Domainᵉ Rᵉ)

  associative-add-functional-vec-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) (v1ᵉ v2ᵉ v3ᵉ : functional-vec-Euclidean-Domainᵉ Rᵉ nᵉ) →
    ( add-functional-vec-Euclidean-Domainᵉ
      ( nᵉ)
      ( add-functional-vec-Euclidean-Domainᵉ nᵉ v1ᵉ v2ᵉ)
      ( v3ᵉ)) ＝ᵉ
    ( add-functional-vec-Euclidean-Domainᵉ
      ( nᵉ)
      ( v1ᵉ)
      ( add-functional-vec-Euclidean-Domainᵉ nᵉ v2ᵉ v3ᵉ))
  associative-add-functional-vec-Euclidean-Domainᵉ nᵉ v1ᵉ v2ᵉ v3ᵉ =
    eq-htpyᵉ (λ iᵉ → associative-add-Euclidean-Domainᵉ Rᵉ (v1ᵉ iᵉ) (v2ᵉ iᵉ) (v3ᵉ iᵉ))

  functional-vec-Euclidean-Domain-Semigroupᵉ : ℕᵉ → Semigroupᵉ lᵉ
  pr1ᵉ (functional-vec-Euclidean-Domain-Semigroupᵉ nᵉ) =
    functional-vec-Setᵉ (set-Euclidean-Domainᵉ Rᵉ) nᵉ
  pr1ᵉ (pr2ᵉ (functional-vec-Euclidean-Domain-Semigroupᵉ nᵉ)) =
    add-functional-vec-Euclidean-Domainᵉ nᵉ
  pr2ᵉ (pr2ᵉ (functional-vec-Euclidean-Domain-Semigroupᵉ nᵉ)) =
    associative-add-functional-vec-Euclidean-Domainᵉ nᵉ

  left-unit-law-add-functional-vec-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) (vᵉ : functional-vec-Euclidean-Domainᵉ Rᵉ nᵉ) →
    ( add-functional-vec-Euclidean-Domainᵉ
      ( nᵉ)
      ( zero-functional-vec-Euclidean-Domainᵉ Rᵉ nᵉ)
      ( vᵉ)) ＝ᵉ
    ( vᵉ)
  left-unit-law-add-functional-vec-Euclidean-Domainᵉ nᵉ vᵉ =
    eq-htpyᵉ (λ iᵉ → left-unit-law-add-Euclidean-Domainᵉ Rᵉ (vᵉ iᵉ))

  right-unit-law-add-functional-vec-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) (vᵉ : functional-vec-Euclidean-Domainᵉ Rᵉ nᵉ) →
    ( add-functional-vec-Euclidean-Domainᵉ
      ( nᵉ)
      ( vᵉ)
      ( zero-functional-vec-Euclidean-Domainᵉ Rᵉ nᵉ)) ＝ᵉ
    ( vᵉ)
  right-unit-law-add-functional-vec-Euclidean-Domainᵉ nᵉ vᵉ =
    eq-htpyᵉ (λ iᵉ → right-unit-law-add-Euclidean-Domainᵉ Rᵉ (vᵉ iᵉ))

  functional-vec-Euclidean-Domain-Monoidᵉ : ℕᵉ → Monoidᵉ lᵉ
  pr1ᵉ (functional-vec-Euclidean-Domain-Monoidᵉ nᵉ) =
    functional-vec-Euclidean-Domain-Semigroupᵉ nᵉ
  pr1ᵉ (pr2ᵉ (functional-vec-Euclidean-Domain-Monoidᵉ nᵉ)) =
    zero-functional-vec-Euclidean-Domainᵉ Rᵉ nᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (functional-vec-Euclidean-Domain-Monoidᵉ nᵉ))) =
    left-unit-law-add-functional-vec-Euclidean-Domainᵉ nᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (functional-vec-Euclidean-Domain-Monoidᵉ nᵉ))) =
    right-unit-law-add-functional-vec-Euclidean-Domainᵉ nᵉ

  commutative-add-functional-vec-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) (vᵉ wᵉ : functional-vec-Euclidean-Domainᵉ Rᵉ nᵉ) →
    add-functional-vec-Euclidean-Domainᵉ nᵉ vᵉ wᵉ ＝ᵉ
    add-functional-vec-Euclidean-Domainᵉ nᵉ wᵉ vᵉ
  commutative-add-functional-vec-Euclidean-Domainᵉ nᵉ vᵉ wᵉ =
    eq-htpyᵉ (λ iᵉ → commutative-add-Euclidean-Domainᵉ Rᵉ (vᵉ iᵉ) (wᵉ iᵉ))

  functional-vec-Euclidean-Domain-Commutative-Monoidᵉ : ℕᵉ → Commutative-Monoidᵉ lᵉ
  pr1ᵉ (functional-vec-Euclidean-Domain-Commutative-Monoidᵉ nᵉ) =
    functional-vec-Euclidean-Domain-Monoidᵉ nᵉ
  pr2ᵉ (functional-vec-Euclidean-Domain-Commutative-Monoidᵉ nᵉ) =
    commutative-add-functional-vec-Euclidean-Domainᵉ nᵉ
```

### The negative of a vector on a euclidean domain

```agda
module _
  {lᵉ : Level} (Rᵉ : Euclidean-Domainᵉ lᵉ)
  where

  neg-vec-Euclidean-Domainᵉ :
    {nᵉ : ℕᵉ} → vec-Euclidean-Domainᵉ Rᵉ nᵉ → vec-Euclidean-Domainᵉ Rᵉ nᵉ
  neg-vec-Euclidean-Domainᵉ = map-vecᵉ (neg-Euclidean-Domainᵉ Rᵉ)

  left-inverse-law-add-vec-Euclidean-Domainᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vec-Euclidean-Domainᵉ Rᵉ nᵉ) →
    Idᵉ
      ( add-vec-Euclidean-Domainᵉ Rᵉ (neg-vec-Euclidean-Domainᵉ vᵉ) vᵉ)
      ( zero-vec-Euclidean-Domainᵉ Rᵉ)
  left-inverse-law-add-vec-Euclidean-Domainᵉ empty-vecᵉ = reflᵉ
  left-inverse-law-add-vec-Euclidean-Domainᵉ (xᵉ ∷ᵉ vᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( left-inverse-law-add-Euclidean-Domainᵉ Rᵉ xᵉ)
      ( left-inverse-law-add-vec-Euclidean-Domainᵉ vᵉ)

  right-inverse-law-add-vec-Euclidean-Domainᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vec-Euclidean-Domainᵉ Rᵉ nᵉ) →
    Idᵉ
      ( add-vec-Euclidean-Domainᵉ Rᵉ vᵉ (neg-vec-Euclidean-Domainᵉ vᵉ))
      ( zero-vec-Euclidean-Domainᵉ Rᵉ)
  right-inverse-law-add-vec-Euclidean-Domainᵉ empty-vecᵉ = reflᵉ
  right-inverse-law-add-vec-Euclidean-Domainᵉ (xᵉ ∷ᵉ vᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( right-inverse-law-add-Euclidean-Domainᵉ Rᵉ xᵉ)
      ( right-inverse-law-add-vec-Euclidean-Domainᵉ vᵉ)

  is-unital-vec-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) → is-unitalᵉ (add-vec-Euclidean-Domainᵉ Rᵉ {nᵉ})
  pr1ᵉ (is-unital-vec-Euclidean-Domainᵉ nᵉ) = zero-vec-Euclidean-Domainᵉ Rᵉ
  pr1ᵉ (pr2ᵉ (is-unital-vec-Euclidean-Domainᵉ nᵉ)) =
    left-unit-law-add-vec-Euclidean-Domainᵉ Rᵉ
  pr2ᵉ (pr2ᵉ (is-unital-vec-Euclidean-Domainᵉ nᵉ)) =
    right-unit-law-add-vec-Euclidean-Domainᵉ Rᵉ

  is-group-vec-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) → is-group-Semigroupᵉ (vec-Euclidean-Domain-Semigroupᵉ Rᵉ nᵉ)
  pr1ᵉ (is-group-vec-Euclidean-Domainᵉ nᵉ) = is-unital-vec-Euclidean-Domainᵉ nᵉ
  pr1ᵉ (pr2ᵉ (is-group-vec-Euclidean-Domainᵉ nᵉ)) = neg-vec-Euclidean-Domainᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (is-group-vec-Euclidean-Domainᵉ nᵉ))) =
    left-inverse-law-add-vec-Euclidean-Domainᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (is-group-vec-Euclidean-Domainᵉ nᵉ))) =
    right-inverse-law-add-vec-Euclidean-Domainᵉ

  vec-Euclidean-Domain-Groupᵉ : ℕᵉ → Groupᵉ lᵉ
  pr1ᵉ (vec-Euclidean-Domain-Groupᵉ nᵉ) = vec-Euclidean-Domain-Semigroupᵉ Rᵉ nᵉ
  pr2ᵉ (vec-Euclidean-Domain-Groupᵉ nᵉ) = is-group-vec-Euclidean-Domainᵉ nᵉ

  vec-Euclidean-Domain-Abᵉ : ℕᵉ → Abᵉ lᵉ
  pr1ᵉ (vec-Euclidean-Domain-Abᵉ nᵉ) = vec-Euclidean-Domain-Groupᵉ nᵉ
  pr2ᵉ (vec-Euclidean-Domain-Abᵉ nᵉ) = commutative-add-vec-Euclidean-Domainᵉ Rᵉ
```