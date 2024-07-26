# Commutative finite rings

```agda
module finite-algebra.commutative-finite-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.commutative-semiringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import finite-algebra.finite-ringsᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-embeddingsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.interchange-lawᵉ
open import foundation.involutionsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.commutative-monoidsᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ

open import lists.concatenation-listsᵉ
open import lists.listsᵉ

open import ring-theory.ringsᵉ
open import ring-theory.semiringsᵉ

open import univalent-combinatorics.dependent-function-typesᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ finiteᵉ ringᵉ `A`ᵉ isᵉ saidᵉ to beᵉ **commutative**ᵉ ifᵉ itsᵉ multiplicativeᵉ operationᵉ
isᵉ commutative,ᵉ i.e.,ᵉ ifᵉ `xyᵉ = yx`ᵉ forᵉ allᵉ `x,ᵉ yᵉ ∈ᵉ A`.ᵉ

## Definition

### Commutative finite rings

```agda
is-commutative-Ring-𝔽ᵉ :
  { lᵉ : Level} → Ring-𝔽ᵉ lᵉ → UUᵉ lᵉ
is-commutative-Ring-𝔽ᵉ Aᵉ =
  is-commutative-Ringᵉ (ring-Ring-𝔽ᵉ Aᵉ)

is-prop-is-commutative-Ring-𝔽ᵉ :
  { lᵉ : Level} (Aᵉ : Ring-𝔽ᵉ lᵉ) → is-propᵉ (is-commutative-Ring-𝔽ᵉ Aᵉ)
is-prop-is-commutative-Ring-𝔽ᵉ Aᵉ =
  is-prop-Πᵉ
    ( λ xᵉ →
      is-prop-Πᵉ
      ( λ yᵉ →
        is-set-type-Ring-𝔽ᵉ Aᵉ (mul-Ring-𝔽ᵉ Aᵉ xᵉ yᵉ) (mul-Ring-𝔽ᵉ Aᵉ yᵉ xᵉ)))

Commutative-Ring-𝔽ᵉ :
  ( lᵉ : Level) → UUᵉ (lsuc lᵉ)
Commutative-Ring-𝔽ᵉ lᵉ = Σᵉ (Ring-𝔽ᵉ lᵉ) is-commutative-Ring-𝔽ᵉ

module _
  {lᵉ : Level} (Aᵉ : Commutative-Ring-𝔽ᵉ lᵉ)
  where

  finite-ring-Commutative-Ring-𝔽ᵉ : Ring-𝔽ᵉ lᵉ
  finite-ring-Commutative-Ring-𝔽ᵉ = pr1ᵉ Aᵉ

  ring-Commutative-Ring-𝔽ᵉ : Ringᵉ lᵉ
  ring-Commutative-Ring-𝔽ᵉ = ring-Ring-𝔽ᵉ (finite-ring-Commutative-Ring-𝔽ᵉ)

  commutative-ring-Commutative-Ring-𝔽ᵉ : Commutative-Ringᵉ lᵉ
  pr1ᵉ commutative-ring-Commutative-Ring-𝔽ᵉ = ring-Commutative-Ring-𝔽ᵉ
  pr2ᵉ commutative-ring-Commutative-Ring-𝔽ᵉ = pr2ᵉ Aᵉ

  ab-Commutative-Ring-𝔽ᵉ : Abᵉ lᵉ
  ab-Commutative-Ring-𝔽ᵉ = ab-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  set-Commutative-Ring-𝔽ᵉ : Setᵉ lᵉ
  set-Commutative-Ring-𝔽ᵉ = set-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  type-Commutative-Ring-𝔽ᵉ : UUᵉ lᵉ
  type-Commutative-Ring-𝔽ᵉ = type-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  is-set-type-Commutative-Ring-𝔽ᵉ : is-setᵉ type-Commutative-Ring-𝔽ᵉ
  is-set-type-Commutative-Ring-𝔽ᵉ =
    is-set-type-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  finite-type-Commutative-Ring-𝔽ᵉ : 𝔽ᵉ lᵉ
  finite-type-Commutative-Ring-𝔽ᵉ =
    finite-type-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  is-finite-type-Commutative-Ring-𝔽ᵉ : is-finiteᵉ (type-Commutative-Ring-𝔽ᵉ)
  is-finite-type-Commutative-Ring-𝔽ᵉ =
    is-finite-type-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ
```

### Addition in a commutative finite ring

```agda
  has-associative-add-Commutative-Ring-𝔽ᵉ :
    has-associative-mul-Setᵉ set-Commutative-Ring-𝔽ᵉ
  has-associative-add-Commutative-Ring-𝔽ᵉ =
    has-associative-add-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  add-Commutative-Ring-𝔽ᵉ :
    type-Commutative-Ring-𝔽ᵉ → type-Commutative-Ring-𝔽ᵉ → type-Commutative-Ring-𝔽ᵉ
  add-Commutative-Ring-𝔽ᵉ = add-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  add-Commutative-Ring-𝔽'ᵉ :
    type-Commutative-Ring-𝔽ᵉ → type-Commutative-Ring-𝔽ᵉ → type-Commutative-Ring-𝔽ᵉ
  add-Commutative-Ring-𝔽'ᵉ = add-Ring-𝔽'ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  ap-add-Commutative-Ring-𝔽ᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Commutative-Ring-𝔽ᵉ} →
    (xᵉ ＝ᵉ x'ᵉ) → (yᵉ ＝ᵉ y'ᵉ) →
    add-Commutative-Ring-𝔽ᵉ xᵉ yᵉ ＝ᵉ add-Commutative-Ring-𝔽ᵉ x'ᵉ y'ᵉ
  ap-add-Commutative-Ring-𝔽ᵉ = ap-add-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  associative-add-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ring-𝔽ᵉ) →
    ( add-Commutative-Ring-𝔽ᵉ (add-Commutative-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Commutative-Ring-𝔽ᵉ xᵉ (add-Commutative-Ring-𝔽ᵉ yᵉ zᵉ))
  associative-add-Commutative-Ring-𝔽ᵉ =
    associative-add-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  additive-semigroup-Commutative-Ring-𝔽ᵉ : Semigroupᵉ lᵉ
  additive-semigroup-Commutative-Ring-𝔽ᵉ = semigroup-Abᵉ ab-Commutative-Ring-𝔽ᵉ

  is-group-additive-semigroup-Commutative-Ring-𝔽ᵉ :
    is-group-Semigroupᵉ additive-semigroup-Commutative-Ring-𝔽ᵉ
  is-group-additive-semigroup-Commutative-Ring-𝔽ᵉ =
    is-group-Abᵉ ab-Commutative-Ring-𝔽ᵉ

  commutative-add-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-Commutative-Ring-𝔽ᵉ) →
    Idᵉ (add-Commutative-Ring-𝔽ᵉ xᵉ yᵉ) (add-Commutative-Ring-𝔽ᵉ yᵉ xᵉ)
  commutative-add-Commutative-Ring-𝔽ᵉ = commutative-add-Abᵉ ab-Commutative-Ring-𝔽ᵉ

  interchange-add-add-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ x'ᵉ y'ᵉ : type-Commutative-Ring-𝔽ᵉ) →
    ( add-Commutative-Ring-𝔽ᵉ
      ( add-Commutative-Ring-𝔽ᵉ xᵉ yᵉ)
      ( add-Commutative-Ring-𝔽ᵉ x'ᵉ y'ᵉ)) ＝ᵉ
    ( add-Commutative-Ring-𝔽ᵉ
      ( add-Commutative-Ring-𝔽ᵉ xᵉ x'ᵉ)
      ( add-Commutative-Ring-𝔽ᵉ yᵉ y'ᵉ))
  interchange-add-add-Commutative-Ring-𝔽ᵉ =
    interchange-add-add-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  right-swap-add-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ring-𝔽ᵉ) →
    ( add-Commutative-Ring-𝔽ᵉ (add-Commutative-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Commutative-Ring-𝔽ᵉ (add-Commutative-Ring-𝔽ᵉ xᵉ zᵉ) yᵉ)
  right-swap-add-Commutative-Ring-𝔽ᵉ =
    right-swap-add-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  left-swap-add-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ring-𝔽ᵉ) →
    ( add-Commutative-Ring-𝔽ᵉ xᵉ (add-Commutative-Ring-𝔽ᵉ yᵉ zᵉ)) ＝ᵉ
    ( add-Commutative-Ring-𝔽ᵉ yᵉ (add-Commutative-Ring-𝔽ᵉ xᵉ zᵉ))
  left-swap-add-Commutative-Ring-𝔽ᵉ =
    left-swap-add-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  is-equiv-add-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) → is-equivᵉ (add-Commutative-Ring-𝔽ᵉ xᵉ)
  is-equiv-add-Commutative-Ring-𝔽ᵉ = is-equiv-add-Abᵉ ab-Commutative-Ring-𝔽ᵉ

  is-equiv-add-Commutative-Ring-𝔽'ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) → is-equivᵉ (add-Commutative-Ring-𝔽'ᵉ xᵉ)
  is-equiv-add-Commutative-Ring-𝔽'ᵉ = is-equiv-add-Ab'ᵉ ab-Commutative-Ring-𝔽ᵉ

  is-binary-equiv-add-Commutative-Ring-𝔽ᵉ :
    is-binary-equivᵉ add-Commutative-Ring-𝔽ᵉ
  pr1ᵉ is-binary-equiv-add-Commutative-Ring-𝔽ᵉ = is-equiv-add-Commutative-Ring-𝔽'ᵉ
  pr2ᵉ is-binary-equiv-add-Commutative-Ring-𝔽ᵉ = is-equiv-add-Commutative-Ring-𝔽ᵉ

  is-binary-emb-add-Commutative-Ring-𝔽ᵉ : is-binary-embᵉ add-Commutative-Ring-𝔽ᵉ
  is-binary-emb-add-Commutative-Ring-𝔽ᵉ =
    is-binary-emb-add-Abᵉ ab-Commutative-Ring-𝔽ᵉ

  is-emb-add-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) → is-embᵉ (add-Commutative-Ring-𝔽ᵉ xᵉ)
  is-emb-add-Commutative-Ring-𝔽ᵉ = is-emb-add-Abᵉ ab-Commutative-Ring-𝔽ᵉ

  is-emb-add-Commutative-Ring-𝔽'ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) → is-embᵉ (add-Commutative-Ring-𝔽'ᵉ xᵉ)
  is-emb-add-Commutative-Ring-𝔽'ᵉ = is-emb-add-Ab'ᵉ ab-Commutative-Ring-𝔽ᵉ

  is-injective-add-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) → is-injectiveᵉ (add-Commutative-Ring-𝔽ᵉ xᵉ)
  is-injective-add-Commutative-Ring-𝔽ᵉ =
    is-injective-add-Abᵉ ab-Commutative-Ring-𝔽ᵉ

  is-injective-add-Commutative-Ring-𝔽'ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) → is-injectiveᵉ (add-Commutative-Ring-𝔽'ᵉ xᵉ)
  is-injective-add-Commutative-Ring-𝔽'ᵉ =
    is-injective-add-Ab'ᵉ ab-Commutative-Ring-𝔽ᵉ
```

### The zero element of a commutative finite ring

```agda
  has-zero-Commutative-Ring-𝔽ᵉ : is-unitalᵉ add-Commutative-Ring-𝔽ᵉ
  has-zero-Commutative-Ring-𝔽ᵉ = has-zero-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  zero-Commutative-Ring-𝔽ᵉ : type-Commutative-Ring-𝔽ᵉ
  zero-Commutative-Ring-𝔽ᵉ = zero-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  is-zero-Commutative-Ring-𝔽ᵉ : type-Commutative-Ring-𝔽ᵉ → UUᵉ lᵉ
  is-zero-Commutative-Ring-𝔽ᵉ = is-zero-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  is-nonzero-Commutative-Ring-𝔽ᵉ : type-Commutative-Ring-𝔽ᵉ → UUᵉ lᵉ
  is-nonzero-Commutative-Ring-𝔽ᵉ =
    is-nonzero-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  is-zero-commutative-finite-ring-Propᵉ : type-Commutative-Ring-𝔽ᵉ → Propᵉ lᵉ
  is-zero-commutative-finite-ring-Propᵉ =
    is-zero-commutative-ring-Propᵉ commutative-ring-Commutative-Ring-𝔽ᵉ

  is-nonzero-commutative-finite-ring-Propᵉ : type-Commutative-Ring-𝔽ᵉ → Propᵉ lᵉ
  is-nonzero-commutative-finite-ring-Propᵉ =
    is-nonzero-commutative-ring-Propᵉ commutative-ring-Commutative-Ring-𝔽ᵉ

  left-unit-law-add-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) →
    add-Commutative-Ring-𝔽ᵉ zero-Commutative-Ring-𝔽ᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Commutative-Ring-𝔽ᵉ =
    left-unit-law-add-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  right-unit-law-add-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) →
    add-Commutative-Ring-𝔽ᵉ xᵉ zero-Commutative-Ring-𝔽ᵉ ＝ᵉ xᵉ
  right-unit-law-add-Commutative-Ring-𝔽ᵉ =
    right-unit-law-add-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ
```

### Additive inverses in a commutative finite ring

```agda
  has-negatives-Commutative-Ring-𝔽ᵉ :
    is-group-is-unital-Semigroupᵉ
      ( additive-semigroup-Commutative-Ring-𝔽ᵉ)
      ( has-zero-Commutative-Ring-𝔽ᵉ)
  has-negatives-Commutative-Ring-𝔽ᵉ = has-negatives-Abᵉ ab-Commutative-Ring-𝔽ᵉ

  neg-Commutative-Ring-𝔽ᵉ : type-Commutative-Ring-𝔽ᵉ → type-Commutative-Ring-𝔽ᵉ
  neg-Commutative-Ring-𝔽ᵉ = neg-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  left-inverse-law-add-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) →
    add-Commutative-Ring-𝔽ᵉ (neg-Commutative-Ring-𝔽ᵉ xᵉ) xᵉ ＝ᵉ
    zero-Commutative-Ring-𝔽ᵉ
  left-inverse-law-add-Commutative-Ring-𝔽ᵉ =
    left-inverse-law-add-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  right-inverse-law-add-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) →
    add-Commutative-Ring-𝔽ᵉ xᵉ (neg-Commutative-Ring-𝔽ᵉ xᵉ) ＝ᵉ
    zero-Commutative-Ring-𝔽ᵉ
  right-inverse-law-add-Commutative-Ring-𝔽ᵉ =
    right-inverse-law-add-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  neg-neg-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) →
    neg-Commutative-Ring-𝔽ᵉ (neg-Commutative-Ring-𝔽ᵉ xᵉ) ＝ᵉ xᵉ
  neg-neg-Commutative-Ring-𝔽ᵉ = neg-neg-Abᵉ ab-Commutative-Ring-𝔽ᵉ

  distributive-neg-add-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-Commutative-Ring-𝔽ᵉ) →
    neg-Commutative-Ring-𝔽ᵉ (add-Commutative-Ring-𝔽ᵉ xᵉ yᵉ) ＝ᵉ
    add-Commutative-Ring-𝔽ᵉ (neg-Commutative-Ring-𝔽ᵉ xᵉ) (neg-Commutative-Ring-𝔽ᵉ yᵉ)
  distributive-neg-add-Commutative-Ring-𝔽ᵉ =
    distributive-neg-add-Abᵉ ab-Commutative-Ring-𝔽ᵉ
```

### Multiplication in a commutative finite ring

```agda
  has-associative-mul-Commutative-Ring-𝔽ᵉ :
    has-associative-mul-Setᵉ set-Commutative-Ring-𝔽ᵉ
  has-associative-mul-Commutative-Ring-𝔽ᵉ =
    has-associative-mul-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  mul-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-Commutative-Ring-𝔽ᵉ) → type-Commutative-Ring-𝔽ᵉ
  mul-Commutative-Ring-𝔽ᵉ = mul-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  mul-Commutative-Ring-𝔽'ᵉ :
    (xᵉ yᵉ : type-Commutative-Ring-𝔽ᵉ) → type-Commutative-Ring-𝔽ᵉ
  mul-Commutative-Ring-𝔽'ᵉ = mul-Ring-𝔽'ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  ap-mul-Commutative-Ring-𝔽ᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Commutative-Ring-𝔽ᵉ} (pᵉ : Idᵉ xᵉ x'ᵉ) (qᵉ : Idᵉ yᵉ y'ᵉ) →
    Idᵉ (mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ) (mul-Commutative-Ring-𝔽ᵉ x'ᵉ y'ᵉ)
  ap-mul-Commutative-Ring-𝔽ᵉ pᵉ qᵉ = ap-binaryᵉ mul-Commutative-Ring-𝔽ᵉ pᵉ qᵉ

  associative-mul-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ (mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Commutative-Ring-𝔽ᵉ xᵉ (mul-Commutative-Ring-𝔽ᵉ yᵉ zᵉ)
  associative-mul-Commutative-Ring-𝔽ᵉ =
    associative-mul-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  multiplicative-semigroup-Commutative-Ring-𝔽ᵉ : Semigroupᵉ lᵉ
  pr1ᵉ multiplicative-semigroup-Commutative-Ring-𝔽ᵉ = set-Commutative-Ring-𝔽ᵉ
  pr2ᵉ multiplicative-semigroup-Commutative-Ring-𝔽ᵉ =
    has-associative-mul-Commutative-Ring-𝔽ᵉ

  left-distributive-mul-add-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ring-𝔽ᵉ) →
    ( mul-Commutative-Ring-𝔽ᵉ xᵉ (add-Commutative-Ring-𝔽ᵉ yᵉ zᵉ)) ＝ᵉ
    ( add-Commutative-Ring-𝔽ᵉ
      ( mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ)
      ( mul-Commutative-Ring-𝔽ᵉ xᵉ zᵉ))
  left-distributive-mul-add-Commutative-Ring-𝔽ᵉ =
    left-distributive-mul-add-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  right-distributive-mul-add-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ring-𝔽ᵉ) →
    ( mul-Commutative-Ring-𝔽ᵉ (add-Commutative-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Commutative-Ring-𝔽ᵉ
      ( mul-Commutative-Ring-𝔽ᵉ xᵉ zᵉ)
      ( mul-Commutative-Ring-𝔽ᵉ yᵉ zᵉ))
  right-distributive-mul-add-Commutative-Ring-𝔽ᵉ =
    right-distributive-mul-add-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  commutative-mul-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ ＝ᵉ mul-Commutative-Ring-𝔽ᵉ yᵉ xᵉ
  commutative-mul-Commutative-Ring-𝔽ᵉ = pr2ᵉ Aᵉ
```

### Multiplicative units in a commutative finite ring

```agda
  is-unital-Commutative-Ring-𝔽ᵉ : is-unitalᵉ mul-Commutative-Ring-𝔽ᵉ
  is-unital-Commutative-Ring-𝔽ᵉ = is-unital-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  multiplicative-monoid-Commutative-Ring-𝔽ᵉ : Monoidᵉ lᵉ
  multiplicative-monoid-Commutative-Ring-𝔽ᵉ =
    multiplicative-monoid-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  one-Commutative-Ring-𝔽ᵉ : type-Commutative-Ring-𝔽ᵉ
  one-Commutative-Ring-𝔽ᵉ = one-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  left-unit-law-mul-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ one-Commutative-Ring-𝔽ᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Commutative-Ring-𝔽ᵉ =
    left-unit-law-mul-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  right-unit-law-mul-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ xᵉ one-Commutative-Ring-𝔽ᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Commutative-Ring-𝔽ᵉ =
    right-unit-law-mul-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  right-swap-mul-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ (mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Commutative-Ring-𝔽ᵉ (mul-Commutative-Ring-𝔽ᵉ xᵉ zᵉ) yᵉ
  right-swap-mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ zᵉ =
    ( associative-mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ zᵉ) ∙ᵉ
    ( ( apᵉ
        ( mul-Commutative-Ring-𝔽ᵉ xᵉ)
        ( commutative-mul-Commutative-Ring-𝔽ᵉ yᵉ zᵉ)) ∙ᵉ
      ( invᵉ (associative-mul-Commutative-Ring-𝔽ᵉ xᵉ zᵉ yᵉ)))

  left-swap-mul-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ xᵉ (mul-Commutative-Ring-𝔽ᵉ yᵉ zᵉ) ＝ᵉ
    mul-Commutative-Ring-𝔽ᵉ yᵉ (mul-Commutative-Ring-𝔽ᵉ xᵉ zᵉ)
  left-swap-mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ zᵉ =
    ( invᵉ (associative-mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ zᵉ)) ∙ᵉ
    ( ( apᵉ
        ( mul-Commutative-Ring-𝔽'ᵉ zᵉ)
        ( commutative-mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ)) ∙ᵉ
      ( associative-mul-Commutative-Ring-𝔽ᵉ yᵉ xᵉ zᵉ))

  interchange-mul-mul-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ wᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ
      ( mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ)
      ( mul-Commutative-Ring-𝔽ᵉ zᵉ wᵉ) ＝ᵉ
    mul-Commutative-Ring-𝔽ᵉ
      ( mul-Commutative-Ring-𝔽ᵉ xᵉ zᵉ)
      ( mul-Commutative-Ring-𝔽ᵉ yᵉ wᵉ)
  interchange-mul-mul-Commutative-Ring-𝔽ᵉ =
    interchange-law-commutative-and-associativeᵉ
      mul-Commutative-Ring-𝔽ᵉ
      commutative-mul-Commutative-Ring-𝔽ᵉ
      associative-mul-Commutative-Ring-𝔽ᵉ
```

### The zero laws for multiplication of a commutative finite ring

```agda
  left-zero-law-mul-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ zero-Commutative-Ring-𝔽ᵉ xᵉ ＝ᵉ
    zero-Commutative-Ring-𝔽ᵉ
  left-zero-law-mul-Commutative-Ring-𝔽ᵉ =
    left-zero-law-mul-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  right-zero-law-mul-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ xᵉ zero-Commutative-Ring-𝔽ᵉ ＝ᵉ
    zero-Commutative-Ring-𝔽ᵉ
  right-zero-law-mul-Commutative-Ring-𝔽ᵉ =
    right-zero-law-mul-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ
```

### Commutative rings are commutative finite semirings

```agda
  multiplicative-commutative-monoid-Commutative-Ring-𝔽ᵉ : Commutative-Monoidᵉ lᵉ
  pr1ᵉ multiplicative-commutative-monoid-Commutative-Ring-𝔽ᵉ =
    multiplicative-monoid-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ
  pr2ᵉ multiplicative-commutative-monoid-Commutative-Ring-𝔽ᵉ =
    commutative-mul-Commutative-Ring-𝔽ᵉ

  semifinite-ring-Commutative-Ring-𝔽ᵉ : Semiringᵉ lᵉ
  semifinite-ring-Commutative-Ring-𝔽ᵉ =
    semiring-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  commutative-semiring-Commutative-Ring-𝔽ᵉ : Commutative-Semiringᵉ lᵉ
  pr1ᵉ commutative-semiring-Commutative-Ring-𝔽ᵉ =
    semifinite-ring-Commutative-Ring-𝔽ᵉ
  pr2ᵉ commutative-semiring-Commutative-Ring-𝔽ᵉ =
    commutative-mul-Commutative-Ring-𝔽ᵉ
```

### Computing multiplication with minus one in a ring

```agda
  neg-one-Commutative-Ring-𝔽ᵉ : type-Commutative-Ring-𝔽ᵉ
  neg-one-Commutative-Ring-𝔽ᵉ = neg-one-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  mul-neg-one-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ neg-one-Commutative-Ring-𝔽ᵉ xᵉ ＝ᵉ
    neg-Commutative-Ring-𝔽ᵉ xᵉ
  mul-neg-one-Commutative-Ring-𝔽ᵉ =
    mul-neg-one-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  mul-neg-one-Commutative-Ring-𝔽'ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ xᵉ neg-one-Commutative-Ring-𝔽ᵉ ＝ᵉ
    neg-Commutative-Ring-𝔽ᵉ xᵉ
  mul-neg-one-Commutative-Ring-𝔽'ᵉ =
    mul-neg-one-Ring-𝔽'ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  is-involution-mul-neg-one-Commutative-Ring-𝔽ᵉ :
    is-involutionᵉ (mul-Commutative-Ring-𝔽ᵉ neg-one-Commutative-Ring-𝔽ᵉ)
  is-involution-mul-neg-one-Commutative-Ring-𝔽ᵉ =
    is-involution-mul-neg-one-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  is-involution-mul-neg-one-Commutative-Ring-𝔽'ᵉ :
    is-involutionᵉ (mul-Commutative-Ring-𝔽'ᵉ neg-one-Commutative-Ring-𝔽ᵉ)
  is-involution-mul-neg-one-Commutative-Ring-𝔽'ᵉ =
    is-involution-mul-neg-one-Ring-𝔽'ᵉ finite-ring-Commutative-Ring-𝔽ᵉ
```

### Left and right negative laws for multiplication

```agda
  left-negative-law-mul-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ (neg-Commutative-Ring-𝔽ᵉ xᵉ) yᵉ ＝ᵉ
    neg-Commutative-Ring-𝔽ᵉ (mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ)
  left-negative-law-mul-Commutative-Ring-𝔽ᵉ =
    left-negative-law-mul-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  right-negative-law-mul-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ xᵉ (neg-Commutative-Ring-𝔽ᵉ yᵉ) ＝ᵉ
    neg-Commutative-Ring-𝔽ᵉ (mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ)
  right-negative-law-mul-Commutative-Ring-𝔽ᵉ =
    right-negative-law-mul-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  mul-neg-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ
      ( neg-Commutative-Ring-𝔽ᵉ xᵉ)
      ( neg-Commutative-Ring-𝔽ᵉ yᵉ) ＝ᵉ
    mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ
  mul-neg-Commutative-Ring-𝔽ᵉ = mul-neg-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ
```

### Scalar multiplication of elements of a commutative finite ring by natural numbers

```agda
  mul-nat-scalar-Commutative-Ring-𝔽ᵉ :
    ℕᵉ → type-Commutative-Ring-𝔽ᵉ → type-Commutative-Ring-𝔽ᵉ
  mul-nat-scalar-Commutative-Ring-𝔽ᵉ =
    mul-nat-scalar-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  ap-mul-nat-scalar-Commutative-Ring-𝔽ᵉ :
    {mᵉ nᵉ : ℕᵉ} {xᵉ yᵉ : type-Commutative-Ring-𝔽ᵉ} →
    (mᵉ ＝ᵉ nᵉ) → (xᵉ ＝ᵉ yᵉ) →
    mul-nat-scalar-Commutative-Ring-𝔽ᵉ mᵉ xᵉ ＝ᵉ
    mul-nat-scalar-Commutative-Ring-𝔽ᵉ nᵉ yᵉ
  ap-mul-nat-scalar-Commutative-Ring-𝔽ᵉ =
    ap-mul-nat-scalar-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  left-zero-law-mul-nat-scalar-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-nat-scalar-Commutative-Ring-𝔽ᵉ 0 xᵉ ＝ᵉ zero-Commutative-Ring-𝔽ᵉ
  left-zero-law-mul-nat-scalar-Commutative-Ring-𝔽ᵉ =
    left-zero-law-mul-nat-scalar-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  right-zero-law-mul-nat-scalar-Commutative-Ring-𝔽ᵉ :
    (nᵉ : ℕᵉ) →
    mul-nat-scalar-Commutative-Ring-𝔽ᵉ nᵉ zero-Commutative-Ring-𝔽ᵉ ＝ᵉ
    zero-Commutative-Ring-𝔽ᵉ
  right-zero-law-mul-nat-scalar-Commutative-Ring-𝔽ᵉ =
    right-zero-law-mul-nat-scalar-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  left-unit-law-mul-nat-scalar-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-nat-scalar-Commutative-Ring-𝔽ᵉ 1 xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-nat-scalar-Commutative-Ring-𝔽ᵉ =
    left-unit-law-mul-nat-scalar-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  left-nat-scalar-law-mul-Commutative-Ring-𝔽ᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ (mul-nat-scalar-Commutative-Ring-𝔽ᵉ nᵉ xᵉ) yᵉ ＝ᵉ
    mul-nat-scalar-Commutative-Ring-𝔽ᵉ nᵉ (mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ)
  left-nat-scalar-law-mul-Commutative-Ring-𝔽ᵉ =
    left-nat-scalar-law-mul-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  right-nat-scalar-law-mul-Commutative-Ring-𝔽ᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-Commutative-Ring-𝔽ᵉ xᵉ (mul-nat-scalar-Commutative-Ring-𝔽ᵉ nᵉ yᵉ) ＝ᵉ
    mul-nat-scalar-Commutative-Ring-𝔽ᵉ nᵉ (mul-Commutative-Ring-𝔽ᵉ xᵉ yᵉ)
  right-nat-scalar-law-mul-Commutative-Ring-𝔽ᵉ =
    right-nat-scalar-law-mul-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  left-distributive-mul-nat-scalar-add-Commutative-Ring-𝔽ᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-nat-scalar-Commutative-Ring-𝔽ᵉ nᵉ (add-Commutative-Ring-𝔽ᵉ xᵉ yᵉ) ＝ᵉ
    add-Commutative-Ring-𝔽ᵉ
      ( mul-nat-scalar-Commutative-Ring-𝔽ᵉ nᵉ xᵉ)
      ( mul-nat-scalar-Commutative-Ring-𝔽ᵉ nᵉ yᵉ)
  left-distributive-mul-nat-scalar-add-Commutative-Ring-𝔽ᵉ =
    left-distributive-mul-nat-scalar-add-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  right-distributive-mul-nat-scalar-add-Commutative-Ring-𝔽ᵉ :
    (mᵉ nᵉ : ℕᵉ) (xᵉ : type-Commutative-Ring-𝔽ᵉ) →
    mul-nat-scalar-Commutative-Ring-𝔽ᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    add-Commutative-Ring-𝔽ᵉ
      ( mul-nat-scalar-Commutative-Ring-𝔽ᵉ mᵉ xᵉ)
      ( mul-nat-scalar-Commutative-Ring-𝔽ᵉ nᵉ xᵉ)
  right-distributive-mul-nat-scalar-add-Commutative-Ring-𝔽ᵉ =
    right-distributive-mul-nat-scalar-add-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ
```

### Addition of a list of elements in a commutative finite ring

```agda
  add-list-Commutative-Ring-𝔽ᵉ :
    listᵉ type-Commutative-Ring-𝔽ᵉ → type-Commutative-Ring-𝔽ᵉ
  add-list-Commutative-Ring-𝔽ᵉ = add-list-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ

  preserves-concat-add-list-Commutative-Ring-𝔽ᵉ :
    (l1ᵉ l2ᵉ : listᵉ type-Commutative-Ring-𝔽ᵉ) →
    Idᵉ
      ( add-list-Commutative-Ring-𝔽ᵉ (concat-listᵉ l1ᵉ l2ᵉ))
      ( add-Commutative-Ring-𝔽ᵉ
        ( add-list-Commutative-Ring-𝔽ᵉ l1ᵉ)
        ( add-list-Commutative-Ring-𝔽ᵉ l2ᵉ))
  preserves-concat-add-list-Commutative-Ring-𝔽ᵉ =
    preserves-concat-add-list-Ring-𝔽ᵉ finite-ring-Commutative-Ring-𝔽ᵉ
```

### Equipping a finite type with the structure of a commutative finite ring

```agda
module _
  {l1ᵉ : Level}
  (Xᵉ : 𝔽ᵉ l1ᵉ)
  where

  structure-commutative-ring-𝔽ᵉ :
    UUᵉ l1ᵉ
  structure-commutative-ring-𝔽ᵉ =
    Σᵉ ( structure-ring-𝔽ᵉ Xᵉ)
      ( λ rᵉ → is-commutative-Ring-𝔽ᵉ (finite-ring-structure-ring-𝔽ᵉ Xᵉ rᵉ))

  finite-commutative-ring-structure-commutative-ring-𝔽ᵉ :
    structure-commutative-ring-𝔽ᵉ →
    Commutative-Ring-𝔽ᵉ l1ᵉ
  pr1ᵉ (finite-commutative-ring-structure-commutative-ring-𝔽ᵉ (rᵉ ,ᵉ cᵉ)) =
    finite-ring-structure-ring-𝔽ᵉ Xᵉ rᵉ
  pr2ᵉ (finite-commutative-ring-structure-commutative-ring-𝔽ᵉ (rᵉ ,ᵉ cᵉ)) = cᵉ

  is-finite-structure-commutative-ring-𝔽ᵉ :
    is-finiteᵉ structure-commutative-ring-𝔽ᵉ
  is-finite-structure-commutative-ring-𝔽ᵉ =
    is-finite-Σᵉ
      ( is-finite-structure-ring-𝔽ᵉ Xᵉ)
      ( λ rᵉ →
        is-finite-Πᵉ
          ( is-finite-type-𝔽ᵉ Xᵉ)
          ( λ _ →
            is-finite-Πᵉ
              ( is-finite-type-𝔽ᵉ Xᵉ)
              ( λ _ → is-finite-eq-𝔽ᵉ Xᵉ)))
```