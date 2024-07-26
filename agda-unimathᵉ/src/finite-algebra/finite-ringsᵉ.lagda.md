# Finite rings

```agda
module finite-algebra.finite-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.finite-abelian-groupsᵉ
open import finite-group-theory.finite-groupsᵉ
open import finite-group-theory.finite-monoidsᵉ

open import foundation.binary-embeddingsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
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

open import univalent-combinatorics.cartesian-product-typesᵉ
open import univalent-combinatorics.dependent-function-typesᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ **finiteᵉ ring**ᵉ isᵉ aᵉ ringᵉ where theᵉ underlyingᵉ typeᵉ isᵉ finite.ᵉ

## Definitions

### Finite Rings

```agda
has-mul-Ab-𝔽ᵉ : {l1ᵉ : Level} (Aᵉ : Ab-𝔽ᵉ l1ᵉ) → UUᵉ l1ᵉ
has-mul-Ab-𝔽ᵉ Aᵉ = has-mul-Abᵉ (ab-Ab-𝔽ᵉ Aᵉ)

Ring-𝔽ᵉ : (l1ᵉ : Level) → UUᵉ (lsuc l1ᵉ)
Ring-𝔽ᵉ l1ᵉ = Σᵉ (Ab-𝔽ᵉ l1ᵉ) (λ Aᵉ → has-mul-Ab-𝔽ᵉ Aᵉ)

finite-ring-is-finite-Ringᵉ :
  {lᵉ : Level} → (Rᵉ : Ringᵉ lᵉ) → is-finiteᵉ (type-Ringᵉ Rᵉ) → Ring-𝔽ᵉ lᵉ
pr1ᵉ (finite-ring-is-finite-Ringᵉ Rᵉ fᵉ) =
  finite-abelian-group-is-finite-Abᵉ (ab-Ringᵉ Rᵉ) fᵉ
pr2ᵉ (finite-ring-is-finite-Ringᵉ Rᵉ fᵉ) = pr2ᵉ Rᵉ

module _
  {lᵉ : Level} (Rᵉ : Ring-𝔽ᵉ lᵉ)
  where

  finite-ab-Ring-𝔽ᵉ : Ab-𝔽ᵉ lᵉ
  finite-ab-Ring-𝔽ᵉ = pr1ᵉ Rᵉ

  ab-Ring-𝔽ᵉ : Abᵉ lᵉ
  ab-Ring-𝔽ᵉ = ab-Ab-𝔽ᵉ finite-ab-Ring-𝔽ᵉ

  ring-Ring-𝔽ᵉ : Ringᵉ lᵉ
  pr1ᵉ ring-Ring-𝔽ᵉ = ab-Ring-𝔽ᵉ
  pr2ᵉ ring-Ring-𝔽ᵉ = pr2ᵉ Rᵉ

  finite-type-Ring-𝔽ᵉ : 𝔽ᵉ lᵉ
  finite-type-Ring-𝔽ᵉ = finite-type-Ab-𝔽ᵉ finite-ab-Ring-𝔽ᵉ

  type-Ring-𝔽ᵉ : UUᵉ lᵉ
  type-Ring-𝔽ᵉ = type-Ab-𝔽ᵉ finite-ab-Ring-𝔽ᵉ

  is-finite-type-Ring-𝔽ᵉ : is-finiteᵉ type-Ring-𝔽ᵉ
  is-finite-type-Ring-𝔽ᵉ = is-finite-type-Ab-𝔽ᵉ finite-ab-Ring-𝔽ᵉ

  finite-group-Ring-𝔽ᵉ : Group-𝔽ᵉ lᵉ
  finite-group-Ring-𝔽ᵉ = finite-group-Ab-𝔽ᵉ finite-ab-Ring-𝔽ᵉ

  group-Ring-𝔽ᵉ : Groupᵉ lᵉ
  group-Ring-𝔽ᵉ = group-Abᵉ ab-Ring-𝔽ᵉ

  additive-commutative-monoid-Ring-𝔽ᵉ : Commutative-Monoidᵉ lᵉ
  additive-commutative-monoid-Ring-𝔽ᵉ =
    commutative-monoid-Abᵉ ab-Ring-𝔽ᵉ

  additive-monoid-Ring-𝔽ᵉ : Monoidᵉ lᵉ
  additive-monoid-Ring-𝔽ᵉ = monoid-Abᵉ ab-Ring-𝔽ᵉ

  additive-semigroup-Ring-𝔽ᵉ : Semigroupᵉ lᵉ
  additive-semigroup-Ring-𝔽ᵉ = semigroup-Abᵉ ab-Ring-𝔽ᵉ

  set-Ring-𝔽ᵉ : Setᵉ lᵉ
  set-Ring-𝔽ᵉ = set-Abᵉ ab-Ring-𝔽ᵉ

  is-set-type-Ring-𝔽ᵉ : is-setᵉ type-Ring-𝔽ᵉ
  is-set-type-Ring-𝔽ᵉ = is-set-type-Abᵉ ab-Ring-𝔽ᵉ
```

### Addition in a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ring-𝔽ᵉ lᵉ)
  where

  has-associative-add-Ring-𝔽ᵉ : has-associative-mul-Setᵉ (set-Ring-𝔽ᵉ Rᵉ)
  has-associative-add-Ring-𝔽ᵉ = has-associative-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  add-Ring-𝔽ᵉ : type-Ring-𝔽ᵉ Rᵉ → type-Ring-𝔽ᵉ Rᵉ → type-Ring-𝔽ᵉ Rᵉ
  add-Ring-𝔽ᵉ = add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  add-Ring-𝔽'ᵉ : type-Ring-𝔽ᵉ Rᵉ → type-Ring-𝔽ᵉ Rᵉ → type-Ring-𝔽ᵉ Rᵉ
  add-Ring-𝔽'ᵉ = add-Ring'ᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  ap-add-Ring-𝔽ᵉ :
    {xᵉ yᵉ x'ᵉ y'ᵉ : type-Ring-𝔽ᵉ Rᵉ} →
    Idᵉ xᵉ x'ᵉ → Idᵉ yᵉ y'ᵉ → Idᵉ (add-Ring-𝔽ᵉ xᵉ yᵉ) (add-Ring-𝔽ᵉ x'ᵉ y'ᵉ)
  ap-add-Ring-𝔽ᵉ = ap-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  associative-add-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Ring-𝔽ᵉ Rᵉ) →
    Idᵉ (add-Ring-𝔽ᵉ (add-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ) (add-Ring-𝔽ᵉ xᵉ (add-Ring-𝔽ᵉ yᵉ zᵉ))
  associative-add-Ring-𝔽ᵉ = associative-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  is-group-additive-semigroup-Ring-𝔽ᵉ :
    is-group-Semigroupᵉ (additive-semigroup-Ring-𝔽ᵉ Rᵉ)
  is-group-additive-semigroup-Ring-𝔽ᵉ =
    is-group-additive-semigroup-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  commutative-add-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-Ring-𝔽ᵉ Rᵉ) → Idᵉ (add-Ring-𝔽ᵉ xᵉ yᵉ) (add-Ring-𝔽ᵉ yᵉ xᵉ)
  commutative-add-Ring-𝔽ᵉ = commutative-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  interchange-add-add-Ring-𝔽ᵉ :
    (xᵉ yᵉ x'ᵉ y'ᵉ : type-Ring-𝔽ᵉ Rᵉ) →
    ( add-Ring-𝔽ᵉ (add-Ring-𝔽ᵉ xᵉ yᵉ) (add-Ring-𝔽ᵉ x'ᵉ y'ᵉ)) ＝ᵉ
    ( add-Ring-𝔽ᵉ (add-Ring-𝔽ᵉ xᵉ x'ᵉ) (add-Ring-𝔽ᵉ yᵉ y'ᵉ))
  interchange-add-add-Ring-𝔽ᵉ =
    interchange-add-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  right-swap-add-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Ring-𝔽ᵉ Rᵉ) →
    add-Ring-𝔽ᵉ (add-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ ＝ᵉ add-Ring-𝔽ᵉ (add-Ring-𝔽ᵉ xᵉ zᵉ) yᵉ
  right-swap-add-Ring-𝔽ᵉ = right-swap-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  left-swap-add-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Ring-𝔽ᵉ Rᵉ) →
    add-Ring-𝔽ᵉ xᵉ (add-Ring-𝔽ᵉ yᵉ zᵉ) ＝ᵉ add-Ring-𝔽ᵉ yᵉ (add-Ring-𝔽ᵉ xᵉ zᵉ)
  left-swap-add-Ring-𝔽ᵉ = left-swap-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  is-equiv-add-Ring-𝔽ᵉ : (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → is-equivᵉ (add-Ring-𝔽ᵉ xᵉ)
  is-equiv-add-Ring-𝔽ᵉ = is-equiv-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  is-equiv-add-Ring-𝔽'ᵉ : (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → is-equivᵉ (add-Ring-𝔽'ᵉ xᵉ)
  is-equiv-add-Ring-𝔽'ᵉ = is-equiv-add-Ring'ᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  is-binary-equiv-add-Ring-𝔽ᵉ : is-binary-equivᵉ add-Ring-𝔽ᵉ
  is-binary-equiv-add-Ring-𝔽ᵉ = is-binary-equiv-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  is-binary-emb-add-Ring-𝔽ᵉ : is-binary-embᵉ add-Ring-𝔽ᵉ
  is-binary-emb-add-Ring-𝔽ᵉ = is-binary-emb-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  is-emb-add-Ring-𝔽ᵉ : (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → is-embᵉ (add-Ring-𝔽ᵉ xᵉ)
  is-emb-add-Ring-𝔽ᵉ = is-emb-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  is-emb-add-Ring-𝔽'ᵉ : (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → is-embᵉ (add-Ring-𝔽'ᵉ xᵉ)
  is-emb-add-Ring-𝔽'ᵉ = is-emb-add-Ring'ᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  is-injective-add-Ring-𝔽ᵉ : (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → is-injectiveᵉ (add-Ring-𝔽ᵉ xᵉ)
  is-injective-add-Ring-𝔽ᵉ = is-injective-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  is-injective-add-Ring-𝔽'ᵉ : (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → is-injectiveᵉ (add-Ring-𝔽'ᵉ xᵉ)
  is-injective-add-Ring-𝔽'ᵉ = is-injective-add-Ring'ᵉ (ring-Ring-𝔽ᵉ Rᵉ)
```

### The zero element of a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ring-𝔽ᵉ lᵉ)
  where

  has-zero-Ring-𝔽ᵉ : is-unitalᵉ (add-Ring-𝔽ᵉ Rᵉ)
  has-zero-Ring-𝔽ᵉ = has-zero-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  zero-Ring-𝔽ᵉ : type-Ring-𝔽ᵉ Rᵉ
  zero-Ring-𝔽ᵉ = zero-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  is-zero-Ring-𝔽ᵉ : type-Ring-𝔽ᵉ Rᵉ → UUᵉ lᵉ
  is-zero-Ring-𝔽ᵉ = is-zero-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  is-nonzero-Ring-𝔽ᵉ : type-Ring-𝔽ᵉ Rᵉ → UUᵉ lᵉ
  is-nonzero-Ring-𝔽ᵉ = is-nonzero-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  is-zero-finite-ring-Propᵉ : type-Ring-𝔽ᵉ Rᵉ → Propᵉ lᵉ
  is-zero-finite-ring-Propᵉ = is-zero-ring-Propᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  is-nonzero-finite-ring-Propᵉ : type-Ring-𝔽ᵉ Rᵉ → Propᵉ lᵉ
  is-nonzero-finite-ring-Propᵉ = is-nonzero-ring-Propᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  left-unit-law-add-Ring-𝔽ᵉ :
    (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → Idᵉ (add-Ring-𝔽ᵉ Rᵉ zero-Ring-𝔽ᵉ xᵉ) xᵉ
  left-unit-law-add-Ring-𝔽ᵉ = left-unit-law-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  right-unit-law-add-Ring-𝔽ᵉ :
    (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → Idᵉ (add-Ring-𝔽ᵉ Rᵉ xᵉ zero-Ring-𝔽ᵉ) xᵉ
  right-unit-law-add-Ring-𝔽ᵉ = right-unit-law-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)
```

### Additive inverses in a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ring-𝔽ᵉ lᵉ)
  where

  has-negatives-Ring-𝔽ᵉ :
    is-group-is-unital-Semigroupᵉ
      ( additive-semigroup-Ring-𝔽ᵉ Rᵉ)
      ( has-zero-Ring-𝔽ᵉ Rᵉ)
  has-negatives-Ring-𝔽ᵉ = has-negatives-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  neg-Ring-𝔽ᵉ : type-Ring-𝔽ᵉ Rᵉ → type-Ring-𝔽ᵉ Rᵉ
  neg-Ring-𝔽ᵉ = neg-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  left-inverse-law-add-Ring-𝔽ᵉ :
    (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → Idᵉ (add-Ring-𝔽ᵉ Rᵉ (neg-Ring-𝔽ᵉ xᵉ) xᵉ) (zero-Ring-𝔽ᵉ Rᵉ)
  left-inverse-law-add-Ring-𝔽ᵉ = left-inverse-law-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  right-inverse-law-add-Ring-𝔽ᵉ :
    (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → Idᵉ (add-Ring-𝔽ᵉ Rᵉ xᵉ (neg-Ring-𝔽ᵉ xᵉ)) (zero-Ring-𝔽ᵉ Rᵉ)
  right-inverse-law-add-Ring-𝔽ᵉ = right-inverse-law-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  neg-neg-Ring-𝔽ᵉ : (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → neg-Ring-𝔽ᵉ (neg-Ring-𝔽ᵉ xᵉ) ＝ᵉ xᵉ
  neg-neg-Ring-𝔽ᵉ = neg-neg-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  distributive-neg-add-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-Ring-𝔽ᵉ Rᵉ) →
    neg-Ring-𝔽ᵉ (add-Ring-𝔽ᵉ Rᵉ xᵉ yᵉ) ＝ᵉ add-Ring-𝔽ᵉ Rᵉ (neg-Ring-𝔽ᵉ xᵉ) (neg-Ring-𝔽ᵉ yᵉ)
  distributive-neg-add-Ring-𝔽ᵉ = distributive-neg-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)
```

### Multiplication in a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ring-𝔽ᵉ lᵉ)
  where

  has-associative-mul-Ring-𝔽ᵉ : has-associative-mul-Setᵉ (set-Ring-𝔽ᵉ Rᵉ)
  has-associative-mul-Ring-𝔽ᵉ = has-associative-mul-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  mul-Ring-𝔽ᵉ : type-Ring-𝔽ᵉ Rᵉ → type-Ring-𝔽ᵉ Rᵉ → type-Ring-𝔽ᵉ Rᵉ
  mul-Ring-𝔽ᵉ = mul-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  mul-Ring-𝔽'ᵉ : type-Ring-𝔽ᵉ Rᵉ → type-Ring-𝔽ᵉ Rᵉ → type-Ring-𝔽ᵉ Rᵉ
  mul-Ring-𝔽'ᵉ = mul-Ring'ᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  ap-mul-Ring-𝔽ᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Ring-𝔽ᵉ Rᵉ} (pᵉ : Idᵉ xᵉ x'ᵉ) (qᵉ : Idᵉ yᵉ y'ᵉ) →
    Idᵉ (mul-Ring-𝔽ᵉ xᵉ yᵉ) (mul-Ring-𝔽ᵉ x'ᵉ y'ᵉ)
  ap-mul-Ring-𝔽ᵉ = ap-mul-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  associative-mul-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Ring-𝔽ᵉ Rᵉ) →
    Idᵉ (mul-Ring-𝔽ᵉ (mul-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ) (mul-Ring-𝔽ᵉ xᵉ (mul-Ring-𝔽ᵉ yᵉ zᵉ))
  associative-mul-Ring-𝔽ᵉ = associative-mul-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  multiplicative-semigroup-Ring-𝔽ᵉ : Semigroupᵉ lᵉ
  multiplicative-semigroup-Ring-𝔽ᵉ =
    multiplicative-semigroup-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  left-distributive-mul-add-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Ring-𝔽ᵉ Rᵉ) →
    mul-Ring-𝔽ᵉ xᵉ (add-Ring-𝔽ᵉ Rᵉ yᵉ zᵉ) ＝ᵉ
    add-Ring-𝔽ᵉ Rᵉ (mul-Ring-𝔽ᵉ xᵉ yᵉ) (mul-Ring-𝔽ᵉ xᵉ zᵉ)
  left-distributive-mul-add-Ring-𝔽ᵉ =
    left-distributive-mul-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  right-distributive-mul-add-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Ring-𝔽ᵉ Rᵉ) →
    mul-Ring-𝔽ᵉ (add-Ring-𝔽ᵉ Rᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    add-Ring-𝔽ᵉ Rᵉ (mul-Ring-𝔽ᵉ xᵉ zᵉ) (mul-Ring-𝔽ᵉ yᵉ zᵉ)
  right-distributive-mul-add-Ring-𝔽ᵉ =
    right-distributive-mul-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)
```

### Multiplicative units in a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ring-𝔽ᵉ lᵉ)
  where

  is-unital-Ring-𝔽ᵉ : is-unitalᵉ (mul-Ring-𝔽ᵉ Rᵉ)
  is-unital-Ring-𝔽ᵉ = is-unital-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  multiplicative-monoid-Ring-𝔽ᵉ : Monoidᵉ lᵉ
  multiplicative-monoid-Ring-𝔽ᵉ = multiplicative-monoid-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  one-Ring-𝔽ᵉ : type-Ring-𝔽ᵉ Rᵉ
  one-Ring-𝔽ᵉ = one-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  left-unit-law-mul-Ring-𝔽ᵉ :
    (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → Idᵉ (mul-Ring-𝔽ᵉ Rᵉ one-Ring-𝔽ᵉ xᵉ) xᵉ
  left-unit-law-mul-Ring-𝔽ᵉ = left-unit-law-mul-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  right-unit-law-mul-Ring-𝔽ᵉ :
    (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → Idᵉ (mul-Ring-𝔽ᵉ Rᵉ xᵉ one-Ring-𝔽ᵉ) xᵉ
  right-unit-law-mul-Ring-𝔽ᵉ = right-unit-law-mul-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)
```

### The zero laws for multiplication of a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ring-𝔽ᵉ lᵉ)
  where

  left-zero-law-mul-Ring-𝔽ᵉ :
    (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → Idᵉ (mul-Ring-𝔽ᵉ Rᵉ (zero-Ring-𝔽ᵉ Rᵉ) xᵉ) (zero-Ring-𝔽ᵉ Rᵉ)
  left-zero-law-mul-Ring-𝔽ᵉ =
    left-zero-law-mul-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  right-zero-law-mul-Ring-𝔽ᵉ :
    (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → Idᵉ (mul-Ring-𝔽ᵉ Rᵉ xᵉ (zero-Ring-𝔽ᵉ Rᵉ)) (zero-Ring-𝔽ᵉ Rᵉ)
  right-zero-law-mul-Ring-𝔽ᵉ =
    right-zero-law-mul-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)
```

### Rings are semirings

```agda
module _
  {lᵉ : Level} (Rᵉ : Ring-𝔽ᵉ lᵉ)
  where

  has-mul-Ring-𝔽ᵉ :
    has-mul-Commutative-Monoidᵉ (additive-commutative-monoid-Ring-𝔽ᵉ Rᵉ)
  has-mul-Ring-𝔽ᵉ = has-mul-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  zero-laws-mul-Ring-𝔽ᵉ :
    zero-laws-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Ring-𝔽ᵉ Rᵉ)
      ( has-mul-Ring-𝔽ᵉ)
  zero-laws-mul-Ring-𝔽ᵉ = zero-laws-mul-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  semiring-Ring-𝔽ᵉ : Semiringᵉ lᵉ
  semiring-Ring-𝔽ᵉ = semiring-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)
```

### Computing multiplication with minus one in a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ring-𝔽ᵉ lᵉ)
  where

  neg-one-Ring-𝔽ᵉ : type-Ring-𝔽ᵉ Rᵉ
  neg-one-Ring-𝔽ᵉ = neg-one-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  mul-neg-one-Ring-𝔽ᵉ :
    (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → mul-Ring-𝔽ᵉ Rᵉ neg-one-Ring-𝔽ᵉ xᵉ ＝ᵉ neg-Ring-𝔽ᵉ Rᵉ xᵉ
  mul-neg-one-Ring-𝔽ᵉ =
    mul-neg-one-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  mul-neg-one-Ring-𝔽'ᵉ :
    (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → mul-Ring-𝔽ᵉ Rᵉ xᵉ neg-one-Ring-𝔽ᵉ ＝ᵉ neg-Ring-𝔽ᵉ Rᵉ xᵉ
  mul-neg-one-Ring-𝔽'ᵉ =
    mul-neg-one-Ring'ᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  is-involution-mul-neg-one-Ring-𝔽ᵉ :
    is-involutionᵉ (mul-Ring-𝔽ᵉ Rᵉ neg-one-Ring-𝔽ᵉ)
  is-involution-mul-neg-one-Ring-𝔽ᵉ =
    is-involution-mul-neg-one-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  is-involution-mul-neg-one-Ring-𝔽'ᵉ :
    is-involutionᵉ (mul-Ring-𝔽'ᵉ Rᵉ neg-one-Ring-𝔽ᵉ)
  is-involution-mul-neg-one-Ring-𝔽'ᵉ =
    is-involution-mul-neg-one-Ring'ᵉ (ring-Ring-𝔽ᵉ Rᵉ)
```

### Left and right negative laws for multiplication

```agda
module _
  {lᵉ : Level} (Rᵉ : Ring-𝔽ᵉ lᵉ)
  where

  left-negative-law-mul-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-Ring-𝔽ᵉ Rᵉ) →
    mul-Ring-𝔽ᵉ Rᵉ (neg-Ring-𝔽ᵉ Rᵉ xᵉ) yᵉ ＝ᵉ neg-Ring-𝔽ᵉ Rᵉ (mul-Ring-𝔽ᵉ Rᵉ xᵉ yᵉ)
  left-negative-law-mul-Ring-𝔽ᵉ =
    left-negative-law-mul-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  right-negative-law-mul-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-Ring-𝔽ᵉ Rᵉ) →
    mul-Ring-𝔽ᵉ Rᵉ xᵉ (neg-Ring-𝔽ᵉ Rᵉ yᵉ) ＝ᵉ neg-Ring-𝔽ᵉ Rᵉ (mul-Ring-𝔽ᵉ Rᵉ xᵉ yᵉ)
  right-negative-law-mul-Ring-𝔽ᵉ =
    right-negative-law-mul-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  mul-neg-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-Ring-𝔽ᵉ Rᵉ) →
    mul-Ring-𝔽ᵉ Rᵉ (neg-Ring-𝔽ᵉ Rᵉ xᵉ) (neg-Ring-𝔽ᵉ Rᵉ yᵉ) ＝ᵉ mul-Ring-𝔽ᵉ Rᵉ xᵉ yᵉ
  mul-neg-Ring-𝔽ᵉ =
    mul-neg-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)
```

### Scalar multiplication of ring elements by a natural number

```agda
module _
  {lᵉ : Level} (Rᵉ : Ring-𝔽ᵉ lᵉ)
  where

  mul-nat-scalar-Ring-𝔽ᵉ : ℕᵉ → type-Ring-𝔽ᵉ Rᵉ → type-Ring-𝔽ᵉ Rᵉ
  mul-nat-scalar-Ring-𝔽ᵉ = mul-nat-scalar-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  ap-mul-nat-scalar-Ring-𝔽ᵉ :
    {mᵉ nᵉ : ℕᵉ} {xᵉ yᵉ : type-Ring-𝔽ᵉ Rᵉ} →
    (mᵉ ＝ᵉ nᵉ) → (xᵉ ＝ᵉ yᵉ) → mul-nat-scalar-Ring-𝔽ᵉ mᵉ xᵉ ＝ᵉ mul-nat-scalar-Ring-𝔽ᵉ nᵉ yᵉ
  ap-mul-nat-scalar-Ring-𝔽ᵉ = ap-mul-nat-scalar-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  left-zero-law-mul-nat-scalar-Ring-𝔽ᵉ :
    (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → mul-nat-scalar-Ring-𝔽ᵉ 0 xᵉ ＝ᵉ zero-Ring-𝔽ᵉ Rᵉ
  left-zero-law-mul-nat-scalar-Ring-𝔽ᵉ =
    left-zero-law-mul-nat-scalar-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  right-zero-law-mul-nat-scalar-Ring-𝔽ᵉ :
    (nᵉ : ℕᵉ) → mul-nat-scalar-Ring-𝔽ᵉ nᵉ (zero-Ring-𝔽ᵉ Rᵉ) ＝ᵉ zero-Ring-𝔽ᵉ Rᵉ
  right-zero-law-mul-nat-scalar-Ring-𝔽ᵉ =
    right-zero-law-mul-nat-scalar-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  left-unit-law-mul-nat-scalar-Ring-𝔽ᵉ :
    (xᵉ : type-Ring-𝔽ᵉ Rᵉ) → mul-nat-scalar-Ring-𝔽ᵉ 1 xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-nat-scalar-Ring-𝔽ᵉ =
    left-unit-law-mul-nat-scalar-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  left-nat-scalar-law-mul-Ring-𝔽ᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Ring-𝔽ᵉ Rᵉ) →
    mul-Ring-𝔽ᵉ Rᵉ (mul-nat-scalar-Ring-𝔽ᵉ nᵉ xᵉ) yᵉ ＝ᵉ
    mul-nat-scalar-Ring-𝔽ᵉ nᵉ (mul-Ring-𝔽ᵉ Rᵉ xᵉ yᵉ)
  left-nat-scalar-law-mul-Ring-𝔽ᵉ =
    left-nat-scalar-law-mul-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  right-nat-scalar-law-mul-Ring-𝔽ᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Ring-𝔽ᵉ Rᵉ) →
    mul-Ring-𝔽ᵉ Rᵉ xᵉ (mul-nat-scalar-Ring-𝔽ᵉ nᵉ yᵉ) ＝ᵉ
    mul-nat-scalar-Ring-𝔽ᵉ nᵉ (mul-Ring-𝔽ᵉ Rᵉ xᵉ yᵉ)
  right-nat-scalar-law-mul-Ring-𝔽ᵉ =
    right-nat-scalar-law-mul-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  left-distributive-mul-nat-scalar-add-Ring-𝔽ᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Ring-𝔽ᵉ Rᵉ) →
    mul-nat-scalar-Ring-𝔽ᵉ nᵉ (add-Ring-𝔽ᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
    add-Ring-𝔽ᵉ Rᵉ (mul-nat-scalar-Ring-𝔽ᵉ nᵉ xᵉ) (mul-nat-scalar-Ring-𝔽ᵉ nᵉ yᵉ)
  left-distributive-mul-nat-scalar-add-Ring-𝔽ᵉ =
    left-distributive-mul-nat-scalar-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  right-distributive-mul-nat-scalar-add-Ring-𝔽ᵉ :
    (mᵉ nᵉ : ℕᵉ) (xᵉ : type-Ring-𝔽ᵉ Rᵉ) →
    mul-nat-scalar-Ring-𝔽ᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    add-Ring-𝔽ᵉ Rᵉ (mul-nat-scalar-Ring-𝔽ᵉ mᵉ xᵉ) (mul-nat-scalar-Ring-𝔽ᵉ nᵉ xᵉ)
  right-distributive-mul-nat-scalar-add-Ring-𝔽ᵉ =
    right-distributive-mul-nat-scalar-add-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)
```

### Addition of a list of elements in an abelian group

```agda
module _
  {lᵉ : Level} (Rᵉ : Ring-𝔽ᵉ lᵉ)
  where

  add-list-Ring-𝔽ᵉ : listᵉ (type-Ring-𝔽ᵉ Rᵉ) → type-Ring-𝔽ᵉ Rᵉ
  add-list-Ring-𝔽ᵉ = add-list-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)

  preserves-concat-add-list-Ring-𝔽ᵉ :
    (l1ᵉ l2ᵉ : listᵉ (type-Ring-𝔽ᵉ Rᵉ)) →
    Idᵉ
      ( add-list-Ring-𝔽ᵉ (concat-listᵉ l1ᵉ l2ᵉ))
      ( add-Ring-𝔽ᵉ Rᵉ (add-list-Ring-𝔽ᵉ l1ᵉ) (add-list-Ring-𝔽ᵉ l2ᵉ))
  preserves-concat-add-list-Ring-𝔽ᵉ =
    preserves-concat-add-list-Ringᵉ (ring-Ring-𝔽ᵉ Rᵉ)
```

## Properties

### There is a finite number of ways to equip a finite type with the structure of a ring

```agda
module _
  {lᵉ : Level}
  (Xᵉ : 𝔽ᵉ lᵉ)
  where

  structure-ring-𝔽ᵉ : UUᵉ lᵉ
  structure-ring-𝔽ᵉ =
    Σᵉ ( structure-abelian-group-𝔽ᵉ Xᵉ)
      ( λ mᵉ → has-mul-Ab-𝔽ᵉ (finite-abelian-group-structure-abelian-group-𝔽ᵉ Xᵉ mᵉ))

  finite-ring-structure-ring-𝔽ᵉ :
    structure-ring-𝔽ᵉ → Ring-𝔽ᵉ lᵉ
  pr1ᵉ (finite-ring-structure-ring-𝔽ᵉ (mᵉ ,ᵉ cᵉ)) =
    finite-abelian-group-structure-abelian-group-𝔽ᵉ Xᵉ mᵉ
  pr2ᵉ (finite-ring-structure-ring-𝔽ᵉ (mᵉ ,ᵉ cᵉ)) = cᵉ

  is-finite-structure-ring-𝔽ᵉ :
    is-finiteᵉ structure-ring-𝔽ᵉ
  is-finite-structure-ring-𝔽ᵉ =
    is-finite-Σᵉ
      ( is-finite-structure-abelian-group-𝔽ᵉ Xᵉ)
      ( λ aᵉ →
        is-finite-Σᵉ
          ( is-finite-Σᵉ
            ( is-finite-Πᵉ
              ( is-finite-type-𝔽ᵉ Xᵉ)
              ( λ _ →
                is-finite-Πᵉ
                  ( is-finite-type-𝔽ᵉ Xᵉ)
                  ( λ _ → is-finite-type-𝔽ᵉ Xᵉ)))
            ( λ mᵉ →
              is-finite-Πᵉ
                ( is-finite-type-𝔽ᵉ Xᵉ)
                ( λ xᵉ →
                  is-finite-Πᵉ
                    ( is-finite-type-𝔽ᵉ Xᵉ)
                    ( λ yᵉ →
                      is-finite-Πᵉ
                        ( is-finite-type-𝔽ᵉ Xᵉ)
                        ( λ zᵉ → is-finite-eq-𝔽ᵉ Xᵉ)))))
          ( λ aᵉ →
            is-finite-productᵉ
              ( is-finite-is-unital-Semigroup-𝔽ᵉ (Xᵉ ,ᵉ aᵉ))
              ( is-finite-productᵉ
                ( is-finite-Πᵉ
                  ( is-finite-type-𝔽ᵉ Xᵉ)
                  ( λ _ →
                    is-finite-Πᵉ
                      ( is-finite-type-𝔽ᵉ Xᵉ)
                      ( λ _ →
                        is-finite-Πᵉ
                          ( is-finite-type-𝔽ᵉ Xᵉ)
                          ( λ _ → is-finite-eq-𝔽ᵉ Xᵉ))))
                ( is-finite-Πᵉ
                  ( is-finite-type-𝔽ᵉ Xᵉ)
                  ( λ _ →
                    is-finite-Πᵉ
                      ( is-finite-type-𝔽ᵉ Xᵉ)
                      ( λ _ →
                        is-finite-Πᵉ
                          ( is-finite-type-𝔽ᵉ Xᵉ)
                          ( λ _ → is-finite-eq-𝔽ᵉ Xᵉ)))))))
```