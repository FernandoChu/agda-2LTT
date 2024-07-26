# Finite fields

```agda
module finite-algebra.finite-fieldsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.commutative-semiringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import finite-algebra.commutative-finite-ringsᵉ
open import finite-algebra.finite-ringsᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.binary-embeddingsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.dependent-pair-typesᵉ
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

open import ring-theory.division-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.semiringsᵉ
```

</details>

## Idea

Aᵉ **discreteᵉ field**ᵉ isᵉ aᵉ commutativeᵉ divisionᵉ ring.ᵉ Theyᵉ areᵉ calledᵉ discrete,ᵉ
becauseᵉ onlyᵉ nonzeroᵉ elementsᵉ areᵉ assumedᵉ to beᵉ invertible.ᵉ

## Definition

```agda
is-finite-field-Commutative-Ring-𝔽ᵉ : {lᵉ : Level} → Commutative-Ring-𝔽ᵉ lᵉ → UUᵉ lᵉ
is-finite-field-Commutative-Ring-𝔽ᵉ Aᵉ =
  is-division-Ringᵉ (ring-Commutative-Ring-𝔽ᵉ Aᵉ)

Field-𝔽ᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Field-𝔽ᵉ lᵉ =
  Σᵉ (Commutative-Ring-𝔽ᵉ lᵉ) (λ Aᵉ → is-finite-field-Commutative-Ring-𝔽ᵉ Aᵉ)

module _
  {lᵉ : Level} (Aᵉ : Field-𝔽ᵉ lᵉ)
  where

  commutative-finite-ring-Field-𝔽ᵉ : Commutative-Ring-𝔽ᵉ lᵉ
  commutative-finite-ring-Field-𝔽ᵉ = pr1ᵉ Aᵉ

  commutative-ring-Field-𝔽ᵉ : Commutative-Ringᵉ lᵉ
  commutative-ring-Field-𝔽ᵉ =
    commutative-ring-Commutative-Ring-𝔽ᵉ commutative-finite-ring-Field-𝔽ᵉ

  finite-ring-Field-𝔽ᵉ : Ring-𝔽ᵉ lᵉ
  finite-ring-Field-𝔽ᵉ =
    finite-ring-Commutative-Ring-𝔽ᵉ commutative-finite-ring-Field-𝔽ᵉ

  ring-Field-𝔽ᵉ : Ringᵉ lᵉ
  ring-Field-𝔽ᵉ = ring-Ring-𝔽ᵉ (finite-ring-Field-𝔽ᵉ)

  ab-Field-𝔽ᵉ : Abᵉ lᵉ
  ab-Field-𝔽ᵉ = ab-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  set-Field-𝔽ᵉ : Setᵉ lᵉ
  set-Field-𝔽ᵉ = set-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  type-Field-𝔽ᵉ : UUᵉ lᵉ
  type-Field-𝔽ᵉ = type-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  is-set-type-Field-𝔽ᵉ : is-setᵉ type-Field-𝔽ᵉ
  is-set-type-Field-𝔽ᵉ = is-set-type-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ
```

### Addition in a finite field

```agda
  has-associative-add-Field-𝔽ᵉ :
    has-associative-mul-Setᵉ set-Field-𝔽ᵉ
  has-associative-add-Field-𝔽ᵉ =
    has-associative-add-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  add-Field-𝔽ᵉ :
    type-Field-𝔽ᵉ → type-Field-𝔽ᵉ → type-Field-𝔽ᵉ
  add-Field-𝔽ᵉ = add-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  add-Field-𝔽'ᵉ :
    type-Field-𝔽ᵉ → type-Field-𝔽ᵉ → type-Field-𝔽ᵉ
  add-Field-𝔽'ᵉ = add-Ring-𝔽'ᵉ finite-ring-Field-𝔽ᵉ

  ap-add-Field-𝔽ᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Field-𝔽ᵉ} →
    (xᵉ ＝ᵉ x'ᵉ) → (yᵉ ＝ᵉ y'ᵉ) →
    add-Field-𝔽ᵉ xᵉ yᵉ ＝ᵉ add-Field-𝔽ᵉ x'ᵉ y'ᵉ
  ap-add-Field-𝔽ᵉ = ap-add-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  associative-add-Field-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Field-𝔽ᵉ) →
    ( add-Field-𝔽ᵉ (add-Field-𝔽ᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Field-𝔽ᵉ xᵉ (add-Field-𝔽ᵉ yᵉ zᵉ))
  associative-add-Field-𝔽ᵉ =
    associative-add-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  additive-semigroup-Field-𝔽ᵉ : Semigroupᵉ lᵉ
  additive-semigroup-Field-𝔽ᵉ = semigroup-Abᵉ ab-Field-𝔽ᵉ

  is-group-additive-semigroup-Field-𝔽ᵉ :
    is-group-Semigroupᵉ additive-semigroup-Field-𝔽ᵉ
  is-group-additive-semigroup-Field-𝔽ᵉ =
    is-group-Abᵉ ab-Field-𝔽ᵉ

  commutative-add-Field-𝔽ᵉ :
    (xᵉ yᵉ : type-Field-𝔽ᵉ) →
    Idᵉ (add-Field-𝔽ᵉ xᵉ yᵉ) (add-Field-𝔽ᵉ yᵉ xᵉ)
  commutative-add-Field-𝔽ᵉ = commutative-add-Abᵉ ab-Field-𝔽ᵉ

  interchange-add-add-Field-𝔽ᵉ :
    (xᵉ yᵉ x'ᵉ y'ᵉ : type-Field-𝔽ᵉ) →
    ( add-Field-𝔽ᵉ
      ( add-Field-𝔽ᵉ xᵉ yᵉ)
      ( add-Field-𝔽ᵉ x'ᵉ y'ᵉ)) ＝ᵉ
    ( add-Field-𝔽ᵉ
      ( add-Field-𝔽ᵉ xᵉ x'ᵉ)
      ( add-Field-𝔽ᵉ yᵉ y'ᵉ))
  interchange-add-add-Field-𝔽ᵉ =
    interchange-add-add-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  right-swap-add-Field-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Field-𝔽ᵉ) →
    ( add-Field-𝔽ᵉ (add-Field-𝔽ᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Field-𝔽ᵉ (add-Field-𝔽ᵉ xᵉ zᵉ) yᵉ)
  right-swap-add-Field-𝔽ᵉ =
    right-swap-add-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  left-swap-add-Field-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Field-𝔽ᵉ) →
    ( add-Field-𝔽ᵉ xᵉ (add-Field-𝔽ᵉ yᵉ zᵉ)) ＝ᵉ
    ( add-Field-𝔽ᵉ yᵉ (add-Field-𝔽ᵉ xᵉ zᵉ))
  left-swap-add-Field-𝔽ᵉ =
    left-swap-add-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  is-equiv-add-Field-𝔽ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) → is-equivᵉ (add-Field-𝔽ᵉ xᵉ)
  is-equiv-add-Field-𝔽ᵉ = is-equiv-add-Abᵉ ab-Field-𝔽ᵉ

  is-equiv-add-Field-𝔽'ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) → is-equivᵉ (add-Field-𝔽'ᵉ xᵉ)
  is-equiv-add-Field-𝔽'ᵉ = is-equiv-add-Ab'ᵉ ab-Field-𝔽ᵉ

  is-binary-equiv-add-Field-𝔽ᵉ : is-binary-equivᵉ add-Field-𝔽ᵉ
  pr1ᵉ is-binary-equiv-add-Field-𝔽ᵉ = is-equiv-add-Field-𝔽'ᵉ
  pr2ᵉ is-binary-equiv-add-Field-𝔽ᵉ = is-equiv-add-Field-𝔽ᵉ

  is-binary-emb-add-Field-𝔽ᵉ : is-binary-embᵉ add-Field-𝔽ᵉ
  is-binary-emb-add-Field-𝔽ᵉ = is-binary-emb-add-Abᵉ ab-Field-𝔽ᵉ

  is-emb-add-Field-𝔽ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) → is-embᵉ (add-Field-𝔽ᵉ xᵉ)
  is-emb-add-Field-𝔽ᵉ = is-emb-add-Abᵉ ab-Field-𝔽ᵉ

  is-emb-add-Field-𝔽'ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) → is-embᵉ (add-Field-𝔽'ᵉ xᵉ)
  is-emb-add-Field-𝔽'ᵉ = is-emb-add-Ab'ᵉ ab-Field-𝔽ᵉ

  is-injective-add-Field-𝔽ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) → is-injectiveᵉ (add-Field-𝔽ᵉ xᵉ)
  is-injective-add-Field-𝔽ᵉ = is-injective-add-Abᵉ ab-Field-𝔽ᵉ

  is-injective-add-Field-𝔽'ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) → is-injectiveᵉ (add-Field-𝔽'ᵉ xᵉ)
  is-injective-add-Field-𝔽'ᵉ = is-injective-add-Ab'ᵉ ab-Field-𝔽ᵉ
```

### The zero element of a finite field

```agda
  has-zero-Field-𝔽ᵉ : is-unitalᵉ add-Field-𝔽ᵉ
  has-zero-Field-𝔽ᵉ = has-zero-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  zero-Field-𝔽ᵉ : type-Field-𝔽ᵉ
  zero-Field-𝔽ᵉ = zero-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  is-zero-Field-𝔽ᵉ : type-Field-𝔽ᵉ → UUᵉ lᵉ
  is-zero-Field-𝔽ᵉ = is-zero-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  is-nonzero-Field-𝔽ᵉ : type-Field-𝔽ᵉ → UUᵉ lᵉ
  is-nonzero-Field-𝔽ᵉ = is-nonzero-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  is-zero-field-finite-Propᵉ : type-Field-𝔽ᵉ → Propᵉ lᵉ
  is-zero-field-finite-Propᵉ = is-zero-finite-ring-Propᵉ finite-ring-Field-𝔽ᵉ

  is-nonzero-field-finite-Propᵉ : type-Field-𝔽ᵉ → Propᵉ lᵉ
  is-nonzero-field-finite-Propᵉ = is-nonzero-finite-ring-Propᵉ finite-ring-Field-𝔽ᵉ

  left-unit-law-add-Field-𝔽ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) →
    add-Field-𝔽ᵉ zero-Field-𝔽ᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Field-𝔽ᵉ =
    left-unit-law-add-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  right-unit-law-add-Field-𝔽ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) →
    add-Field-𝔽ᵉ xᵉ zero-Field-𝔽ᵉ ＝ᵉ xᵉ
  right-unit-law-add-Field-𝔽ᵉ =
    right-unit-law-add-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ
```

### Additive inverses in a finite fields

```agda
  has-negatives-Field-𝔽ᵉ :
    is-group-is-unital-Semigroupᵉ additive-semigroup-Field-𝔽ᵉ has-zero-Field-𝔽ᵉ
  has-negatives-Field-𝔽ᵉ = has-negatives-Abᵉ ab-Field-𝔽ᵉ

  neg-Field-𝔽ᵉ : type-Field-𝔽ᵉ → type-Field-𝔽ᵉ
  neg-Field-𝔽ᵉ = neg-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  left-inverse-law-add-Field-𝔽ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) →
    add-Field-𝔽ᵉ (neg-Field-𝔽ᵉ xᵉ) xᵉ ＝ᵉ zero-Field-𝔽ᵉ
  left-inverse-law-add-Field-𝔽ᵉ =
    left-inverse-law-add-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  right-inverse-law-add-Field-𝔽ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) →
    add-Field-𝔽ᵉ xᵉ (neg-Field-𝔽ᵉ xᵉ) ＝ᵉ zero-Field-𝔽ᵉ
  right-inverse-law-add-Field-𝔽ᵉ =
    right-inverse-law-add-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  neg-neg-Field-𝔽ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) →
    neg-Field-𝔽ᵉ (neg-Field-𝔽ᵉ xᵉ) ＝ᵉ xᵉ
  neg-neg-Field-𝔽ᵉ = neg-neg-Abᵉ ab-Field-𝔽ᵉ

  distributive-neg-add-Field-𝔽ᵉ :
    (xᵉ yᵉ : type-Field-𝔽ᵉ) →
    neg-Field-𝔽ᵉ (add-Field-𝔽ᵉ xᵉ yᵉ) ＝ᵉ
    add-Field-𝔽ᵉ (neg-Field-𝔽ᵉ xᵉ) (neg-Field-𝔽ᵉ yᵉ)
  distributive-neg-add-Field-𝔽ᵉ =
    distributive-neg-add-Abᵉ ab-Field-𝔽ᵉ
```

### Multiplication in a finite fields

```agda
  has-associative-mul-Field-𝔽ᵉ :
    has-associative-mul-Setᵉ set-Field-𝔽ᵉ
  has-associative-mul-Field-𝔽ᵉ =
    has-associative-mul-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  mul-Field-𝔽ᵉ : (xᵉ yᵉ : type-Field-𝔽ᵉ) → type-Field-𝔽ᵉ
  mul-Field-𝔽ᵉ = mul-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  mul-Field-𝔽'ᵉ : (xᵉ yᵉ : type-Field-𝔽ᵉ) → type-Field-𝔽ᵉ
  mul-Field-𝔽'ᵉ = mul-Ring-𝔽'ᵉ finite-ring-Field-𝔽ᵉ

  ap-mul-Field-𝔽ᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Field-𝔽ᵉ} (pᵉ : Idᵉ xᵉ x'ᵉ) (qᵉ : Idᵉ yᵉ y'ᵉ) →
    Idᵉ (mul-Field-𝔽ᵉ xᵉ yᵉ) (mul-Field-𝔽ᵉ x'ᵉ y'ᵉ)
  ap-mul-Field-𝔽ᵉ pᵉ qᵉ = ap-binaryᵉ mul-Field-𝔽ᵉ pᵉ qᵉ

  associative-mul-Field-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ (mul-Field-𝔽ᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Field-𝔽ᵉ xᵉ (mul-Field-𝔽ᵉ yᵉ zᵉ)
  associative-mul-Field-𝔽ᵉ =
    associative-mul-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  multiplicative-semigroup-Field-𝔽ᵉ : Semigroupᵉ lᵉ
  pr1ᵉ multiplicative-semigroup-Field-𝔽ᵉ = set-Field-𝔽ᵉ
  pr2ᵉ multiplicative-semigroup-Field-𝔽ᵉ =
    has-associative-mul-Field-𝔽ᵉ

  left-distributive-mul-add-Field-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Field-𝔽ᵉ) →
    ( mul-Field-𝔽ᵉ xᵉ (add-Field-𝔽ᵉ yᵉ zᵉ)) ＝ᵉ
    ( add-Field-𝔽ᵉ
      ( mul-Field-𝔽ᵉ xᵉ yᵉ)
      ( mul-Field-𝔽ᵉ xᵉ zᵉ))
  left-distributive-mul-add-Field-𝔽ᵉ =
    left-distributive-mul-add-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  right-distributive-mul-add-Field-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Field-𝔽ᵉ) →
    ( mul-Field-𝔽ᵉ (add-Field-𝔽ᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Field-𝔽ᵉ
      ( mul-Field-𝔽ᵉ xᵉ zᵉ)
      ( mul-Field-𝔽ᵉ yᵉ zᵉ))
  right-distributive-mul-add-Field-𝔽ᵉ =
    right-distributive-mul-add-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  commutative-mul-Field-𝔽ᵉ :
    (xᵉ yᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ xᵉ yᵉ ＝ᵉ mul-Field-𝔽ᵉ yᵉ xᵉ
  commutative-mul-Field-𝔽ᵉ =
    commutative-mul-Commutative-Ring-𝔽ᵉ commutative-finite-ring-Field-𝔽ᵉ
```

### Multiplicative units in a finite fields

```agda
  is-unital-Field-𝔽ᵉ : is-unitalᵉ mul-Field-𝔽ᵉ
  is-unital-Field-𝔽ᵉ = is-unital-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  multiplicative-monoid-Field-𝔽ᵉ : Monoidᵉ lᵉ
  multiplicative-monoid-Field-𝔽ᵉ =
    multiplicative-monoid-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  one-Field-𝔽ᵉ : type-Field-𝔽ᵉ
  one-Field-𝔽ᵉ = one-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  left-unit-law-mul-Field-𝔽ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ one-Field-𝔽ᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Field-𝔽ᵉ =
    left-unit-law-mul-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  right-unit-law-mul-Field-𝔽ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ xᵉ one-Field-𝔽ᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Field-𝔽ᵉ =
    right-unit-law-mul-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  right-swap-mul-Field-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ (mul-Field-𝔽ᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Field-𝔽ᵉ (mul-Field-𝔽ᵉ xᵉ zᵉ) yᵉ
  right-swap-mul-Field-𝔽ᵉ =
    right-swap-mul-Commutative-Ring-𝔽ᵉ commutative-finite-ring-Field-𝔽ᵉ

  left-swap-mul-Field-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ xᵉ (mul-Field-𝔽ᵉ yᵉ zᵉ) ＝ᵉ
    mul-Field-𝔽ᵉ yᵉ (mul-Field-𝔽ᵉ xᵉ zᵉ)
  left-swap-mul-Field-𝔽ᵉ =
    left-swap-mul-Commutative-Ring-𝔽ᵉ commutative-finite-ring-Field-𝔽ᵉ

  interchange-mul-mul-Field-𝔽ᵉ :
    (xᵉ yᵉ zᵉ wᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ
      ( mul-Field-𝔽ᵉ xᵉ yᵉ)
      ( mul-Field-𝔽ᵉ zᵉ wᵉ) ＝ᵉ
    mul-Field-𝔽ᵉ
      ( mul-Field-𝔽ᵉ xᵉ zᵉ)
      ( mul-Field-𝔽ᵉ yᵉ wᵉ)
  interchange-mul-mul-Field-𝔽ᵉ =
    interchange-mul-mul-Commutative-Ring-𝔽ᵉ commutative-finite-ring-Field-𝔽ᵉ
```

### The zero laws for multiplication of a finite field

```agda
  left-zero-law-mul-Field-𝔽ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ zero-Field-𝔽ᵉ xᵉ ＝ᵉ
    zero-Field-𝔽ᵉ
  left-zero-law-mul-Field-𝔽ᵉ =
    left-zero-law-mul-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  right-zero-law-mul-Field-𝔽ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ xᵉ zero-Field-𝔽ᵉ ＝ᵉ
    zero-Field-𝔽ᵉ
  right-zero-law-mul-Field-𝔽ᵉ =
    right-zero-law-mul-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ
```

### Finite fields are commutative finite semirings

```agda
  multiplicative-commutative-monoid-Field-𝔽ᵉ : Commutative-Monoidᵉ lᵉ
  multiplicative-commutative-monoid-Field-𝔽ᵉ =
    multiplicative-commutative-monoid-Commutative-Ring-𝔽ᵉ
      commutative-finite-ring-Field-𝔽ᵉ

  semifinite-ring-Field-𝔽ᵉ : Semiringᵉ lᵉ
  semifinite-ring-Field-𝔽ᵉ = semiring-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  commutative-semiring-Field-𝔽ᵉ : Commutative-Semiringᵉ lᵉ
  commutative-semiring-Field-𝔽ᵉ =
    commutative-semiring-Commutative-Ring-𝔽ᵉ commutative-finite-ring-Field-𝔽ᵉ
```

### Computing multiplication with minus one in a finite field

```agda
  neg-one-Field-𝔽ᵉ : type-Field-𝔽ᵉ
  neg-one-Field-𝔽ᵉ = neg-one-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  mul-neg-one-Field-𝔽ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ neg-one-Field-𝔽ᵉ xᵉ ＝ᵉ
    neg-Field-𝔽ᵉ xᵉ
  mul-neg-one-Field-𝔽ᵉ = mul-neg-one-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  mul-neg-one-Field-𝔽'ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ xᵉ neg-one-Field-𝔽ᵉ ＝ᵉ
    neg-Field-𝔽ᵉ xᵉ
  mul-neg-one-Field-𝔽'ᵉ = mul-neg-one-Ring-𝔽'ᵉ finite-ring-Field-𝔽ᵉ

  is-involution-mul-neg-one-Field-𝔽ᵉ :
    is-involutionᵉ (mul-Field-𝔽ᵉ neg-one-Field-𝔽ᵉ)
  is-involution-mul-neg-one-Field-𝔽ᵉ =
    is-involution-mul-neg-one-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  is-involution-mul-neg-one-Field-𝔽'ᵉ :
    is-involutionᵉ (mul-Field-𝔽'ᵉ neg-one-Field-𝔽ᵉ)
  is-involution-mul-neg-one-Field-𝔽'ᵉ =
    is-involution-mul-neg-one-Ring-𝔽'ᵉ finite-ring-Field-𝔽ᵉ
```

### Left and right negative laws for multiplication

```agda
  left-negative-law-mul-Field-𝔽ᵉ :
    (xᵉ yᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ (neg-Field-𝔽ᵉ xᵉ) yᵉ ＝ᵉ
    neg-Field-𝔽ᵉ (mul-Field-𝔽ᵉ xᵉ yᵉ)
  left-negative-law-mul-Field-𝔽ᵉ =
    left-negative-law-mul-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  right-negative-law-mul-Field-𝔽ᵉ :
    (xᵉ yᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ xᵉ (neg-Field-𝔽ᵉ yᵉ) ＝ᵉ
    neg-Field-𝔽ᵉ (mul-Field-𝔽ᵉ xᵉ yᵉ)
  right-negative-law-mul-Field-𝔽ᵉ =
    right-negative-law-mul-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  mul-neg-Field-𝔽ᵉ :
    (xᵉ yᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ (neg-Field-𝔽ᵉ xᵉ) (neg-Field-𝔽ᵉ yᵉ) ＝ᵉ
    mul-Field-𝔽ᵉ xᵉ yᵉ
  mul-neg-Field-𝔽ᵉ = mul-neg-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ
```

### Scalar multiplication of elements of a commutative finite ring by natural numbers

```agda
  mul-nat-scalar-Field-𝔽ᵉ :
    ℕᵉ → type-Field-𝔽ᵉ → type-Field-𝔽ᵉ
  mul-nat-scalar-Field-𝔽ᵉ =
    mul-nat-scalar-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  ap-mul-nat-scalar-Field-𝔽ᵉ :
    {mᵉ nᵉ : ℕᵉ} {xᵉ yᵉ : type-Field-𝔽ᵉ} →
    (mᵉ ＝ᵉ nᵉ) → (xᵉ ＝ᵉ yᵉ) →
    mul-nat-scalar-Field-𝔽ᵉ mᵉ xᵉ ＝ᵉ
    mul-nat-scalar-Field-𝔽ᵉ nᵉ yᵉ
  ap-mul-nat-scalar-Field-𝔽ᵉ =
    ap-mul-nat-scalar-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  left-zero-law-mul-nat-scalar-Field-𝔽ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) →
    mul-nat-scalar-Field-𝔽ᵉ 0 xᵉ ＝ᵉ zero-Field-𝔽ᵉ
  left-zero-law-mul-nat-scalar-Field-𝔽ᵉ =
    left-zero-law-mul-nat-scalar-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  right-zero-law-mul-nat-scalar-Field-𝔽ᵉ :
    (nᵉ : ℕᵉ) →
    mul-nat-scalar-Field-𝔽ᵉ nᵉ zero-Field-𝔽ᵉ ＝ᵉ
    zero-Field-𝔽ᵉ
  right-zero-law-mul-nat-scalar-Field-𝔽ᵉ =
    right-zero-law-mul-nat-scalar-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  left-unit-law-mul-nat-scalar-Field-𝔽ᵉ :
    (xᵉ : type-Field-𝔽ᵉ) →
    mul-nat-scalar-Field-𝔽ᵉ 1 xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-nat-scalar-Field-𝔽ᵉ =
    left-unit-law-mul-nat-scalar-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  left-nat-scalar-law-mul-Field-𝔽ᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ (mul-nat-scalar-Field-𝔽ᵉ nᵉ xᵉ) yᵉ ＝ᵉ
    mul-nat-scalar-Field-𝔽ᵉ nᵉ (mul-Field-𝔽ᵉ xᵉ yᵉ)
  left-nat-scalar-law-mul-Field-𝔽ᵉ =
    left-nat-scalar-law-mul-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  right-nat-scalar-law-mul-Field-𝔽ᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Field-𝔽ᵉ) →
    mul-Field-𝔽ᵉ xᵉ (mul-nat-scalar-Field-𝔽ᵉ nᵉ yᵉ) ＝ᵉ
    mul-nat-scalar-Field-𝔽ᵉ nᵉ (mul-Field-𝔽ᵉ xᵉ yᵉ)
  right-nat-scalar-law-mul-Field-𝔽ᵉ =
    right-nat-scalar-law-mul-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  left-distributive-mul-nat-scalar-add-Field-𝔽ᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Field-𝔽ᵉ) →
    mul-nat-scalar-Field-𝔽ᵉ nᵉ (add-Field-𝔽ᵉ xᵉ yᵉ) ＝ᵉ
    add-Field-𝔽ᵉ
      ( mul-nat-scalar-Field-𝔽ᵉ nᵉ xᵉ)
      ( mul-nat-scalar-Field-𝔽ᵉ nᵉ yᵉ)
  left-distributive-mul-nat-scalar-add-Field-𝔽ᵉ =
    left-distributive-mul-nat-scalar-add-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  right-distributive-mul-nat-scalar-add-Field-𝔽ᵉ :
    (mᵉ nᵉ : ℕᵉ) (xᵉ : type-Field-𝔽ᵉ) →
    mul-nat-scalar-Field-𝔽ᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    add-Field-𝔽ᵉ
      ( mul-nat-scalar-Field-𝔽ᵉ mᵉ xᵉ)
      ( mul-nat-scalar-Field-𝔽ᵉ nᵉ xᵉ)
  right-distributive-mul-nat-scalar-add-Field-𝔽ᵉ =
    right-distributive-mul-nat-scalar-add-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ
```

### Addition of a list of elements in a finite field

```agda
  add-list-Field-𝔽ᵉ : listᵉ type-Field-𝔽ᵉ → type-Field-𝔽ᵉ
  add-list-Field-𝔽ᵉ = add-list-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ

  preserves-concat-add-list-Field-𝔽ᵉ :
    (l1ᵉ l2ᵉ : listᵉ type-Field-𝔽ᵉ) →
    Idᵉ
      ( add-list-Field-𝔽ᵉ (concat-listᵉ l1ᵉ l2ᵉ))
      ( add-Field-𝔽ᵉ
        ( add-list-Field-𝔽ᵉ l1ᵉ)
        ( add-list-Field-𝔽ᵉ l2ᵉ))
  preserves-concat-add-list-Field-𝔽ᵉ =
    preserves-concat-add-list-Ring-𝔽ᵉ finite-ring-Field-𝔽ᵉ
```