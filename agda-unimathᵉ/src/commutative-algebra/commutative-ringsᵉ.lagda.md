# Commutative rings

```agda
module commutative-algebra.commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semiringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-embeddingsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.interchange-lawᵉ
open import foundation.involutionsᵉ
open import foundation.negationᵉ
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
```

</details>

## Idea

Aᵉ ringᵉ `A`ᵉ isᵉ saidᵉ to beᵉ **commutative**ᵉ ifᵉ itsᵉ multiplicativeᵉ operationᵉ isᵉ
commutative,ᵉ i.e.,ᵉ ifᵉ `xyᵉ = yx`ᵉ forᵉ allᵉ `x,ᵉ yᵉ ∈ᵉ A`.ᵉ

## Definition

### The predicate on rings of being commutative

```agda
module _
  {lᵉ : Level} (Aᵉ : Ringᵉ lᵉ)
  where

  is-commutative-Ringᵉ : UUᵉ lᵉ
  is-commutative-Ringᵉ =
    (xᵉ yᵉ : type-Ringᵉ Aᵉ) → mul-Ringᵉ Aᵉ xᵉ yᵉ ＝ᵉ mul-Ringᵉ Aᵉ yᵉ xᵉ

  is-prop-is-commutative-Ringᵉ : is-propᵉ is-commutative-Ringᵉ
  is-prop-is-commutative-Ringᵉ =
    is-prop-Πᵉ
      ( λ xᵉ →
        is-prop-Πᵉ
        ( λ yᵉ →
          is-set-type-Ringᵉ Aᵉ (mul-Ringᵉ Aᵉ xᵉ yᵉ) (mul-Ringᵉ Aᵉ yᵉ xᵉ)))

  is-commutative-prop-Ringᵉ : Propᵉ lᵉ
  is-commutative-prop-Ringᵉ = is-commutative-Ringᵉ ,ᵉ is-prop-is-commutative-Ringᵉ
```

### Commutative rings

```agda
Commutative-Ringᵉ :
  ( lᵉ : Level) → UUᵉ (lsuc lᵉ)
Commutative-Ringᵉ lᵉ = Σᵉ (Ringᵉ lᵉ) is-commutative-Ringᵉ

module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  ring-Commutative-Ringᵉ : Ringᵉ lᵉ
  ring-Commutative-Ringᵉ = pr1ᵉ Aᵉ

  ab-Commutative-Ringᵉ : Abᵉ lᵉ
  ab-Commutative-Ringᵉ = ab-Ringᵉ ring-Commutative-Ringᵉ

  set-Commutative-Ringᵉ : Setᵉ lᵉ
  set-Commutative-Ringᵉ = set-Ringᵉ ring-Commutative-Ringᵉ

  type-Commutative-Ringᵉ : UUᵉ lᵉ
  type-Commutative-Ringᵉ = type-Ringᵉ ring-Commutative-Ringᵉ

  is-set-type-Commutative-Ringᵉ : is-setᵉ type-Commutative-Ringᵉ
  is-set-type-Commutative-Ringᵉ = is-set-type-Ringᵉ ring-Commutative-Ringᵉ
```

### Addition in a commutative ring

```agda
  has-associative-add-Commutative-Ringᵉ :
    has-associative-mul-Setᵉ set-Commutative-Ringᵉ
  has-associative-add-Commutative-Ringᵉ =
    has-associative-add-Ringᵉ ring-Commutative-Ringᵉ

  add-Commutative-Ringᵉ :
    type-Commutative-Ringᵉ → type-Commutative-Ringᵉ → type-Commutative-Ringᵉ
  add-Commutative-Ringᵉ = add-Ringᵉ ring-Commutative-Ringᵉ

  add-Commutative-Ring'ᵉ :
    type-Commutative-Ringᵉ → type-Commutative-Ringᵉ → type-Commutative-Ringᵉ
  add-Commutative-Ring'ᵉ = add-Ring'ᵉ ring-Commutative-Ringᵉ

  ap-add-Commutative-Ringᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Commutative-Ringᵉ} →
    (xᵉ ＝ᵉ x'ᵉ) → (yᵉ ＝ᵉ y'ᵉ) →
    add-Commutative-Ringᵉ xᵉ yᵉ ＝ᵉ add-Commutative-Ringᵉ x'ᵉ y'ᵉ
  ap-add-Commutative-Ringᵉ = ap-add-Ringᵉ ring-Commutative-Ringᵉ

  associative-add-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ringᵉ) →
    ( add-Commutative-Ringᵉ (add-Commutative-Ringᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Commutative-Ringᵉ xᵉ (add-Commutative-Ringᵉ yᵉ zᵉ))
  associative-add-Commutative-Ringᵉ =
    associative-add-Ringᵉ ring-Commutative-Ringᵉ

  additive-semigroup-Commutative-Ringᵉ : Semigroupᵉ lᵉ
  additive-semigroup-Commutative-Ringᵉ = semigroup-Abᵉ ab-Commutative-Ringᵉ

  is-group-additive-semigroup-Commutative-Ringᵉ :
    is-group-Semigroupᵉ additive-semigroup-Commutative-Ringᵉ
  is-group-additive-semigroup-Commutative-Ringᵉ =
    is-group-Abᵉ ab-Commutative-Ringᵉ

  commutative-add-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-Commutative-Ringᵉ) →
    Idᵉ (add-Commutative-Ringᵉ xᵉ yᵉ) (add-Commutative-Ringᵉ yᵉ xᵉ)
  commutative-add-Commutative-Ringᵉ = commutative-add-Abᵉ ab-Commutative-Ringᵉ

  interchange-add-add-Commutative-Ringᵉ :
    (xᵉ yᵉ x'ᵉ y'ᵉ : type-Commutative-Ringᵉ) →
    ( add-Commutative-Ringᵉ
      ( add-Commutative-Ringᵉ xᵉ yᵉ)
      ( add-Commutative-Ringᵉ x'ᵉ y'ᵉ)) ＝ᵉ
    ( add-Commutative-Ringᵉ
      ( add-Commutative-Ringᵉ xᵉ x'ᵉ)
      ( add-Commutative-Ringᵉ yᵉ y'ᵉ))
  interchange-add-add-Commutative-Ringᵉ =
    interchange-add-add-Ringᵉ ring-Commutative-Ringᵉ

  right-swap-add-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ringᵉ) →
    ( add-Commutative-Ringᵉ (add-Commutative-Ringᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Commutative-Ringᵉ (add-Commutative-Ringᵉ xᵉ zᵉ) yᵉ)
  right-swap-add-Commutative-Ringᵉ =
    right-swap-add-Ringᵉ ring-Commutative-Ringᵉ

  left-swap-add-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ringᵉ) →
    ( add-Commutative-Ringᵉ xᵉ (add-Commutative-Ringᵉ yᵉ zᵉ)) ＝ᵉ
    ( add-Commutative-Ringᵉ yᵉ (add-Commutative-Ringᵉ xᵉ zᵉ))
  left-swap-add-Commutative-Ringᵉ =
    left-swap-add-Ringᵉ ring-Commutative-Ringᵉ

  left-subtraction-Commutative-Ringᵉ :
    type-Commutative-Ringᵉ → type-Commutative-Ringᵉ → type-Commutative-Ringᵉ
  left-subtraction-Commutative-Ringᵉ =
    left-subtraction-Ringᵉ ring-Commutative-Ringᵉ

  is-section-left-subtraction-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    (add-Commutative-Ringᵉ xᵉ ∘ᵉ left-subtraction-Commutative-Ringᵉ xᵉ) ~ᵉ idᵉ
  is-section-left-subtraction-Commutative-Ringᵉ =
    is-section-left-subtraction-Ringᵉ ring-Commutative-Ringᵉ

  is-retraction-left-subtraction-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    (left-subtraction-Commutative-Ringᵉ xᵉ ∘ᵉ add-Commutative-Ringᵉ xᵉ) ~ᵉ idᵉ
  is-retraction-left-subtraction-Commutative-Ringᵉ =
    is-retraction-left-subtraction-Ringᵉ ring-Commutative-Ringᵉ

  is-equiv-add-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) → is-equivᵉ (add-Commutative-Ringᵉ xᵉ)
  is-equiv-add-Commutative-Ringᵉ = is-equiv-add-Abᵉ ab-Commutative-Ringᵉ

  equiv-add-Commutative-Ringᵉ :
    type-Commutative-Ringᵉ → (type-Commutative-Ringᵉ ≃ᵉ type-Commutative-Ringᵉ)
  equiv-add-Commutative-Ringᵉ = equiv-add-Ringᵉ ring-Commutative-Ringᵉ

  right-subtraction-Commutative-Ringᵉ :
    type-Commutative-Ringᵉ → type-Commutative-Ringᵉ → type-Commutative-Ringᵉ
  right-subtraction-Commutative-Ringᵉ =
    right-subtraction-Ringᵉ ring-Commutative-Ringᵉ

  is-section-right-subtraction-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    ( add-Commutative-Ring'ᵉ xᵉ ∘ᵉ
      (λ yᵉ → right-subtraction-Commutative-Ringᵉ yᵉ xᵉ)) ~ᵉ idᵉ
  is-section-right-subtraction-Commutative-Ringᵉ =
    is-section-right-subtraction-Ringᵉ ring-Commutative-Ringᵉ

  is-retraction-right-subtraction-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    ( ( λ yᵉ → right-subtraction-Commutative-Ringᵉ yᵉ xᵉ) ∘ᵉ
      add-Commutative-Ring'ᵉ xᵉ) ~ᵉ idᵉ
  is-retraction-right-subtraction-Commutative-Ringᵉ =
    is-retraction-right-subtraction-Ringᵉ ring-Commutative-Ringᵉ

  is-equiv-add-Commutative-Ring'ᵉ :
    (xᵉ : type-Commutative-Ringᵉ) → is-equivᵉ (add-Commutative-Ring'ᵉ xᵉ)
  is-equiv-add-Commutative-Ring'ᵉ = is-equiv-add-Ab'ᵉ ab-Commutative-Ringᵉ

  equiv-add-Commutative-Ring'ᵉ :
    type-Commutative-Ringᵉ → (type-Commutative-Ringᵉ ≃ᵉ type-Commutative-Ringᵉ)
  equiv-add-Commutative-Ring'ᵉ =
    equiv-add-Ring'ᵉ ring-Commutative-Ringᵉ

  is-binary-equiv-add-Commutative-Ringᵉ : is-binary-equivᵉ add-Commutative-Ringᵉ
  pr1ᵉ is-binary-equiv-add-Commutative-Ringᵉ = is-equiv-add-Commutative-Ring'ᵉ
  pr2ᵉ is-binary-equiv-add-Commutative-Ringᵉ = is-equiv-add-Commutative-Ringᵉ

  is-binary-emb-add-Commutative-Ringᵉ : is-binary-embᵉ add-Commutative-Ringᵉ
  is-binary-emb-add-Commutative-Ringᵉ = is-binary-emb-add-Abᵉ ab-Commutative-Ringᵉ

  is-emb-add-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) → is-embᵉ (add-Commutative-Ringᵉ xᵉ)
  is-emb-add-Commutative-Ringᵉ = is-emb-add-Abᵉ ab-Commutative-Ringᵉ

  is-emb-add-Commutative-Ring'ᵉ :
    (xᵉ : type-Commutative-Ringᵉ) → is-embᵉ (add-Commutative-Ring'ᵉ xᵉ)
  is-emb-add-Commutative-Ring'ᵉ = is-emb-add-Ab'ᵉ ab-Commutative-Ringᵉ

  is-injective-add-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) → is-injectiveᵉ (add-Commutative-Ringᵉ xᵉ)
  is-injective-add-Commutative-Ringᵉ = is-injective-add-Abᵉ ab-Commutative-Ringᵉ

  is-injective-add-Commutative-Ring'ᵉ :
    (xᵉ : type-Commutative-Ringᵉ) → is-injectiveᵉ (add-Commutative-Ring'ᵉ xᵉ)
  is-injective-add-Commutative-Ring'ᵉ = is-injective-add-Ab'ᵉ ab-Commutative-Ringᵉ
```

### The zero element of a commutative ring

```agda
  has-zero-Commutative-Ringᵉ : is-unitalᵉ add-Commutative-Ringᵉ
  has-zero-Commutative-Ringᵉ = has-zero-Ringᵉ ring-Commutative-Ringᵉ

  zero-Commutative-Ringᵉ : type-Commutative-Ringᵉ
  zero-Commutative-Ringᵉ = zero-Ringᵉ ring-Commutative-Ringᵉ

  is-zero-Commutative-Ringᵉ : type-Commutative-Ringᵉ → UUᵉ lᵉ
  is-zero-Commutative-Ringᵉ = is-zero-Ringᵉ ring-Commutative-Ringᵉ

  is-nonzero-Commutative-Ringᵉ : type-Commutative-Ringᵉ → UUᵉ lᵉ
  is-nonzero-Commutative-Ringᵉ = is-nonzero-Ringᵉ ring-Commutative-Ringᵉ

  is-zero-commutative-ring-Propᵉ : type-Commutative-Ringᵉ → Propᵉ lᵉ
  is-zero-commutative-ring-Propᵉ xᵉ =
    Id-Propᵉ set-Commutative-Ringᵉ xᵉ zero-Commutative-Ringᵉ

  is-nonzero-commutative-ring-Propᵉ : type-Commutative-Ringᵉ → Propᵉ lᵉ
  is-nonzero-commutative-ring-Propᵉ xᵉ =
    neg-Propᵉ (is-zero-commutative-ring-Propᵉ xᵉ)

  left-unit-law-add-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    add-Commutative-Ringᵉ zero-Commutative-Ringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Commutative-Ringᵉ =
    left-unit-law-add-Ringᵉ ring-Commutative-Ringᵉ

  right-unit-law-add-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    add-Commutative-Ringᵉ xᵉ zero-Commutative-Ringᵉ ＝ᵉ xᵉ
  right-unit-law-add-Commutative-Ringᵉ =
    right-unit-law-add-Ringᵉ ring-Commutative-Ringᵉ
```

### Additive inverses in a commutative ring

```agda
  has-negatives-Commutative-Ringᵉ :
    is-group-is-unital-Semigroupᵉ
      ( additive-semigroup-Commutative-Ringᵉ)
      ( has-zero-Commutative-Ringᵉ)
  has-negatives-Commutative-Ringᵉ = has-negatives-Abᵉ ab-Commutative-Ringᵉ

  neg-Commutative-Ringᵉ : type-Commutative-Ringᵉ → type-Commutative-Ringᵉ
  neg-Commutative-Ringᵉ = neg-Ringᵉ ring-Commutative-Ringᵉ

  left-inverse-law-add-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    add-Commutative-Ringᵉ (neg-Commutative-Ringᵉ xᵉ) xᵉ ＝ᵉ zero-Commutative-Ringᵉ
  left-inverse-law-add-Commutative-Ringᵉ =
    left-inverse-law-add-Ringᵉ ring-Commutative-Ringᵉ

  right-inverse-law-add-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    add-Commutative-Ringᵉ xᵉ (neg-Commutative-Ringᵉ xᵉ) ＝ᵉ zero-Commutative-Ringᵉ
  right-inverse-law-add-Commutative-Ringᵉ =
    right-inverse-law-add-Ringᵉ ring-Commutative-Ringᵉ

  neg-neg-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    neg-Commutative-Ringᵉ (neg-Commutative-Ringᵉ xᵉ) ＝ᵉ xᵉ
  neg-neg-Commutative-Ringᵉ = neg-neg-Abᵉ ab-Commutative-Ringᵉ

  distributive-neg-add-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-Commutative-Ringᵉ) →
    neg-Commutative-Ringᵉ (add-Commutative-Ringᵉ xᵉ yᵉ) ＝ᵉ
    add-Commutative-Ringᵉ (neg-Commutative-Ringᵉ xᵉ) (neg-Commutative-Ringᵉ yᵉ)
  distributive-neg-add-Commutative-Ringᵉ =
    distributive-neg-add-Abᵉ ab-Commutative-Ringᵉ
```

### Multiplication in a commutative ring

```agda
  has-associative-mul-Commutative-Ringᵉ :
    has-associative-mul-Setᵉ set-Commutative-Ringᵉ
  has-associative-mul-Commutative-Ringᵉ =
    has-associative-mul-Ringᵉ ring-Commutative-Ringᵉ

  mul-Commutative-Ringᵉ : (xᵉ yᵉ : type-Commutative-Ringᵉ) → type-Commutative-Ringᵉ
  mul-Commutative-Ringᵉ = mul-Ringᵉ ring-Commutative-Ringᵉ

  mul-Commutative-Ring'ᵉ : (xᵉ yᵉ : type-Commutative-Ringᵉ) → type-Commutative-Ringᵉ
  mul-Commutative-Ring'ᵉ = mul-Ring'ᵉ ring-Commutative-Ringᵉ

  ap-mul-Commutative-Ringᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Commutative-Ringᵉ} (pᵉ : Idᵉ xᵉ x'ᵉ) (qᵉ : Idᵉ yᵉ y'ᵉ) →
    Idᵉ (mul-Commutative-Ringᵉ xᵉ yᵉ) (mul-Commutative-Ringᵉ x'ᵉ y'ᵉ)
  ap-mul-Commutative-Ringᵉ pᵉ qᵉ = ap-binaryᵉ mul-Commutative-Ringᵉ pᵉ qᵉ

  associative-mul-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ (mul-Commutative-Ringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Commutative-Ringᵉ xᵉ (mul-Commutative-Ringᵉ yᵉ zᵉ)
  associative-mul-Commutative-Ringᵉ =
    associative-mul-Ringᵉ ring-Commutative-Ringᵉ

  multiplicative-semigroup-Commutative-Ringᵉ : Semigroupᵉ lᵉ
  pr1ᵉ multiplicative-semigroup-Commutative-Ringᵉ = set-Commutative-Ringᵉ
  pr2ᵉ multiplicative-semigroup-Commutative-Ringᵉ =
    has-associative-mul-Commutative-Ringᵉ

  left-distributive-mul-add-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ringᵉ) →
    ( mul-Commutative-Ringᵉ xᵉ (add-Commutative-Ringᵉ yᵉ zᵉ)) ＝ᵉ
    ( add-Commutative-Ringᵉ
      ( mul-Commutative-Ringᵉ xᵉ yᵉ)
      ( mul-Commutative-Ringᵉ xᵉ zᵉ))
  left-distributive-mul-add-Commutative-Ringᵉ =
    left-distributive-mul-add-Ringᵉ ring-Commutative-Ringᵉ

  right-distributive-mul-add-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ringᵉ) →
    ( mul-Commutative-Ringᵉ (add-Commutative-Ringᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Commutative-Ringᵉ
      ( mul-Commutative-Ringᵉ xᵉ zᵉ)
      ( mul-Commutative-Ringᵉ yᵉ zᵉ))
  right-distributive-mul-add-Commutative-Ringᵉ =
    right-distributive-mul-add-Ringᵉ ring-Commutative-Ringᵉ

  bidistributive-mul-add-Commutative-Ringᵉ :
    (uᵉ vᵉ xᵉ yᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ
      ( add-Commutative-Ringᵉ uᵉ vᵉ)
      ( add-Commutative-Ringᵉ xᵉ yᵉ) ＝ᵉ
    add-Commutative-Ringᵉ
      ( add-Commutative-Ringᵉ
        ( mul-Commutative-Ringᵉ uᵉ xᵉ)
        ( mul-Commutative-Ringᵉ uᵉ yᵉ))
      ( add-Commutative-Ringᵉ
        ( mul-Commutative-Ringᵉ vᵉ xᵉ)
        ( mul-Commutative-Ringᵉ vᵉ yᵉ))
  bidistributive-mul-add-Commutative-Ringᵉ =
    bidistributive-mul-add-Ringᵉ ring-Commutative-Ringᵉ

  commutative-mul-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ xᵉ yᵉ ＝ᵉ mul-Commutative-Ringᵉ yᵉ xᵉ
  commutative-mul-Commutative-Ringᵉ = pr2ᵉ Aᵉ
```

### Multiplicative units in a commutative ring

```agda
  is-unital-Commutative-Ringᵉ : is-unitalᵉ mul-Commutative-Ringᵉ
  is-unital-Commutative-Ringᵉ = is-unital-Ringᵉ ring-Commutative-Ringᵉ

  multiplicative-monoid-Commutative-Ringᵉ : Monoidᵉ lᵉ
  multiplicative-monoid-Commutative-Ringᵉ =
    multiplicative-monoid-Ringᵉ ring-Commutative-Ringᵉ

  one-Commutative-Ringᵉ : type-Commutative-Ringᵉ
  one-Commutative-Ringᵉ = one-Ringᵉ ring-Commutative-Ringᵉ

  left-unit-law-mul-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ one-Commutative-Ringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Commutative-Ringᵉ =
    left-unit-law-mul-Ringᵉ ring-Commutative-Ringᵉ

  right-unit-law-mul-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ xᵉ one-Commutative-Ringᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Commutative-Ringᵉ =
    right-unit-law-mul-Ringᵉ ring-Commutative-Ringᵉ

  right-swap-mul-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ (mul-Commutative-Ringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Commutative-Ringᵉ (mul-Commutative-Ringᵉ xᵉ zᵉ) yᵉ
  right-swap-mul-Commutative-Ringᵉ xᵉ yᵉ zᵉ =
    ( associative-mul-Commutative-Ringᵉ xᵉ yᵉ zᵉ) ∙ᵉ
    ( ( apᵉ
        ( mul-Commutative-Ringᵉ xᵉ)
        ( commutative-mul-Commutative-Ringᵉ yᵉ zᵉ)) ∙ᵉ
      ( invᵉ (associative-mul-Commutative-Ringᵉ xᵉ zᵉ yᵉ)))

  left-swap-mul-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ xᵉ (mul-Commutative-Ringᵉ yᵉ zᵉ) ＝ᵉ
    mul-Commutative-Ringᵉ yᵉ (mul-Commutative-Ringᵉ xᵉ zᵉ)
  left-swap-mul-Commutative-Ringᵉ xᵉ yᵉ zᵉ =
    ( invᵉ (associative-mul-Commutative-Ringᵉ xᵉ yᵉ zᵉ)) ∙ᵉ
    ( ( apᵉ
        ( mul-Commutative-Ring'ᵉ zᵉ)
        ( commutative-mul-Commutative-Ringᵉ xᵉ yᵉ)) ∙ᵉ
      ( associative-mul-Commutative-Ringᵉ yᵉ xᵉ zᵉ))

  interchange-mul-mul-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ wᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ
      ( mul-Commutative-Ringᵉ xᵉ yᵉ)
      ( mul-Commutative-Ringᵉ zᵉ wᵉ) ＝ᵉ
    mul-Commutative-Ringᵉ
      ( mul-Commutative-Ringᵉ xᵉ zᵉ)
      ( mul-Commutative-Ringᵉ yᵉ wᵉ)
  interchange-mul-mul-Commutative-Ringᵉ =
    interchange-law-commutative-and-associativeᵉ
      mul-Commutative-Ringᵉ
      commutative-mul-Commutative-Ringᵉ
      associative-mul-Commutative-Ringᵉ
```

### The zero laws for multiplication of a commutative ring

```agda
  left-zero-law-mul-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ zero-Commutative-Ringᵉ xᵉ ＝ᵉ
    zero-Commutative-Ringᵉ
  left-zero-law-mul-Commutative-Ringᵉ =
    left-zero-law-mul-Ringᵉ ring-Commutative-Ringᵉ

  right-zero-law-mul-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ xᵉ zero-Commutative-Ringᵉ ＝ᵉ
    zero-Commutative-Ringᵉ
  right-zero-law-mul-Commutative-Ringᵉ =
    right-zero-law-mul-Ringᵉ ring-Commutative-Ringᵉ
```

### Commutative rings are commutative semirings

```agda
  multiplicative-commutative-monoid-Commutative-Ringᵉ : Commutative-Monoidᵉ lᵉ
  pr1ᵉ multiplicative-commutative-monoid-Commutative-Ringᵉ =
    multiplicative-monoid-Ringᵉ ring-Commutative-Ringᵉ
  pr2ᵉ multiplicative-commutative-monoid-Commutative-Ringᵉ =
    commutative-mul-Commutative-Ringᵉ

  semiring-Commutative-Ringᵉ : Semiringᵉ lᵉ
  semiring-Commutative-Ringᵉ = semiring-Ringᵉ ring-Commutative-Ringᵉ

  commutative-semiring-Commutative-Ringᵉ : Commutative-Semiringᵉ lᵉ
  pr1ᵉ commutative-semiring-Commutative-Ringᵉ = semiring-Commutative-Ringᵉ
  pr2ᵉ commutative-semiring-Commutative-Ringᵉ = commutative-mul-Commutative-Ringᵉ
```

### Computing multiplication with minus one in a ring

```agda
  neg-one-Commutative-Ringᵉ : type-Commutative-Ringᵉ
  neg-one-Commutative-Ringᵉ = neg-one-Ringᵉ ring-Commutative-Ringᵉ

  mul-neg-one-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ neg-one-Commutative-Ringᵉ xᵉ ＝ᵉ
    neg-Commutative-Ringᵉ xᵉ
  mul-neg-one-Commutative-Ringᵉ = mul-neg-one-Ringᵉ ring-Commutative-Ringᵉ

  mul-neg-one-Commutative-Ring'ᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ xᵉ neg-one-Commutative-Ringᵉ ＝ᵉ
    neg-Commutative-Ringᵉ xᵉ
  mul-neg-one-Commutative-Ring'ᵉ = mul-neg-one-Ring'ᵉ ring-Commutative-Ringᵉ

  is-involution-mul-neg-one-Commutative-Ringᵉ :
    is-involutionᵉ (mul-Commutative-Ringᵉ neg-one-Commutative-Ringᵉ)
  is-involution-mul-neg-one-Commutative-Ringᵉ =
    is-involution-mul-neg-one-Ringᵉ ring-Commutative-Ringᵉ

  is-involution-mul-neg-one-Commutative-Ring'ᵉ :
    is-involutionᵉ (mul-Commutative-Ring'ᵉ neg-one-Commutative-Ringᵉ)
  is-involution-mul-neg-one-Commutative-Ring'ᵉ =
    is-involution-mul-neg-one-Ring'ᵉ ring-Commutative-Ringᵉ
```

### Left and right negative laws for multiplication

```agda
  left-negative-law-mul-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ (neg-Commutative-Ringᵉ xᵉ) yᵉ ＝ᵉ
    neg-Commutative-Ringᵉ (mul-Commutative-Ringᵉ xᵉ yᵉ)
  left-negative-law-mul-Commutative-Ringᵉ =
    left-negative-law-mul-Ringᵉ ring-Commutative-Ringᵉ

  right-negative-law-mul-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ xᵉ (neg-Commutative-Ringᵉ yᵉ) ＝ᵉ
    neg-Commutative-Ringᵉ (mul-Commutative-Ringᵉ xᵉ yᵉ)
  right-negative-law-mul-Commutative-Ringᵉ =
    right-negative-law-mul-Ringᵉ ring-Commutative-Ringᵉ

  mul-neg-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ (neg-Commutative-Ringᵉ xᵉ) (neg-Commutative-Ringᵉ yᵉ) ＝ᵉ
    mul-Commutative-Ringᵉ xᵉ yᵉ
  mul-neg-Commutative-Ringᵉ = mul-neg-Ringᵉ ring-Commutative-Ringᵉ
```

### Distributivity of multiplication over subtraction

```agda
  left-distributive-mul-left-subtraction-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ xᵉ (left-subtraction-Commutative-Ringᵉ yᵉ zᵉ) ＝ᵉ
    left-subtraction-Commutative-Ringᵉ
      ( mul-Commutative-Ringᵉ xᵉ yᵉ)
      ( mul-Commutative-Ringᵉ xᵉ zᵉ)
  left-distributive-mul-left-subtraction-Commutative-Ringᵉ =
    left-distributive-mul-left-subtraction-Ringᵉ ring-Commutative-Ringᵉ

  right-distributive-mul-left-subtraction-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ (left-subtraction-Commutative-Ringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    left-subtraction-Commutative-Ringᵉ
      ( mul-Commutative-Ringᵉ xᵉ zᵉ)
      ( mul-Commutative-Ringᵉ yᵉ zᵉ)
  right-distributive-mul-left-subtraction-Commutative-Ringᵉ =
    right-distributive-mul-left-subtraction-Ringᵉ ring-Commutative-Ringᵉ

  left-distributive-mul-right-subtraction-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ xᵉ (right-subtraction-Commutative-Ringᵉ yᵉ zᵉ) ＝ᵉ
    right-subtraction-Commutative-Ringᵉ
      ( mul-Commutative-Ringᵉ xᵉ yᵉ)
      ( mul-Commutative-Ringᵉ xᵉ zᵉ)
  left-distributive-mul-right-subtraction-Commutative-Ringᵉ =
    left-distributive-mul-right-subtraction-Ringᵉ ring-Commutative-Ringᵉ

  right-distributive-mul-right-subtraction-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ (right-subtraction-Commutative-Ringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    right-subtraction-Commutative-Ringᵉ
      ( mul-Commutative-Ringᵉ xᵉ zᵉ)
      ( mul-Commutative-Ringᵉ yᵉ zᵉ)
  right-distributive-mul-right-subtraction-Commutative-Ringᵉ =
    right-distributive-mul-right-subtraction-Ringᵉ ring-Commutative-Ringᵉ
```

### Scalar multiplication of elements of a commutative ring by natural numbers

```agda
  mul-nat-scalar-Commutative-Ringᵉ :
    ℕᵉ → type-Commutative-Ringᵉ → type-Commutative-Ringᵉ
  mul-nat-scalar-Commutative-Ringᵉ =
    mul-nat-scalar-Ringᵉ ring-Commutative-Ringᵉ

  ap-mul-nat-scalar-Commutative-Ringᵉ :
    {mᵉ nᵉ : ℕᵉ} {xᵉ yᵉ : type-Commutative-Ringᵉ} →
    (mᵉ ＝ᵉ nᵉ) → (xᵉ ＝ᵉ yᵉ) →
    mul-nat-scalar-Commutative-Ringᵉ mᵉ xᵉ ＝ᵉ
    mul-nat-scalar-Commutative-Ringᵉ nᵉ yᵉ
  ap-mul-nat-scalar-Commutative-Ringᵉ =
    ap-mul-nat-scalar-Ringᵉ ring-Commutative-Ringᵉ

  left-zero-law-mul-nat-scalar-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    mul-nat-scalar-Commutative-Ringᵉ 0 xᵉ ＝ᵉ zero-Commutative-Ringᵉ
  left-zero-law-mul-nat-scalar-Commutative-Ringᵉ =
    left-zero-law-mul-nat-scalar-Ringᵉ ring-Commutative-Ringᵉ

  right-zero-law-mul-nat-scalar-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) →
    mul-nat-scalar-Commutative-Ringᵉ nᵉ zero-Commutative-Ringᵉ ＝ᵉ
    zero-Commutative-Ringᵉ
  right-zero-law-mul-nat-scalar-Commutative-Ringᵉ =
    right-zero-law-mul-nat-scalar-Ringᵉ ring-Commutative-Ringᵉ

  left-unit-law-mul-nat-scalar-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ) →
    mul-nat-scalar-Commutative-Ringᵉ 1 xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-nat-scalar-Commutative-Ringᵉ =
    left-unit-law-mul-nat-scalar-Ringᵉ ring-Commutative-Ringᵉ

  left-nat-scalar-law-mul-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ (mul-nat-scalar-Commutative-Ringᵉ nᵉ xᵉ) yᵉ ＝ᵉ
    mul-nat-scalar-Commutative-Ringᵉ nᵉ (mul-Commutative-Ringᵉ xᵉ yᵉ)
  left-nat-scalar-law-mul-Commutative-Ringᵉ =
    left-nat-scalar-law-mul-Ringᵉ ring-Commutative-Ringᵉ

  right-nat-scalar-law-mul-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Commutative-Ringᵉ) →
    mul-Commutative-Ringᵉ xᵉ (mul-nat-scalar-Commutative-Ringᵉ nᵉ yᵉ) ＝ᵉ
    mul-nat-scalar-Commutative-Ringᵉ nᵉ (mul-Commutative-Ringᵉ xᵉ yᵉ)
  right-nat-scalar-law-mul-Commutative-Ringᵉ =
    right-nat-scalar-law-mul-Ringᵉ ring-Commutative-Ringᵉ

  left-distributive-mul-nat-scalar-add-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Commutative-Ringᵉ) →
    mul-nat-scalar-Commutative-Ringᵉ nᵉ (add-Commutative-Ringᵉ xᵉ yᵉ) ＝ᵉ
    add-Commutative-Ringᵉ
      ( mul-nat-scalar-Commutative-Ringᵉ nᵉ xᵉ)
      ( mul-nat-scalar-Commutative-Ringᵉ nᵉ yᵉ)
  left-distributive-mul-nat-scalar-add-Commutative-Ringᵉ =
    left-distributive-mul-nat-scalar-add-Ringᵉ ring-Commutative-Ringᵉ

  right-distributive-mul-nat-scalar-add-Commutative-Ringᵉ :
    (mᵉ nᵉ : ℕᵉ) (xᵉ : type-Commutative-Ringᵉ) →
    mul-nat-scalar-Commutative-Ringᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    add-Commutative-Ringᵉ
      ( mul-nat-scalar-Commutative-Ringᵉ mᵉ xᵉ)
      ( mul-nat-scalar-Commutative-Ringᵉ nᵉ xᵉ)
  right-distributive-mul-nat-scalar-add-Commutative-Ringᵉ =
    right-distributive-mul-nat-scalar-add-Ringᵉ ring-Commutative-Ringᵉ
```

### Addition of a list of elements in a commutative ring

```agda
  add-list-Commutative-Ringᵉ : listᵉ type-Commutative-Ringᵉ → type-Commutative-Ringᵉ
  add-list-Commutative-Ringᵉ = add-list-Ringᵉ ring-Commutative-Ringᵉ

  preserves-concat-add-list-Commutative-Ringᵉ :
    (l1ᵉ l2ᵉ : listᵉ type-Commutative-Ringᵉ) →
    Idᵉ
      ( add-list-Commutative-Ringᵉ (concat-listᵉ l1ᵉ l2ᵉ))
      ( add-Commutative-Ringᵉ
        ( add-list-Commutative-Ringᵉ l1ᵉ)
        ( add-list-Commutative-Ringᵉ l2ᵉ))
  preserves-concat-add-list-Commutative-Ringᵉ =
    preserves-concat-add-list-Ringᵉ ring-Commutative-Ringᵉ
```