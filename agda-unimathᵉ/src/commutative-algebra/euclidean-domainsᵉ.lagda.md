# Euclidean domains

```agda
module commutative-algebra.euclidean-domainsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.commutative-semiringsᵉ
open import commutative-algebra.integral-domainsᵉ
open import commutative-algebra.trivial-commutative-ringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-embeddingsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
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

Aᵉ **Euclideanᵉ domain**ᵉ isᵉ anᵉ
[integralᵉ domain](commutative-algebra.integral-domains.mdᵉ) `R`ᵉ thatᵉ hasᵉ aᵉ
**Euclideanᵉ valuation**,ᵉ i.e.,ᵉ aᵉ functionᵉ `vᵉ : Rᵉ → ℕ`ᵉ suchᵉ thatᵉ forᵉ everyᵉ
`xᵉ yᵉ : R`,ᵉ ifᵉ `y`ᵉ isᵉ nonzeroᵉ thenᵉ thereᵉ areᵉ `qᵉ rᵉ : R`ᵉ with `xᵉ = qᵉ yᵉ +ᵉ r`ᵉ andᵉ
`vᵉ rᵉ <ᵉ vᵉ y`.ᵉ

## Definition

### The condition of being a Euclidean valuation

```agda
is-euclidean-valuationᵉ :
  { lᵉ : Level} (Rᵉ : Integral-Domainᵉ lᵉ) →
  ( type-Integral-Domainᵉ Rᵉ → ℕᵉ) →
  UUᵉ lᵉ
is-euclidean-valuationᵉ Rᵉ vᵉ =
  ( xᵉ yᵉ : type-Integral-Domainᵉ Rᵉ) →
  ( is-nonzero-Integral-Domainᵉ Rᵉ yᵉ) →
  Σᵉ ( type-Integral-Domainᵉ Rᵉ ×ᵉ type-Integral-Domainᵉ Rᵉ)
    ( λ (qᵉ ,ᵉ rᵉ) →
      ( Idᵉ xᵉ (add-Integral-Domainᵉ Rᵉ (mul-Integral-Domainᵉ Rᵉ qᵉ yᵉ) rᵉ)) ×ᵉ
        ( is-zero-Integral-Domainᵉ Rᵉ rᵉ +ᵉ
        ( vᵉ rᵉ <-ℕᵉ vᵉ yᵉ)))
```

### The condition of being a Euclidean domain

```agda
is-euclidean-domain-Integral-Domainᵉ :
  { lᵉ : Level} (Rᵉ : Integral-Domainᵉ lᵉ) → UUᵉ lᵉ
is-euclidean-domain-Integral-Domainᵉ Rᵉ =
  Σᵉ (type-Integral-Domainᵉ Rᵉ → ℕᵉ) (is-euclidean-valuationᵉ Rᵉ)
```

### Euclidean domains

```agda
Euclidean-Domainᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Euclidean-Domainᵉ lᵉ =
  Σᵉ (Integral-Domainᵉ lᵉ) is-euclidean-domain-Integral-Domainᵉ

module _
  {lᵉ : Level} (Rᵉ : Euclidean-Domainᵉ lᵉ)
  where

  integral-domain-Euclidean-Domainᵉ : Integral-Domainᵉ lᵉ
  integral-domain-Euclidean-Domainᵉ = pr1ᵉ Rᵉ

  is-euclidean-domain-Euclidean-Domainᵉ :
    is-euclidean-domain-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ
  is-euclidean-domain-Euclidean-Domainᵉ = pr2ᵉ Rᵉ

  commutative-ring-Euclidean-Domainᵉ : Commutative-Ringᵉ lᵉ
  commutative-ring-Euclidean-Domainᵉ =
    commutative-ring-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  has-cancellation-property-Euclidean-Domainᵉ :
    cancellation-property-Commutative-Ringᵉ commutative-ring-Euclidean-Domainᵉ
  has-cancellation-property-Euclidean-Domainᵉ =
    has-cancellation-property-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  is-nontrivial-Euclidean-Domainᵉ :
    is-nontrivial-Commutative-Ringᵉ commutative-ring-Euclidean-Domainᵉ
  is-nontrivial-Euclidean-Domainᵉ =
    is-nontrivial-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  ab-Euclidean-Domainᵉ : Abᵉ lᵉ
  ab-Euclidean-Domainᵉ =
    ab-Commutative-Ringᵉ commutative-ring-Euclidean-Domainᵉ

  ring-Euclidean-Domainᵉ : Ringᵉ lᵉ
  ring-Euclidean-Domainᵉ =
    ring-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  set-Euclidean-Domainᵉ : Setᵉ lᵉ
  set-Euclidean-Domainᵉ = set-Ringᵉ ring-Euclidean-Domainᵉ

  type-Euclidean-Domainᵉ : UUᵉ lᵉ
  type-Euclidean-Domainᵉ = type-Ringᵉ ring-Euclidean-Domainᵉ

  is-set-type-Euclidean-Domainᵉ : is-setᵉ type-Euclidean-Domainᵉ
  is-set-type-Euclidean-Domainᵉ = is-set-type-Ringᵉ ring-Euclidean-Domainᵉ
```

### Addition in a Euclidean domain

```agda
  has-associative-add-Euclidean-Domainᵉ :
    has-associative-mul-Setᵉ set-Euclidean-Domainᵉ
  has-associative-add-Euclidean-Domainᵉ =
    has-associative-add-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  add-Euclidean-Domainᵉ :
    type-Euclidean-Domainᵉ → type-Euclidean-Domainᵉ → type-Euclidean-Domainᵉ
  add-Euclidean-Domainᵉ = add-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  add-Euclidean-Domain'ᵉ :
    type-Euclidean-Domainᵉ → type-Euclidean-Domainᵉ → type-Euclidean-Domainᵉ
  add-Euclidean-Domain'ᵉ = add-Integral-Domain'ᵉ integral-domain-Euclidean-Domainᵉ

  ap-add-Euclidean-Domainᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Euclidean-Domainᵉ} →
    (xᵉ ＝ᵉ x'ᵉ) → (yᵉ ＝ᵉ y'ᵉ) →
    add-Euclidean-Domainᵉ xᵉ yᵉ ＝ᵉ add-Euclidean-Domainᵉ x'ᵉ y'ᵉ
  ap-add-Euclidean-Domainᵉ =
    ap-add-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  associative-add-Euclidean-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Euclidean-Domainᵉ) →
    ( add-Euclidean-Domainᵉ (add-Euclidean-Domainᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Euclidean-Domainᵉ xᵉ (add-Euclidean-Domainᵉ yᵉ zᵉ))
  associative-add-Euclidean-Domainᵉ =
    associative-add-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  additive-semigroup-Euclidean-Domainᵉ : Semigroupᵉ lᵉ
  additive-semigroup-Euclidean-Domainᵉ = semigroup-Abᵉ ab-Euclidean-Domainᵉ

  is-group-additive-semigroup-Euclidean-Domainᵉ :
    is-group-Semigroupᵉ additive-semigroup-Euclidean-Domainᵉ
  is-group-additive-semigroup-Euclidean-Domainᵉ =
    is-group-Abᵉ ab-Euclidean-Domainᵉ

  commutative-add-Euclidean-Domainᵉ :
    (xᵉ yᵉ : type-Euclidean-Domainᵉ) →
    Idᵉ (add-Euclidean-Domainᵉ xᵉ yᵉ) (add-Euclidean-Domainᵉ yᵉ xᵉ)
  commutative-add-Euclidean-Domainᵉ = commutative-add-Abᵉ ab-Euclidean-Domainᵉ

  interchange-add-add-Euclidean-Domainᵉ :
    (xᵉ yᵉ x'ᵉ y'ᵉ : type-Euclidean-Domainᵉ) →
    ( add-Euclidean-Domainᵉ
      ( add-Euclidean-Domainᵉ xᵉ yᵉ)
      ( add-Euclidean-Domainᵉ x'ᵉ y'ᵉ)) ＝ᵉ
    ( add-Euclidean-Domainᵉ
      ( add-Euclidean-Domainᵉ xᵉ x'ᵉ)
      ( add-Euclidean-Domainᵉ yᵉ y'ᵉ))
  interchange-add-add-Euclidean-Domainᵉ =
    interchange-add-add-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  right-swap-add-Euclidean-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Euclidean-Domainᵉ) →
    ( add-Euclidean-Domainᵉ (add-Euclidean-Domainᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Euclidean-Domainᵉ (add-Euclidean-Domainᵉ xᵉ zᵉ) yᵉ)
  right-swap-add-Euclidean-Domainᵉ =
    right-swap-add-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  left-swap-add-Euclidean-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Euclidean-Domainᵉ) →
    ( add-Euclidean-Domainᵉ xᵉ (add-Euclidean-Domainᵉ yᵉ zᵉ)) ＝ᵉ
    ( add-Euclidean-Domainᵉ yᵉ (add-Euclidean-Domainᵉ xᵉ zᵉ))
  left-swap-add-Euclidean-Domainᵉ =
    left-swap-add-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  is-equiv-add-Euclidean-Domainᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) → is-equivᵉ (add-Euclidean-Domainᵉ xᵉ)
  is-equiv-add-Euclidean-Domainᵉ = is-equiv-add-Abᵉ ab-Euclidean-Domainᵉ

  is-equiv-add-Euclidean-Domain'ᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) → is-equivᵉ (add-Euclidean-Domain'ᵉ xᵉ)
  is-equiv-add-Euclidean-Domain'ᵉ = is-equiv-add-Ab'ᵉ ab-Euclidean-Domainᵉ

  is-binary-equiv-add-Euclidean-Domainᵉ : is-binary-equivᵉ add-Euclidean-Domainᵉ
  pr1ᵉ is-binary-equiv-add-Euclidean-Domainᵉ = is-equiv-add-Euclidean-Domain'ᵉ
  pr2ᵉ is-binary-equiv-add-Euclidean-Domainᵉ = is-equiv-add-Euclidean-Domainᵉ

  is-binary-emb-add-Euclidean-Domainᵉ : is-binary-embᵉ add-Euclidean-Domainᵉ
  is-binary-emb-add-Euclidean-Domainᵉ = is-binary-emb-add-Abᵉ ab-Euclidean-Domainᵉ

  is-emb-add-Euclidean-Domainᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) → is-embᵉ (add-Euclidean-Domainᵉ xᵉ)
  is-emb-add-Euclidean-Domainᵉ = is-emb-add-Abᵉ ab-Euclidean-Domainᵉ

  is-emb-add-Euclidean-Domain'ᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) → is-embᵉ (add-Euclidean-Domain'ᵉ xᵉ)
  is-emb-add-Euclidean-Domain'ᵉ = is-emb-add-Ab'ᵉ ab-Euclidean-Domainᵉ

  is-injective-add-Euclidean-Domainᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) → is-injectiveᵉ (add-Euclidean-Domainᵉ xᵉ)
  is-injective-add-Euclidean-Domainᵉ = is-injective-add-Abᵉ ab-Euclidean-Domainᵉ

  is-injective-add-Euclidean-Domain'ᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) → is-injectiveᵉ (add-Euclidean-Domain'ᵉ xᵉ)
  is-injective-add-Euclidean-Domain'ᵉ = is-injective-add-Ab'ᵉ ab-Euclidean-Domainᵉ
```

### The zero element of a Euclidean domain

```agda
  has-zero-Euclidean-Domainᵉ : is-unitalᵉ add-Euclidean-Domainᵉ
  has-zero-Euclidean-Domainᵉ =
    has-zero-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  zero-Euclidean-Domainᵉ : type-Euclidean-Domainᵉ
  zero-Euclidean-Domainᵉ =
    zero-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  is-zero-Euclidean-Domainᵉ : type-Euclidean-Domainᵉ → UUᵉ lᵉ
  is-zero-Euclidean-Domainᵉ =
    is-zero-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  is-nonzero-Euclidean-Domainᵉ : type-Euclidean-Domainᵉ → UUᵉ lᵉ
  is-nonzero-Euclidean-Domainᵉ =
    is-nonzero-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  is-zero-euclidean-domain-Propᵉ : type-Euclidean-Domainᵉ → Propᵉ lᵉ
  is-zero-euclidean-domain-Propᵉ xᵉ =
    Id-Propᵉ set-Euclidean-Domainᵉ xᵉ zero-Euclidean-Domainᵉ

  is-nonzero-euclidean-domain-Propᵉ : type-Euclidean-Domainᵉ → Propᵉ lᵉ
  is-nonzero-euclidean-domain-Propᵉ xᵉ =
    neg-Propᵉ (is-zero-euclidean-domain-Propᵉ xᵉ)

  left-unit-law-add-Euclidean-Domainᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) →
    add-Euclidean-Domainᵉ zero-Euclidean-Domainᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Euclidean-Domainᵉ =
    left-unit-law-add-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  right-unit-law-add-Euclidean-Domainᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) →
    add-Euclidean-Domainᵉ xᵉ zero-Euclidean-Domainᵉ ＝ᵉ xᵉ
  right-unit-law-add-Euclidean-Domainᵉ =
    right-unit-law-add-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ
```

### Additive inverses in a Euclidean domain

```agda
  has-negatives-Euclidean-Domainᵉ :
    is-group-is-unital-Semigroupᵉ
      ( additive-semigroup-Euclidean-Domainᵉ)
      ( has-zero-Euclidean-Domainᵉ)
  has-negatives-Euclidean-Domainᵉ = has-negatives-Abᵉ ab-Euclidean-Domainᵉ

  neg-Euclidean-Domainᵉ : type-Euclidean-Domainᵉ → type-Euclidean-Domainᵉ
  neg-Euclidean-Domainᵉ = neg-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  left-inverse-law-add-Euclidean-Domainᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) →
    add-Euclidean-Domainᵉ (neg-Euclidean-Domainᵉ xᵉ) xᵉ ＝ᵉ zero-Euclidean-Domainᵉ
  left-inverse-law-add-Euclidean-Domainᵉ =
    left-inverse-law-add-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  right-inverse-law-add-Euclidean-Domainᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) →
    add-Euclidean-Domainᵉ xᵉ (neg-Euclidean-Domainᵉ xᵉ) ＝ᵉ zero-Euclidean-Domainᵉ
  right-inverse-law-add-Euclidean-Domainᵉ =
    right-inverse-law-add-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  neg-neg-Euclidean-Domainᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) →
    neg-Euclidean-Domainᵉ (neg-Euclidean-Domainᵉ xᵉ) ＝ᵉ xᵉ
  neg-neg-Euclidean-Domainᵉ = neg-neg-Abᵉ ab-Euclidean-Domainᵉ

  distributive-neg-add-Euclidean-Domainᵉ :
    (xᵉ yᵉ : type-Euclidean-Domainᵉ) →
    neg-Euclidean-Domainᵉ (add-Euclidean-Domainᵉ xᵉ yᵉ) ＝ᵉ
    add-Euclidean-Domainᵉ (neg-Euclidean-Domainᵉ xᵉ) (neg-Euclidean-Domainᵉ yᵉ)
  distributive-neg-add-Euclidean-Domainᵉ =
    distributive-neg-add-Abᵉ ab-Euclidean-Domainᵉ
```

### Multiplication in a Euclidean domain

```agda
  has-associative-mul-Euclidean-Domainᵉ :
    has-associative-mul-Setᵉ set-Euclidean-Domainᵉ
  has-associative-mul-Euclidean-Domainᵉ =
    has-associative-mul-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  mul-Euclidean-Domainᵉ :
    (xᵉ yᵉ : type-Euclidean-Domainᵉ) → type-Euclidean-Domainᵉ
  mul-Euclidean-Domainᵉ =
    mul-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  mul-Euclidean-Domain'ᵉ :
    (xᵉ yᵉ : type-Euclidean-Domainᵉ) → type-Euclidean-Domainᵉ
  mul-Euclidean-Domain'ᵉ =
    mul-Integral-Domain'ᵉ integral-domain-Euclidean-Domainᵉ

  ap-mul-Euclidean-Domainᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Euclidean-Domainᵉ} (pᵉ : Idᵉ xᵉ x'ᵉ) (qᵉ : Idᵉ yᵉ y'ᵉ) →
    Idᵉ (mul-Euclidean-Domainᵉ xᵉ yᵉ) (mul-Euclidean-Domainᵉ x'ᵉ y'ᵉ)
  ap-mul-Euclidean-Domainᵉ pᵉ qᵉ = ap-binaryᵉ mul-Euclidean-Domainᵉ pᵉ qᵉ

  associative-mul-Euclidean-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ (mul-Euclidean-Domainᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Euclidean-Domainᵉ xᵉ (mul-Euclidean-Domainᵉ yᵉ zᵉ)
  associative-mul-Euclidean-Domainᵉ =
    associative-mul-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  multiplicative-semigroup-Euclidean-Domainᵉ : Semigroupᵉ lᵉ
  multiplicative-semigroup-Euclidean-Domainᵉ =
    multiplicative-semigroup-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  left-distributive-mul-add-Euclidean-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Euclidean-Domainᵉ) →
    ( mul-Euclidean-Domainᵉ xᵉ (add-Euclidean-Domainᵉ yᵉ zᵉ)) ＝ᵉ
    ( add-Euclidean-Domainᵉ
      ( mul-Euclidean-Domainᵉ xᵉ yᵉ)
      ( mul-Euclidean-Domainᵉ xᵉ zᵉ))
  left-distributive-mul-add-Euclidean-Domainᵉ =
    left-distributive-mul-add-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  right-distributive-mul-add-Euclidean-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Euclidean-Domainᵉ) →
    ( mul-Euclidean-Domainᵉ (add-Euclidean-Domainᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Euclidean-Domainᵉ
      ( mul-Euclidean-Domainᵉ xᵉ zᵉ)
      ( mul-Euclidean-Domainᵉ yᵉ zᵉ))
  right-distributive-mul-add-Euclidean-Domainᵉ =
    right-distributive-mul-add-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  commutative-mul-Euclidean-Domainᵉ :
    (xᵉ yᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ xᵉ yᵉ ＝ᵉ mul-Euclidean-Domainᵉ yᵉ xᵉ
  commutative-mul-Euclidean-Domainᵉ =
    commutative-mul-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ
```

### Multiplicative units in a Euclidean domain

```agda
  is-unital-Euclidean-Domainᵉ : is-unitalᵉ mul-Euclidean-Domainᵉ
  is-unital-Euclidean-Domainᵉ =
    is-unital-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  multiplicative-monoid-Euclidean-Domainᵉ : Monoidᵉ lᵉ
  multiplicative-monoid-Euclidean-Domainᵉ =
    multiplicative-monoid-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  one-Euclidean-Domainᵉ : type-Euclidean-Domainᵉ
  one-Euclidean-Domainᵉ =
    one-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  left-unit-law-mul-Euclidean-Domainᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ one-Euclidean-Domainᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Euclidean-Domainᵉ =
    left-unit-law-mul-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  right-unit-law-mul-Euclidean-Domainᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ xᵉ one-Euclidean-Domainᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Euclidean-Domainᵉ =
    right-unit-law-mul-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  right-swap-mul-Euclidean-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ (mul-Euclidean-Domainᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Euclidean-Domainᵉ (mul-Euclidean-Domainᵉ xᵉ zᵉ) yᵉ
  right-swap-mul-Euclidean-Domainᵉ xᵉ yᵉ zᵉ =
    ( associative-mul-Euclidean-Domainᵉ xᵉ yᵉ zᵉ) ∙ᵉ
    ( ( apᵉ
        ( mul-Euclidean-Domainᵉ xᵉ)
        ( commutative-mul-Euclidean-Domainᵉ yᵉ zᵉ)) ∙ᵉ
      ( invᵉ (associative-mul-Euclidean-Domainᵉ xᵉ zᵉ yᵉ)))

  left-swap-mul-Euclidean-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ xᵉ (mul-Euclidean-Domainᵉ yᵉ zᵉ) ＝ᵉ
    mul-Euclidean-Domainᵉ yᵉ (mul-Euclidean-Domainᵉ xᵉ zᵉ)
  left-swap-mul-Euclidean-Domainᵉ xᵉ yᵉ zᵉ =
    ( invᵉ (associative-mul-Euclidean-Domainᵉ xᵉ yᵉ zᵉ)) ∙ᵉ
    ( ( apᵉ
        ( mul-Euclidean-Domain'ᵉ zᵉ)
        ( commutative-mul-Euclidean-Domainᵉ xᵉ yᵉ)) ∙ᵉ
      ( associative-mul-Euclidean-Domainᵉ yᵉ xᵉ zᵉ))

  interchange-mul-mul-Euclidean-Domainᵉ :
    (xᵉ yᵉ zᵉ wᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ
      ( mul-Euclidean-Domainᵉ xᵉ yᵉ)
      ( mul-Euclidean-Domainᵉ zᵉ wᵉ) ＝ᵉ
    mul-Euclidean-Domainᵉ
      ( mul-Euclidean-Domainᵉ xᵉ zᵉ)
      ( mul-Euclidean-Domainᵉ yᵉ wᵉ)
  interchange-mul-mul-Euclidean-Domainᵉ =
    interchange-law-commutative-and-associativeᵉ
      mul-Euclidean-Domainᵉ
      commutative-mul-Euclidean-Domainᵉ
      associative-mul-Euclidean-Domainᵉ
```

### The zero laws for multiplication of a Euclidean domain

```agda
  left-zero-law-mul-Euclidean-Domainᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ zero-Euclidean-Domainᵉ xᵉ ＝ᵉ
    zero-Euclidean-Domainᵉ
  left-zero-law-mul-Euclidean-Domainᵉ =
    left-zero-law-mul-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  right-zero-law-mul-Euclidean-Domainᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ xᵉ zero-Euclidean-Domainᵉ ＝ᵉ
    zero-Euclidean-Domainᵉ
  right-zero-law-mul-Euclidean-Domainᵉ =
    right-zero-law-mul-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ
```

### Euclidean domains are commutative semirings

```agda
  multiplicative-commutative-monoid-Euclidean-Domainᵉ : Commutative-Monoidᵉ lᵉ
  multiplicative-commutative-monoid-Euclidean-Domainᵉ =
    multiplicative-commutative-monoid-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  semiring-Euclidean-Domainᵉ : Semiringᵉ lᵉ
  semiring-Euclidean-Domainᵉ =
    semiring-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  commutative-semiring-Euclidean-Domainᵉ : Commutative-Semiringᵉ lᵉ
  commutative-semiring-Euclidean-Domainᵉ =
    commutative-semiring-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ
```

### Computing multiplication with minus one in a Euclidean domain

```agda
  neg-one-Euclidean-Domainᵉ : type-Euclidean-Domainᵉ
  neg-one-Euclidean-Domainᵉ =
    neg-one-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  mul-neg-one-Euclidean-Domainᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ neg-one-Euclidean-Domainᵉ xᵉ ＝ᵉ
    neg-Euclidean-Domainᵉ xᵉ
  mul-neg-one-Euclidean-Domainᵉ =
    mul-neg-one-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  mul-neg-one-Euclidean-Domain'ᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ xᵉ neg-one-Euclidean-Domainᵉ ＝ᵉ
    neg-Euclidean-Domainᵉ xᵉ
  mul-neg-one-Euclidean-Domain'ᵉ =
    mul-neg-one-Integral-Domain'ᵉ
      integral-domain-Euclidean-Domainᵉ

  is-involution-mul-neg-one-Euclidean-Domainᵉ :
    is-involutionᵉ (mul-Euclidean-Domainᵉ neg-one-Euclidean-Domainᵉ)
  is-involution-mul-neg-one-Euclidean-Domainᵉ =
    is-involution-mul-neg-one-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  is-involution-mul-neg-one-Euclidean-Domain'ᵉ :
    is-involutionᵉ (mul-Euclidean-Domain'ᵉ neg-one-Euclidean-Domainᵉ)
  is-involution-mul-neg-one-Euclidean-Domain'ᵉ =
    is-involution-mul-neg-one-Integral-Domain'ᵉ
      integral-domain-Euclidean-Domainᵉ
```

### Left and right negative laws for multiplication

```agda
  left-negative-law-mul-Euclidean-Domainᵉ :
    (xᵉ yᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ (neg-Euclidean-Domainᵉ xᵉ) yᵉ ＝ᵉ
    neg-Euclidean-Domainᵉ (mul-Euclidean-Domainᵉ xᵉ yᵉ)
  left-negative-law-mul-Euclidean-Domainᵉ =
    left-negative-law-mul-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  right-negative-law-mul-Euclidean-Domainᵉ :
    (xᵉ yᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ xᵉ (neg-Euclidean-Domainᵉ yᵉ) ＝ᵉ
    neg-Euclidean-Domainᵉ (mul-Euclidean-Domainᵉ xᵉ yᵉ)
  right-negative-law-mul-Euclidean-Domainᵉ =
    right-negative-law-mul-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  mul-neg-Euclidean-Domainᵉ :
    (xᵉ yᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ (neg-Euclidean-Domainᵉ xᵉ) (neg-Euclidean-Domainᵉ yᵉ) ＝ᵉ
    mul-Euclidean-Domainᵉ xᵉ yᵉ
  mul-neg-Euclidean-Domainᵉ =
    mul-neg-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ
```

### Scalar multiplication of elements of a Euclidean domain by natural numbers

```agda
  mul-nat-scalar-Euclidean-Domainᵉ :
    ℕᵉ → type-Euclidean-Domainᵉ → type-Euclidean-Domainᵉ
  mul-nat-scalar-Euclidean-Domainᵉ =
    mul-nat-scalar-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  ap-mul-nat-scalar-Euclidean-Domainᵉ :
    {mᵉ nᵉ : ℕᵉ} {xᵉ yᵉ : type-Euclidean-Domainᵉ} →
    (mᵉ ＝ᵉ nᵉ) → (xᵉ ＝ᵉ yᵉ) →
    mul-nat-scalar-Euclidean-Domainᵉ mᵉ xᵉ ＝ᵉ
    mul-nat-scalar-Euclidean-Domainᵉ nᵉ yᵉ
  ap-mul-nat-scalar-Euclidean-Domainᵉ =
    ap-mul-nat-scalar-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  left-zero-law-mul-nat-scalar-Euclidean-Domainᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) →
    mul-nat-scalar-Euclidean-Domainᵉ 0 xᵉ ＝ᵉ zero-Euclidean-Domainᵉ
  left-zero-law-mul-nat-scalar-Euclidean-Domainᵉ =
    left-zero-law-mul-nat-scalar-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  right-zero-law-mul-nat-scalar-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) →
    mul-nat-scalar-Euclidean-Domainᵉ nᵉ zero-Euclidean-Domainᵉ ＝ᵉ
    zero-Euclidean-Domainᵉ
  right-zero-law-mul-nat-scalar-Euclidean-Domainᵉ =
    right-zero-law-mul-nat-scalar-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  left-unit-law-mul-nat-scalar-Euclidean-Domainᵉ :
    (xᵉ : type-Euclidean-Domainᵉ) →
    mul-nat-scalar-Euclidean-Domainᵉ 1 xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-nat-scalar-Euclidean-Domainᵉ =
    left-unit-law-mul-nat-scalar-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  left-nat-scalar-law-mul-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ (mul-nat-scalar-Euclidean-Domainᵉ nᵉ xᵉ) yᵉ ＝ᵉ
    mul-nat-scalar-Euclidean-Domainᵉ nᵉ (mul-Euclidean-Domainᵉ xᵉ yᵉ)
  left-nat-scalar-law-mul-Euclidean-Domainᵉ =
    left-nat-scalar-law-mul-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  right-nat-scalar-law-mul-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Euclidean-Domainᵉ) →
    mul-Euclidean-Domainᵉ xᵉ (mul-nat-scalar-Euclidean-Domainᵉ nᵉ yᵉ) ＝ᵉ
    mul-nat-scalar-Euclidean-Domainᵉ nᵉ (mul-Euclidean-Domainᵉ xᵉ yᵉ)
  right-nat-scalar-law-mul-Euclidean-Domainᵉ =
    right-nat-scalar-law-mul-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  left-distributive-mul-nat-scalar-add-Euclidean-Domainᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Euclidean-Domainᵉ) →
    mul-nat-scalar-Euclidean-Domainᵉ nᵉ (add-Euclidean-Domainᵉ xᵉ yᵉ) ＝ᵉ
    add-Euclidean-Domainᵉ
      ( mul-nat-scalar-Euclidean-Domainᵉ nᵉ xᵉ)
      ( mul-nat-scalar-Euclidean-Domainᵉ nᵉ yᵉ)
  left-distributive-mul-nat-scalar-add-Euclidean-Domainᵉ =
    left-distributive-mul-nat-scalar-add-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ

  right-distributive-mul-nat-scalar-add-Euclidean-Domainᵉ :
    (mᵉ nᵉ : ℕᵉ) (xᵉ : type-Euclidean-Domainᵉ) →
    mul-nat-scalar-Euclidean-Domainᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    add-Euclidean-Domainᵉ
      ( mul-nat-scalar-Euclidean-Domainᵉ mᵉ xᵉ)
      ( mul-nat-scalar-Euclidean-Domainᵉ nᵉ xᵉ)
  right-distributive-mul-nat-scalar-add-Euclidean-Domainᵉ =
    right-distributive-mul-nat-scalar-add-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ
```

### Addition of a list of elements in a Euclidean domain

```agda
  add-list-Euclidean-Domainᵉ :
    listᵉ type-Euclidean-Domainᵉ → type-Euclidean-Domainᵉ
  add-list-Euclidean-Domainᵉ =
    add-list-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ

  preserves-concat-add-list-Euclidean-Domainᵉ :
    (l1ᵉ l2ᵉ : listᵉ type-Euclidean-Domainᵉ) →
    Idᵉ
      ( add-list-Euclidean-Domainᵉ (concat-listᵉ l1ᵉ l2ᵉ))
      ( add-Euclidean-Domainᵉ
        ( add-list-Euclidean-Domainᵉ l1ᵉ)
        ( add-list-Euclidean-Domainᵉ l2ᵉ))
  preserves-concat-add-list-Euclidean-Domainᵉ =
    preserves-concat-add-list-Integral-Domainᵉ
      integral-domain-Euclidean-Domainᵉ
```

### Euclidean division in a Euclidean domain

```agda
  euclidean-valuation-Euclidean-Domainᵉ :
    type-Euclidean-Domainᵉ → ℕᵉ
  euclidean-valuation-Euclidean-Domainᵉ =
    pr1ᵉ is-euclidean-domain-Euclidean-Domainᵉ

  euclidean-division-Euclidean-Domainᵉ :
    ( xᵉ yᵉ : type-Euclidean-Domainᵉ) →
    ( is-nonzero-Euclidean-Domainᵉ yᵉ) →
    type-Euclidean-Domainᵉ ×ᵉ type-Euclidean-Domainᵉ
  euclidean-division-Euclidean-Domainᵉ xᵉ yᵉ pᵉ =
    pr1ᵉ (pr2ᵉ is-euclidean-domain-Euclidean-Domainᵉ xᵉ yᵉ pᵉ)

  quotient-euclidean-division-Euclidean-Domainᵉ :
    ( xᵉ yᵉ : type-Euclidean-Domainᵉ) →
    ( is-nonzero-Euclidean-Domainᵉ yᵉ) →
    type-Euclidean-Domainᵉ
  quotient-euclidean-division-Euclidean-Domainᵉ xᵉ yᵉ pᵉ =
    pr1ᵉ (euclidean-division-Euclidean-Domainᵉ xᵉ yᵉ pᵉ)

  remainder-euclidean-division-Euclidean-Domainᵉ :
    ( xᵉ yᵉ : type-Euclidean-Domainᵉ) →
    ( is-nonzero-Euclidean-Domainᵉ yᵉ) →
    type-Euclidean-Domainᵉ
  remainder-euclidean-division-Euclidean-Domainᵉ xᵉ yᵉ pᵉ =
    pr2ᵉ (euclidean-division-Euclidean-Domainᵉ xᵉ yᵉ pᵉ)

  equation-euclidean-division-Euclidean-Domainᵉ :
    ( xᵉ yᵉ : type-Euclidean-Domainᵉ) →
    ( pᵉ : is-nonzero-Euclidean-Domainᵉ yᵉ) →
    ( Idᵉ
      ( xᵉ)
      ( add-Euclidean-Domainᵉ
        ( mul-Euclidean-Domainᵉ
          ( quotient-euclidean-division-Euclidean-Domainᵉ xᵉ yᵉ pᵉ)
          ( yᵉ))
        ( remainder-euclidean-division-Euclidean-Domainᵉ xᵉ yᵉ pᵉ)))
  equation-euclidean-division-Euclidean-Domainᵉ xᵉ yᵉ pᵉ =
    pr1ᵉ (pr2ᵉ (pr2ᵉ is-euclidean-domain-Euclidean-Domainᵉ xᵉ yᵉ pᵉ))

  remainder-condition-euclidean-division-Euclidean-Domainᵉ :
    ( xᵉ yᵉ : type-Euclidean-Domainᵉ) →
    ( pᵉ : is-nonzero-Integral-Domainᵉ integral-domain-Euclidean-Domainᵉ yᵉ) →
    ( is-zero-Euclidean-Domainᵉ
      ( remainder-euclidean-division-Euclidean-Domainᵉ xᵉ yᵉ pᵉ)) +ᵉ
    ( euclidean-valuation-Euclidean-Domainᵉ
      ( remainder-euclidean-division-Euclidean-Domainᵉ xᵉ yᵉ pᵉ) <-ℕᵉ
    ( euclidean-valuation-Euclidean-Domainᵉ yᵉ))
  remainder-condition-euclidean-division-Euclidean-Domainᵉ xᵉ yᵉ pᵉ =
    pr2ᵉ (pr2ᵉ (pr2ᵉ is-euclidean-domain-Euclidean-Domainᵉ xᵉ yᵉ pᵉ))
```