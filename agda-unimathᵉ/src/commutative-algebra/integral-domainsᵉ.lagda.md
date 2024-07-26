# Integral domains

```agda
module commutative-algebra.integral-domainsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.commutative-semiringsᵉ
open import commutative-algebra.trivial-commutative-ringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-embeddingsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.cartesian-product-typesᵉ
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

Anᵉ **integralᵉ domain**ᵉ isᵉ aᵉ nonzeroᵉ commutativeᵉ ringᵉ `R`ᵉ suchᵉ thatᵉ theᵉ productᵉ
ofᵉ anyᵉ twoᵉ nonzeroᵉ elementsᵉ in `R`ᵉ isᵉ nonzero.ᵉ Equivalently,ᵉ aᵉ commutativeᵉ ringᵉ
`R`ᵉ isᵉ anᵉ integralᵉ domainᵉ ifᵉ andᵉ onlyᵉ ifᵉ multiplicationᵉ byᵉ anyᵉ nonzeroᵉ elementᵉ
`a`ᵉ satisfiesᵉ theᵉ cancellationᵉ propertyᵉ: `axᵉ = ayᵉ ⇒ᵉ xᵉ = y`.ᵉ

## Definition

### The cancellation property for a commutative ring

```agda
cancellation-property-Commutative-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Commutative-Ringᵉ lᵉ) → UUᵉ lᵉ
cancellation-property-Commutative-Ringᵉ Rᵉ =
  (xᵉ : type-Commutative-Ringᵉ Rᵉ) → is-nonzero-Commutative-Ringᵉ Rᵉ xᵉ →
  is-injectiveᵉ (mul-Commutative-Ringᵉ Rᵉ xᵉ)
```

### Integral domains

```agda
Integral-Domainᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Integral-Domainᵉ lᵉ =
  Σᵉ ( Commutative-Ringᵉ lᵉ)
    ( λ Rᵉ →
      cancellation-property-Commutative-Ringᵉ Rᵉ ×ᵉ
      is-nontrivial-Commutative-Ringᵉ Rᵉ)

module _
  {lᵉ : Level} (Rᵉ : Integral-Domainᵉ lᵉ)
  where

  commutative-ring-Integral-Domainᵉ : Commutative-Ringᵉ lᵉ
  commutative-ring-Integral-Domainᵉ = pr1ᵉ Rᵉ

  has-cancellation-property-Integral-Domainᵉ :
    cancellation-property-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ
  has-cancellation-property-Integral-Domainᵉ = pr1ᵉ (pr2ᵉ Rᵉ)

  is-nontrivial-Integral-Domainᵉ :
    is-nontrivial-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ
  is-nontrivial-Integral-Domainᵉ = pr2ᵉ (pr2ᵉ Rᵉ)

  ab-Integral-Domainᵉ : Abᵉ lᵉ
  ab-Integral-Domainᵉ = ab-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  ring-Integral-Domainᵉ : Ringᵉ lᵉ
  ring-Integral-Domainᵉ = ring-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  set-Integral-Domainᵉ : Setᵉ lᵉ
  set-Integral-Domainᵉ = set-Ringᵉ ring-Integral-Domainᵉ

  type-Integral-Domainᵉ : UUᵉ lᵉ
  type-Integral-Domainᵉ = type-Ringᵉ ring-Integral-Domainᵉ

  is-set-type-Integral-Domainᵉ : is-setᵉ type-Integral-Domainᵉ
  is-set-type-Integral-Domainᵉ = is-set-type-Ringᵉ ring-Integral-Domainᵉ
```

### Addition in an integral domain

```agda
  has-associative-add-Integral-Domainᵉ :
    has-associative-mul-Setᵉ set-Integral-Domainᵉ
  has-associative-add-Integral-Domainᵉ =
    has-associative-add-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  add-Integral-Domainᵉ :
    type-Integral-Domainᵉ → type-Integral-Domainᵉ → type-Integral-Domainᵉ
  add-Integral-Domainᵉ = add-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  add-Integral-Domain'ᵉ :
    type-Integral-Domainᵉ → type-Integral-Domainᵉ → type-Integral-Domainᵉ
  add-Integral-Domain'ᵉ = add-Commutative-Ring'ᵉ commutative-ring-Integral-Domainᵉ

  ap-add-Integral-Domainᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Integral-Domainᵉ} →
    (xᵉ ＝ᵉ x'ᵉ) → (yᵉ ＝ᵉ y'ᵉ) →
    add-Integral-Domainᵉ xᵉ yᵉ ＝ᵉ add-Integral-Domainᵉ x'ᵉ y'ᵉ
  ap-add-Integral-Domainᵉ =
    ap-add-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  associative-add-Integral-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Integral-Domainᵉ) →
    ( add-Integral-Domainᵉ (add-Integral-Domainᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Integral-Domainᵉ xᵉ (add-Integral-Domainᵉ yᵉ zᵉ))
  associative-add-Integral-Domainᵉ =
    associative-add-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  additive-semigroup-Integral-Domainᵉ : Semigroupᵉ lᵉ
  additive-semigroup-Integral-Domainᵉ = semigroup-Abᵉ ab-Integral-Domainᵉ

  is-group-additive-semigroup-Integral-Domainᵉ :
    is-group-Semigroupᵉ additive-semigroup-Integral-Domainᵉ
  is-group-additive-semigroup-Integral-Domainᵉ =
    is-group-Abᵉ ab-Integral-Domainᵉ

  commutative-add-Integral-Domainᵉ :
    (xᵉ yᵉ : type-Integral-Domainᵉ) →
    Idᵉ (add-Integral-Domainᵉ xᵉ yᵉ) (add-Integral-Domainᵉ yᵉ xᵉ)
  commutative-add-Integral-Domainᵉ = commutative-add-Abᵉ ab-Integral-Domainᵉ

  interchange-add-add-Integral-Domainᵉ :
    (xᵉ yᵉ x'ᵉ y'ᵉ : type-Integral-Domainᵉ) →
    ( add-Integral-Domainᵉ
      ( add-Integral-Domainᵉ xᵉ yᵉ)
      ( add-Integral-Domainᵉ x'ᵉ y'ᵉ)) ＝ᵉ
    ( add-Integral-Domainᵉ
      ( add-Integral-Domainᵉ xᵉ x'ᵉ)
      ( add-Integral-Domainᵉ yᵉ y'ᵉ))
  interchange-add-add-Integral-Domainᵉ =
    interchange-add-add-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  right-swap-add-Integral-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Integral-Domainᵉ) →
    ( add-Integral-Domainᵉ (add-Integral-Domainᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Integral-Domainᵉ (add-Integral-Domainᵉ xᵉ zᵉ) yᵉ)
  right-swap-add-Integral-Domainᵉ =
    right-swap-add-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  left-swap-add-Integral-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Integral-Domainᵉ) →
    ( add-Integral-Domainᵉ xᵉ (add-Integral-Domainᵉ yᵉ zᵉ)) ＝ᵉ
    ( add-Integral-Domainᵉ yᵉ (add-Integral-Domainᵉ xᵉ zᵉ))
  left-swap-add-Integral-Domainᵉ =
    left-swap-add-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  is-equiv-add-Integral-Domainᵉ :
    (xᵉ : type-Integral-Domainᵉ) → is-equivᵉ (add-Integral-Domainᵉ xᵉ)
  is-equiv-add-Integral-Domainᵉ = is-equiv-add-Abᵉ ab-Integral-Domainᵉ

  is-equiv-add-Integral-Domain'ᵉ :
    (xᵉ : type-Integral-Domainᵉ) → is-equivᵉ (add-Integral-Domain'ᵉ xᵉ)
  is-equiv-add-Integral-Domain'ᵉ = is-equiv-add-Ab'ᵉ ab-Integral-Domainᵉ

  is-binary-equiv-add-Integral-Domainᵉ : is-binary-equivᵉ add-Integral-Domainᵉ
  pr1ᵉ is-binary-equiv-add-Integral-Domainᵉ = is-equiv-add-Integral-Domain'ᵉ
  pr2ᵉ is-binary-equiv-add-Integral-Domainᵉ = is-equiv-add-Integral-Domainᵉ

  is-binary-emb-add-Integral-Domainᵉ : is-binary-embᵉ add-Integral-Domainᵉ
  is-binary-emb-add-Integral-Domainᵉ = is-binary-emb-add-Abᵉ ab-Integral-Domainᵉ

  is-emb-add-Integral-Domainᵉ :
    (xᵉ : type-Integral-Domainᵉ) → is-embᵉ (add-Integral-Domainᵉ xᵉ)
  is-emb-add-Integral-Domainᵉ = is-emb-add-Abᵉ ab-Integral-Domainᵉ

  is-emb-add-Integral-Domain'ᵉ :
    (xᵉ : type-Integral-Domainᵉ) → is-embᵉ (add-Integral-Domain'ᵉ xᵉ)
  is-emb-add-Integral-Domain'ᵉ = is-emb-add-Ab'ᵉ ab-Integral-Domainᵉ

  is-injective-add-Integral-Domainᵉ :
    (xᵉ : type-Integral-Domainᵉ) → is-injectiveᵉ (add-Integral-Domainᵉ xᵉ)
  is-injective-add-Integral-Domainᵉ = is-injective-add-Abᵉ ab-Integral-Domainᵉ

  is-injective-add-Integral-Domain'ᵉ :
    (xᵉ : type-Integral-Domainᵉ) → is-injectiveᵉ (add-Integral-Domain'ᵉ xᵉ)
  is-injective-add-Integral-Domain'ᵉ = is-injective-add-Ab'ᵉ ab-Integral-Domainᵉ
```

### The zero element of an integral domain

```agda
  has-zero-Integral-Domainᵉ : is-unitalᵉ add-Integral-Domainᵉ
  has-zero-Integral-Domainᵉ =
    has-zero-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  zero-Integral-Domainᵉ : type-Integral-Domainᵉ
  zero-Integral-Domainᵉ =
    zero-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  is-zero-Integral-Domainᵉ : type-Integral-Domainᵉ → UUᵉ lᵉ
  is-zero-Integral-Domainᵉ =
    is-zero-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  is-nonzero-Integral-Domainᵉ : type-Integral-Domainᵉ → UUᵉ lᵉ
  is-nonzero-Integral-Domainᵉ =
    is-nonzero-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  is-zero-integral-domain-Propᵉ : type-Integral-Domainᵉ → Propᵉ lᵉ
  is-zero-integral-domain-Propᵉ xᵉ =
    Id-Propᵉ set-Integral-Domainᵉ xᵉ zero-Integral-Domainᵉ

  is-nonzero-integral-domain-Propᵉ : type-Integral-Domainᵉ → Propᵉ lᵉ
  is-nonzero-integral-domain-Propᵉ xᵉ =
    neg-Propᵉ (is-zero-integral-domain-Propᵉ xᵉ)

  left-unit-law-add-Integral-Domainᵉ :
    (xᵉ : type-Integral-Domainᵉ) →
    add-Integral-Domainᵉ zero-Integral-Domainᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Integral-Domainᵉ =
    left-unit-law-add-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  right-unit-law-add-Integral-Domainᵉ :
    (xᵉ : type-Integral-Domainᵉ) →
    add-Integral-Domainᵉ xᵉ zero-Integral-Domainᵉ ＝ᵉ xᵉ
  right-unit-law-add-Integral-Domainᵉ =
    right-unit-law-add-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ
```

### Additive inverses in an integral domain

```agda
  has-negatives-Integral-Domainᵉ :
    is-group-is-unital-Semigroupᵉ
      ( additive-semigroup-Integral-Domainᵉ)
      ( has-zero-Integral-Domainᵉ)
  has-negatives-Integral-Domainᵉ = has-negatives-Abᵉ ab-Integral-Domainᵉ

  neg-Integral-Domainᵉ : type-Integral-Domainᵉ → type-Integral-Domainᵉ
  neg-Integral-Domainᵉ = neg-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  left-inverse-law-add-Integral-Domainᵉ :
    (xᵉ : type-Integral-Domainᵉ) →
    add-Integral-Domainᵉ (neg-Integral-Domainᵉ xᵉ) xᵉ ＝ᵉ zero-Integral-Domainᵉ
  left-inverse-law-add-Integral-Domainᵉ =
    left-inverse-law-add-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  right-inverse-law-add-Integral-Domainᵉ :
    (xᵉ : type-Integral-Domainᵉ) →
    add-Integral-Domainᵉ xᵉ (neg-Integral-Domainᵉ xᵉ) ＝ᵉ zero-Integral-Domainᵉ
  right-inverse-law-add-Integral-Domainᵉ =
    right-inverse-law-add-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  neg-neg-Integral-Domainᵉ :
    (xᵉ : type-Integral-Domainᵉ) →
    neg-Integral-Domainᵉ (neg-Integral-Domainᵉ xᵉ) ＝ᵉ xᵉ
  neg-neg-Integral-Domainᵉ = neg-neg-Abᵉ ab-Integral-Domainᵉ

  distributive-neg-add-Integral-Domainᵉ :
    (xᵉ yᵉ : type-Integral-Domainᵉ) →
    neg-Integral-Domainᵉ (add-Integral-Domainᵉ xᵉ yᵉ) ＝ᵉ
    add-Integral-Domainᵉ (neg-Integral-Domainᵉ xᵉ) (neg-Integral-Domainᵉ yᵉ)
  distributive-neg-add-Integral-Domainᵉ =
    distributive-neg-add-Abᵉ ab-Integral-Domainᵉ
```

### Multiplication in an integral domain

```agda
  has-associative-mul-Integral-Domainᵉ :
    has-associative-mul-Setᵉ set-Integral-Domainᵉ
  has-associative-mul-Integral-Domainᵉ =
    has-associative-mul-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  mul-Integral-Domainᵉ :
    (xᵉ yᵉ : type-Integral-Domainᵉ) → type-Integral-Domainᵉ
  mul-Integral-Domainᵉ =
    mul-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  mul-Integral-Domain'ᵉ :
    (xᵉ yᵉ : type-Integral-Domainᵉ) → type-Integral-Domainᵉ
  mul-Integral-Domain'ᵉ =
    mul-Commutative-Ring'ᵉ commutative-ring-Integral-Domainᵉ

  ap-mul-Integral-Domainᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Integral-Domainᵉ} (pᵉ : Idᵉ xᵉ x'ᵉ) (qᵉ : Idᵉ yᵉ y'ᵉ) →
    Idᵉ (mul-Integral-Domainᵉ xᵉ yᵉ) (mul-Integral-Domainᵉ x'ᵉ y'ᵉ)
  ap-mul-Integral-Domainᵉ pᵉ qᵉ = ap-binaryᵉ mul-Integral-Domainᵉ pᵉ qᵉ

  associative-mul-Integral-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ (mul-Integral-Domainᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Integral-Domainᵉ xᵉ (mul-Integral-Domainᵉ yᵉ zᵉ)
  associative-mul-Integral-Domainᵉ =
    associative-mul-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  multiplicative-semigroup-Integral-Domainᵉ : Semigroupᵉ lᵉ
  multiplicative-semigroup-Integral-Domainᵉ =
    multiplicative-semigroup-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  left-distributive-mul-add-Integral-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Integral-Domainᵉ) →
    ( mul-Integral-Domainᵉ xᵉ (add-Integral-Domainᵉ yᵉ zᵉ)) ＝ᵉ
    ( add-Integral-Domainᵉ
      ( mul-Integral-Domainᵉ xᵉ yᵉ)
      ( mul-Integral-Domainᵉ xᵉ zᵉ))
  left-distributive-mul-add-Integral-Domainᵉ =
    left-distributive-mul-add-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  right-distributive-mul-add-Integral-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Integral-Domainᵉ) →
    ( mul-Integral-Domainᵉ (add-Integral-Domainᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( add-Integral-Domainᵉ
      ( mul-Integral-Domainᵉ xᵉ zᵉ)
      ( mul-Integral-Domainᵉ yᵉ zᵉ))
  right-distributive-mul-add-Integral-Domainᵉ =
    right-distributive-mul-add-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  commutative-mul-Integral-Domainᵉ :
    (xᵉ yᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ xᵉ yᵉ ＝ᵉ mul-Integral-Domainᵉ yᵉ xᵉ
  commutative-mul-Integral-Domainᵉ =
    commutative-mul-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ
```

### Multiplicative units in an integral domain

```agda
  is-unital-Integral-Domainᵉ : is-unitalᵉ mul-Integral-Domainᵉ
  is-unital-Integral-Domainᵉ =
    is-unital-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  multiplicative-monoid-Integral-Domainᵉ : Monoidᵉ lᵉ
  multiplicative-monoid-Integral-Domainᵉ =
    multiplicative-monoid-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  one-Integral-Domainᵉ : type-Integral-Domainᵉ
  one-Integral-Domainᵉ =
    one-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  left-unit-law-mul-Integral-Domainᵉ :
    (xᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ one-Integral-Domainᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Integral-Domainᵉ =
    left-unit-law-mul-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  right-unit-law-mul-Integral-Domainᵉ :
    (xᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ xᵉ one-Integral-Domainᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Integral-Domainᵉ =
    right-unit-law-mul-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  right-swap-mul-Integral-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ (mul-Integral-Domainᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Integral-Domainᵉ (mul-Integral-Domainᵉ xᵉ zᵉ) yᵉ
  right-swap-mul-Integral-Domainᵉ xᵉ yᵉ zᵉ =
    ( associative-mul-Integral-Domainᵉ xᵉ yᵉ zᵉ) ∙ᵉ
    ( ( apᵉ
        ( mul-Integral-Domainᵉ xᵉ)
        ( commutative-mul-Integral-Domainᵉ yᵉ zᵉ)) ∙ᵉ
      ( invᵉ (associative-mul-Integral-Domainᵉ xᵉ zᵉ yᵉ)))

  left-swap-mul-Integral-Domainᵉ :
    (xᵉ yᵉ zᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ xᵉ (mul-Integral-Domainᵉ yᵉ zᵉ) ＝ᵉ
    mul-Integral-Domainᵉ yᵉ (mul-Integral-Domainᵉ xᵉ zᵉ)
  left-swap-mul-Integral-Domainᵉ xᵉ yᵉ zᵉ =
    ( invᵉ (associative-mul-Integral-Domainᵉ xᵉ yᵉ zᵉ)) ∙ᵉ
    ( ( apᵉ
        ( mul-Integral-Domain'ᵉ zᵉ)
        ( commutative-mul-Integral-Domainᵉ xᵉ yᵉ)) ∙ᵉ
      ( associative-mul-Integral-Domainᵉ yᵉ xᵉ zᵉ))

  interchange-mul-mul-Integral-Domainᵉ :
    (xᵉ yᵉ zᵉ wᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ
      ( mul-Integral-Domainᵉ xᵉ yᵉ)
      ( mul-Integral-Domainᵉ zᵉ wᵉ) ＝ᵉ
    mul-Integral-Domainᵉ
      ( mul-Integral-Domainᵉ xᵉ zᵉ)
      ( mul-Integral-Domainᵉ yᵉ wᵉ)
  interchange-mul-mul-Integral-Domainᵉ =
    interchange-law-commutative-and-associativeᵉ
      mul-Integral-Domainᵉ
      commutative-mul-Integral-Domainᵉ
      associative-mul-Integral-Domainᵉ
```

### The zero laws for multiplication of a integral domains

```agda
  left-zero-law-mul-Integral-Domainᵉ :
    (xᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ zero-Integral-Domainᵉ xᵉ ＝ᵉ
    zero-Integral-Domainᵉ
  left-zero-law-mul-Integral-Domainᵉ =
    left-zero-law-mul-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  right-zero-law-mul-Integral-Domainᵉ :
    (xᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ xᵉ zero-Integral-Domainᵉ ＝ᵉ
    zero-Integral-Domainᵉ
  right-zero-law-mul-Integral-Domainᵉ =
    right-zero-law-mul-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ
```

### Integral domains are commutative semirings

```agda
  multiplicative-commutative-monoid-Integral-Domainᵉ : Commutative-Monoidᵉ lᵉ
  multiplicative-commutative-monoid-Integral-Domainᵉ =
    multiplicative-commutative-monoid-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  semiring-Integral-Domainᵉ : Semiringᵉ lᵉ
  semiring-Integral-Domainᵉ =
    semiring-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  commutative-semiring-Integral-Domainᵉ : Commutative-Semiringᵉ lᵉ
  commutative-semiring-Integral-Domainᵉ =
    commutative-semiring-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ
```

### Computing multiplication with minus one in an integral domain

```agda
  neg-one-Integral-Domainᵉ : type-Integral-Domainᵉ
  neg-one-Integral-Domainᵉ =
    neg-one-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  mul-neg-one-Integral-Domainᵉ :
    (xᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ neg-one-Integral-Domainᵉ xᵉ ＝ᵉ
    neg-Integral-Domainᵉ xᵉ
  mul-neg-one-Integral-Domainᵉ =
    mul-neg-one-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  mul-neg-one-Integral-Domain'ᵉ :
    (xᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ xᵉ neg-one-Integral-Domainᵉ ＝ᵉ
    neg-Integral-Domainᵉ xᵉ
  mul-neg-one-Integral-Domain'ᵉ =
    mul-neg-one-Commutative-Ring'ᵉ
      commutative-ring-Integral-Domainᵉ

  is-involution-mul-neg-one-Integral-Domainᵉ :
    is-involutionᵉ (mul-Integral-Domainᵉ neg-one-Integral-Domainᵉ)
  is-involution-mul-neg-one-Integral-Domainᵉ =
    is-involution-mul-neg-one-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  is-involution-mul-neg-one-Integral-Domain'ᵉ :
    is-involutionᵉ (mul-Integral-Domain'ᵉ neg-one-Integral-Domainᵉ)
  is-involution-mul-neg-one-Integral-Domain'ᵉ =
    is-involution-mul-neg-one-Commutative-Ring'ᵉ
      commutative-ring-Integral-Domainᵉ
```

### Left and right negative laws for multiplication

```agda
  left-negative-law-mul-Integral-Domainᵉ :
    (xᵉ yᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ (neg-Integral-Domainᵉ xᵉ) yᵉ ＝ᵉ
    neg-Integral-Domainᵉ (mul-Integral-Domainᵉ xᵉ yᵉ)
  left-negative-law-mul-Integral-Domainᵉ =
    left-negative-law-mul-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  right-negative-law-mul-Integral-Domainᵉ :
    (xᵉ yᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ xᵉ (neg-Integral-Domainᵉ yᵉ) ＝ᵉ
    neg-Integral-Domainᵉ (mul-Integral-Domainᵉ xᵉ yᵉ)
  right-negative-law-mul-Integral-Domainᵉ =
    right-negative-law-mul-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  mul-neg-Integral-Domainᵉ :
    (xᵉ yᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ (neg-Integral-Domainᵉ xᵉ) (neg-Integral-Domainᵉ yᵉ) ＝ᵉ
    mul-Integral-Domainᵉ xᵉ yᵉ
  mul-neg-Integral-Domainᵉ =
    mul-neg-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ
```

### Scalar multiplication of elements of a integral domain by natural numbers

```agda
  mul-nat-scalar-Integral-Domainᵉ :
    ℕᵉ → type-Integral-Domainᵉ → type-Integral-Domainᵉ
  mul-nat-scalar-Integral-Domainᵉ =
    mul-nat-scalar-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  ap-mul-nat-scalar-Integral-Domainᵉ :
    {mᵉ nᵉ : ℕᵉ} {xᵉ yᵉ : type-Integral-Domainᵉ} →
    (mᵉ ＝ᵉ nᵉ) → (xᵉ ＝ᵉ yᵉ) →
    mul-nat-scalar-Integral-Domainᵉ mᵉ xᵉ ＝ᵉ
    mul-nat-scalar-Integral-Domainᵉ nᵉ yᵉ
  ap-mul-nat-scalar-Integral-Domainᵉ =
    ap-mul-nat-scalar-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  left-zero-law-mul-nat-scalar-Integral-Domainᵉ :
    (xᵉ : type-Integral-Domainᵉ) →
    mul-nat-scalar-Integral-Domainᵉ 0 xᵉ ＝ᵉ zero-Integral-Domainᵉ
  left-zero-law-mul-nat-scalar-Integral-Domainᵉ =
    left-zero-law-mul-nat-scalar-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  right-zero-law-mul-nat-scalar-Integral-Domainᵉ :
    (nᵉ : ℕᵉ) →
    mul-nat-scalar-Integral-Domainᵉ nᵉ zero-Integral-Domainᵉ ＝ᵉ
    zero-Integral-Domainᵉ
  right-zero-law-mul-nat-scalar-Integral-Domainᵉ =
    right-zero-law-mul-nat-scalar-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  left-unit-law-mul-nat-scalar-Integral-Domainᵉ :
    (xᵉ : type-Integral-Domainᵉ) →
    mul-nat-scalar-Integral-Domainᵉ 1 xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-nat-scalar-Integral-Domainᵉ =
    left-unit-law-mul-nat-scalar-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  left-nat-scalar-law-mul-Integral-Domainᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ (mul-nat-scalar-Integral-Domainᵉ nᵉ xᵉ) yᵉ ＝ᵉ
    mul-nat-scalar-Integral-Domainᵉ nᵉ (mul-Integral-Domainᵉ xᵉ yᵉ)
  left-nat-scalar-law-mul-Integral-Domainᵉ =
    left-nat-scalar-law-mul-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  right-nat-scalar-law-mul-Integral-Domainᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Integral-Domainᵉ) →
    mul-Integral-Domainᵉ xᵉ (mul-nat-scalar-Integral-Domainᵉ nᵉ yᵉ) ＝ᵉ
    mul-nat-scalar-Integral-Domainᵉ nᵉ (mul-Integral-Domainᵉ xᵉ yᵉ)
  right-nat-scalar-law-mul-Integral-Domainᵉ =
    right-nat-scalar-law-mul-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  left-distributive-mul-nat-scalar-add-Integral-Domainᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Integral-Domainᵉ) →
    mul-nat-scalar-Integral-Domainᵉ nᵉ (add-Integral-Domainᵉ xᵉ yᵉ) ＝ᵉ
    add-Integral-Domainᵉ
      ( mul-nat-scalar-Integral-Domainᵉ nᵉ xᵉ)
      ( mul-nat-scalar-Integral-Domainᵉ nᵉ yᵉ)
  left-distributive-mul-nat-scalar-add-Integral-Domainᵉ =
    left-distributive-mul-nat-scalar-add-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ

  right-distributive-mul-nat-scalar-add-Integral-Domainᵉ :
    (mᵉ nᵉ : ℕᵉ) (xᵉ : type-Integral-Domainᵉ) →
    mul-nat-scalar-Integral-Domainᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    add-Integral-Domainᵉ
      ( mul-nat-scalar-Integral-Domainᵉ mᵉ xᵉ)
      ( mul-nat-scalar-Integral-Domainᵉ nᵉ xᵉ)
  right-distributive-mul-nat-scalar-add-Integral-Domainᵉ =
    right-distributive-mul-nat-scalar-add-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ
```

### Addition of a list of elements in an integral domain

```agda
  add-list-Integral-Domainᵉ :
    listᵉ type-Integral-Domainᵉ → type-Integral-Domainᵉ
  add-list-Integral-Domainᵉ =
    add-list-Commutative-Ringᵉ commutative-ring-Integral-Domainᵉ

  preserves-concat-add-list-Integral-Domainᵉ :
    (l1ᵉ l2ᵉ : listᵉ type-Integral-Domainᵉ) →
    Idᵉ
      ( add-list-Integral-Domainᵉ (concat-listᵉ l1ᵉ l2ᵉ))
      ( add-Integral-Domainᵉ
        ( add-list-Integral-Domainᵉ l1ᵉ)
        ( add-list-Integral-Domainᵉ l2ᵉ))
  preserves-concat-add-list-Integral-Domainᵉ =
    preserves-concat-add-list-Commutative-Ringᵉ
      commutative-ring-Integral-Domainᵉ
```