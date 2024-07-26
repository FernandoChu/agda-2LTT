# Finite groups

```agda
module finite-group-theory.finite-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.finite-monoidsᵉ
open import finite-group-theory.finite-semigroupsᵉ

open import foundation.binary-embeddingsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.set-truncationsᵉ
open import foundation.setsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commuting-elements-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ

open import structured-types.pointed-typesᵉ

open import univalent-combinatorics.cartesian-product-typesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.counting-dependent-pair-typesᵉ
open import univalent-combinatorics.decidable-dependent-function-typesᵉ
open import univalent-combinatorics.decidable-dependent-pair-typesᵉ
open import univalent-combinatorics.decidable-propositionsᵉ
open import univalent-combinatorics.dependent-function-typesᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.function-typesᵉ
open import univalent-combinatorics.pi-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Anᵉ {{#conceptᵉ "(abstractᵉ) finiteᵉ group"ᵉ Agda=Group-𝔽ᵉ}} isᵉ aᵉ finiteᵉ groupᵉ in theᵉ
usualᵉ algebraicᵉ sense,ᵉ i.e.,ᵉ itᵉ consistsᵉ ofᵉ aᵉ
[finiteᵉ type](univalent-combinatorics.finite-types.mdᵉ)
[equipped](foundation.structure.mdᵉ) with aᵉ unitᵉ elementᵉ `e`,ᵉ aᵉ binaryᵉ operationᵉ
`x,ᵉ yᵉ ↦ᵉ xy`,ᵉ andᵉ anᵉ inverseᵉ operationᵉ `xᵉ ↦ᵉ x⁻¹`ᵉ satisfyingᵉ theᵉ
[group](group-theory.groups.mdᵉ) lawsᵉ

```text
  (xy)zᵉ = x(yzᵉ)      (associativityᵉ)
     exᵉ = xᵉ          (leftᵉ unitᵉ lawᵉ)
     xeᵉ = xᵉ          (rightᵉ unitᵉ lawᵉ)
   x⁻¹xᵉ = eᵉ          (leftᵉ inverseᵉ lawᵉ)
   xx⁻¹ᵉ = eᵉ          (rightᵉ inverseᵉ lawᵉ)
```

## Definitions

### The condition that a finite semigroup is a finite group

```agda
is-group-𝔽ᵉ :
  {lᵉ : Level} (Gᵉ : Semigroup-𝔽ᵉ lᵉ) → UUᵉ lᵉ
is-group-𝔽ᵉ Gᵉ = is-group-Semigroupᵉ (semigroup-Semigroup-𝔽ᵉ Gᵉ)
```

### The type of finite groups

```agda
Group-𝔽ᵉ :
  (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Group-𝔽ᵉ lᵉ = Σᵉ (Semigroup-𝔽ᵉ lᵉ) (is-group-𝔽ᵉ)

module _
  {lᵉ : Level} (Gᵉ : Group-𝔽ᵉ lᵉ)
  where

  finite-semigroup-Group-𝔽ᵉ : Semigroup-𝔽ᵉ lᵉ
  finite-semigroup-Group-𝔽ᵉ = pr1ᵉ Gᵉ

  semigroup-Group-𝔽ᵉ : Semigroupᵉ lᵉ
  semigroup-Group-𝔽ᵉ =
    semigroup-Semigroup-𝔽ᵉ finite-semigroup-Group-𝔽ᵉ

  is-group-Group-𝔽ᵉ : is-group-Semigroupᵉ semigroup-Group-𝔽ᵉ
  is-group-Group-𝔽ᵉ = pr2ᵉ Gᵉ

  group-Group-𝔽ᵉ : Groupᵉ lᵉ
  pr1ᵉ group-Group-𝔽ᵉ = semigroup-Group-𝔽ᵉ
  pr2ᵉ group-Group-𝔽ᵉ = is-group-Group-𝔽ᵉ

  finite-type-Group-𝔽ᵉ : 𝔽ᵉ lᵉ
  finite-type-Group-𝔽ᵉ =
    finite-type-Semigroup-𝔽ᵉ finite-semigroup-Group-𝔽ᵉ

  type-Group-𝔽ᵉ : UUᵉ lᵉ
  type-Group-𝔽ᵉ = type-Groupᵉ group-Group-𝔽ᵉ

  is-finite-type-Group-𝔽ᵉ : is-finiteᵉ type-Group-𝔽ᵉ
  is-finite-type-Group-𝔽ᵉ = is-finite-type-𝔽ᵉ finite-type-Group-𝔽ᵉ

  has-decidable-equality-Group-𝔽ᵉ : has-decidable-equalityᵉ type-Group-𝔽ᵉ
  has-decidable-equality-Group-𝔽ᵉ =
    has-decidable-equality-is-finiteᵉ is-finite-type-Group-𝔽ᵉ

  is-set-type-Group-𝔽ᵉ : is-setᵉ type-Group-𝔽ᵉ
  is-set-type-Group-𝔽ᵉ = is-set-type-Groupᵉ group-Group-𝔽ᵉ

  set-Group-𝔽ᵉ : Setᵉ lᵉ
  set-Group-𝔽ᵉ = set-Groupᵉ group-Group-𝔽ᵉ

  has-associative-mul-Group-𝔽ᵉ : has-associative-mulᵉ type-Group-𝔽ᵉ
  has-associative-mul-Group-𝔽ᵉ =
    has-associative-mul-Groupᵉ group-Group-𝔽ᵉ

  mul-Group-𝔽ᵉ : (xᵉ yᵉ : type-Group-𝔽ᵉ) → type-Group-𝔽ᵉ
  mul-Group-𝔽ᵉ = mul-Groupᵉ group-Group-𝔽ᵉ

  ap-mul-Group-𝔽ᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Group-𝔽ᵉ} → (xᵉ ＝ᵉ x'ᵉ) → (yᵉ ＝ᵉ y'ᵉ) →
    mul-Group-𝔽ᵉ xᵉ yᵉ ＝ᵉ mul-Group-𝔽ᵉ x'ᵉ y'ᵉ
  ap-mul-Group-𝔽ᵉ = ap-mul-Groupᵉ group-Group-𝔽ᵉ

  mul-Group-𝔽'ᵉ : (xᵉ yᵉ : type-Group-𝔽ᵉ) → type-Group-𝔽ᵉ
  mul-Group-𝔽'ᵉ = mul-Group'ᵉ group-Group-𝔽ᵉ

  associative-mul-Group-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Group-𝔽ᵉ) →
    ( mul-Group-𝔽ᵉ (mul-Group-𝔽ᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( mul-Group-𝔽ᵉ xᵉ (mul-Group-𝔽ᵉ yᵉ zᵉ))
  associative-mul-Group-𝔽ᵉ = associative-mul-Groupᵉ group-Group-𝔽ᵉ

  is-unital-Group-𝔽ᵉ : is-unital-Semigroupᵉ semigroup-Group-𝔽ᵉ
  is-unital-Group-𝔽ᵉ = is-unital-Groupᵉ group-Group-𝔽ᵉ

  monoid-Group-𝔽ᵉ : Monoidᵉ lᵉ
  monoid-Group-𝔽ᵉ = monoid-Groupᵉ group-Group-𝔽ᵉ

  unit-Group-𝔽ᵉ : type-Group-𝔽ᵉ
  unit-Group-𝔽ᵉ = unit-Groupᵉ group-Group-𝔽ᵉ

  is-unit-Group-𝔽ᵉ : type-Group-𝔽ᵉ → UUᵉ lᵉ
  is-unit-Group-𝔽ᵉ = is-unit-Groupᵉ group-Group-𝔽ᵉ

  is-decidable-is-unit-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) → is-decidableᵉ (is-unit-Group-𝔽ᵉ xᵉ)
  is-decidable-is-unit-Group-𝔽ᵉ xᵉ =
    has-decidable-equality-Group-𝔽ᵉ xᵉ unit-Group-𝔽ᵉ

  is-prop-is-unit-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) → is-propᵉ (is-unit-Group-𝔽ᵉ xᵉ)
  is-prop-is-unit-Group-𝔽ᵉ = is-prop-is-unit-Groupᵉ group-Group-𝔽ᵉ

  is-decidable-prop-is-unit-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) → is-decidable-propᵉ (is-unit-Group-𝔽ᵉ xᵉ)
  pr1ᵉ (is-decidable-prop-is-unit-Group-𝔽ᵉ xᵉ) =
    is-prop-is-unit-Group-𝔽ᵉ xᵉ
  pr2ᵉ (is-decidable-prop-is-unit-Group-𝔽ᵉ xᵉ) =
    is-decidable-is-unit-Group-𝔽ᵉ xᵉ

  is-unit-prop-Group-𝔽ᵉ : type-Group-𝔽ᵉ → Propᵉ lᵉ
  is-unit-prop-Group-𝔽ᵉ = is-unit-prop-Groupᵉ group-Group-𝔽ᵉ

  is-unit-finite-group-Decidable-Propᵉ : type-Group-𝔽ᵉ → Decidable-Propᵉ lᵉ
  pr1ᵉ (is-unit-finite-group-Decidable-Propᵉ xᵉ) =
    is-unit-Group-𝔽ᵉ xᵉ
  pr2ᵉ (is-unit-finite-group-Decidable-Propᵉ xᵉ) =
    is-decidable-prop-is-unit-Group-𝔽ᵉ xᵉ

  left-unit-law-mul-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) → mul-Group-𝔽ᵉ unit-Group-𝔽ᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Group-𝔽ᵉ =
    left-unit-law-mul-Groupᵉ group-Group-𝔽ᵉ

  right-unit-law-mul-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) → mul-Group-𝔽ᵉ xᵉ unit-Group-𝔽ᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Group-𝔽ᵉ =
    right-unit-law-mul-Groupᵉ group-Group-𝔽ᵉ

  pointed-type-Group-𝔽ᵉ : Pointed-Typeᵉ lᵉ
  pointed-type-Group-𝔽ᵉ = pointed-type-Groupᵉ group-Group-𝔽ᵉ

  has-inverses-Group-𝔽ᵉ :
    is-group-is-unital-Semigroupᵉ semigroup-Group-𝔽ᵉ is-unital-Group-𝔽ᵉ
  has-inverses-Group-𝔽ᵉ = has-inverses-Groupᵉ group-Group-𝔽ᵉ

  inv-Group-𝔽ᵉ : type-Group-𝔽ᵉ → type-Group-𝔽ᵉ
  inv-Group-𝔽ᵉ = inv-Groupᵉ group-Group-𝔽ᵉ

  left-inverse-law-mul-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) →
    mul-Group-𝔽ᵉ (inv-Group-𝔽ᵉ xᵉ) xᵉ ＝ᵉ unit-Group-𝔽ᵉ
  left-inverse-law-mul-Group-𝔽ᵉ =
    left-inverse-law-mul-Groupᵉ group-Group-𝔽ᵉ

  right-inverse-law-mul-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) →
    mul-Group-𝔽ᵉ xᵉ (inv-Group-𝔽ᵉ xᵉ) ＝ᵉ unit-Group-𝔽ᵉ
  right-inverse-law-mul-Group-𝔽ᵉ =
    right-inverse-law-mul-Groupᵉ group-Group-𝔽ᵉ

  inv-unit-Group-𝔽ᵉ :
    inv-Group-𝔽ᵉ unit-Group-𝔽ᵉ ＝ᵉ unit-Group-𝔽ᵉ
  inv-unit-Group-𝔽ᵉ = inv-unit-Groupᵉ group-Group-𝔽ᵉ

  is-section-left-div-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) →
    ( mul-Group-𝔽ᵉ xᵉ ∘ᵉ mul-Group-𝔽ᵉ (inv-Group-𝔽ᵉ xᵉ)) ~ᵉ idᵉ
  is-section-left-div-Group-𝔽ᵉ = is-section-left-div-Groupᵉ group-Group-𝔽ᵉ

  is-retraction-left-div-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) →
    ( mul-Group-𝔽ᵉ (inv-Group-𝔽ᵉ xᵉ) ∘ᵉ mul-Group-𝔽ᵉ xᵉ) ~ᵉ idᵉ
  is-retraction-left-div-Group-𝔽ᵉ = is-retraction-left-div-Groupᵉ group-Group-𝔽ᵉ

  is-equiv-mul-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) → is-equivᵉ (mul-Group-𝔽ᵉ xᵉ)
  is-equiv-mul-Group-𝔽ᵉ = is-equiv-mul-Groupᵉ group-Group-𝔽ᵉ

  equiv-mul-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) → type-Group-𝔽ᵉ ≃ᵉ type-Group-𝔽ᵉ
  equiv-mul-Group-𝔽ᵉ = equiv-mul-Groupᵉ group-Group-𝔽ᵉ

  is-section-right-div-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) →
    (mul-Group-𝔽'ᵉ xᵉ ∘ᵉ mul-Group-𝔽'ᵉ (inv-Group-𝔽ᵉ xᵉ)) ~ᵉ idᵉ
  is-section-right-div-Group-𝔽ᵉ = is-section-right-div-Groupᵉ group-Group-𝔽ᵉ

  is-retraction-right-div-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) →
    (mul-Group-𝔽'ᵉ (inv-Group-𝔽ᵉ xᵉ) ∘ᵉ mul-Group-𝔽'ᵉ xᵉ) ~ᵉ idᵉ
  is-retraction-right-div-Group-𝔽ᵉ = is-retraction-right-div-Groupᵉ group-Group-𝔽ᵉ

  is-equiv-mul-Group-𝔽'ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) → is-equivᵉ (mul-Group-𝔽'ᵉ xᵉ)
  is-equiv-mul-Group-𝔽'ᵉ = is-equiv-mul-Group'ᵉ group-Group-𝔽ᵉ

  equiv-mul-Group-𝔽'ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) → type-Group-𝔽ᵉ ≃ᵉ type-Group-𝔽ᵉ
  equiv-mul-Group-𝔽'ᵉ = equiv-mul-Group'ᵉ group-Group-𝔽ᵉ

  is-binary-equiv-mul-Group-𝔽ᵉ : is-binary-equivᵉ mul-Group-𝔽ᵉ
  is-binary-equiv-mul-Group-𝔽ᵉ =
    is-binary-equiv-mul-Groupᵉ group-Group-𝔽ᵉ

  is-binary-emb-mul-Group-𝔽ᵉ : is-binary-embᵉ mul-Group-𝔽ᵉ
  is-binary-emb-mul-Group-𝔽ᵉ =
    is-binary-emb-mul-Groupᵉ group-Group-𝔽ᵉ

  is-emb-mul-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) → is-embᵉ (mul-Group-𝔽ᵉ xᵉ)
  is-emb-mul-Group-𝔽ᵉ = is-emb-mul-Groupᵉ group-Group-𝔽ᵉ

  is-emb-mul-Group-𝔽'ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) → is-embᵉ (mul-Group-𝔽'ᵉ xᵉ)
  is-emb-mul-Group-𝔽'ᵉ = is-emb-mul-Group'ᵉ group-Group-𝔽ᵉ

  is-injective-mul-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) → is-injectiveᵉ (mul-Group-𝔽ᵉ xᵉ)
  is-injective-mul-Group-𝔽ᵉ =
    is-injective-mul-Groupᵉ group-Group-𝔽ᵉ

  is-injective-mul-Group-𝔽'ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) → is-injectiveᵉ (mul-Group-𝔽'ᵉ xᵉ)
  is-injective-mul-Group-𝔽'ᵉ =
    is-injective-mul-Group'ᵉ group-Group-𝔽ᵉ

  transpose-eq-mul-Group-𝔽ᵉ :
    {xᵉ yᵉ zᵉ : type-Group-𝔽ᵉ} →
    (mul-Group-𝔽ᵉ xᵉ yᵉ ＝ᵉ zᵉ) → (xᵉ ＝ᵉ mul-Group-𝔽ᵉ zᵉ (inv-Group-𝔽ᵉ yᵉ))
  transpose-eq-mul-Group-𝔽ᵉ =
    transpose-eq-mul-Groupᵉ group-Group-𝔽ᵉ

  transpose-eq-mul-Group-𝔽'ᵉ :
    {xᵉ yᵉ zᵉ : type-Group-𝔽ᵉ} →
    (mul-Group-𝔽ᵉ xᵉ yᵉ ＝ᵉ zᵉ) → (yᵉ ＝ᵉ mul-Group-𝔽ᵉ (inv-Group-𝔽ᵉ xᵉ) zᵉ)
  transpose-eq-mul-Group-𝔽'ᵉ =
    transpose-eq-mul-Group'ᵉ group-Group-𝔽ᵉ

  distributive-inv-mul-Group-𝔽ᵉ :
    {xᵉ yᵉ : type-Group-𝔽ᵉ} →
    ( inv-Group-𝔽ᵉ (mul-Group-𝔽ᵉ xᵉ yᵉ)) ＝ᵉ
    ( mul-Group-𝔽ᵉ (inv-Group-𝔽ᵉ yᵉ) (inv-Group-𝔽ᵉ xᵉ))
  distributive-inv-mul-Group-𝔽ᵉ =
    distributive-inv-mul-Groupᵉ group-Group-𝔽ᵉ

  inv-inv-Group-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ) → inv-Group-𝔽ᵉ (inv-Group-𝔽ᵉ xᵉ) ＝ᵉ xᵉ
  inv-inv-Group-𝔽ᵉ = inv-inv-Groupᵉ group-Group-𝔽ᵉ

finite-group-is-finite-Groupᵉ :
  {lᵉ : Level} → (Gᵉ : Groupᵉ lᵉ) → is-finiteᵉ (type-Groupᵉ Gᵉ) → Group-𝔽ᵉ lᵉ
pr1ᵉ (finite-group-is-finite-Groupᵉ Gᵉ fᵉ) =
  finite-semigroup-is-finite-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) fᵉ
pr2ᵉ (finite-group-is-finite-Groupᵉ Gᵉ fᵉ) = is-group-Groupᵉ Gᵉ

module _
  {lᵉ : Level} (Gᵉ : Group-𝔽ᵉ lᵉ)
  where

  commute-Group-𝔽ᵉ : type-Group-𝔽ᵉ Gᵉ → type-Group-𝔽ᵉ Gᵉ → UUᵉ lᵉ
  commute-Group-𝔽ᵉ = commute-Groupᵉ (group-Group-𝔽ᵉ Gᵉ)

  finite-monoid-Group-𝔽ᵉ : Monoid-𝔽ᵉ lᵉ
  pr1ᵉ finite-monoid-Group-𝔽ᵉ = finite-semigroup-Group-𝔽ᵉ Gᵉ
  pr2ᵉ finite-monoid-Group-𝔽ᵉ = is-unital-Group-𝔽ᵉ Gᵉ
```

### Groups of fixed finite order

```agda
Group-of-Orderᵉ : (lᵉ : Level) (nᵉ : ℕᵉ) → UUᵉ (lsuc lᵉ)
Group-of-Orderᵉ lᵉ nᵉ = Σᵉ (Groupᵉ lᵉ) (λ Gᵉ → mere-equivᵉ (Finᵉ nᵉ) (type-Groupᵉ Gᵉ))
```

## Properties

### The type `is-group-Semigroup G` is finite for any semigroup of fixed finite order

```agda
is-finite-is-group-Semigroupᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Gᵉ : Semigroup-of-Orderᵉ lᵉ nᵉ) →
  is-finiteᵉ {lᵉ} (is-group-Semigroupᵉ (pr1ᵉ Gᵉ))
is-finite-is-group-Semigroupᵉ {lᵉ} nᵉ Gᵉ =
  apply-universal-property-trunc-Propᵉ
    ( pr2ᵉ Gᵉ)
    ( is-finite-Propᵉ _)
    ( λ eᵉ →
      is-finite-is-decidable-Propᵉ
        ( is-group-prop-Semigroupᵉ (pr1ᵉ Gᵉ))
        ( is-decidable-Σ-countᵉ
          ( count-Σᵉ
            ( pairᵉ nᵉ eᵉ)
            ( λ uᵉ →
              count-productᵉ
                ( count-Πᵉ
                  ( pairᵉ nᵉ eᵉ)
                  ( λ xᵉ →
                    count-eqᵉ
                      ( has-decidable-equality-countᵉ (pairᵉ nᵉ eᵉ))
                      ( mul-Semigroupᵉ (pr1ᵉ Gᵉ) uᵉ xᵉ)
                      ( xᵉ)))
                ( count-Πᵉ
                  ( pairᵉ nᵉ eᵉ)
                  ( λ xᵉ →
                    count-eqᵉ
                      ( has-decidable-equality-countᵉ (pairᵉ nᵉ eᵉ))
                      ( mul-Semigroupᵉ (pr1ᵉ Gᵉ) xᵉ uᵉ)
                      ( xᵉ)))))
          ( λ uᵉ →
            is-decidable-Σ-countᵉ
              ( count-function-typeᵉ (pairᵉ nᵉ eᵉ) (pairᵉ nᵉ eᵉ))
              ( λ iᵉ →
                is-decidable-productᵉ
                  ( is-decidable-Π-countᵉ
                    ( pairᵉ nᵉ eᵉ)
                    ( λ xᵉ →
                      has-decidable-equality-countᵉ
                        ( pairᵉ nᵉ eᵉ)
                        ( mul-Semigroupᵉ (pr1ᵉ Gᵉ) (iᵉ xᵉ) xᵉ)
                        ( pr1ᵉ uᵉ)))
                  ( is-decidable-Π-countᵉ
                    ( pairᵉ nᵉ eᵉ)
                    ( λ xᵉ →
                      has-decidable-equality-countᵉ
                        ( pairᵉ nᵉ eᵉ)
                        ( mul-Semigroupᵉ (pr1ᵉ Gᵉ) xᵉ (iᵉ xᵉ))
                        ( pr1ᵉ uᵉ)))))))

is-π-finite-Group-of-Orderᵉ :
  {lᵉ : Level} (kᵉ nᵉ : ℕᵉ) → is-π-finiteᵉ kᵉ (Group-of-Orderᵉ lᵉ nᵉ)
is-π-finite-Group-of-Orderᵉ {lᵉ} kᵉ nᵉ =
  is-π-finite-equivᵉ kᵉ eᵉ
    ( is-π-finite-Σᵉ kᵉ
      ( is-π-finite-Semigroup-of-Orderᵉ (succ-ℕᵉ kᵉ) nᵉ)
      ( λ Xᵉ →
        is-π-finite-is-finiteᵉ kᵉ
          ( is-finite-is-group-Semigroupᵉ nᵉ Xᵉ)))
  where
  eᵉ :
    Group-of-Orderᵉ lᵉ nᵉ ≃ᵉ
    Σᵉ (Semigroup-of-Orderᵉ lᵉ nᵉ) (λ Xᵉ → is-group-Semigroupᵉ (pr1ᵉ Xᵉ))
  eᵉ = equiv-right-swap-Σᵉ

number-of-groups-of-orderᵉ : ℕᵉ → ℕᵉ
number-of-groups-of-orderᵉ nᵉ =
  number-of-connected-componentsᵉ
    ( is-π-finite-Group-of-Orderᵉ {lzeroᵉ} zero-ℕᵉ nᵉ)

mere-equiv-number-of-groups-of-orderᵉ :
  (nᵉ : ℕᵉ) →
  mere-equivᵉ
    ( Finᵉ (number-of-groups-of-orderᵉ nᵉ))
    ( type-trunc-Setᵉ (Group-of-Orderᵉ lzero nᵉ))
mere-equiv-number-of-groups-of-orderᵉ nᵉ =
  mere-equiv-number-of-connected-componentsᵉ
    ( is-π-finite-Group-of-Orderᵉ {lzeroᵉ} zero-ℕᵉ nᵉ)
```

### There is a finite number of ways to equip a finite type with the structure of a group

```agda
module _
  {lᵉ : Level}
  (Xᵉ : 𝔽ᵉ lᵉ)
  where

  structure-group-𝔽ᵉ : UUᵉ lᵉ
  structure-group-𝔽ᵉ =
    Σᵉ (structure-semigroup-𝔽ᵉ Xᵉ) (λ sᵉ → is-group-𝔽ᵉ (Xᵉ ,ᵉ sᵉ))

  finite-group-structure-group-𝔽ᵉ :
    structure-group-𝔽ᵉ → Group-𝔽ᵉ lᵉ
  pr1ᵉ (finite-group-structure-group-𝔽ᵉ (sᵉ ,ᵉ gᵉ)) = (Xᵉ ,ᵉ sᵉ)
  pr2ᵉ (finite-group-structure-group-𝔽ᵉ (sᵉ ,ᵉ gᵉ)) = gᵉ

  is-finite-structure-group-𝔽ᵉ :
    is-finiteᵉ (structure-group-𝔽ᵉ)
  is-finite-structure-group-𝔽ᵉ =
    is-finite-Σᵉ
      ( is-finite-structure-semigroup-𝔽ᵉ Xᵉ)
      ( λ sᵉ →
        is-finite-Σᵉ
          ( is-finite-is-unital-Semigroup-𝔽ᵉ (Xᵉ ,ᵉ sᵉ))
          ( λ uᵉ →
            is-finite-Σᵉ
              ( is-finite-Πᵉ
                ( is-finite-type-𝔽ᵉ Xᵉ)
                ( λ _ → is-finite-type-𝔽ᵉ Xᵉ))
              ( λ iᵉ →
                is-finite-productᵉ
                  ( is-finite-Πᵉ
                    ( is-finite-type-𝔽ᵉ Xᵉ)
                    ( λ xᵉ → is-finite-eq-𝔽ᵉ Xᵉ))
                  ( is-finite-Πᵉ
                    ( is-finite-type-𝔽ᵉ Xᵉ)
                    ( λ xᵉ → is-finite-eq-𝔽ᵉ Xᵉ)))))
```