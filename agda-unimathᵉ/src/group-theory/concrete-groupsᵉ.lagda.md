# Concrete groups

```agda
module group-theory.concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.1-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.opposite-groupsᵉ
open import group-theory.opposite-semigroupsᵉ
open import group-theory.semigroupsᵉ

open import higher-group-theory.higher-groupsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ **concreteᵉ group**ᵉ isᵉ aᵉ [pointed](structured-types.pointed-types.mdᵉ)
[connected](foundation.0-connected-types.mdᵉ)
[1-type](foundation-core.1-types.md).ᵉ

## Definitions

### Concrete groups

```agda
Concrete-Groupᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Concrete-Groupᵉ lᵉ = Σᵉ (∞-Groupᵉ lᵉ) (λ Gᵉ → is-setᵉ (type-∞-Groupᵉ Gᵉ))

module _
  {lᵉ : Level} (Gᵉ : Concrete-Groupᵉ lᵉ)
  where

  ∞-group-Concrete-Groupᵉ : ∞-Groupᵉ lᵉ
  ∞-group-Concrete-Groupᵉ = pr1ᵉ Gᵉ

  classifying-pointed-type-Concrete-Groupᵉ : Pointed-Typeᵉ lᵉ
  classifying-pointed-type-Concrete-Groupᵉ =
    classifying-pointed-type-∞-Groupᵉ ∞-group-Concrete-Groupᵉ

  classifying-type-Concrete-Groupᵉ : UUᵉ lᵉ
  classifying-type-Concrete-Groupᵉ =
    classifying-type-∞-Groupᵉ ∞-group-Concrete-Groupᵉ

  shape-Concrete-Groupᵉ : classifying-type-Concrete-Groupᵉ
  shape-Concrete-Groupᵉ =
    shape-∞-Groupᵉ ∞-group-Concrete-Groupᵉ

  is-0-connected-classifying-type-Concrete-Groupᵉ :
    is-0-connectedᵉ classifying-type-Concrete-Groupᵉ
  is-0-connected-classifying-type-Concrete-Groupᵉ =
    is-0-connected-classifying-type-∞-Groupᵉ ∞-group-Concrete-Groupᵉ

  mere-eq-classifying-type-Concrete-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-Concrete-Groupᵉ) → mere-eqᵉ Xᵉ Yᵉ
  mere-eq-classifying-type-Concrete-Groupᵉ =
    mere-eq-classifying-type-∞-Groupᵉ ∞-group-Concrete-Groupᵉ

  elim-prop-classifying-type-Concrete-Groupᵉ :
    {l2ᵉ : Level} (Pᵉ : classifying-type-Concrete-Groupᵉ → Propᵉ l2ᵉ) →
    type-Propᵉ (Pᵉ shape-Concrete-Groupᵉ) →
    ((Xᵉ : classifying-type-Concrete-Groupᵉ) → type-Propᵉ (Pᵉ Xᵉ))
  elim-prop-classifying-type-Concrete-Groupᵉ =
    elim-prop-classifying-type-∞-Groupᵉ ∞-group-Concrete-Groupᵉ

  type-Concrete-Groupᵉ : UUᵉ lᵉ
  type-Concrete-Groupᵉ = type-∞-Groupᵉ ∞-group-Concrete-Groupᵉ

  is-set-type-Concrete-Groupᵉ : is-setᵉ type-Concrete-Groupᵉ
  is-set-type-Concrete-Groupᵉ = pr2ᵉ Gᵉ

  set-Concrete-Groupᵉ : Setᵉ lᵉ
  pr1ᵉ set-Concrete-Groupᵉ = type-Concrete-Groupᵉ
  pr2ᵉ set-Concrete-Groupᵉ = is-set-type-Concrete-Groupᵉ

  abstract
    is-1-type-classifying-type-Concrete-Groupᵉ :
      is-truncᵉ one-𝕋ᵉ classifying-type-Concrete-Groupᵉ
    is-1-type-classifying-type-Concrete-Groupᵉ Xᵉ Yᵉ =
      apply-universal-property-trunc-Propᵉ
        ( mere-eq-classifying-type-Concrete-Groupᵉ shape-Concrete-Groupᵉ Xᵉ)
        ( is-set-Propᵉ (Xᵉ ＝ᵉ Yᵉ))
        ( λ where
          reflᵉ →
            apply-universal-property-trunc-Propᵉ
              ( mere-eq-classifying-type-Concrete-Groupᵉ shape-Concrete-Groupᵉ Yᵉ)
              ( is-set-Propᵉ (shape-Concrete-Groupᵉ ＝ᵉ Yᵉ))
              ( λ where reflᵉ → is-set-type-Concrete-Groupᵉ))

  classifying-1-type-Concrete-Groupᵉ : Truncated-Typeᵉ lᵉ one-𝕋ᵉ
  pr1ᵉ classifying-1-type-Concrete-Groupᵉ = classifying-type-Concrete-Groupᵉ
  pr2ᵉ classifying-1-type-Concrete-Groupᵉ =
    is-1-type-classifying-type-Concrete-Groupᵉ

  Id-BG-Setᵉ :
    (Xᵉ Yᵉ : classifying-type-Concrete-Groupᵉ) → Setᵉ lᵉ
  Id-BG-Setᵉ Xᵉ Yᵉ = Id-Setᵉ classifying-1-type-Concrete-Groupᵉ Xᵉ Yᵉ
```

### The abstract group associated to a concrete group

```agda
module _
  {lᵉ : Level} (Gᵉ : Concrete-Groupᵉ lᵉ)
  where

  unit-Concrete-Groupᵉ : type-Concrete-Groupᵉ Gᵉ
  unit-Concrete-Groupᵉ = unit-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ)

  mul-Concrete-Groupᵉ : (xᵉ yᵉ : type-Concrete-Groupᵉ Gᵉ) → type-Concrete-Groupᵉ Gᵉ
  mul-Concrete-Groupᵉ = mul-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ)

  mul-Concrete-Group'ᵉ : (xᵉ yᵉ : type-Concrete-Groupᵉ Gᵉ) → type-Concrete-Groupᵉ Gᵉ
  mul-Concrete-Group'ᵉ xᵉ yᵉ = mul-Concrete-Groupᵉ yᵉ xᵉ

  associative-mul-Concrete-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-Concrete-Groupᵉ Gᵉ) →
    ( mul-Concrete-Groupᵉ (mul-Concrete-Groupᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( mul-Concrete-Groupᵉ xᵉ (mul-Concrete-Groupᵉ yᵉ zᵉ))
  associative-mul-Concrete-Groupᵉ =
    associative-mul-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ)

  left-unit-law-mul-Concrete-Groupᵉ :
    (xᵉ : type-Concrete-Groupᵉ Gᵉ) → mul-Concrete-Groupᵉ unit-Concrete-Groupᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Concrete-Groupᵉ =
    left-unit-law-mul-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ)

  right-unit-law-mul-Concrete-Groupᵉ :
    (yᵉ : type-Concrete-Groupᵉ Gᵉ) → mul-Concrete-Groupᵉ yᵉ unit-Concrete-Groupᵉ ＝ᵉ yᵉ
  right-unit-law-mul-Concrete-Groupᵉ =
    right-unit-law-mul-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ)

  coherence-unit-laws-mul-Concrete-Groupᵉ :
    left-unit-law-mul-Concrete-Groupᵉ unit-Concrete-Groupᵉ ＝ᵉ
    right-unit-law-mul-Concrete-Groupᵉ unit-Concrete-Groupᵉ
  coherence-unit-laws-mul-Concrete-Groupᵉ =
    coherence-unit-laws-mul-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ)

  inv-Concrete-Groupᵉ : type-Concrete-Groupᵉ Gᵉ → type-Concrete-Groupᵉ Gᵉ
  inv-Concrete-Groupᵉ = inv-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ)

  left-inverse-law-mul-Concrete-Groupᵉ :
    (xᵉ : type-Concrete-Groupᵉ Gᵉ) →
    mul-Concrete-Groupᵉ (inv-Concrete-Groupᵉ xᵉ) xᵉ ＝ᵉ unit-Concrete-Groupᵉ
  left-inverse-law-mul-Concrete-Groupᵉ =
    left-inverse-law-mul-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ)

  right-inverse-law-mul-Concrete-Groupᵉ :
    (xᵉ : type-Concrete-Groupᵉ Gᵉ) →
    mul-Concrete-Groupᵉ xᵉ (inv-Concrete-Groupᵉ xᵉ) ＝ᵉ unit-Concrete-Groupᵉ
  right-inverse-law-mul-Concrete-Groupᵉ =
    right-inverse-law-mul-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ)

  semigroup-Concrete-Groupᵉ : Semigroupᵉ lᵉ
  pr1ᵉ semigroup-Concrete-Groupᵉ = set-Concrete-Groupᵉ Gᵉ
  pr1ᵉ (pr2ᵉ semigroup-Concrete-Groupᵉ) = mul-Concrete-Groupᵉ
  pr2ᵉ (pr2ᵉ semigroup-Concrete-Groupᵉ) = associative-mul-Concrete-Groupᵉ

  is-unital-semigroup-Concrete-Groupᵉ :
    is-unital-Semigroupᵉ semigroup-Concrete-Groupᵉ
  pr1ᵉ is-unital-semigroup-Concrete-Groupᵉ = unit-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ is-unital-semigroup-Concrete-Groupᵉ) =
    left-unit-law-mul-Concrete-Groupᵉ
  pr2ᵉ (pr2ᵉ is-unital-semigroup-Concrete-Groupᵉ) =
    right-unit-law-mul-Concrete-Groupᵉ

  is-group-Concrete-Group'ᵉ :
    is-group-is-unital-Semigroupᵉ
      ( semigroup-Concrete-Groupᵉ)
      ( is-unital-semigroup-Concrete-Groupᵉ)
  pr1ᵉ is-group-Concrete-Group'ᵉ = inv-Concrete-Groupᵉ
  pr1ᵉ (pr2ᵉ is-group-Concrete-Group'ᵉ) =
    left-inverse-law-mul-Concrete-Groupᵉ
  pr2ᵉ (pr2ᵉ is-group-Concrete-Group'ᵉ) =
    right-inverse-law-mul-Concrete-Groupᵉ

  is-group-Concrete-Groupᵉ : is-group-Semigroupᵉ semigroup-Concrete-Groupᵉ
  pr1ᵉ is-group-Concrete-Groupᵉ = is-unital-semigroup-Concrete-Groupᵉ
  pr2ᵉ is-group-Concrete-Groupᵉ = is-group-Concrete-Group'ᵉ

  group-Concrete-Groupᵉ : Groupᵉ lᵉ
  pr1ᵉ group-Concrete-Groupᵉ = semigroup-Concrete-Groupᵉ
  pr2ᵉ group-Concrete-Groupᵉ = is-group-Concrete-Groupᵉ
```

### The opposite abstract group associated to a concrete group

```agda
module _
  {lᵉ : Level} (Gᵉ : Concrete-Groupᵉ lᵉ)
  where

  op-semigroup-Concrete-Groupᵉ : Semigroupᵉ lᵉ
  op-semigroup-Concrete-Groupᵉ = op-Semigroupᵉ (semigroup-Concrete-Groupᵉ Gᵉ)

  is-unital-op-semigroup-Concrete-Groupᵉ :
    is-unital-Semigroupᵉ op-semigroup-Concrete-Groupᵉ
  is-unital-op-semigroup-Concrete-Groupᵉ =
    is-unital-op-Groupᵉ (group-Concrete-Groupᵉ Gᵉ)

  is-group-op-Concrete-Groupᵉ : is-group-Semigroupᵉ op-semigroup-Concrete-Groupᵉ
  is-group-op-Concrete-Groupᵉ = is-group-op-Groupᵉ (group-Concrete-Groupᵉ Gᵉ)

  op-group-Concrete-Groupᵉ : Groupᵉ lᵉ
  op-group-Concrete-Groupᵉ = op-Groupᵉ (group-Concrete-Groupᵉ Gᵉ)
```