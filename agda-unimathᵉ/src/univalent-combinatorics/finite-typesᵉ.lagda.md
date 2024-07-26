# Finite types

```agda
module univalent-combinatorics.finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.0-connected-typesᵉ
open import foundation.1-typesᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.connected-components-universesᵉ
open import foundation.contractible-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.identity-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.subuniversesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.torsorial-type-familiesᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ **finite**ᵉ ifᵉ itᵉ isᵉ
[merelyᵉ equivalent](foundation.mere-equivalences.mdᵉ) to aᵉ
[standardᵉ finiteᵉ type](univalent-combinatorics.standard-finite-types.md).ᵉ

## Definition

### Finite types

```agda
is-finite-Propᵉ :
  {lᵉ : Level} → UUᵉ lᵉ → Propᵉ lᵉ
is-finite-Propᵉ Xᵉ = trunc-Propᵉ (countᵉ Xᵉ)

is-finiteᵉ :
  {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
is-finiteᵉ Xᵉ = type-Propᵉ (is-finite-Propᵉ Xᵉ)

abstract
  is-prop-is-finiteᵉ :
    {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-propᵉ (is-finiteᵉ Xᵉ)
  is-prop-is-finiteᵉ Xᵉ = is-prop-type-Propᵉ (is-finite-Propᵉ Xᵉ)

abstract
  is-finite-countᵉ :
    {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → countᵉ Xᵉ → is-finiteᵉ Xᵉ
  is-finite-countᵉ = unit-trunc-Propᵉ
```

### The type of all finite types of a universe level

```agda
𝔽ᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
𝔽ᵉ lᵉ = Σᵉ (UUᵉ lᵉ) is-finiteᵉ

type-𝔽ᵉ : {lᵉ : Level} → 𝔽ᵉ lᵉ → UUᵉ lᵉ
type-𝔽ᵉ = pr1ᵉ

is-finite-type-𝔽ᵉ :
  {lᵉ : Level} (Xᵉ : 𝔽ᵉ lᵉ) → is-finiteᵉ (type-𝔽ᵉ Xᵉ)
is-finite-type-𝔽ᵉ = pr2ᵉ
```

### Types with cardinality `k`

```agda
has-cardinality-Propᵉ :
  {lᵉ : Level} → ℕᵉ → UUᵉ lᵉ → Propᵉ lᵉ
has-cardinality-Propᵉ kᵉ = mere-equiv-Propᵉ (Finᵉ kᵉ)

has-cardinalityᵉ :
  {lᵉ : Level} → ℕᵉ → UUᵉ lᵉ → UUᵉ lᵉ
has-cardinalityᵉ kᵉ = mere-equivᵉ (Finᵉ kᵉ)
```

### The type of all types of cardinality `k` of a given universe level

```agda
UU-Finᵉ : (lᵉ : Level) → ℕᵉ → UUᵉ (lsuc lᵉ)
UU-Finᵉ lᵉ kᵉ = Σᵉ (UUᵉ lᵉ) (mere-equivᵉ (Finᵉ kᵉ))

type-UU-Finᵉ : {lᵉ : Level} (kᵉ : ℕᵉ) → UU-Finᵉ lᵉ kᵉ → UUᵉ lᵉ
type-UU-Finᵉ kᵉ = pr1ᵉ

abstract
  has-cardinality-type-UU-Finᵉ :
    {lᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ lᵉ kᵉ) →
    mere-equivᵉ (Finᵉ kᵉ) (type-UU-Finᵉ kᵉ Xᵉ)
  has-cardinality-type-UU-Finᵉ kᵉ = pr2ᵉ
```

### Types of finite cardinality

```agda
has-finite-cardinalityᵉ :
  {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
has-finite-cardinalityᵉ Xᵉ = Σᵉ ℕᵉ (λ kᵉ → has-cardinalityᵉ kᵉ Xᵉ)

number-of-elements-has-finite-cardinalityᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → has-finite-cardinalityᵉ Xᵉ → ℕᵉ
number-of-elements-has-finite-cardinalityᵉ = pr1ᵉ

abstract
  mere-equiv-has-finite-cardinalityᵉ :
    {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (cᵉ : has-finite-cardinalityᵉ Xᵉ) →
    type-trunc-Propᵉ (Finᵉ (number-of-elements-has-finite-cardinalityᵉ cᵉ) ≃ᵉ Xᵉ)
  mere-equiv-has-finite-cardinalityᵉ = pr2ᵉ
```

## Properties

### Finite types are closed under equivalences

```agda
abstract
  is-finite-equivᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
    is-finiteᵉ Aᵉ → is-finiteᵉ Bᵉ
  is-finite-equivᵉ eᵉ =
    map-universal-property-trunc-Propᵉ
      ( is-finite-Propᵉ _)
      ( is-finite-countᵉ ∘ᵉ (count-equivᵉ eᵉ))

abstract
  is-finite-is-equivᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
    is-equivᵉ fᵉ → is-finiteᵉ Aᵉ → is-finiteᵉ Bᵉ
  is-finite-is-equivᵉ is-equiv-fᵉ =
    map-universal-property-trunc-Propᵉ
      ( is-finite-Propᵉ _)
      ( is-finite-countᵉ ∘ᵉ (count-equivᵉ (pairᵉ _ is-equiv-fᵉ)))

abstract
  is-finite-equiv'ᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
    is-finiteᵉ Bᵉ → is-finiteᵉ Aᵉ
  is-finite-equiv'ᵉ eᵉ = is-finite-equivᵉ (inv-equivᵉ eᵉ)
```

### Finite types are closed under mere equivalences

```agda
abstract
  is-finite-mere-equivᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → mere-equivᵉ Aᵉ Bᵉ →
    is-finiteᵉ Aᵉ → is-finiteᵉ Bᵉ
  is-finite-mere-equivᵉ eᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ eᵉ
      ( is-finite-Propᵉ _)
      ( λ e'ᵉ → is-finite-equivᵉ e'ᵉ Hᵉ)
```

### The empty type is finite

```agda
abstract
  is-finite-emptyᵉ : is-finiteᵉ emptyᵉ
  is-finite-emptyᵉ = is-finite-countᵉ count-emptyᵉ

empty-𝔽ᵉ : 𝔽ᵉ lzero
pr1ᵉ empty-𝔽ᵉ = emptyᵉ
pr2ᵉ empty-𝔽ᵉ = is-finite-emptyᵉ

empty-UU-Finᵉ : UU-Finᵉ lzero zero-ℕᵉ
pr1ᵉ empty-UU-Finᵉ = emptyᵉ
pr2ᵉ empty-UU-Finᵉ = unit-trunc-Propᵉ id-equivᵉ
```

### The empty type has finite cardinality

```agda
has-finite-cardinality-emptyᵉ : has-finite-cardinalityᵉ emptyᵉ
pr1ᵉ has-finite-cardinality-emptyᵉ = zero-ℕᵉ
pr2ᵉ has-finite-cardinality-emptyᵉ = unit-trunc-Propᵉ id-equivᵉ
```

### Empty types are finite

```agda
abstract
  is-finite-is-emptyᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → is-emptyᵉ Xᵉ → is-finiteᵉ Xᵉ
  is-finite-is-emptyᵉ Hᵉ = is-finite-countᵉ (count-is-emptyᵉ Hᵉ)
```

### Empty types have finite cardinality

```agda
has-finite-cardinality-is-emptyᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → is-emptyᵉ Xᵉ → has-finite-cardinalityᵉ Xᵉ
pr1ᵉ (has-finite-cardinality-is-emptyᵉ fᵉ) = zero-ℕᵉ
pr2ᵉ (has-finite-cardinality-is-emptyᵉ fᵉ) =
  unit-trunc-Propᵉ (equiv-countᵉ (count-is-emptyᵉ fᵉ))
```

### The unit type is finite

```agda
abstract
  is-finite-unitᵉ : is-finiteᵉ unitᵉ
  is-finite-unitᵉ = is-finite-countᵉ count-unitᵉ

abstract
  is-finite-raise-unitᵉ :
    {l1ᵉ : Level} → is-finiteᵉ (raise-unitᵉ l1ᵉ)
  is-finite-raise-unitᵉ {l1ᵉ} =
    is-finite-equivᵉ (compute-raise-unitᵉ l1ᵉ) is-finite-unitᵉ

unit-𝔽ᵉ : 𝔽ᵉ lzero
pr1ᵉ unit-𝔽ᵉ = unitᵉ
pr2ᵉ unit-𝔽ᵉ = is-finite-unitᵉ

unit-UU-Finᵉ : UU-Finᵉ lzero 1
pr1ᵉ unit-UU-Finᵉ = unitᵉ
pr2ᵉ unit-UU-Finᵉ = unit-trunc-Propᵉ (left-unit-law-coproductᵉ unitᵉ)
```

### Contractible types are finite

```agda
abstract
  is-finite-is-contrᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → is-contrᵉ Xᵉ → is-finiteᵉ Xᵉ
  is-finite-is-contrᵉ Hᵉ = is-finite-countᵉ (count-is-contrᵉ Hᵉ)

abstract
  has-cardinality-is-contrᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → is-contrᵉ Xᵉ → has-cardinalityᵉ 1 Xᵉ
  has-cardinality-is-contrᵉ Hᵉ =
    unit-trunc-Propᵉ (equiv-is-contrᵉ is-contr-Fin-one-ℕᵉ Hᵉ)
```

### The standard finite types are finite

```agda
abstract
  is-finite-Finᵉ : (kᵉ : ℕᵉ) → is-finiteᵉ (Finᵉ kᵉ)
  is-finite-Finᵉ kᵉ = is-finite-countᵉ (count-Finᵉ kᵉ)

Fin-𝔽ᵉ : ℕᵉ → 𝔽ᵉ lzero
pr1ᵉ (Fin-𝔽ᵉ kᵉ) = Finᵉ kᵉ
pr2ᵉ (Fin-𝔽ᵉ kᵉ) = is-finite-Finᵉ kᵉ

has-cardinality-raise-Finᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) → has-cardinalityᵉ kᵉ (raise-Finᵉ lᵉ kᵉ)
has-cardinality-raise-Finᵉ {lᵉ} kᵉ = unit-trunc-Propᵉ (compute-raise-Finᵉ lᵉ kᵉ)

Fin-UU-Finᵉ : (lᵉ : Level) (kᵉ : ℕᵉ) → UU-Finᵉ lᵉ kᵉ
pr1ᵉ (Fin-UU-Finᵉ lᵉ kᵉ) = raise-Finᵉ lᵉ kᵉ
pr2ᵉ (Fin-UU-Finᵉ lᵉ kᵉ) = has-cardinality-raise-Finᵉ kᵉ

Fin-UU-Fin'ᵉ : (kᵉ : ℕᵉ) → UU-Finᵉ lzero kᵉ
pr1ᵉ (Fin-UU-Fin'ᵉ kᵉ) = Finᵉ kᵉ
pr2ᵉ (Fin-UU-Fin'ᵉ kᵉ) = unit-trunc-Propᵉ id-equivᵉ
```

### Every type of cardinality `k` is finite

```agda
abstract
  is-finite-type-UU-Finᵉ :
    {lᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ lᵉ kᵉ) →
    is-finiteᵉ (type-UU-Finᵉ kᵉ Xᵉ)
  is-finite-type-UU-Finᵉ kᵉ Xᵉ =
    is-finite-mere-equivᵉ
      ( has-cardinality-type-UU-Finᵉ kᵉ Xᵉ)
      ( is-finite-Finᵉ kᵉ)

finite-type-UU-Finᵉ : {lᵉ : Level} (kᵉ : ℕᵉ) → UU-Finᵉ lᵉ kᵉ → 𝔽ᵉ lᵉ
pr1ᵉ (finite-type-UU-Finᵉ kᵉ Xᵉ) = type-UU-Finᵉ kᵉ Xᵉ
pr2ᵉ (finite-type-UU-Finᵉ kᵉ Xᵉ) = is-finite-type-UU-Finᵉ kᵉ Xᵉ
```

### Having a finite cardinality is a proposition

```agda
abstract
  all-elements-equal-has-finite-cardinalityᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → all-elements-equalᵉ (has-finite-cardinalityᵉ Xᵉ)
  all-elements-equal-has-finite-cardinalityᵉ {l1ᵉ} {Xᵉ} (pairᵉ kᵉ Kᵉ) (pairᵉ lᵉ Lᵉ) =
    eq-type-subtypeᵉ
      ( λ kᵉ → mere-equiv-Propᵉ (Finᵉ kᵉ) Xᵉ)
      ( apply-universal-property-trunc-Propᵉ Kᵉ
        ( Id-Propᵉ ℕ-Setᵉ kᵉ lᵉ)
        ( λ (eᵉ : Finᵉ kᵉ ≃ᵉ Xᵉ) →
          apply-universal-property-trunc-Propᵉ Lᵉ
            ( Id-Propᵉ ℕ-Setᵉ kᵉ lᵉ)
            ( λ (fᵉ : Finᵉ lᵉ ≃ᵉ Xᵉ) →
              is-equivalence-injective-Finᵉ (inv-equivᵉ fᵉ ∘eᵉ eᵉ))))

abstract
  is-prop-has-finite-cardinalityᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → is-propᵉ (has-finite-cardinalityᵉ Xᵉ)
  is-prop-has-finite-cardinalityᵉ =
    is-prop-all-elements-equalᵉ all-elements-equal-has-finite-cardinalityᵉ

has-finite-cardinality-Propᵉ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) → Propᵉ l1ᵉ
pr1ᵉ (has-finite-cardinality-Propᵉ Xᵉ) = has-finite-cardinalityᵉ Xᵉ
pr2ᵉ (has-finite-cardinality-Propᵉ Xᵉ) = is-prop-has-finite-cardinalityᵉ
```

### A type has a finite cardinality if and only if it is finite

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  abstract
    is-finite-has-finite-cardinalityᵉ : has-finite-cardinalityᵉ Xᵉ → is-finiteᵉ Xᵉ
    is-finite-has-finite-cardinalityᵉ (pairᵉ kᵉ Kᵉ) =
      apply-universal-property-trunc-Propᵉ Kᵉ
        ( is-finite-Propᵉ Xᵉ)
        ( is-finite-countᵉ ∘ᵉ pairᵉ kᵉ)

  abstract
    is-finite-has-cardinalityᵉ : (kᵉ : ℕᵉ) → has-cardinalityᵉ kᵉ Xᵉ → is-finiteᵉ Xᵉ
    is-finite-has-cardinalityᵉ kᵉ Hᵉ =
      is-finite-has-finite-cardinalityᵉ (pairᵉ kᵉ Hᵉ)

  has-finite-cardinality-countᵉ : countᵉ Xᵉ → has-finite-cardinalityᵉ Xᵉ
  pr1ᵉ (has-finite-cardinality-countᵉ eᵉ) = number-of-elements-countᵉ eᵉ
  pr2ᵉ (has-finite-cardinality-countᵉ eᵉ) = unit-trunc-Propᵉ (equiv-countᵉ eᵉ)

  abstract
    has-finite-cardinality-is-finiteᵉ : is-finiteᵉ Xᵉ → has-finite-cardinalityᵉ Xᵉ
    has-finite-cardinality-is-finiteᵉ =
      map-universal-property-trunc-Propᵉ
        ( has-finite-cardinality-Propᵉ Xᵉ)
        ( has-finite-cardinality-countᵉ)

  number-of-elements-is-finiteᵉ : is-finiteᵉ Xᵉ → ℕᵉ
  number-of-elements-is-finiteᵉ =
    number-of-elements-has-finite-cardinalityᵉ ∘ᵉ has-finite-cardinality-is-finiteᵉ

  abstract
    mere-equiv-is-finiteᵉ :
      (fᵉ : is-finiteᵉ Xᵉ) → mere-equivᵉ (Finᵉ (number-of-elements-is-finiteᵉ fᵉ)) Xᵉ
    mere-equiv-is-finiteᵉ fᵉ =
      mere-equiv-has-finite-cardinalityᵉ (has-finite-cardinality-is-finiteᵉ fᵉ)

  abstract
    compute-number-of-elements-is-finiteᵉ :
      (eᵉ : countᵉ Xᵉ) (fᵉ : is-finiteᵉ Xᵉ) →
      Idᵉ (number-of-elements-countᵉ eᵉ) (number-of-elements-is-finiteᵉ fᵉ)
    compute-number-of-elements-is-finiteᵉ eᵉ fᵉ =
      ind-trunc-Propᵉ
        ( λ gᵉ →
          Id-Propᵉ ℕ-Setᵉ
            ( number-of-elements-countᵉ eᵉ)
            ( number-of-elements-is-finiteᵉ gᵉ))
        ( λ gᵉ →
          ( is-equivalence-injective-Finᵉ
            ( inv-equivᵉ (equiv-countᵉ gᵉ) ∘eᵉ equiv-countᵉ eᵉ)) ∙ᵉ
          ( apᵉ pr1ᵉ
            ( eq-is-prop'ᵉ is-prop-has-finite-cardinalityᵉ
              ( has-finite-cardinality-countᵉ gᵉ)
              ( has-finite-cardinality-is-finiteᵉ (unit-trunc-Propᵉ gᵉ)))))
        ( fᵉ)

  has-cardinality-is-finiteᵉ :
    (Hᵉ : is-finiteᵉ Xᵉ) → has-cardinalityᵉ (number-of-elements-is-finiteᵉ Hᵉ) Xᵉ
  has-cardinality-is-finiteᵉ Hᵉ =
    pr2ᵉ (has-finite-cardinality-is-finiteᵉ Hᵉ)

number-of-elements-𝔽ᵉ : {lᵉ : Level} → 𝔽ᵉ lᵉ → ℕᵉ
number-of-elements-𝔽ᵉ Xᵉ = number-of-elements-is-finiteᵉ (is-finite-type-𝔽ᵉ Xᵉ)
```

### If a type has cardinality `k` and cardinality `l`, then `k = l`

```agda
eq-cardinalityᵉ :
  {l1ᵉ : Level} {kᵉ lᵉ : ℕᵉ} {Aᵉ : UUᵉ l1ᵉ} →
  has-cardinalityᵉ kᵉ Aᵉ → has-cardinalityᵉ lᵉ Aᵉ → Idᵉ kᵉ lᵉ
eq-cardinalityᵉ Hᵉ Kᵉ =
  apply-universal-property-trunc-Propᵉ Hᵉ
    ( Id-Propᵉ ℕ-Setᵉ _ _)
    ( λ eᵉ →
      apply-universal-property-trunc-Propᵉ Kᵉ
        ( Id-Propᵉ ℕ-Setᵉ _ _)
        ( λ fᵉ → is-equivalence-injective-Finᵉ (inv-equivᵉ fᵉ ∘eᵉ eᵉ)))
```

### Any finite type is a set

```agda
abstract
  is-set-is-finiteᵉ :
    {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → is-finiteᵉ Xᵉ → is-setᵉ Xᵉ
  is-set-is-finiteᵉ {lᵉ} {Xᵉ} Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( is-set-Propᵉ Xᵉ)
      ( λ eᵉ → is-set-countᵉ eᵉ)

is-set-type-𝔽ᵉ : {lᵉ : Level} (Xᵉ : 𝔽ᵉ lᵉ) → is-setᵉ (type-𝔽ᵉ Xᵉ)
is-set-type-𝔽ᵉ Xᵉ = is-set-is-finiteᵉ (is-finite-type-𝔽ᵉ Xᵉ)

set-𝔽ᵉ : {lᵉ : Level} → 𝔽ᵉ lᵉ → Setᵉ lᵉ
pr1ᵉ (set-𝔽ᵉ Xᵉ) = type-𝔽ᵉ Xᵉ
pr2ᵉ (set-𝔽ᵉ Xᵉ) = is-set-is-finiteᵉ (is-finite-type-𝔽ᵉ Xᵉ)
```

### Any type of cardinality `k` is a set

```agda
is-set-has-cardinalityᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (kᵉ : ℕᵉ) → has-cardinalityᵉ kᵉ Xᵉ → is-setᵉ Xᵉ
is-set-has-cardinalityᵉ kᵉ Hᵉ = is-set-mere-equiv'ᵉ Hᵉ (is-set-Finᵉ kᵉ)

is-set-type-UU-Finᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ lᵉ kᵉ) → is-setᵉ (type-UU-Finᵉ kᵉ Xᵉ)
is-set-type-UU-Finᵉ kᵉ Xᵉ =
  is-set-has-cardinalityᵉ kᵉ (has-cardinality-type-UU-Finᵉ kᵉ Xᵉ)

set-UU-Finᵉ : {l1ᵉ : Level} (kᵉ : ℕᵉ) → UU-Finᵉ l1ᵉ kᵉ → Setᵉ l1ᵉ
pr1ᵉ (set-UU-Finᵉ kᵉ Xᵉ) = type-UU-Finᵉ kᵉ Xᵉ
pr2ᵉ (set-UU-Finᵉ kᵉ Xᵉ) = is-set-type-UU-Finᵉ kᵉ Xᵉ
```

### A finite type is empty if and only if it has 0 elements

```agda
abstract
  is-empty-is-zero-number-of-elements-is-finiteᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (fᵉ : is-finiteᵉ Xᵉ) →
    is-zero-ℕᵉ (number-of-elements-is-finiteᵉ fᵉ) → is-emptyᵉ Xᵉ
  is-empty-is-zero-number-of-elements-is-finiteᵉ {l1ᵉ} {Xᵉ} fᵉ pᵉ =
    apply-universal-property-trunc-Propᵉ fᵉ
      ( is-empty-Propᵉ Xᵉ)
      ( λ eᵉ →
        is-empty-is-zero-number-of-elements-countᵉ eᵉ
          ( compute-number-of-elements-is-finiteᵉ eᵉ fᵉ ∙ᵉ pᵉ))
```

### A finite type is contractible if and only if it has one element

```agda
is-one-number-of-elements-is-finite-is-contrᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (Hᵉ : is-finiteᵉ Xᵉ) →
  is-contrᵉ Xᵉ → is-one-ℕᵉ (number-of-elements-is-finiteᵉ Hᵉ)
is-one-number-of-elements-is-finite-is-contrᵉ Hᵉ Kᵉ =
  eq-cardinalityᵉ
    ( has-cardinality-is-finiteᵉ Hᵉ)
    ( has-cardinality-is-contrᵉ Kᵉ)

is-contr-is-one-number-of-elements-is-finiteᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (Hᵉ : is-finiteᵉ Xᵉ) →
  is-one-ℕᵉ (number-of-elements-is-finiteᵉ Hᵉ) → is-contrᵉ Xᵉ
is-contr-is-one-number-of-elements-is-finiteᵉ Hᵉ pᵉ =
  apply-universal-property-trunc-Propᵉ Hᵉ
    ( is-contr-Propᵉ _)
    ( λ eᵉ →
      is-contr-equiv'ᵉ
        ( Finᵉ 1ᵉ)
        ( ( equiv-countᵉ eᵉ) ∘eᵉ
          ( equiv-trᵉ Finᵉ
            ( invᵉ pᵉ ∙ᵉ invᵉ (compute-number-of-elements-is-finiteᵉ eᵉ Hᵉ))))
        ( is-contr-Fin-one-ℕᵉ))

is-decidable-is-contr-is-finiteᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (Hᵉ : is-finiteᵉ Xᵉ) → is-decidableᵉ (is-contrᵉ Xᵉ)
is-decidable-is-contr-is-finiteᵉ Hᵉ =
  is-decidable-iffᵉ
    ( is-contr-is-one-number-of-elements-is-finiteᵉ Hᵉ)
    ( is-one-number-of-elements-is-finite-is-contrᵉ Hᵉ)
    ( has-decidable-equality-ℕᵉ (number-of-elements-is-finiteᵉ Hᵉ) 1ᵉ)
```

### The type of all pairs consisting of a natural number `k` and a type of cardinality `k` is equivalent to the type of all finite types

```agda
map-compute-total-UU-Finᵉ : {lᵉ : Level} → Σᵉ ℕᵉ (UU-Finᵉ lᵉ) → 𝔽ᵉ lᵉ
pr1ᵉ (map-compute-total-UU-Finᵉ (pairᵉ kᵉ (pairᵉ Xᵉ eᵉ))) = Xᵉ
pr2ᵉ (map-compute-total-UU-Finᵉ (pairᵉ kᵉ (pairᵉ Xᵉ eᵉ))) =
  is-finite-has-finite-cardinalityᵉ (pairᵉ kᵉ eᵉ)

compute-total-UU-Finᵉ : {lᵉ : Level} → Σᵉ ℕᵉ (UU-Finᵉ lᵉ) ≃ᵉ 𝔽ᵉ lᵉ
compute-total-UU-Finᵉ =
  ( equiv-totᵉ
    ( λ Xᵉ →
      equiv-iff-is-propᵉ
        ( is-prop-has-finite-cardinalityᵉ)
        ( is-prop-is-finiteᵉ Xᵉ)
        ( is-finite-has-finite-cardinalityᵉ)
        ( has-finite-cardinality-is-finiteᵉ))) ∘eᵉ
  ( equiv-left-swap-Σᵉ)
```

### Finite types are either inhabited or empty

```agda
is-inhabited-or-empty-is-finiteᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-finiteᵉ Aᵉ → is-inhabited-or-emptyᵉ Aᵉ
is-inhabited-or-empty-is-finiteᵉ {l1ᵉ} {Aᵉ} fᵉ =
  apply-universal-property-trunc-Propᵉ fᵉ
    ( is-inhabited-or-empty-Propᵉ Aᵉ)
    ( is-inhabited-or-empty-countᵉ)
```

### Finite types of cardinality greater than one are inhabited

```agda
is-inhabited-type-UU-Fin-succ-ℕᵉ :
  {l1ᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : UU-Finᵉ l1ᵉ (succ-ℕᵉ nᵉ)) →
  is-inhabitedᵉ (type-UU-Finᵉ (succ-ℕᵉ nᵉ) Aᵉ)
is-inhabited-type-UU-Fin-succ-ℕᵉ nᵉ Aᵉ =
  apply-universal-property-trunc-Propᵉ
    ( pr2ᵉ Aᵉ)
    ( is-inhabited-Propᵉ (type-UU-Finᵉ (succ-ℕᵉ nᵉ) Aᵉ))
    ( λ eᵉ → unit-trunc-Propᵉ (map-equivᵉ eᵉ (zero-Finᵉ nᵉ)))
```

### If `X` is finite, then its propositional truncation is decidable

```agda
is-decidable-type-trunc-Prop-is-finiteᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-finiteᵉ Aᵉ → is-decidableᵉ (type-trunc-Propᵉ Aᵉ)
is-decidable-type-trunc-Prop-is-finiteᵉ Hᵉ =
  map-coproductᵉ
    ( idᵉ)
    ( map-universal-property-trunc-Propᵉ empty-Propᵉ)
      ( is-inhabited-or-empty-is-finiteᵉ Hᵉ)
```

### If a type is finite, then its propositional truncation is finite

```agda
abstract
  is-finite-type-trunc-Propᵉ :
    {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-finiteᵉ Aᵉ → is-finiteᵉ (type-trunc-Propᵉ Aᵉ)
  is-finite-type-trunc-Propᵉ = map-trunc-Propᵉ count-type-trunc-Propᵉ

trunc-Prop-𝔽ᵉ : {lᵉ : Level} → 𝔽ᵉ lᵉ → 𝔽ᵉ lᵉ
pr1ᵉ (trunc-Prop-𝔽ᵉ Aᵉ) = type-trunc-Propᵉ (type-𝔽ᵉ Aᵉ)
pr2ᵉ (trunc-Prop-𝔽ᵉ Aᵉ) = is-finite-type-trunc-Propᵉ (is-finite-type-𝔽ᵉ Aᵉ)
```

### We characterize the identity type of 𝔽

```agda
equiv-𝔽ᵉ : {l1ᵉ l2ᵉ : Level} → 𝔽ᵉ l1ᵉ → 𝔽ᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
equiv-𝔽ᵉ Xᵉ Yᵉ = type-𝔽ᵉ Xᵉ ≃ᵉ type-𝔽ᵉ Yᵉ

id-equiv-𝔽ᵉ : {lᵉ : Level} → (Xᵉ : 𝔽ᵉ lᵉ) → equiv-𝔽ᵉ Xᵉ Xᵉ
id-equiv-𝔽ᵉ Xᵉ = id-equivᵉ

extensionality-𝔽ᵉ : {lᵉ : Level} → (Xᵉ Yᵉ : 𝔽ᵉ lᵉ) → Idᵉ Xᵉ Yᵉ ≃ᵉ equiv-𝔽ᵉ Xᵉ Yᵉ
extensionality-𝔽ᵉ = extensionality-subuniverseᵉ is-finite-Propᵉ

is-torsorial-equiv-𝔽ᵉ :
  {lᵉ : Level} → (Xᵉ : 𝔽ᵉ lᵉ) → is-torsorialᵉ (λ (Yᵉ : 𝔽ᵉ lᵉ) → equiv-𝔽ᵉ Xᵉ Yᵉ)
is-torsorial-equiv-𝔽ᵉ {lᵉ} Xᵉ =
  is-contr-equiv'ᵉ
    ( Σᵉ (𝔽ᵉ lᵉ) (Idᵉ Xᵉ))
    ( equiv-totᵉ (extensionality-𝔽ᵉ Xᵉ))
    ( is-torsorial-Idᵉ Xᵉ)

equiv-eq-𝔽ᵉ : {lᵉ : Level} → (Xᵉ Yᵉ : 𝔽ᵉ lᵉ) → Idᵉ Xᵉ Yᵉ → equiv-𝔽ᵉ Xᵉ Yᵉ
equiv-eq-𝔽ᵉ Xᵉ Yᵉ = map-equivᵉ (extensionality-𝔽ᵉ Xᵉ Yᵉ)

eq-equiv-𝔽ᵉ : {lᵉ : Level} → (Xᵉ Yᵉ : 𝔽ᵉ lᵉ) → equiv-𝔽ᵉ Xᵉ Yᵉ → Idᵉ Xᵉ Yᵉ
eq-equiv-𝔽ᵉ Xᵉ Yᵉ = map-inv-equivᵉ (extensionality-𝔽ᵉ Xᵉ Yᵉ)
```

### We characterize the identity type of families of finite types

```agda
equiv-fam-𝔽ᵉ : {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Yᵉ Zᵉ : Xᵉ → 𝔽ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
equiv-fam-𝔽ᵉ Yᵉ Zᵉ = equiv-famᵉ (type-𝔽ᵉ ∘ᵉ Yᵉ) (type-𝔽ᵉ ∘ᵉ Zᵉ)

id-equiv-fam-𝔽ᵉ : {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → (Yᵉ : Xᵉ → 𝔽ᵉ l2ᵉ) → equiv-fam-𝔽ᵉ Yᵉ Yᵉ
id-equiv-fam-𝔽ᵉ Yᵉ xᵉ = id-equivᵉ

extensionality-fam-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Yᵉ Zᵉ : Xᵉ → 𝔽ᵉ l2ᵉ) → Idᵉ Yᵉ Zᵉ ≃ᵉ equiv-fam-𝔽ᵉ Yᵉ Zᵉ
extensionality-fam-𝔽ᵉ = extensionality-fam-subuniverseᵉ is-finite-Propᵉ
```

### We characterize the identity type of `UU-Fin`

```agda
equiv-UU-Finᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) → UU-Finᵉ l1ᵉ kᵉ → UU-Finᵉ l2ᵉ kᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
equiv-UU-Finᵉ kᵉ Xᵉ Yᵉ = type-UU-Finᵉ kᵉ Xᵉ ≃ᵉ type-UU-Finᵉ kᵉ Yᵉ

id-equiv-UU-Finᵉ :
  {lᵉ : Level} {kᵉ : ℕᵉ} (Xᵉ : UU-Finᵉ lᵉ kᵉ) → equiv-UU-Finᵉ kᵉ Xᵉ Xᵉ
id-equiv-UU-Finᵉ Xᵉ = id-equiv-component-UU-Levelᵉ Xᵉ

equiv-eq-UU-Finᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Xᵉ Yᵉ : UU-Finᵉ lᵉ kᵉ} → Idᵉ Xᵉ Yᵉ → equiv-UU-Finᵉ kᵉ Xᵉ Yᵉ
equiv-eq-UU-Finᵉ kᵉ pᵉ = equiv-eq-component-UU-Levelᵉ pᵉ

abstract
  is-torsorial-equiv-UU-Finᵉ :
    {lᵉ : Level} {kᵉ : ℕᵉ} (Xᵉ : UU-Finᵉ lᵉ kᵉ) →
    is-torsorialᵉ (λ (Yᵉ : UU-Finᵉ lᵉ kᵉ) → equiv-UU-Finᵉ kᵉ Xᵉ Yᵉ)
  is-torsorial-equiv-UU-Finᵉ {lᵉ} {kᵉ} Xᵉ =
    is-torsorial-equiv-component-UU-Levelᵉ Xᵉ

abstract
  is-equiv-equiv-eq-UU-Finᵉ :
    {lᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ Yᵉ : UU-Finᵉ lᵉ kᵉ) →
    is-equivᵉ (equiv-eq-UU-Finᵉ kᵉ {Xᵉ = Xᵉ} {Yᵉ})
  is-equiv-equiv-eq-UU-Finᵉ kᵉ Xᵉ =
    is-equiv-equiv-eq-component-UU-Levelᵉ Xᵉ

eq-equiv-UU-Finᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ Yᵉ : UU-Finᵉ lᵉ kᵉ) →
  equiv-UU-Finᵉ kᵉ Xᵉ Yᵉ → Idᵉ Xᵉ Yᵉ
eq-equiv-UU-Finᵉ kᵉ Xᵉ Yᵉ =
  eq-equiv-component-UU-Levelᵉ Xᵉ Yᵉ

equiv-equiv-eq-UU-Finᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ Yᵉ : UU-Finᵉ lᵉ kᵉ) →
  Idᵉ Xᵉ Yᵉ ≃ᵉ equiv-UU-Finᵉ kᵉ Xᵉ Yᵉ
pr1ᵉ (equiv-equiv-eq-UU-Finᵉ kᵉ Xᵉ Yᵉ) = equiv-eq-UU-Finᵉ kᵉ
pr2ᵉ (equiv-equiv-eq-UU-Finᵉ kᵉ Xᵉ Yᵉ) = is-equiv-equiv-eq-UU-Finᵉ kᵉ Xᵉ Yᵉ
```

### The type `UU-Fin l k` is a 1-type

```agda
is-1-type-UU-Finᵉ : {lᵉ : Level} (kᵉ : ℕᵉ) → is-1-typeᵉ (UU-Finᵉ lᵉ kᵉ)
is-1-type-UU-Finᵉ kᵉ Xᵉ Yᵉ =
  is-set-equivᵉ
    ( equiv-UU-Finᵉ kᵉ Xᵉ Yᵉ)
    ( equiv-equiv-eq-UU-Finᵉ kᵉ Xᵉ Yᵉ)
    ( is-set-equiv-is-setᵉ
      ( is-set-type-UU-Finᵉ kᵉ Xᵉ)
      ( is-set-type-UU-Finᵉ kᵉ Yᵉ))

UU-Fin-1-Typeᵉ : (lᵉ : Level) (kᵉ : ℕᵉ) → 1-Typeᵉ (lsuc lᵉ)
pr1ᵉ (UU-Fin-1-Typeᵉ lᵉ kᵉ) = UU-Finᵉ lᵉ kᵉ
pr2ᵉ (UU-Fin-1-Typeᵉ lᵉ kᵉ) = is-1-type-UU-Finᵉ kᵉ
```

### The type `UU-Fin` is connected

```agda
abstract
  is-0-connected-UU-Finᵉ :
    {lᵉ : Level} (nᵉ : ℕᵉ) → is-0-connectedᵉ (UU-Finᵉ lᵉ nᵉ)
  is-0-connected-UU-Finᵉ {lᵉ} nᵉ =
    is-0-connected-mere-eqᵉ
      ( Fin-UU-Finᵉ lᵉ nᵉ)
      ( λ Aᵉ →
        map-trunc-Propᵉ
          ( ( eq-equiv-UU-Finᵉ nᵉ (Fin-UU-Finᵉ lᵉ nᵉ) Aᵉ) ∘ᵉ
            ( map-equivᵉ
              ( equiv-precomp-equivᵉ
                ( inv-equivᵉ (compute-raiseᵉ lᵉ (Finᵉ nᵉ)))
                ( type-UU-Finᵉ nᵉ Aᵉ))))
          ( pr2ᵉ Aᵉ))
```

```agda
  equiv-has-cardinality-id-number-of-elements-is-finiteᵉ :
    {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) ( Hᵉ : is-finiteᵉ Xᵉ) (nᵉ : ℕᵉ) →
    ( has-cardinalityᵉ nᵉ Xᵉ ≃ᵉ Idᵉ (number-of-elements-is-finiteᵉ Hᵉ) nᵉ)
  pr1ᵉ (equiv-has-cardinality-id-number-of-elements-is-finiteᵉ Xᵉ Hᵉ nᵉ) Qᵉ =
    apᵉ
      ( number-of-elements-has-finite-cardinalityᵉ)
      ( all-elements-equal-has-finite-cardinalityᵉ
        ( has-finite-cardinality-is-finiteᵉ Hᵉ)
        ( pairᵉ nᵉ Qᵉ))
  pr2ᵉ (equiv-has-cardinality-id-number-of-elements-is-finiteᵉ Xᵉ Hᵉ nᵉ) =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-type-trunc-Propᵉ)
      ( is-set-ℕᵉ (number-of-elements-is-finiteᵉ Hᵉ) nᵉ)
      ( λ pᵉ →
        trᵉ
          ( λ mᵉ → has-cardinalityᵉ mᵉ Xᵉ)
          ( pᵉ)
          ( pr2ᵉ (has-finite-cardinality-is-finiteᵉ Hᵉ)))
```