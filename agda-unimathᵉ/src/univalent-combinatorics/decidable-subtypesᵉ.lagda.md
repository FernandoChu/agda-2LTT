# Decidable subtypes of finite types

```agda
module univalent-combinatorics.decidable-subtypesᵉ where

open import foundation.decidable-subtypesᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.embeddingsᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.decidable-dependent-pair-typesᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.function-typesᵉ
```

</details>

## Definitions

### Finite subsets of a finite set

```agda
subset-𝔽ᵉ : {l1ᵉ : Level} (l2ᵉ : Level) → 𝔽ᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
subset-𝔽ᵉ l2ᵉ Xᵉ = decidable-subtypeᵉ l2ᵉ (type-𝔽ᵉ Xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Pᵉ : subset-𝔽ᵉ l2ᵉ Xᵉ)
  where

  subtype-subset-𝔽ᵉ : subtypeᵉ l2ᵉ (type-𝔽ᵉ Xᵉ)
  subtype-subset-𝔽ᵉ = subtype-decidable-subtypeᵉ Pᵉ

  is-decidable-subset-𝔽ᵉ : is-decidable-subtypeᵉ subtype-subset-𝔽ᵉ
  is-decidable-subset-𝔽ᵉ =
    is-decidable-decidable-subtypeᵉ Pᵉ

  is-in-subset-𝔽ᵉ : type-𝔽ᵉ Xᵉ → UUᵉ l2ᵉ
  is-in-subset-𝔽ᵉ = is-in-decidable-subtypeᵉ Pᵉ

  is-prop-is-in-subset-𝔽ᵉ :
    (xᵉ : type-𝔽ᵉ Xᵉ) → is-propᵉ (is-in-subset-𝔽ᵉ xᵉ)
  is-prop-is-in-subset-𝔽ᵉ = is-prop-is-in-decidable-subtypeᵉ Pᵉ
```

### The underlying type of a decidable subtype

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Pᵉ : subset-𝔽ᵉ l2ᵉ Xᵉ)
  where

  type-subset-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-subset-𝔽ᵉ = type-decidable-subtypeᵉ Pᵉ

  inclusion-subset-𝔽ᵉ : type-subset-𝔽ᵉ → type-𝔽ᵉ Xᵉ
  inclusion-subset-𝔽ᵉ = inclusion-decidable-subtypeᵉ Pᵉ

  is-emb-inclusion-subset-𝔽ᵉ : is-embᵉ inclusion-subset-𝔽ᵉ
  is-emb-inclusion-subset-𝔽ᵉ = is-emb-inclusion-decidable-subtypeᵉ Pᵉ

  is-injective-inclusion-subset-𝔽ᵉ : is-injectiveᵉ inclusion-subset-𝔽ᵉ
  is-injective-inclusion-subset-𝔽ᵉ =
    is-injective-inclusion-decidable-subtypeᵉ Pᵉ

  emb-subset-𝔽ᵉ : type-subset-𝔽ᵉ ↪ᵉ type-𝔽ᵉ Xᵉ
  emb-subset-𝔽ᵉ = emb-decidable-subtypeᵉ Pᵉ
```

## Properties

### The type of decidable subtypes of a finite type is finite

```agda
is-finite-decidable-subtype-is-finiteᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} →
  is-finiteᵉ Xᵉ → is-finiteᵉ (decidable-subtypeᵉ l2ᵉ Xᵉ)
is-finite-decidable-subtype-is-finiteᵉ Hᵉ =
  is-finite-function-typeᵉ Hᵉ is-finite-Decidable-Propᵉ

Subset-𝔽ᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → 𝔽ᵉ l1ᵉ → 𝔽ᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
pr1ᵉ (Subset-𝔽ᵉ l2ᵉ Xᵉ) = subset-𝔽ᵉ l2ᵉ Xᵉ
pr2ᵉ (Subset-𝔽ᵉ l2ᵉ Xᵉ) = is-finite-decidable-subtype-is-finiteᵉ (is-finite-type-𝔽ᵉ Xᵉ)
```

### The type of decidable subsets of a finite type has decidable equality

```agda
has-decidable-equality-Subset-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) →
  has-decidable-equalityᵉ (decidable-subtypeᵉ l2ᵉ (type-𝔽ᵉ Xᵉ))
has-decidable-equality-Subset-𝔽ᵉ {l1ᵉ} {l2ᵉ} Xᵉ =
  has-decidable-equality-is-finiteᵉ
    ( is-finite-decidable-subtype-is-finiteᵉ (is-finite-type-𝔽ᵉ Xᵉ))
```

### Decidable subtypes of finite types are finite

```agda
is-finite-type-decidable-subtypeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : decidable-subtypeᵉ l2ᵉ Xᵉ) →
    is-finiteᵉ Xᵉ → is-finiteᵉ (type-decidable-subtypeᵉ Pᵉ)
is-finite-type-decidable-subtypeᵉ Pᵉ Hᵉ =
  is-finite-Σᵉ Hᵉ
    ( λ xᵉ →
      is-finite-is-decidable-Propᵉ
        ( prop-Decidable-Propᵉ (Pᵉ xᵉ))
        ( is-decidable-Decidable-Propᵉ (Pᵉ xᵉ)))

is-finite-type-subset-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Pᵉ : subset-𝔽ᵉ l2ᵉ Xᵉ) →
  is-finiteᵉ (type-subset-𝔽ᵉ Xᵉ Pᵉ)
is-finite-type-subset-𝔽ᵉ Xᵉ Pᵉ =
  is-finite-type-decidable-subtypeᵉ Pᵉ (is-finite-type-𝔽ᵉ Xᵉ)

finite-type-subset-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) → subset-𝔽ᵉ l2ᵉ Xᵉ → 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (finite-type-subset-𝔽ᵉ Xᵉ Pᵉ) = type-subset-𝔽ᵉ Xᵉ Pᵉ
pr2ᵉ (finite-type-subset-𝔽ᵉ Xᵉ Pᵉ) = is-finite-type-subset-𝔽ᵉ Xᵉ Pᵉ
```

### The underlying type of a decidable subtype has decidable equality

```agda
has-decidable-equality-type-decidable-subtype-is-finiteᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : decidable-subtypeᵉ l2ᵉ Xᵉ) → is-finiteᵉ Xᵉ →
  has-decidable-equalityᵉ (type-decidable-subtypeᵉ Pᵉ)
has-decidable-equality-type-decidable-subtype-is-finiteᵉ Pᵉ Hᵉ =
  has-decidable-equality-is-finiteᵉ (is-finite-type-decidable-subtypeᵉ Pᵉ Hᵉ)

has-decidable-equality-type-subset-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Pᵉ : subset-𝔽ᵉ l2ᵉ Xᵉ) →
  has-decidable-equalityᵉ (type-subset-𝔽ᵉ Xᵉ Pᵉ)
has-decidable-equality-type-subset-𝔽ᵉ Xᵉ Pᵉ =
  has-decidable-equality-is-finiteᵉ (is-finite-type-subset-𝔽ᵉ Xᵉ Pᵉ)
```

### The underlying type of a decidable subtype of a finite type is a set

```agda
is-set-type-subset-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Pᵉ : subset-𝔽ᵉ l2ᵉ Xᵉ) → is-setᵉ (type-subset-𝔽ᵉ Xᵉ Pᵉ)
is-set-type-subset-𝔽ᵉ Xᵉ Pᵉ = is-set-type-decidable-subtypeᵉ Pᵉ (is-set-type-𝔽ᵉ Xᵉ)

set-subset-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Pᵉ : subset-𝔽ᵉ l2ᵉ Xᵉ) → Setᵉ (l1ᵉ ⊔ l2ᵉ)
set-subset-𝔽ᵉ Xᵉ Pᵉ = set-decidable-subsetᵉ (set-𝔽ᵉ Xᵉ) Pᵉ
```

### The number of elements of a decidable subtype of a finite type is smaller than the number of elements of the ambient type

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Pᵉ : subset-𝔽ᵉ l2ᵉ Xᵉ)
  where

  number-of-elements-subset-𝔽ᵉ : ℕᵉ
  number-of-elements-subset-𝔽ᵉ = number-of-elements-𝔽ᵉ (finite-type-subset-𝔽ᵉ Xᵉ Pᵉ)
```

### A subtype `S` over a type `A` with decidable equalities such that the underlying type generated by `S` is finite is a decidable subtype

```agda
is-decidable-subtype-is-finite-has-decidable-eqᵉ :
  {l1ᵉ l2ᵉ : Level} → {Aᵉ : UUᵉ l1ᵉ} → (Sᵉ : subtypeᵉ l2ᵉ Aᵉ) →
  has-decidable-equalityᵉ Aᵉ → is-finiteᵉ (type-subtypeᵉ Sᵉ) →
  is-decidable-subtypeᵉ Sᵉ
is-decidable-subtype-is-finite-has-decidable-eqᵉ Sᵉ dec-Aᵉ fin-Sᵉ aᵉ =
  apply-universal-property-trunc-Propᵉ
    ( fin-Sᵉ)
    ( is-decidable-Propᵉ (Sᵉ aᵉ))
    ( λ count-Sᵉ →
      rec-coproductᵉ
        ( λ xᵉ → inlᵉ (trᵉ (type-Propᵉ ∘ᵉ Sᵉ) (invᵉ (pr2ᵉ xᵉ)) (pr2ᵉ (pr1ᵉ xᵉ))))
        ( λ xᵉ → inrᵉ λ S-aᵉ → xᵉ (( (aᵉ ,ᵉ S-aᵉ) ,ᵉ reflᵉ)))
        ( is-decidable-Σ-countᵉ count-Sᵉ λ sᵉ → dec-Aᵉ aᵉ (pr1ᵉ sᵉ)))
```