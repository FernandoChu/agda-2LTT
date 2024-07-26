# Trivial concrete groups

```agda
module group-theory.trivial-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.truncation-levelsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ

open import higher-group-theory.trivial-higher-groupsᵉ
```

</details>

## Idea

Aᵉ [concreteᵉ group](group-theory.concrete-groups.mdᵉ) `G`ᵉ isᵉ **trivial**ᵉ ifᵉ itsᵉ
classifyingᵉ typeᵉ isᵉ contractible.ᵉ

## Definitions

### Trivial higher groups

```agda
module _
  {lᵉ : Level} (Gᵉ : Concrete-Groupᵉ lᵉ)
  where

  is-trivial-prop-Concrete-Groupᵉ : Propᵉ lᵉ
  is-trivial-prop-Concrete-Groupᵉ =
    is-trivial-prop-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ)

  is-trivial-Concrete-Groupᵉ : UUᵉ lᵉ
  is-trivial-Concrete-Groupᵉ = type-Propᵉ is-trivial-prop-Concrete-Groupᵉ

  is-property-is-trivial-Concrete-Groupᵉ : is-propᵉ (is-trivial-Concrete-Groupᵉ)
  is-property-is-trivial-Concrete-Groupᵉ =
    is-prop-type-Propᵉ is-trivial-prop-Concrete-Groupᵉ
```

### Higher groups with contractible classifying type

```agda
module _
  {lᵉ : Level} (Gᵉ : Concrete-Groupᵉ lᵉ)
  where

  has-contractible-classifying-type-prop-Concrete-Groupᵉ : Propᵉ lᵉ
  has-contractible-classifying-type-prop-Concrete-Groupᵉ =
    has-contractible-classifying-type-prop-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ)

  has-contractible-classifying-type-Concrete-Groupᵉ : UUᵉ lᵉ
  has-contractible-classifying-type-Concrete-Groupᵉ =
    type-Propᵉ has-contractible-classifying-type-prop-Concrete-Groupᵉ

  is-property-has-contractible-classifying-type-Concrete-Groupᵉ :
    is-propᵉ (has-contractible-classifying-type-Concrete-Groupᵉ)
  is-property-has-contractible-classifying-type-Concrete-Groupᵉ =
    is-prop-type-Propᵉ has-contractible-classifying-type-prop-Concrete-Groupᵉ
```

### The trivial concrete group

```agda
trivial-Concrete-Groupᵉ : {lᵉ : Level} → Concrete-Groupᵉ lᵉ
pr1ᵉ trivial-Concrete-Groupᵉ = trivial-∞-Groupᵉ
pr2ᵉ trivial-Concrete-Groupᵉ =
  is-trunc-is-contrᵉ (one-𝕋ᵉ) (is-contr-raise-unitᵉ) (raise-starᵉ) (raise-starᵉ)

has-contractible-classifying-type-trivial-Concrete-Groupᵉ :
  {lᵉ : Level} →
  has-contractible-classifying-type-Concrete-Groupᵉ (trivial-Concrete-Groupᵉ {lᵉ})
has-contractible-classifying-type-trivial-Concrete-Groupᵉ =
  has-contractible-classifying-type-trivial-∞-Groupᵉ
```

## Properties

### Having contractible classifying type is equivalent to having contractible underlying type

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ