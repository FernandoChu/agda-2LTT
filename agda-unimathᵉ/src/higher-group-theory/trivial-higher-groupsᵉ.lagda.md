# Trivial higher groups

```agda
module higher-group-theory.trivial-higher-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-groupsᵉ
```

</details>

## Idea

Aᵉ [higherᵉ group](higher-group-theory.higher-groups.mdᵉ) `G`ᵉ isᵉ **trivial**ᵉ ifᵉ itsᵉ
underlyingᵉ typeᵉ isᵉ contractible.ᵉ

## Definitions

### Trivial higher groups

```agda
module _
  {lᵉ : Level} (Gᵉ : ∞-Groupᵉ lᵉ)
  where

  is-trivial-prop-∞-Groupᵉ : Propᵉ lᵉ
  is-trivial-prop-∞-Groupᵉ = is-contr-Propᵉ (type-∞-Groupᵉ Gᵉ)

  is-trivial-∞-Groupᵉ : UUᵉ lᵉ
  is-trivial-∞-Groupᵉ = type-Propᵉ is-trivial-prop-∞-Groupᵉ

  is-property-is-trivial-∞-Groupᵉ : is-propᵉ (is-trivial-∞-Groupᵉ)
  is-property-is-trivial-∞-Groupᵉ = is-prop-type-Propᵉ is-trivial-prop-∞-Groupᵉ
```

### Higher groups with contractible classifying type

```agda
module _
  {lᵉ : Level} (Gᵉ : ∞-Groupᵉ lᵉ)
  where

  has-contractible-classifying-type-prop-∞-Groupᵉ : Propᵉ lᵉ
  has-contractible-classifying-type-prop-∞-Groupᵉ =
    is-contr-Propᵉ (classifying-type-∞-Groupᵉ Gᵉ)

  has-contractible-classifying-type-∞-Groupᵉ : UUᵉ lᵉ
  has-contractible-classifying-type-∞-Groupᵉ =
    type-Propᵉ has-contractible-classifying-type-prop-∞-Groupᵉ

  is-property-has-contractible-classifying-type-∞-Groupᵉ :
    is-propᵉ (has-contractible-classifying-type-∞-Groupᵉ)
  is-property-has-contractible-classifying-type-∞-Groupᵉ =
    is-prop-type-Propᵉ has-contractible-classifying-type-prop-∞-Groupᵉ
```

### The trivial higher group

```agda
trivial-∞-Groupᵉ : {lᵉ : Level} → ∞-Groupᵉ lᵉ
pr1ᵉ (pr1ᵉ (trivial-∞-Groupᵉ {lᵉ})) = raise-unitᵉ lᵉ
pr2ᵉ (pr1ᵉ trivial-∞-Groupᵉ) = raise-starᵉ
pr2ᵉ (trivial-∞-Groupᵉ {lᵉ}) =
  is-0-connected-is-contrᵉ (raise-unitᵉ lᵉ) is-contr-raise-unitᵉ

has-contractible-classifying-type-trivial-∞-Groupᵉ :
  {lᵉ : Level} → has-contractible-classifying-type-∞-Groupᵉ (trivial-∞-Groupᵉ {lᵉ})
has-contractible-classifying-type-trivial-∞-Groupᵉ = is-contr-raise-unitᵉ
```

## Properties

### Having contractible classifying type is equivalent to having contractible underlying type

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ