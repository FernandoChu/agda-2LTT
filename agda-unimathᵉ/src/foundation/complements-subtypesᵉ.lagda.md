# Complements of subtypes

```agda
module foundation.complements-subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-subtypesᵉ
open import foundation.full-subtypesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.unions-subtypesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.subtypesᵉ
```

</details>

## Idea

Theᵉ **complement**ᵉ ofᵉ aᵉ [subtype](foundation-core.subtypes.mdᵉ) `P`ᵉ ofᵉ `A`ᵉ
consistsᵉ ofᵉ theᵉ elementsᵉ thatᵉ areᵉ notᵉ in `P`.ᵉ

## Definition

### Complements of subtypes

```agda
complement-subtypeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → subtypeᵉ l2ᵉ Aᵉ → subtypeᵉ l2ᵉ Aᵉ
complement-subtypeᵉ Pᵉ xᵉ = neg-Propᵉ (Pᵉ xᵉ)
```

### Complements of decidable subtypes

```agda
complement-decidable-subtypeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → decidable-subtypeᵉ l2ᵉ Aᵉ → decidable-subtypeᵉ l2ᵉ Aᵉ
complement-decidable-subtypeᵉ Pᵉ xᵉ = neg-Decidable-Propᵉ (Pᵉ xᵉ)
```

## Properties

### The union of a subtype `P` with its complement is the full subtype if and only if `P` is a decidable subtype

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  is-full-union-subtype-complement-subtypeᵉ :
    (Pᵉ : subtypeᵉ l2ᵉ Aᵉ) → is-decidable-subtypeᵉ Pᵉ →
    is-full-subtypeᵉ (union-subtypeᵉ Pᵉ (complement-subtypeᵉ Pᵉ))
  is-full-union-subtype-complement-subtypeᵉ Pᵉ dᵉ xᵉ =
    unit-trunc-Propᵉ (dᵉ xᵉ)

  is-decidable-subtype-is-full-union-subtype-complement-subtypeᵉ :
    (Pᵉ : subtypeᵉ l2ᵉ Aᵉ) →
    is-full-subtypeᵉ (union-subtypeᵉ Pᵉ (complement-subtypeᵉ Pᵉ)) →
    is-decidable-subtypeᵉ Pᵉ
  is-decidable-subtype-is-full-union-subtype-complement-subtypeᵉ Pᵉ Hᵉ xᵉ =
    apply-universal-property-trunc-Propᵉ
      ( Hᵉ xᵉ)
      ( is-decidable-Propᵉ (Pᵉ xᵉ))
      ( idᵉ)

  is-full-union-subtype-complement-decidable-subtypeᵉ :
    (Pᵉ : decidable-subtypeᵉ l2ᵉ Aᵉ) →
    is-full-decidable-subtypeᵉ
      ( union-decidable-subtypeᵉ Pᵉ (complement-decidable-subtypeᵉ Pᵉ))
  is-full-union-subtype-complement-decidable-subtypeᵉ Pᵉ =
    is-full-union-subtype-complement-subtypeᵉ
      ( subtype-decidable-subtypeᵉ Pᵉ)
      ( is-decidable-decidable-subtypeᵉ Pᵉ)
```