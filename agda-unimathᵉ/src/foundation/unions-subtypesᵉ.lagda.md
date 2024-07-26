# Unions of subtypes

```agda
module foundation.unions-subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-subtypesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.disjunctionᵉ
open import foundation.large-locale-of-subtypesᵉ
open import foundation.powersetsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.subtypesᵉ

open import order-theory.least-upper-bounds-large-posetsᵉ
```

</details>

## Idea

Theᵉ **union**ᵉ ofᵉ twoᵉ [subtypes](foundation-core.subtypes.mdᵉ) `A`ᵉ andᵉ `B`ᵉ isᵉ theᵉ
subtypeᵉ thatᵉ containsᵉ theᵉ elementsᵉ thatᵉ areᵉ in `A`ᵉ orᵉ in `B`.ᵉ

## Definition

### Unions of subtypes

```agda
module _
  {lᵉ l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  union-subtypeᵉ : subtypeᵉ l1ᵉ Xᵉ → subtypeᵉ l2ᵉ Xᵉ → subtypeᵉ (l1ᵉ ⊔ l2ᵉ) Xᵉ
  union-subtypeᵉ Pᵉ Qᵉ xᵉ = (Pᵉ xᵉ) ∨ᵉ (Qᵉ xᵉ)
```

### Unions of decidable subtypes

```agda
  union-decidable-subtypeᵉ :
    decidable-subtypeᵉ l1ᵉ Xᵉ → decidable-subtypeᵉ l2ᵉ Xᵉ →
    decidable-subtypeᵉ (l1ᵉ ⊔ l2ᵉ) Xᵉ
  union-decidable-subtypeᵉ Pᵉ Qᵉ xᵉ = disjunction-Decidable-Propᵉ (Pᵉ xᵉ) (Qᵉ xᵉ)
```

### Unions of families of subtypes

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ}
  where

  union-family-of-subtypesᵉ :
    {Iᵉ : UUᵉ l2ᵉ} (Aᵉ : Iᵉ → subtypeᵉ l3ᵉ Xᵉ) → subtypeᵉ (l2ᵉ ⊔ l3ᵉ) Xᵉ
  union-family-of-subtypesᵉ = sup-powerset-Large-Localeᵉ

  is-least-upper-bound-union-family-of-subtypesᵉ :
    {Iᵉ : UUᵉ l2ᵉ} (Aᵉ : Iᵉ → subtypeᵉ l3ᵉ Xᵉ) →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( powerset-Large-Posetᵉ Xᵉ)
      ( Aᵉ)
      ( union-family-of-subtypesᵉ Aᵉ)
  is-least-upper-bound-union-family-of-subtypesᵉ =
    is-least-upper-bound-sup-powerset-Large-Localeᵉ
```

## Properties

### The union of families of subtypes preserves indexed inclusion

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Iᵉ : UUᵉ l2ᵉ}
  (Aᵉ : Iᵉ → subtypeᵉ l3ᵉ Xᵉ) (Bᵉ : Iᵉ → subtypeᵉ l4ᵉ Xᵉ)
  where

  preserves-order-union-family-of-subtypesᵉ :
    ((iᵉ : Iᵉ) → Aᵉ iᵉ ⊆ᵉ Bᵉ iᵉ) →
    union-family-of-subtypesᵉ Aᵉ ⊆ᵉ union-family-of-subtypesᵉ Bᵉ
  preserves-order-union-family-of-subtypesᵉ Hᵉ xᵉ pᵉ =
    apply-universal-property-trunc-Propᵉ pᵉ
      ( union-family-of-subtypesᵉ Bᵉ xᵉ)
      ( λ (iᵉ ,ᵉ qᵉ) → unit-trunc-Propᵉ (iᵉ ,ᵉ Hᵉ iᵉ xᵉ qᵉ))
```