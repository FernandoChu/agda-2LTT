# Noncontractible types

```agda
module foundation.noncontractible-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.negationᵉ
```

</details>

## Idea

Aᵉ typeᵉ `X`ᵉ isᵉ noncontractibleᵉ ifᵉ itᵉ comesᵉ equippedᵉ with anᵉ elementᵉ ofᵉ typeᵉ
`¬ᵉ (is-contrᵉ X)`.ᵉ

## Definitions

### The negation of being contractible

```agda
is-not-contractibleᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
is-not-contractibleᵉ Xᵉ = ¬ᵉ (is-contrᵉ Xᵉ)
```

### A positive formulation of being noncontractible

Noncontractibilityᵉ isᵉ aᵉ moreᵉ positiveᵉ wayᵉ to proveᵉ thatᵉ aᵉ typeᵉ isᵉ notᵉ
contractible.ᵉ Whenᵉ `A`ᵉ isᵉ noncontractibleᵉ in theᵉ followingᵉ sense,ᵉ thenᵉ itᵉ isᵉ
apartᵉ fromᵉ theᵉ unitᵉ type.ᵉ

```agda
is-noncontractible'ᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → ℕᵉ → UUᵉ lᵉ
is-noncontractible'ᵉ Aᵉ zero-ℕᵉ = is-emptyᵉ Aᵉ
is-noncontractible'ᵉ Aᵉ (succ-ℕᵉ kᵉ) =
  Σᵉ Aᵉ (λ xᵉ → Σᵉ Aᵉ (λ yᵉ → is-noncontractible'ᵉ (xᵉ ＝ᵉ yᵉ) kᵉ))

is-noncontractibleᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → UUᵉ lᵉ
is-noncontractibleᵉ Aᵉ = Σᵉ ℕᵉ (is-noncontractible'ᵉ Aᵉ)
```

## Properties

### Empty types are not contractible

```agda
is-not-contractible-is-emptyᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → is-emptyᵉ Xᵉ → is-not-contractibleᵉ Xᵉ
is-not-contractible-is-emptyᵉ Hᵉ Cᵉ = Hᵉ (centerᵉ Cᵉ)

is-not-contractible-emptyᵉ : is-not-contractibleᵉ emptyᵉ
is-not-contractible-emptyᵉ = is-not-contractible-is-emptyᵉ idᵉ
```

### Noncontractible types are not contractible

```agda
is-not-contractible-is-noncontractibleᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → is-noncontractibleᵉ Xᵉ → is-not-contractibleᵉ Xᵉ
is-not-contractible-is-noncontractibleᵉ
  ( pairᵉ zero-ℕᵉ Hᵉ) = is-not-contractible-is-emptyᵉ Hᵉ
is-not-contractible-is-noncontractibleᵉ (pairᵉ (succ-ℕᵉ nᵉ) (pairᵉ xᵉ (pairᵉ yᵉ Hᵉ))) Cᵉ =
  is-not-contractible-is-noncontractibleᵉ (pairᵉ nᵉ Hᵉ) (is-prop-is-contrᵉ Cᵉ xᵉ yᵉ)
```