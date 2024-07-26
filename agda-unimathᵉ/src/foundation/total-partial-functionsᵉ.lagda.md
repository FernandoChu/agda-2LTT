# Total partial functions

```agda
module foundation.total-partial-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.partial-functionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ
```

</details>

## Idea

Aᵉ [partialᵉ function](foundation.partial-functions.mdᵉ) `fᵉ : Aᵉ → B`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "total"ᵉ Disambiguation="partialᵉ function"ᵉ Agda=is-total-partial-functionᵉ}}
ifᵉ theᵉ [partialᵉ element](foundation.partial-elements.mdᵉ) `fᵉ a`ᵉ ofᵉ `B`ᵉ isᵉ definedᵉ
forᵉ everyᵉ `aᵉ : A`.ᵉ Theᵉ typeᵉ ofᵉ totalᵉ partialᵉ functionsᵉ fromᵉ `A`ᵉ to `B`ᵉ isᵉ
[equivalent](foundation-core.equivalences.mdᵉ) to theᵉ typeᵉ ofᵉ
[functions](foundation-core.function-types.mdᵉ) fromᵉ `A`ᵉ to `B`.ᵉ

## Definitions

### The predicate of being a total partial function

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : partial-functionᵉ l3ᵉ Aᵉ Bᵉ)
  where

  is-total-prop-partial-functionᵉ : Propᵉ (l1ᵉ ⊔ l3ᵉ)
  is-total-prop-partial-functionᵉ =
    Π-Propᵉ Aᵉ (is-defined-prop-partial-functionᵉ fᵉ)

  is-total-partial-functionᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  is-total-partial-functionᵉ = type-Propᵉ is-total-prop-partial-functionᵉ
```

### The type of total partial functions

```agda
total-partial-functionᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
total-partial-functionᵉ l3ᵉ Aᵉ Bᵉ =
  Σᵉ (partial-functionᵉ l3ᵉ Aᵉ Bᵉ) is-total-partial-functionᵉ
```