# Total partial elements

```agda
module foundation.total-partial-elementsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.partial-elementsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [partialᵉ element](foundation.partial-elements.mdᵉ) `a`ᵉ ofᵉ `A`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "total"ᵉ Disambiguation="partialᵉ element"ᵉ Agda=total-partial-elementᵉ}}
ifᵉ itᵉ isᵉ defined.ᵉ Theᵉ typeᵉ ofᵉ totalᵉ partialᵉ elementsᵉ ofᵉ `A`ᵉ isᵉ
[equivalent](foundation-core.equivalences.mdᵉ) to theᵉ typeᵉ `A`.ᵉ

## Definitions

### The type of total partial elements

```agda
total-partial-elementᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
total-partial-elementᵉ l2ᵉ Aᵉ =
  Σᵉ (partial-elementᵉ l2ᵉ Aᵉ) is-defined-partial-elementᵉ
```