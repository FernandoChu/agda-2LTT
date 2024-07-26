# Impredicative universes

```agda
module foundation.impredicative-universesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ
open import foundation-core.small-typesᵉ
```

</details>

## Idea

Aᵉ universeᵉ `𝒰`ᵉ isᵉ {{#conceptᵉ "impredicative"ᵉ}} ifᵉ theᵉ typeᵉ ofᵉ
[propositions](foundation-core.propositions.mdᵉ) in `𝒰`ᵉ isᵉ `𝒰`-small.ᵉ

## Definition

```agda
is-impredicative-UUᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
is-impredicative-UUᵉ lᵉ = is-smallᵉ lᵉ (Propᵉ lᵉ)
```

## See also

-ᵉ [Impredicativeᵉ encodingsᵉ ofᵉ theᵉ logicalᵉ operations](foundation.impredicative-encodings.mdᵉ)