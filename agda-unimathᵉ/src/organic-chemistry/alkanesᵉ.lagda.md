# Alkanes

```agda
module organic-chemistry.alkanesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import organic-chemistry.hydrocarbonsᵉ
open import organic-chemistry.saturated-carbonsᵉ
```

</details>

## Idea

Anᵉ **alkane**ᵉ isᵉ aᵉ hydrocarbonᵉ thatᵉ onlyᵉ hasᵉ saturatedᵉ carbons,ᵉ i.e.,ᵉ itᵉ doesᵉ
notᵉ haveᵉ anyᵉ doubleᵉ orᵉ tripleᵉ carbon-carbonᵉ bonds.ᵉ

## Definition

```agda
is-alkane-hydrocarbonᵉ : {l1ᵉ l2ᵉ : Level} → hydrocarbonᵉ l1ᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-alkane-hydrocarbonᵉ Hᵉ =
  (cᵉ : vertex-hydrocarbonᵉ Hᵉ) → is-saturated-carbon-hydrocarbonᵉ Hᵉ cᵉ
```