# Derivatives of species

```agda
module species.derivatives-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-typesᵉ
```

</details>

## Idea

Whenᵉ weᵉ thinkᵉ ofᵉ aᵉ speciesᵉ ofᵉ typesᵉ asᵉ theᵉ coefficientsᵉ ofᵉ aᵉ formalᵉ powerᵉ
series,ᵉ theᵉ derivativeᵉ ofᵉ aᵉ speciesᵉ ofᵉ typesᵉ isᵉ theᵉ speciesᵉ ofᵉ typesᵉ
representingᵉ theᵉ derivativeᵉ ofᵉ thatᵉ formalᵉ powerᵉ series.ᵉ

## Definition

```agda
derivative-species-typesᵉ :
  {l1ᵉ l2ᵉ : Level} → species-typesᵉ l1ᵉ l2ᵉ → species-typesᵉ l1ᵉ l2ᵉ
derivative-species-typesᵉ Fᵉ Xᵉ = Fᵉ (Xᵉ +ᵉ unitᵉ)
```