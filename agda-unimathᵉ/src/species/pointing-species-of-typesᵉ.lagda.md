# Pointing of species of types

```agda
module species.pointing-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-typesᵉ
```

</details>

## Idea

Aᵉ pointingᵉ ofᵉ aᵉ speciesᵉ ofᵉ typesᵉ `F`ᵉ isᵉ theᵉ speciesᵉ ofᵉ typesᵉ `F*`ᵉ givenᵉ byᵉ
`F*ᵉ Xᵉ :=ᵉ Xᵉ ×ᵉ (Fᵉ X)`.ᵉ Inᵉ otherᵉ words,ᵉ itᵉ isᵉ theᵉ speciesᵉ ofᵉ pointedᵉ `F`-structuresᵉ

## Definition

```agda
pointing-species-typesᵉ :
  {l1ᵉ l2ᵉ : Level} → species-typesᵉ l1ᵉ l2ᵉ → species-typesᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)
pointing-species-typesᵉ Fᵉ Xᵉ = Xᵉ ×ᵉ Fᵉ Xᵉ
```