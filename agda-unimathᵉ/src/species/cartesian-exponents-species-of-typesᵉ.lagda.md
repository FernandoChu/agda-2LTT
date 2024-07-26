# Cartesian exponents of species

```agda
module species.cartesian-exponents-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import species.species-of-typesᵉ
```

</details>

## Idea

Theᵉ **Cartesianᵉ exponent**ᵉ ofᵉ twoᵉ speciesᵉ `F`ᵉ andᵉ `G`ᵉ isᵉ theᵉ pointwiseᵉ exponentᵉ
ofᵉ `F`ᵉ andᵉ `G`.ᵉ

Noteᵉ thatᵉ weᵉ callᵉ suchᵉ exponentsᵉ cartesianᵉ to disambiguateᵉ fromᵉ otherᵉ notionsᵉ ofᵉ
exponents,ᵉ suchᵉ asᵉ
[Cauchyᵉ exponentials](species.cauchy-exponentials-species-of-types.md).ᵉ

## Definitions

### Cartesian exponents of species of types

```agda
function-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} →
  species-typesᵉ l1ᵉ l2ᵉ → species-typesᵉ l1ᵉ l3ᵉ → species-typesᵉ l1ᵉ (l2ᵉ ⊔ l3ᵉ)
function-species-typesᵉ Fᵉ Gᵉ Xᵉ = Fᵉ Xᵉ → Gᵉ Xᵉ
```