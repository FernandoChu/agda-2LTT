# Multiset-indexed dependent products of types

```agda
module trees.multiset-indexed-dependent-products-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ

open import trees.multisetsᵉ
open import trees.w-typesᵉ
```

</details>

## Idea

Considerᵉ aᵉ [multiset](trees.multisets.mdᵉ) `M`.ᵉ Thenᵉ `M`ᵉ canᵉ beᵉ seenᵉ asᵉ aᵉ towerᵉ
ofᵉ typeᵉ families,ᵉ viaᵉ theᵉ inclusionᵉ fromᵉ theᵉ typeᵉ ofᵉ allᵉ multisets,ᵉ whichᵉ areᵉ
theᵉ well-foundedᵉ trees,ᵉ intoᵉ theᵉ typeᵉ ofᵉ allᵉ trees.ᵉ

Thisᵉ leadsᵉ to theᵉ ideaᵉ thatᵉ weᵉ shouldᵉ beᵉ ableᵉ to takeᵉ theᵉ iteratedᵉ dependentᵉ
productᵉ ofᵉ thisᵉ towerᵉ ofᵉ typeᵉ families.ᵉ

## Definitions

### The iterated dependent product of types indexed by a multiset

```agda
iterated-Π-𝕍ᵉ : {lᵉ : Level} → ℕᵉ → 𝕍ᵉ lᵉ → UUᵉ lᵉ
iterated-Π-𝕍ᵉ zero-ℕᵉ (tree-𝕎ᵉ Xᵉ Yᵉ) = Xᵉ
iterated-Π-𝕍ᵉ (succ-ℕᵉ nᵉ) (tree-𝕎ᵉ Xᵉ Yᵉ) = (xᵉ : Xᵉ) → iterated-Π-𝕍ᵉ nᵉ (Yᵉ xᵉ)
```