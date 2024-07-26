# The universal property of pointed equivalences

```agda
module structured-types.universal-property-pointed-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.precomposition-pointed-mapsᵉ
```

</details>

## Idea

Analogousᵉ to theᵉ
[universalᵉ propertyᵉ ofᵉ equivalences](foundation.universal-property-equivalences.md),ᵉ
theᵉ
{{#conceptᵉ "universalᵉ propertyᵉ ofᵉ pointedᵉ equivalences"ᵉ Agda=universal-property-pointed-equivᵉ}}
assertsᵉ aboutᵉ aᵉ [pointedᵉ map](structured-types.pointed-maps.mdᵉ) `fᵉ : Aᵉ →∗ᵉ B`ᵉ
thatᵉ theᵉ
[precompositionᵉ function](structured-types.precomposition-pointed-maps.mdᵉ)

```text
  -ᵉ ∘∗ᵉ fᵉ : (Bᵉ →∗ᵉ Cᵉ) → (Aᵉ →∗ᵉ Cᵉ)
```

isᵉ anᵉ [equivalence](foundation.equivalences.mdᵉ) forᵉ everyᵉ
[pointedᵉ type](structured-types.pointed-types.mdᵉ) `C`.ᵉ

## Definitions

### The universal property of pointed equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  universal-property-pointed-equivᵉ : UUωᵉ
  universal-property-pointed-equivᵉ =
    {lᵉ : Level} (Cᵉ : Pointed-Typeᵉ lᵉ) → is-equivᵉ (precomp-pointed-mapᵉ fᵉ Cᵉ)
```