# Precomposition of pointed maps

```agda
module structured-types.precomposition-pointed-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "precompositionᵉ operation"ᵉ Disambiguation="pointedᵉ maps"ᵉ Agda=precomp-pointed-mapᵉ}}
onᵉ [pointedᵉ maps](structured-types.pointed-maps.mdᵉ) byᵉ aᵉ pointedᵉ mapᵉ
`fᵉ : Aᵉ →∗ᵉ B`ᵉ isᵉ aᵉ familyᵉ ofᵉ operationsᵉ

```text
  -ᵉ ∘∗ᵉ fᵉ : (Bᵉ →∗ᵉ Cᵉ) → (Aᵉ →∗ᵉ Cᵉ)
```

indexedᵉ byᵉ aᵉ [pointedᵉ type](structured-types.pointed-types.mdᵉ) `C`.ᵉ

## Definitions

### Precomposition by pointed maps

```agda
precomp-pointed-mapᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  (Cᵉ : Pointed-Typeᵉ l3ᵉ) → (Bᵉ →∗ᵉ Cᵉ) → (Aᵉ →∗ᵉ Cᵉ)
precomp-pointed-mapᵉ fᵉ Cᵉ gᵉ = comp-pointed-mapᵉ gᵉ fᵉ
```