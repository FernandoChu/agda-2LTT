# Postcomposition of pointed maps

```agda
module structured-types.postcomposition-pointed-mapsᵉ where
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
{{#conceptᵉ "postcompositionᵉ operation"ᵉ Disambiguation="pointedᵉ maps"ᵉ Agda=postcomp-pointed-mapᵉ}}
onᵉ [pointedᵉ maps](structured-types.pointed-maps.mdᵉ) byᵉ aᵉ pointedᵉ mapᵉ
`fᵉ : Aᵉ →∗ᵉ B`ᵉ isᵉ aᵉ familyᵉ ofᵉ operationsᵉ

```text
  fᵉ ∘∗ᵉ -ᵉ : (Xᵉ →∗ᵉ Aᵉ) → (Xᵉ →∗ᵉ Bᵉ)
```

indexedᵉ byᵉ aᵉ [pointedᵉ type](structured-types.pointed-types.mdᵉ) `X`.ᵉ

## Definitions

### Postcomposition by pointed maps

```agda
postcomp-pointed-mapᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  (Xᵉ : Pointed-Typeᵉ l3ᵉ) → (Xᵉ →∗ᵉ Aᵉ) → (Xᵉ →∗ᵉ Bᵉ)
postcomp-pointed-mapᵉ fᵉ Xᵉ gᵉ = comp-pointed-mapᵉ fᵉ gᵉ
```