# Permutations of spans of families of types

```agda
module foundation.permutations-spans-families-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.spans-families-of-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
```

</details>

## Idea

Permutationsᵉ ofᵉ spansᵉ ofᵉ familiesᵉ ofᵉ typesᵉ areᵉ aᵉ generalizationᵉ ofᵉ theᵉ
[opposite](foundation.opposite-spans.mdᵉ) ofᵉ aᵉ
[binaryᵉ span](foundation.spans.md).ᵉ Considerᵉ aᵉ
[span](foundation.spans-families-of-types.mdᵉ) `(Sᵉ ,ᵉ f)`ᵉ onᵉ aᵉ typeᵉ familyᵉ
`Aᵉ : Iᵉ → 𝒰`ᵉ andᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) `eᵉ : Iᵉ ≃ᵉ I`.ᵉ
Thenᵉ theᵉ {{#conceptᵉ "permutation"ᵉ Disambiguation="spansᵉ ofᵉ familiesᵉ ofᵉ types"ᵉ}}
isᵉ theᵉ spanᵉ `(Sᵉ ,ᵉ fᵉ ∘ᵉ e)`ᵉ onᵉ theᵉ typeᵉ familyᵉ `Aᵉ ∘ᵉ e`.ᵉ

## Definitions

### Permutations of spans of families of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ}
  where

  permutation-span-type-familyᵉ :
    (eᵉ : Iᵉ ≃ᵉ Iᵉ) → span-type-familyᵉ l3ᵉ Aᵉ →
    span-type-familyᵉ l3ᵉ (Aᵉ ∘ᵉ map-equivᵉ eᵉ)
  pr1ᵉ (permutation-span-type-familyᵉ eᵉ sᵉ) =
    spanning-type-span-type-familyᵉ sᵉ
  pr2ᵉ (permutation-span-type-familyᵉ eᵉ sᵉ) iᵉ =
    map-span-type-familyᵉ sᵉ (map-equivᵉ eᵉ iᵉ)
```