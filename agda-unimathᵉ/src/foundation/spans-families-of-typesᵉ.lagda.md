# Spans of families of types

```agda
module foundation.spans-families-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
```

</details>

## Idea

Considerᵉ aᵉ familyᵉ ofᵉ typesᵉ `Aᵉ i`ᵉ indexedᵉ byᵉ `iᵉ : I`.ᵉ Aᵉ
{{#conceptᵉ "span"ᵉ Disambiguation="familyᵉ ofᵉ types"ᵉ Agda=span-type-familyᵉ}} onᵉ
`A`ᵉ consistsᵉ ofᵉ aᵉ typeᵉ `S`ᵉ equippedᵉ with aᵉ familyᵉ ofᵉ mapsᵉ

```text
  (iᵉ : Iᵉ) → Sᵉ → Aᵉ i.ᵉ
```

Theᵉ typeᵉ `S`ᵉ isᵉ calledᵉ theᵉ
{{#conceptᵉ "spanningᵉ type"ᵉ Disambiguation="spanᵉ ofᵉ familyᵉ ofᵉ types"ᵉ Agda=spanning-type-span-type-familyᵉ}}
ofᵉ theᵉ span.ᵉ

## Definitions

### Spans on families of types

```agda
module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) {Iᵉ : UUᵉ l1ᵉ} (Aᵉ : Iᵉ → UUᵉ l2ᵉ)
  where

  span-type-familyᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  span-type-familyᵉ = Σᵉ (UUᵉ l3ᵉ) (λ Sᵉ → (iᵉ : Iᵉ) → Sᵉ → Aᵉ iᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ}
  (sᵉ : span-type-familyᵉ l3ᵉ Aᵉ)
  where

  spanning-type-span-type-familyᵉ : UUᵉ l3ᵉ
  spanning-type-span-type-familyᵉ = pr1ᵉ sᵉ

  map-span-type-familyᵉ :
    (iᵉ : Iᵉ) → spanning-type-span-type-familyᵉ → Aᵉ iᵉ
  map-span-type-familyᵉ = pr2ᵉ sᵉ
```

## See also

-ᵉ [(Binaryᵉ) spans](foundation.spans.mdᵉ)
-ᵉ [Spanᵉ diagramsᵉ onᵉ familiesᵉ ofᵉ types](foundation.span-diagrams-families-of-types.mdᵉ)
-ᵉ [Permutationsᵉ ofᵉ spansᵉ ofᵉ onᵉ familiesᵉ ofᵉ types](foundation.permutations-spans-families-of-types.mdᵉ)