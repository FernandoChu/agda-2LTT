# Span diagrams on families of types

```agda
module foundation.span-diagrams-families-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.spans-families-of-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "spanᵉ diagram"ᵉ Disambiguation="familyᵉ ofᵉ types"ᵉ}} onᵉ aᵉ familyᵉ ofᵉ
typesᵉ indexedᵉ byᵉ aᵉ typeᵉ `I`ᵉ consistsᵉ ofᵉ aᵉ typeᵉ familyᵉ `Aᵉ : Iᵉ → 𝒰`,ᵉ andᵉ aᵉ
[span](foundation.spans-families-of-types.mdᵉ) onᵉ theᵉ typeᵉ familyᵉ `A`.ᵉ Moreᵉ
explicitly,ᵉ aᵉ spanᵉ diagramᵉ onᵉ aᵉ familyᵉ ofᵉ typesᵉ indexedᵉ byᵉ `I`ᵉ consistsᵉ ofᵉ aᵉ
typeᵉ familyᵉ `Aᵉ : Iᵉ → 𝒰`,ᵉ aᵉ
{{#conceptᵉ "spanningᵉ type"ᵉ Disambiguation="spanᵉ diagramᵉ onᵉ aᵉ familyᵉ ofᵉ types"ᵉ}}
`S`,ᵉ andᵉ aᵉ familyᵉ ofᵉ mapsᵉ `fᵉ : (iᵉ : Iᵉ) → Sᵉ → Aᵉ i`.ᵉ

## Definitions

### Span diagrams of families of types

```agda
span-diagram-type-familyᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
span-diagram-type-familyᵉ l2ᵉ l3ᵉ Iᵉ =
  Σᵉ (Iᵉ → UUᵉ l2ᵉ) (λ Aᵉ → span-type-familyᵉ l3ᵉ Aᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (sᵉ : span-diagram-type-familyᵉ l2ᵉ l3ᵉ Iᵉ)
  where

  family-span-diagram-type-familyᵉ : Iᵉ → UUᵉ l2ᵉ
  family-span-diagram-type-familyᵉ = pr1ᵉ sᵉ

  span-span-diagram-type-familyᵉ :
    span-type-familyᵉ l3ᵉ family-span-diagram-type-familyᵉ
  span-span-diagram-type-familyᵉ = pr2ᵉ sᵉ

  spanning-type-span-diagram-type-familyᵉ : UUᵉ l3ᵉ
  spanning-type-span-diagram-type-familyᵉ =
    spanning-type-span-type-familyᵉ
      ( span-span-diagram-type-familyᵉ)

  map-span-diagram-type-familyᵉ :
    (iᵉ : Iᵉ) → spanning-type-span-diagram-type-familyᵉ →
    family-span-diagram-type-familyᵉ iᵉ
  map-span-diagram-type-familyᵉ =
    map-span-type-familyᵉ
      ( span-span-diagram-type-familyᵉ)
```