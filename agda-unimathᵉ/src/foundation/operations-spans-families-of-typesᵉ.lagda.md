# Operations on spans of families of types

```agda
module foundation.operations-spans-families-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.spans-families-of-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
```

</details>

## Idea

Thisᵉ fileᵉ containsᵉ aᵉ collectionᵉ ofᵉ operationsᵉ thatᵉ produceᵉ newᵉ
[spansᵉ ofᵉ familiesᵉ ofᵉ types](foundation.spans-families-of-types.mdᵉ) fromᵉ givenᵉ
spansᵉ ofᵉ familiesᵉ ofᵉ types.ᵉ

## Definitions

### Concatenation of spans and families of maps

Considerᵉ aᵉ spanᵉ `𝒮ᵉ :=ᵉ (Sᵉ ,ᵉ s)`ᵉ onᵉ aᵉ familyᵉ ofᵉ typesᵉ `Aᵉ : Iᵉ → 𝒰`ᵉ andᵉ considerᵉ aᵉ
familyᵉ ofᵉ mapsᵉ `fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ i`.ᵉ Thenᵉ weᵉ canᵉ concatenateᵉ theᵉ spanᵉ `𝒮`ᵉ
with theᵉ familyᵉ ofᵉ mapsᵉ `f`ᵉ to obtainᵉ theᵉ spanᵉ `(Sᵉ ,ᵉ λ iᵉ → fᵉ iᵉ ∘ᵉ sᵉ i)`ᵉ onᵉ `B`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
  (𝒮ᵉ : span-type-familyᵉ l4ᵉ Aᵉ)
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ)
  where

  spanning-type-concat-span-hom-family-of-typesᵉ : UUᵉ l4ᵉ
  spanning-type-concat-span-hom-family-of-typesᵉ =
    spanning-type-span-type-familyᵉ 𝒮ᵉ

  map-concat-span-hom-family-of-typesᵉ :
    (iᵉ : Iᵉ) → spanning-type-concat-span-hom-family-of-typesᵉ → Bᵉ iᵉ
  map-concat-span-hom-family-of-typesᵉ iᵉ =
    fᵉ iᵉ ∘ᵉ map-span-type-familyᵉ 𝒮ᵉ iᵉ

  concat-span-hom-family-of-typesᵉ :
    span-type-familyᵉ l4ᵉ Bᵉ
  pr1ᵉ concat-span-hom-family-of-typesᵉ =
    spanning-type-concat-span-hom-family-of-typesᵉ
  pr2ᵉ concat-span-hom-family-of-typesᵉ =
    map-concat-span-hom-family-of-typesᵉ
```