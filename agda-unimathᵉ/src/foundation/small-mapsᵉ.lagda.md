# Small maps

```agda
module foundation.small-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.locally-small-typesᵉ
open import foundation.retracts-of-mapsᵉ
open import foundation.split-idempotent-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.small-typesᵉ
```

</details>

## Idea

Aᵉ mapᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "small"ᵉ Disambiguation="mapᵉ ofᵉ types"ᵉ Agda=is-small-mapᵉ}} ifᵉ itsᵉ
[fibers](foundation-core.fibers-of-maps.mdᵉ) areᵉ
[small](foundation-core.small-types.md).ᵉ

Moreᵉ specifically,ᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ _smallᵉ_ with respectᵉ to aᵉ universeᵉ `𝒰`ᵉ
if,ᵉ forᵉ everyᵉ `bᵉ : B`,ᵉ theᵉ fiberᵉ ofᵉ `f`ᵉ overᵉ `y`ᵉ

```text
  fiberᵉ fᵉ bᵉ ≐ᵉ Σᵉ (xᵉ : A),ᵉ (fᵉ xᵉ ＝ᵉ b),ᵉ
```

isᵉ [equivalent](foundation-core.equivalences.mdᵉ) to aᵉ typeᵉ in `𝒰`ᵉ thatᵉ mayᵉ varyᵉ
dependingᵉ onᵉ `b`.ᵉ

## Definition

```agda
is-small-mapᵉ :
  (lᵉ : Level) {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (Aᵉ → Bᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
is-small-mapᵉ lᵉ {Bᵉ = Bᵉ} fᵉ = (bᵉ : Bᵉ) → is-smallᵉ lᵉ (fiberᵉ fᵉ bᵉ)
```

## Properties

### Any map between small types is small

```agda
abstract
  is-small-fiberᵉ :
    {lᵉ l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-smallᵉ lᵉ Aᵉ → is-smallᵉ lᵉ Bᵉ → (bᵉ : Bᵉ) → is-smallᵉ lᵉ (fiberᵉ fᵉ bᵉ)
  is-small-fiberᵉ fᵉ Hᵉ Kᵉ bᵉ =
    is-small-Σᵉ Hᵉ (λ aᵉ → is-locally-small-is-smallᵉ Kᵉ (fᵉ aᵉ) bᵉ)
```

### Being a small map is a property

```agda
module _
  (lᵉ : Level) {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-prop-is-small-mapᵉ : is-propᵉ (is-small-mapᵉ lᵉ fᵉ)
    is-prop-is-small-mapᵉ = is-prop-Πᵉ (λ xᵉ → is-prop-is-smallᵉ lᵉ (fiberᵉ fᵉ xᵉ))

  is-small-map-Propᵉ : Propᵉ (lsuc lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  is-small-map-Propᵉ = is-small-mapᵉ lᵉ fᵉ ,ᵉ is-prop-is-small-mapᵉ
```

### Small maps are closed under retracts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ lᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  {fᵉ : Aᵉ → Bᵉ} {gᵉ : Xᵉ → Yᵉ} (Rᵉ : fᵉ retract-of-mapᵉ gᵉ)
  where

  is-small-map-retractᵉ : is-small-mapᵉ lᵉ gᵉ → is-small-mapᵉ lᵉ fᵉ
  is-small-map-retractᵉ is-small-gᵉ bᵉ =
    is-small-retractᵉ
      ( is-small-gᵉ (map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
      ( retract-fiber-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ)
```