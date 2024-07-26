# Retracts of types

```agda
module foundation-core.retracts-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.postcomposition-functionsᵉ
open import foundation-core.precomposition-functionsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
```

</details>

## Idea

Weᵉ sayᵉ thatᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ
{{#conceptᵉ "retract"ᵉ Disambiguation="ofᵉ types"ᵉ Agda=retractsᵉ}} ofᵉ aᵉ typeᵉ `B`ᵉ ifᵉ
theᵉ typesᵉ `A`ᵉ andᵉ `B`ᵉ comeᵉ equippedᵉ with
{{#conceptᵉ "retractᵉ data"ᵉ Disambiguation="ofᵉ types"ᵉ Agda=retract}},ᵉ i.e.,ᵉ with
mapsᵉ

```text
      iᵉ        rᵉ
  Aᵉ ----->ᵉ Bᵉ ----->ᵉ Aᵉ
```

suchᵉ thatᵉ `r`ᵉ isᵉ aᵉ [retraction](foundation-core.retractions.mdᵉ) ofᵉ `i`,ᵉ i.e.,ᵉ
thereᵉ isᵉ aᵉ [homotopy](foundation-core.homotopies.mdᵉ) `rᵉ ∘ᵉ iᵉ ~ᵉ id`.ᵉ Theᵉ mapᵉ `i`ᵉ
isᵉ calledᵉ theᵉ **inclusion**ᵉ ofᵉ theᵉ retractᵉ data,ᵉ andᵉ theᵉ mapᵉ `r`ᵉ isᵉ calledᵉ theᵉ
**underlyingᵉ mapᵉ ofᵉ theᵉ retraction**.ᵉ

## Definitions

### The type of witnesses that `A` is a retract of `B`

Theᵉ predicateᵉ `retractᵉ B`ᵉ isᵉ usedᵉ to assertᵉ thatᵉ aᵉ typeᵉ isᵉ aᵉ retractᵉ ofᵉ `B`,ᵉ
i.e.,ᵉ theᵉ typeᵉ `retractᵉ Bᵉ A`ᵉ isᵉ theᵉ typeᵉ ofᵉ mapsᵉ fromᵉ `A`ᵉ to `B`ᵉ thatᵉ comeᵉ
equippedᵉ with aᵉ retraction.ᵉ

Weᵉ alsoᵉ introduceᵉ moreᵉ intuitiveᵉ infix notationᵉ `Aᵉ retract-ofᵉ B`ᵉ to assertᵉ thatᵉ
`A`ᵉ isᵉ aᵉ retractᵉ ofᵉ `B`.ᵉ

```agda
retractᵉ : {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
retractᵉ Bᵉ Aᵉ = Σᵉ (Aᵉ → Bᵉ) (retractionᵉ)

infix 6 _retract-ofᵉ_

_retract-ofᵉ_ :
  {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
Aᵉ retract-ofᵉ Bᵉ = retractᵉ Bᵉ Aᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Rᵉ : retractᵉ Bᵉ Aᵉ)
  where

  inclusion-retractᵉ : Aᵉ → Bᵉ
  inclusion-retractᵉ = pr1ᵉ Rᵉ

  retraction-retractᵉ : retractionᵉ inclusion-retractᵉ
  retraction-retractᵉ = pr2ᵉ Rᵉ

  map-retraction-retractᵉ : Bᵉ → Aᵉ
  map-retraction-retractᵉ = map-retractionᵉ inclusion-retractᵉ retraction-retractᵉ

  is-retraction-map-retraction-retractᵉ :
    is-sectionᵉ map-retraction-retractᵉ inclusion-retractᵉ
  is-retraction-map-retraction-retractᵉ =
    is-retraction-map-retractionᵉ inclusion-retractᵉ retraction-retractᵉ

  section-retractᵉ : sectionᵉ map-retraction-retractᵉ
  pr1ᵉ section-retractᵉ = inclusion-retractᵉ
  pr2ᵉ section-retractᵉ = is-retraction-map-retraction-retractᵉ
```

### The type of retracts of a type

```agda
retractsᵉ : {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
retractsᵉ l2ᵉ Aᵉ = Σᵉ (UUᵉ l2ᵉ) (_retract-ofᵉ Aᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : retractsᵉ l2ᵉ Aᵉ)
  where

  type-retractsᵉ : UUᵉ l2ᵉ
  type-retractsᵉ = pr1ᵉ Rᵉ

  retract-retractsᵉ : type-retractsᵉ retract-ofᵉ Aᵉ
  retract-retractsᵉ = pr2ᵉ Rᵉ

  inclusion-retractsᵉ : type-retractsᵉ → Aᵉ
  inclusion-retractsᵉ = inclusion-retractᵉ retract-retractsᵉ

  retraction-retractsᵉ : retractionᵉ inclusion-retractsᵉ
  retraction-retractsᵉ = retraction-retractᵉ retract-retractsᵉ

  map-retraction-retractsᵉ : Aᵉ → type-retractsᵉ
  map-retraction-retractsᵉ = map-retraction-retractᵉ retract-retractsᵉ

  is-retraction-map-retraction-retractsᵉ :
    is-sectionᵉ map-retraction-retractsᵉ inclusion-retractsᵉ
  is-retraction-map-retraction-retractsᵉ =
    is-retraction-map-retraction-retractᵉ retract-retractsᵉ

  section-retractsᵉ : sectionᵉ map-retraction-retractsᵉ
  section-retractsᵉ = section-retractᵉ retract-retractsᵉ
```

## Properties

### If `A` is a retract of `B` with inclusion `i : A → B`, then `x ＝ y` is a retract of `i x ＝ i y` for any two elements `x y : A`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Rᵉ : Aᵉ retract-ofᵉ Bᵉ) (xᵉ yᵉ : Aᵉ)
  where

  retract-eqᵉ :
    (xᵉ ＝ᵉ yᵉ) retract-ofᵉ (inclusion-retractᵉ Rᵉ xᵉ ＝ᵉ inclusion-retractᵉ Rᵉ yᵉ)
  pr1ᵉ retract-eqᵉ = apᵉ (inclusion-retractᵉ Rᵉ)
  pr2ᵉ retract-eqᵉ = retraction-apᵉ (inclusion-retractᵉ Rᵉ) (retraction-retractᵉ Rᵉ)
```

### If `A` is a retract of `B` then `A → S` is a retract of `B → S` via precomposition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Rᵉ : Aᵉ retract-ofᵉ Bᵉ) (Sᵉ : UUᵉ l3ᵉ)
  where

  retract-precompᵉ :
    (Aᵉ → Sᵉ) retract-ofᵉ (Bᵉ → Sᵉ)
  pr1ᵉ retract-precompᵉ =
    precompᵉ (map-retraction-retractᵉ Rᵉ) Sᵉ
  pr1ᵉ (pr2ᵉ retract-precompᵉ) =
    precompᵉ (inclusion-retractᵉ Rᵉ) Sᵉ
  pr2ᵉ (pr2ᵉ retract-precompᵉ) hᵉ =
    eq-htpyᵉ (hᵉ ·lᵉ is-retraction-map-retraction-retractᵉ Rᵉ)
```

### If `A` is a retract of `B` then `S → A` is a retract of `S → B` via postcomposition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Sᵉ : UUᵉ l3ᵉ) (Rᵉ : Aᵉ retract-ofᵉ Bᵉ)
  where

  retract-postcompᵉ :
    (Sᵉ → Aᵉ) retract-ofᵉ (Sᵉ → Bᵉ)
  pr1ᵉ retract-postcompᵉ =
    postcompᵉ Sᵉ (inclusion-retractᵉ Rᵉ)
  pr1ᵉ (pr2ᵉ retract-postcompᵉ) =
    postcompᵉ Sᵉ (map-retraction-retractᵉ Rᵉ)
  pr2ᵉ (pr2ᵉ retract-postcompᵉ) hᵉ =
    eq-htpyᵉ (is-retraction-map-retraction-retractᵉ Rᵉ ·rᵉ hᵉ)
```

### Every type is a retract of itself

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  id-retractᵉ : Aᵉ retract-ofᵉ Aᵉ
  id-retractᵉ = (idᵉ ,ᵉ idᵉ ,ᵉ refl-htpyᵉ)
```

### Composition of retracts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  comp-retractᵉ : Bᵉ retract-ofᵉ Cᵉ → Aᵉ retract-ofᵉ Bᵉ → Aᵉ retract-ofᵉ Cᵉ
  pr1ᵉ (comp-retractᵉ rᵉ r'ᵉ) =
    inclusion-retractᵉ rᵉ ∘ᵉ inclusion-retractᵉ r'ᵉ
  pr2ᵉ (comp-retractᵉ rᵉ r'ᵉ) =
    retraction-compᵉ
      ( inclusion-retractᵉ rᵉ)
      ( inclusion-retractᵉ r'ᵉ)
      ( retraction-retractᵉ rᵉ)
      ( retraction-retractᵉ r'ᵉ)
```

## See also

-ᵉ [Retractsᵉ ofᵉ maps](foundation.retracts-of-maps.mdᵉ)