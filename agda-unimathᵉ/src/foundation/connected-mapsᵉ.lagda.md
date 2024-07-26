# Connected maps

```agda
module foundation.connected-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.precomposition-dependent-functionsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.truncationsᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-family-of-fibers-of-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.truncated-mapsᵉ
```

</details>

## Idea

Aᵉ mapᵉ isᵉ saidᵉ to beᵉ **`k`-connected**ᵉ ifᵉ itsᵉ
[fibers](foundation-core.fibers-of-maps.mdᵉ) areᵉ
[`k`-connectedᵉ types](foundation.connected-types.md).ᵉ

## Definitions

### Connected maps

```agda
is-connected-map-Propᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-connected-map-Propᵉ kᵉ {Bᵉ = Bᵉ} fᵉ =
  Π-Propᵉ Bᵉ (λ bᵉ → is-connected-Propᵉ kᵉ (fiberᵉ fᵉ bᵉ))

is-connected-mapᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-connected-mapᵉ kᵉ fᵉ = type-Propᵉ (is-connected-map-Propᵉ kᵉ fᵉ)

is-prop-is-connected-mapᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-propᵉ (is-connected-mapᵉ kᵉ fᵉ)
is-prop-is-connected-mapᵉ kᵉ fᵉ = is-prop-type-Propᵉ (is-connected-map-Propᵉ kᵉ fᵉ)
```

### The type of connected maps between two types

```agda
connected-mapᵉ : {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
connected-mapᵉ kᵉ Aᵉ Bᵉ = type-subtypeᵉ (is-connected-map-Propᵉ kᵉ {Aᵉ} {Bᵉ})

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  map-connected-mapᵉ : connected-mapᵉ kᵉ Aᵉ Bᵉ → Aᵉ → Bᵉ
  map-connected-mapᵉ = inclusion-subtypeᵉ (is-connected-map-Propᵉ kᵉ)

  is-connected-map-connected-mapᵉ :
    (fᵉ : connected-mapᵉ kᵉ Aᵉ Bᵉ) → is-connected-mapᵉ kᵉ (map-connected-mapᵉ fᵉ)
  is-connected-map-connected-mapᵉ =
    is-in-subtype-inclusion-subtypeᵉ (is-connected-map-Propᵉ kᵉ)

  emb-inclusion-connected-mapᵉ : connected-mapᵉ kᵉ Aᵉ Bᵉ ↪ᵉ (Aᵉ → Bᵉ)
  emb-inclusion-connected-mapᵉ = emb-subtypeᵉ (is-connected-map-Propᵉ kᵉ)

  htpy-connected-mapᵉ : (fᵉ gᵉ : connected-mapᵉ kᵉ Aᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-connected-mapᵉ fᵉ gᵉ = (map-connected-mapᵉ fᵉ) ~ᵉ (map-connected-mapᵉ gᵉ)

  refl-htpy-connected-mapᵉ : (fᵉ : connected-mapᵉ kᵉ Aᵉ Bᵉ) → htpy-connected-mapᵉ fᵉ fᵉ
  refl-htpy-connected-mapᵉ fᵉ = refl-htpyᵉ

  is-torsorial-htpy-connected-mapᵉ :
    (fᵉ : connected-mapᵉ kᵉ Aᵉ Bᵉ) → is-torsorialᵉ (htpy-connected-mapᵉ fᵉ)
  is-torsorial-htpy-connected-mapᵉ fᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-htpyᵉ (map-connected-mapᵉ fᵉ))
      ( is-prop-is-connected-mapᵉ kᵉ)
      ( map-connected-mapᵉ fᵉ)
      ( refl-htpy-connected-mapᵉ fᵉ)
      ( is-connected-map-connected-mapᵉ fᵉ)

  htpy-eq-connected-mapᵉ :
    (fᵉ gᵉ : connected-mapᵉ kᵉ Aᵉ Bᵉ) → fᵉ ＝ᵉ gᵉ → htpy-connected-mapᵉ fᵉ gᵉ
  htpy-eq-connected-mapᵉ fᵉ .fᵉ reflᵉ = refl-htpy-connected-mapᵉ fᵉ

  is-equiv-htpy-eq-connected-mapᵉ :
    (fᵉ gᵉ : connected-mapᵉ kᵉ Aᵉ Bᵉ) → is-equivᵉ (htpy-eq-connected-mapᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-connected-mapᵉ fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-connected-mapᵉ fᵉ)
      ( htpy-eq-connected-mapᵉ fᵉ)

  extensionality-connected-mapᵉ :
    (fᵉ gᵉ : connected-mapᵉ kᵉ Aᵉ Bᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-connected-mapᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-connected-mapᵉ fᵉ gᵉ) = htpy-eq-connected-mapᵉ fᵉ gᵉ
  pr2ᵉ (extensionality-connected-mapᵉ fᵉ gᵉ) = is-equiv-htpy-eq-connected-mapᵉ fᵉ gᵉ

  eq-htpy-connected-mapᵉ :
    (fᵉ gᵉ : connected-mapᵉ kᵉ Aᵉ Bᵉ) → htpy-connected-mapᵉ fᵉ gᵉ → (fᵉ ＝ᵉ gᵉ)
  eq-htpy-connected-mapᵉ fᵉ gᵉ =
    map-inv-equivᵉ (extensionality-connected-mapᵉ fᵉ gᵉ)
```

### The type of connected maps into a type

```agda
Connected-Mapᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (kᵉ : 𝕋ᵉ) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Connected-Mapᵉ l2ᵉ kᵉ Aᵉ = Σᵉ (UUᵉ l2ᵉ) (λ Xᵉ → connected-mapᵉ kᵉ Aᵉ Xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} (fᵉ : Connected-Mapᵉ l2ᵉ kᵉ Aᵉ)
  where

  type-Connected-Mapᵉ : UUᵉ l2ᵉ
  type-Connected-Mapᵉ = pr1ᵉ fᵉ

  connected-map-Connected-Mapᵉ : connected-mapᵉ kᵉ Aᵉ type-Connected-Mapᵉ
  connected-map-Connected-Mapᵉ = pr2ᵉ fᵉ

  map-Connected-Mapᵉ : Aᵉ → type-Connected-Mapᵉ
  map-Connected-Mapᵉ = map-connected-mapᵉ connected-map-Connected-Mapᵉ

  is-connected-map-Connected-Mapᵉ : is-connected-mapᵉ kᵉ map-Connected-Mapᵉ
  is-connected-map-Connected-Mapᵉ =
    is-connected-map-connected-mapᵉ connected-map-Connected-Mapᵉ
```

### The type of connected maps into a truncated type

```agda
Connected-Map-Into-Truncated-Typeᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (kᵉ lᵉ : 𝕋ᵉ) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Connected-Map-Into-Truncated-Typeᵉ l2ᵉ kᵉ lᵉ Aᵉ =
  Σᵉ (Truncated-Typeᵉ l2ᵉ lᵉ) (λ Xᵉ → connected-mapᵉ kᵉ Aᵉ (type-Truncated-Typeᵉ Xᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ lᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ}
  (fᵉ : Connected-Map-Into-Truncated-Typeᵉ l2ᵉ kᵉ lᵉ Aᵉ)
  where

  truncated-type-Connected-Map-Into-Truncated-Typeᵉ : Truncated-Typeᵉ l2ᵉ lᵉ
  truncated-type-Connected-Map-Into-Truncated-Typeᵉ = pr1ᵉ fᵉ

  type-Connected-Map-Into-Truncated-Typeᵉ : UUᵉ l2ᵉ
  type-Connected-Map-Into-Truncated-Typeᵉ =
    type-Truncated-Typeᵉ truncated-type-Connected-Map-Into-Truncated-Typeᵉ

  is-trunc-type-Connected-Map-Into-Truncated-Typeᵉ :
    is-truncᵉ lᵉ type-Connected-Map-Into-Truncated-Typeᵉ
  is-trunc-type-Connected-Map-Into-Truncated-Typeᵉ =
    is-trunc-type-Truncated-Typeᵉ
      truncated-type-Connected-Map-Into-Truncated-Typeᵉ

  connected-map-Connected-Map-Into-Truncated-Typeᵉ :
    connected-mapᵉ kᵉ Aᵉ type-Connected-Map-Into-Truncated-Typeᵉ
  connected-map-Connected-Map-Into-Truncated-Typeᵉ = pr2ᵉ fᵉ

  map-Connected-Map-Into-Truncated-Typeᵉ :
    Aᵉ → type-Connected-Map-Into-Truncated-Typeᵉ
  map-Connected-Map-Into-Truncated-Typeᵉ =
    map-connected-mapᵉ connected-map-Connected-Map-Into-Truncated-Typeᵉ

  is-connected-map-Connected-Map-Into-Truncated-Typeᵉ :
    is-connected-mapᵉ kᵉ map-Connected-Map-Into-Truncated-Typeᵉ
  is-connected-map-Connected-Map-Into-Truncated-Typeᵉ =
    is-connected-map-connected-mapᵉ
      connected-map-Connected-Map-Into-Truncated-Typeᵉ
```

## Properties

### All maps are `(-2)`-connected

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-neg-two-connected-mapᵉ : is-connected-mapᵉ neg-two-𝕋ᵉ fᵉ
  is-neg-two-connected-mapᵉ bᵉ = is-neg-two-connectedᵉ (fiberᵉ fᵉ bᵉ)
```

### Equivalences are `k`-connected for any `k`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-connected-map-is-equivᵉ :
    {fᵉ : Aᵉ → Bᵉ} → is-equivᵉ fᵉ → is-connected-mapᵉ kᵉ fᵉ
  is-connected-map-is-equivᵉ Hᵉ bᵉ =
    is-connected-is-contrᵉ kᵉ (is-contr-map-is-equivᵉ Hᵉ bᵉ)

  is-connected-map-equivᵉ :
    (eᵉ : Aᵉ ≃ᵉ Bᵉ) → is-connected-mapᵉ kᵉ (map-equivᵉ eᵉ)
  is-connected-map-equivᵉ eᵉ =
    is-connected-map-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)

  connected-map-equivᵉ :
    (Aᵉ ≃ᵉ Bᵉ) → connected-mapᵉ kᵉ Aᵉ Bᵉ
  pr1ᵉ (connected-map-equivᵉ eᵉ) = map-equivᵉ eᵉ
  pr2ᵉ (connected-map-equivᵉ eᵉ) = is-connected-map-equivᵉ eᵉ
```

### A `(k+1)`-connected map is `k`-connected

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  is-connected-map-is-connected-map-succ-𝕋ᵉ :
    is-connected-mapᵉ (succ-𝕋ᵉ kᵉ) fᵉ → is-connected-mapᵉ kᵉ fᵉ
  is-connected-map-is-connected-map-succ-𝕋ᵉ Hᵉ bᵉ =
    is-connected-is-connected-succ-𝕋ᵉ kᵉ (Hᵉ bᵉ)
```

### The composition of two `k`-connected maps is `k`-connected

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  is-connected-map-compᵉ :
    {gᵉ : Bᵉ → Cᵉ} {fᵉ : Aᵉ → Bᵉ} →
    is-connected-mapᵉ kᵉ gᵉ → is-connected-mapᵉ kᵉ fᵉ → is-connected-mapᵉ kᵉ (gᵉ ∘ᵉ fᵉ)
  is-connected-map-compᵉ Kᵉ Hᵉ cᵉ =
    is-connected-equivᵉ
      ( compute-fiber-compᵉ _ _ cᵉ)
      ( is-connected-Σᵉ kᵉ (Kᵉ cᵉ) (Hᵉ ∘ᵉ pr1ᵉ))

  comp-connected-mapᵉ :
    connected-mapᵉ kᵉ Bᵉ Cᵉ → connected-mapᵉ kᵉ Aᵉ Bᵉ → connected-mapᵉ kᵉ Aᵉ Cᵉ
  pr1ᵉ (comp-connected-mapᵉ gᵉ fᵉ) =
    map-connected-mapᵉ gᵉ ∘ᵉ map-connected-mapᵉ fᵉ
  pr2ᵉ (comp-connected-mapᵉ gᵉ fᵉ) =
    is-connected-map-compᵉ
      ( is-connected-map-connected-mapᵉ gᵉ)
      ( is-connected-map-connected-mapᵉ fᵉ)
```

### The total map induced by a family of maps is `k`-connected if and only if all maps in the family are `k`-connected

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ)
  where

  is-connected-map-tot-is-fiberwise-connected-mapᵉ :
    ((xᵉ : Aᵉ) → is-connected-mapᵉ kᵉ (fᵉ xᵉ)) →
    is-connected-mapᵉ kᵉ (totᵉ fᵉ)
  is-connected-map-tot-is-fiberwise-connected-mapᵉ Hᵉ (xᵉ ,ᵉ yᵉ) =
    is-connected-equivᵉ (compute-fiber-totᵉ fᵉ (xᵉ ,ᵉ yᵉ)) (Hᵉ xᵉ yᵉ)

  is-fiberwise-connected-map-is-connected-map-totᵉ :
    is-connected-mapᵉ kᵉ (totᵉ fᵉ) →
    (xᵉ : Aᵉ) → is-connected-mapᵉ kᵉ (fᵉ xᵉ)
  is-fiberwise-connected-map-is-connected-map-totᵉ Hᵉ xᵉ yᵉ =
    is-connected-equivᵉ (inv-compute-fiber-totᵉ fᵉ (xᵉ ,ᵉ yᵉ)) (Hᵉ (xᵉ ,ᵉ yᵉ))
```

### Dependent universal property for connected maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  dependent-universal-property-connected-mapᵉ : UUωᵉ
  dependent-universal-property-connected-mapᵉ =
    {l3ᵉ : Level} (Pᵉ : Bᵉ → Truncated-Typeᵉ l3ᵉ kᵉ) →
    is-equivᵉ (precomp-Πᵉ fᵉ (λ bᵉ → type-Truncated-Typeᵉ (Pᵉ bᵉ)))

module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  dependent-universal-property-is-connected-mapᵉ :
    is-connected-mapᵉ kᵉ fᵉ → dependent-universal-property-connected-mapᵉ kᵉ fᵉ
  dependent-universal-property-is-connected-mapᵉ Hᵉ Pᵉ =
    is-equiv-precomp-Π-fiber-conditionᵉ
      ( λ bᵉ → is-equiv-diagonal-exponential-is-connectedᵉ (Pᵉ bᵉ) (Hᵉ bᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : connected-mapᵉ kᵉ Aᵉ Bᵉ)
  where

  equiv-dependent-universal-property-is-connected-mapᵉ :
    {l3ᵉ : Level} (Pᵉ : Bᵉ → Truncated-Typeᵉ l3ᵉ kᵉ) →
    ((bᵉ : Bᵉ) → type-Truncated-Typeᵉ (Pᵉ bᵉ)) ≃ᵉ
    ((aᵉ : Aᵉ) → type-Truncated-Typeᵉ (Pᵉ (map-connected-mapᵉ fᵉ aᵉ)))
  pr1ᵉ (equiv-dependent-universal-property-is-connected-mapᵉ Pᵉ) =
    precomp-Πᵉ (map-connected-mapᵉ fᵉ) (λ bᵉ → type-Truncated-Typeᵉ (Pᵉ bᵉ))
  pr2ᵉ (equiv-dependent-universal-property-is-connected-mapᵉ Pᵉ) =
    dependent-universal-property-is-connected-mapᵉ kᵉ
      ( is-connected-map-connected-mapᵉ fᵉ)
      ( Pᵉ)
```

### A map that satisfies the dependent universal property for connected maps is a connected map

**Proof:**ᵉ Considerᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ suchᵉ thatᵉ theᵉ precompositionᵉ functionᵉ

```text
  -ᵉ ∘ᵉ fᵉ : ((bᵉ : Bᵉ) → Pᵉ bᵉ) → ((aᵉ : Aᵉ) → Pᵉ (fᵉ aᵉ))
```

isᵉ anᵉ equivalenceᵉ forᵉ everyᵉ familyᵉ `P`ᵉ ofᵉ `k`-truncatedᵉ types.ᵉ Thenᵉ itᵉ followsᵉ
thatᵉ theᵉ precompositionᵉ functionᵉ

```text
  -ᵉ ∘ᵉ fᵉ : ((bᵉ : Bᵉ) → ∥fiberᵉ fᵉ b∥_kᵉ) → ((aᵉ : Aᵉ) → ∥fiberᵉ fᵉ (fᵉ a)∥_kᵉ)
```

isᵉ anᵉ equivalence.ᵉ Inᵉ particular,ᵉ theᵉ elementᵉ `λᵉ aᵉ → ηᵉ (aᵉ ,ᵉ refl)`ᵉ in theᵉ
codomainᵉ ofᵉ thisᵉ equivalenceᵉ inducesᵉ anᵉ elementᵉ `cᵉ bᵉ : ∥fiberᵉ fᵉ b∥_k`ᵉ forᵉ eachᵉ
`bᵉ : B`.ᵉ Weᵉ takeᵉ theseᵉ elementsᵉ asᵉ ourᵉ centersᵉ ofᵉ contraction.ᵉ Noteᵉ thatᵉ byᵉ
construction,ᵉ weᵉ haveᵉ anᵉ identificationᵉ `cᵉ (fᵉ aᵉ) ＝ᵉ ηᵉ (aᵉ ,ᵉ refl)`.ᵉ

Toᵉ constructᵉ aᵉ contractionᵉ ofᵉ `∥fiberᵉ fᵉ b∥_k`ᵉ forᵉ eachᵉ `bᵉ : B`,ᵉ weᵉ haveᵉ to showᵉ
thatᵉ

```text
  (bᵉ : Bᵉ) (uᵉ : ∥fiberᵉ fᵉ b∥_kᵉ) → cᵉ bᵉ ＝ᵉ u.ᵉ
```

Sinceᵉ theᵉ typeᵉ `cᵉ bᵉ ＝ᵉ u`ᵉ isᵉ `k`-truncated,ᵉ thisᵉ typeᵉ isᵉ equivalentᵉ to theᵉ typeᵉ
`(bᵉ : Bᵉ) (uᵉ : fiberᵉ fᵉ bᵉ) → cᵉ bᵉ ＝ᵉ ηᵉ u`.ᵉ Byᵉ reductionᵉ ofᵉ theᵉ universalᵉ
quantificationᵉ overᵉ theᵉ fibersᵉ weᵉ seeᵉ thatᵉ thisᵉ typeᵉ isᵉ equivalentᵉ to theᵉ typeᵉ

```text
  (aᵉ : Aᵉ) → cᵉ (fᵉ aᵉ) ＝ᵉ ηᵉ (aᵉ ,ᵉ refl).ᵉ
```

Thisᵉ identificationᵉ holdsᵉ byᵉ constructionᵉ ofᵉ `c`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  (Hᵉ : dependent-universal-property-connected-mapᵉ kᵉ fᵉ)
  where

  center-is-connected-map-dependent-universal-property-connected-mapᵉ :
    (bᵉ : Bᵉ) → type-truncᵉ kᵉ (fiberᵉ fᵉ bᵉ)
  center-is-connected-map-dependent-universal-property-connected-mapᵉ =
    map-inv-is-equivᵉ
      ( Hᵉ (λ bᵉ → truncᵉ kᵉ (fiberᵉ fᵉ bᵉ)))
      ( λ aᵉ → unit-truncᵉ (aᵉ ,ᵉ reflᵉ))

  compute-center-is-connected-map-dependent-universal-property-connected-mapᵉ :
    (aᵉ : Aᵉ) →
    center-is-connected-map-dependent-universal-property-connected-mapᵉ (fᵉ aᵉ) ＝ᵉ
    unit-truncᵉ (aᵉ ,ᵉ reflᵉ)
  compute-center-is-connected-map-dependent-universal-property-connected-mapᵉ =
    htpy-eqᵉ
      ( is-section-map-inv-is-equivᵉ
        ( Hᵉ (λ bᵉ → truncᵉ kᵉ (fiberᵉ fᵉ bᵉ)))
        ( λ aᵉ → unit-truncᵉ (aᵉ ,ᵉ reflᵉ)))

  contraction-is-connected-map-dependent-universal-property-connected-mapᵉ :
    (bᵉ : Bᵉ) (uᵉ : type-truncᵉ kᵉ (fiberᵉ fᵉ bᵉ)) →
    center-is-connected-map-dependent-universal-property-connected-mapᵉ bᵉ ＝ᵉ uᵉ
  contraction-is-connected-map-dependent-universal-property-connected-mapᵉ =
    map-Πᵉ
      ( λ bᵉ →
        function-dependent-universal-property-truncᵉ
          ( Id-Truncated-Type'ᵉ (truncᵉ kᵉ (fiberᵉ fᵉ bᵉ)) _))
      ( extend-lift-family-of-elements-fiberᵉ fᵉ
        ( λ bᵉ uᵉ → _ ＝ᵉ unit-truncᵉ uᵉ)
        ( compute-center-is-connected-map-dependent-universal-property-connected-mapᵉ))

  abstract
    is-connected-map-dependent-universal-property-connected-mapᵉ :
      is-connected-mapᵉ kᵉ fᵉ
    pr1ᵉ (is-connected-map-dependent-universal-property-connected-mapᵉ bᵉ) =
      center-is-connected-map-dependent-universal-property-connected-mapᵉ bᵉ
    pr2ᵉ (is-connected-map-dependent-universal-property-connected-mapᵉ bᵉ) =
      contraction-is-connected-map-dependent-universal-property-connected-mapᵉ bᵉ
```

### The map `unit-trunc {k}` is `k`-connected

```agda
module _
  {l1ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ}
  where

  is-connected-map-unit-truncᵉ :
    is-connected-mapᵉ kᵉ (unit-truncᵉ {kᵉ = kᵉ} {Aᵉ = Aᵉ})
  is-connected-map-unit-truncᵉ =
    is-connected-map-dependent-universal-property-connected-mapᵉ kᵉ
      dependent-universal-property-truncᵉ
```

### A map `f : A → B` is `k`-connected if and only if precomposing dependent functions into `k + n`-truncated types is an `n-2`-truncated map for all `n : ℕ`

```agda
is-trunc-map-precomp-Π-is-connected-mapᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ lᵉ nᵉ : 𝕋ᵉ) → kᵉ +𝕋ᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ nᵉ)) ＝ᵉ lᵉ →
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} → is-connected-mapᵉ kᵉ fᵉ →
  (Pᵉ : Bᵉ → Truncated-Typeᵉ l3ᵉ lᵉ) →
  is-trunc-mapᵉ
    ( nᵉ)
    ( precomp-Πᵉ fᵉ (λ bᵉ → type-Truncated-Typeᵉ (Pᵉ bᵉ)))
is-trunc-map-precomp-Π-is-connected-mapᵉ
  {l1ᵉ} {l2ᵉ} {l3ᵉ} kᵉ ._ neg-two-𝕋ᵉ reflᵉ {Aᵉ} {Bᵉ} Hᵉ Pᵉ =
  is-contr-map-is-equivᵉ
    ( dependent-universal-property-is-connected-mapᵉ kᵉ Hᵉ
      ( λ bᵉ →
        pairᵉ
          ( type-Truncated-Typeᵉ (Pᵉ bᵉ))
          ( is-trunc-eqᵉ
            ( right-unit-law-add-𝕋ᵉ kᵉ)
            ( is-trunc-type-Truncated-Typeᵉ (Pᵉ bᵉ)))))
is-trunc-map-precomp-Π-is-connected-mapᵉ kᵉ ._ (succ-𝕋ᵉ nᵉ) reflᵉ {Aᵉ} {Bᵉ} {fᵉ} Hᵉ Pᵉ =
  is-trunc-map-succ-precomp-Πᵉ
    ( λ gᵉ hᵉ →
      is-trunc-map-precomp-Π-is-connected-mapᵉ kᵉ _ nᵉ reflᵉ Hᵉ
        ( λ bᵉ →
          pairᵉ
            ( eq-valueᵉ gᵉ hᵉ bᵉ)
            ( is-trunc-eqᵉ
              ( right-successor-law-add-𝕋ᵉ kᵉ nᵉ)
              ( is-trunc-type-Truncated-Typeᵉ (Pᵉ bᵉ))
              ( gᵉ bᵉ)
              ( hᵉ bᵉ))))
```

### Characterization of the identity type of `Connected-Map l2 k A`

```agda
equiv-Connected-Mapᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} →
  (fᵉ gᵉ : Connected-Mapᵉ l2ᵉ kᵉ Aᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
equiv-Connected-Mapᵉ fᵉ gᵉ =
  Σᵉ ( type-Connected-Mapᵉ fᵉ ≃ᵉ type-Connected-Mapᵉ gᵉ)
    ( λ eᵉ → (map-equivᵉ eᵉ ∘ᵉ map-Connected-Mapᵉ fᵉ) ~ᵉ map-Connected-Mapᵉ gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} (fᵉ : Connected-Mapᵉ l2ᵉ kᵉ Aᵉ)
  where

  id-equiv-Connected-Mapᵉ : equiv-Connected-Mapᵉ fᵉ fᵉ
  pr1ᵉ id-equiv-Connected-Mapᵉ = id-equivᵉ
  pr2ᵉ id-equiv-Connected-Mapᵉ = refl-htpyᵉ

  is-torsorial-equiv-Connected-Mapᵉ :
    is-torsorialᵉ (equiv-Connected-Mapᵉ fᵉ)
  is-torsorial-equiv-Connected-Mapᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ (type-Connected-Mapᵉ fᵉ))
      ( pairᵉ (type-Connected-Mapᵉ fᵉ) id-equivᵉ)
      ( is-torsorial-htpy-connected-mapᵉ (connected-map-Connected-Mapᵉ fᵉ))

  equiv-eq-Connected-Mapᵉ :
    (gᵉ : Connected-Mapᵉ l2ᵉ kᵉ Aᵉ) → (fᵉ ＝ᵉ gᵉ) → equiv-Connected-Mapᵉ fᵉ gᵉ
  equiv-eq-Connected-Mapᵉ .fᵉ reflᵉ = id-equiv-Connected-Mapᵉ

  is-equiv-equiv-eq-Connected-Mapᵉ :
    (gᵉ : Connected-Mapᵉ l2ᵉ kᵉ Aᵉ) → is-equivᵉ (equiv-eq-Connected-Mapᵉ gᵉ)
  is-equiv-equiv-eq-Connected-Mapᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-Connected-Mapᵉ
      equiv-eq-Connected-Mapᵉ

  extensionality-Connected-Mapᵉ :
    (gᵉ : Connected-Mapᵉ l2ᵉ kᵉ Aᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ equiv-Connected-Mapᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-Connected-Mapᵉ gᵉ) = equiv-eq-Connected-Mapᵉ gᵉ
  pr2ᵉ (extensionality-Connected-Mapᵉ gᵉ) = is-equiv-equiv-eq-Connected-Mapᵉ gᵉ

  eq-equiv-Connected-Mapᵉ :
    (gᵉ : Connected-Mapᵉ l2ᵉ kᵉ Aᵉ) → equiv-Connected-Mapᵉ fᵉ gᵉ → (fᵉ ＝ᵉ gᵉ)
  eq-equiv-Connected-Mapᵉ gᵉ =
    map-inv-equivᵉ (extensionality-Connected-Mapᵉ gᵉ)
```

### Characterization of the identity type of `Connected-Map-Into-Truncated-Type l2 k A`

```agda
equiv-Connected-Map-Into-Truncated-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ lᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} →
  (fᵉ gᵉ : Connected-Map-Into-Truncated-Typeᵉ l2ᵉ kᵉ lᵉ Aᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
equiv-Connected-Map-Into-Truncated-Typeᵉ fᵉ gᵉ =
  Σᵉ ( type-Connected-Map-Into-Truncated-Typeᵉ fᵉ ≃ᵉ
      type-Connected-Map-Into-Truncated-Typeᵉ gᵉ)
    ( λ eᵉ →
      ( map-equivᵉ eᵉ ∘ᵉ map-Connected-Map-Into-Truncated-Typeᵉ fᵉ) ~ᵉ
      ( map-Connected-Map-Into-Truncated-Typeᵉ gᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ lᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ}
  (fᵉ : Connected-Map-Into-Truncated-Typeᵉ l2ᵉ kᵉ lᵉ Aᵉ)
  where

  id-equiv-Connected-Map-Into-Truncated-Typeᵉ :
    equiv-Connected-Map-Into-Truncated-Typeᵉ fᵉ fᵉ
  pr1ᵉ id-equiv-Connected-Map-Into-Truncated-Typeᵉ = id-equivᵉ
  pr2ᵉ id-equiv-Connected-Map-Into-Truncated-Typeᵉ = refl-htpyᵉ

  is-torsorial-equiv-Connected-Map-Into-Truncated-Typeᵉ :
    is-torsorialᵉ (equiv-Connected-Map-Into-Truncated-Typeᵉ fᵉ)
  is-torsorial-equiv-Connected-Map-Into-Truncated-Typeᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equiv-Truncated-Typeᵉ
        ( truncated-type-Connected-Map-Into-Truncated-Typeᵉ fᵉ))
      ( pairᵉ (truncated-type-Connected-Map-Into-Truncated-Typeᵉ fᵉ) id-equivᵉ)
      ( is-torsorial-htpy-connected-mapᵉ
        ( connected-map-Connected-Map-Into-Truncated-Typeᵉ fᵉ))

  equiv-eq-Connected-Map-Into-Truncated-Typeᵉ :
    (gᵉ : Connected-Map-Into-Truncated-Typeᵉ l2ᵉ kᵉ lᵉ Aᵉ) →
    (fᵉ ＝ᵉ gᵉ) → equiv-Connected-Map-Into-Truncated-Typeᵉ fᵉ gᵉ
  equiv-eq-Connected-Map-Into-Truncated-Typeᵉ .fᵉ reflᵉ =
    id-equiv-Connected-Map-Into-Truncated-Typeᵉ

  is-equiv-equiv-eq-Connected-Map-Into-Truncated-Typeᵉ :
    (gᵉ : Connected-Map-Into-Truncated-Typeᵉ l2ᵉ kᵉ lᵉ Aᵉ) →
    is-equivᵉ (equiv-eq-Connected-Map-Into-Truncated-Typeᵉ gᵉ)
  is-equiv-equiv-eq-Connected-Map-Into-Truncated-Typeᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-Connected-Map-Into-Truncated-Typeᵉ
      equiv-eq-Connected-Map-Into-Truncated-Typeᵉ

  extensionality-Connected-Map-Into-Truncated-Typeᵉ :
    (gᵉ : Connected-Map-Into-Truncated-Typeᵉ l2ᵉ kᵉ lᵉ Aᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ equiv-Connected-Map-Into-Truncated-Typeᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-Connected-Map-Into-Truncated-Typeᵉ gᵉ) =
    equiv-eq-Connected-Map-Into-Truncated-Typeᵉ gᵉ
  pr2ᵉ (extensionality-Connected-Map-Into-Truncated-Typeᵉ gᵉ) =
    is-equiv-equiv-eq-Connected-Map-Into-Truncated-Typeᵉ gᵉ

  eq-equiv-Connected-Map-Into-Truncated-Typeᵉ :
    (gᵉ : Connected-Map-Into-Truncated-Typeᵉ l2ᵉ kᵉ lᵉ Aᵉ) →
      equiv-Connected-Map-Into-Truncated-Typeᵉ fᵉ gᵉ → (fᵉ ＝ᵉ gᵉ)
  eq-equiv-Connected-Map-Into-Truncated-Typeᵉ gᵉ =
    map-inv-equivᵉ (extensionality-Connected-Map-Into-Truncated-Typeᵉ gᵉ)
```

### The type `Connected-Map-Into-Truncated-Type l2 k k A` is contractible

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#733](https://github.com/UniMath/agda-unimath/issues/733ᵉ)

### The type `Connected-Map-Into-Truncated-Type l2 k l A` is `k - l - 2`-truncated

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#733](https://github.com/UniMath/agda-unimath/issues/733ᵉ)