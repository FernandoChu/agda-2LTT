# `k`-Equivalences

```agda
module foundation.truncation-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.connected-mapsᵉ
open import foundation.connected-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-truncationᵉ
open import foundation.identity-typesᵉ
open import foundation.precomposition-functions-into-subuniversesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.truncationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universal-property-truncationᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.precomposition-functionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.transport-along-identificationsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ saidᵉ to beᵉ aᵉ `k`-equivalenceᵉ ifᵉ theᵉ mapᵉ
`map-truncᵉ kᵉ fᵉ : truncᵉ kᵉ Aᵉ → truncᵉ kᵉ B`ᵉ isᵉ anᵉ equivalence.ᵉ

## Definition

```agda
is-truncation-equivalenceᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-truncation-equivalenceᵉ kᵉ fᵉ = is-equivᵉ (map-truncᵉ kᵉ fᵉ)

truncation-equivalenceᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
truncation-equivalenceᵉ kᵉ Aᵉ Bᵉ = Σᵉ (Aᵉ → Bᵉ) (is-truncation-equivalenceᵉ kᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (fᵉ : truncation-equivalenceᵉ kᵉ Aᵉ Bᵉ)
  where

  map-truncation-equivalenceᵉ : Aᵉ → Bᵉ
  map-truncation-equivalenceᵉ = pr1ᵉ fᵉ

  is-truncation-equivalence-truncation-equivalenceᵉ :
    is-truncation-equivalenceᵉ kᵉ map-truncation-equivalenceᵉ
  is-truncation-equivalence-truncation-equivalenceᵉ = pr2ᵉ fᵉ
```

## Properties

### A map `f : A → B` is a `k`-equivalence if and only if `- ∘ f : (B → X) → (A → X)` is an equivalence for every `k`-truncated type `X`

```agda
is-equiv-precomp-is-truncation-equivalenceᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-truncation-equivalenceᵉ kᵉ fᵉ →
  (Xᵉ : Truncated-Typeᵉ l3ᵉ kᵉ) → is-equivᵉ (precompᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))
is-equiv-precomp-is-truncation-equivalenceᵉ kᵉ fᵉ Hᵉ Xᵉ =
  is-equiv-bottom-is-equiv-top-squareᵉ
    ( precompᵉ unit-truncᵉ (type-Truncated-Typeᵉ Xᵉ))
    ( precompᵉ unit-truncᵉ (type-Truncated-Typeᵉ Xᵉ))
    ( precompᵉ (map-truncᵉ kᵉ fᵉ) (type-Truncated-Typeᵉ Xᵉ))
    ( precompᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))
    ( precomp-coherence-square-mapsᵉ
      ( unit-truncᵉ)
      ( fᵉ)
      ( map-truncᵉ kᵉ fᵉ)
      ( unit-truncᵉ)
      ( inv-htpyᵉ (coherence-square-map-truncᵉ kᵉ fᵉ))
      ( type-Truncated-Typeᵉ Xᵉ))
    ( is-truncation-truncᵉ Xᵉ)
    ( is-truncation-truncᵉ Xᵉ)
    ( is-equiv-precomp-is-equivᵉ (map-truncᵉ kᵉ fᵉ) Hᵉ (type-Truncated-Typeᵉ Xᵉ))

is-truncation-equivalence-is-equiv-precompᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  ( (lᵉ : Level) (Xᵉ : Truncated-Typeᵉ lᵉ kᵉ) →
    is-equivᵉ (precompᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))) →
  is-truncation-equivalenceᵉ kᵉ fᵉ
is-truncation-equivalence-is-equiv-precompᵉ kᵉ {Aᵉ} {Bᵉ} fᵉ Hᵉ =
  is-equiv-is-equiv-precomp-Truncated-Typeᵉ kᵉ
    ( truncᵉ kᵉ Aᵉ)
    ( truncᵉ kᵉ Bᵉ)
    ( map-truncᵉ kᵉ fᵉ)
    ( λ Xᵉ →
      is-equiv-top-is-equiv-bottom-squareᵉ
        ( precompᵉ unit-truncᵉ (type-Truncated-Typeᵉ Xᵉ))
        ( precompᵉ unit-truncᵉ (type-Truncated-Typeᵉ Xᵉ))
        ( precompᵉ (map-truncᵉ kᵉ fᵉ) (type-Truncated-Typeᵉ Xᵉ))
        ( precompᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))
        ( precomp-coherence-square-mapsᵉ
          ( unit-truncᵉ)
          ( fᵉ)
          ( map-truncᵉ kᵉ fᵉ)
          ( unit-truncᵉ)
          ( inv-htpyᵉ (coherence-square-map-truncᵉ kᵉ fᵉ))
          ( type-Truncated-Typeᵉ Xᵉ))
        ( is-truncation-truncᵉ Xᵉ)
        ( is-truncation-truncᵉ Xᵉ)
        ( Hᵉ _ Xᵉ))
```

### An equivalence is a `k`-equivalence for all `k`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-truncation-equivalence-is-equivᵉ :
    is-equivᵉ fᵉ → is-truncation-equivalenceᵉ kᵉ fᵉ
  is-truncation-equivalence-is-equivᵉ eᵉ = is-equiv-map-equiv-truncᵉ kᵉ (fᵉ ,ᵉ eᵉ)
```

### Every `k`-connected map is a `k`-equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-truncation-equivalence-is-connected-mapᵉ :
    is-connected-mapᵉ kᵉ fᵉ → is-truncation-equivalenceᵉ kᵉ fᵉ
  is-truncation-equivalence-is-connected-mapᵉ cᵉ =
    is-truncation-equivalence-is-equiv-precompᵉ kᵉ fᵉ
      ( λ lᵉ Xᵉ → dependent-universal-property-is-connected-mapᵉ kᵉ cᵉ (λ _ → Xᵉ))
```

### The `k`-equivalences are closed under composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  is-truncation-equivalence-compᵉ :
    (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ) →
    is-truncation-equivalenceᵉ kᵉ fᵉ →
    is-truncation-equivalenceᵉ kᵉ gᵉ →
    is-truncation-equivalenceᵉ kᵉ (gᵉ ∘ᵉ fᵉ)
  is-truncation-equivalence-compᵉ gᵉ fᵉ efᵉ egᵉ =
    is-equiv-htpyᵉ
      ( map-truncᵉ kᵉ gᵉ ∘ᵉ map-truncᵉ kᵉ fᵉ)
        ( preserves-comp-map-truncᵉ kᵉ gᵉ fᵉ)
      ( is-equiv-compᵉ (map-truncᵉ kᵉ gᵉ) (map-truncᵉ kᵉ fᵉ) efᵉ egᵉ)

  truncation-equivalence-compᵉ :
    truncation-equivalenceᵉ kᵉ Bᵉ Cᵉ →
    truncation-equivalenceᵉ kᵉ Aᵉ Bᵉ →
    truncation-equivalenceᵉ kᵉ Aᵉ Cᵉ
  pr1ᵉ (truncation-equivalence-compᵉ gᵉ fᵉ) =
    map-truncation-equivalenceᵉ kᵉ gᵉ ∘ᵉ map-truncation-equivalenceᵉ kᵉ fᵉ
  pr2ᵉ (truncation-equivalence-compᵉ gᵉ fᵉ) =
    is-truncation-equivalence-compᵉ
      ( map-truncation-equivalenceᵉ kᵉ gᵉ)
      ( map-truncation-equivalenceᵉ kᵉ fᵉ)
      ( is-truncation-equivalence-truncation-equivalenceᵉ kᵉ fᵉ)
      ( is-truncation-equivalence-truncation-equivalenceᵉ kᵉ gᵉ)
```

### The class of `k`-equivalences has the 3-for-2 property

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ) (eᵉ : is-truncation-equivalenceᵉ kᵉ (gᵉ ∘ᵉ fᵉ))
  where

  is-truncation-equivalence-left-factorᵉ :
    is-truncation-equivalenceᵉ kᵉ fᵉ → is-truncation-equivalenceᵉ kᵉ gᵉ
  is-truncation-equivalence-left-factorᵉ efᵉ =
    is-equiv-left-factorᵉ
      ( map-truncᵉ kᵉ gᵉ)
      ( map-truncᵉ kᵉ fᵉ)
      ( is-equiv-htpyᵉ
        ( map-truncᵉ kᵉ (gᵉ ∘ᵉ fᵉ))
        ( inv-htpyᵉ (preserves-comp-map-truncᵉ kᵉ gᵉ fᵉ)) eᵉ)
      ( efᵉ)

  is-truncation-equivalence-right-factorᵉ :
    is-truncation-equivalenceᵉ kᵉ gᵉ → is-truncation-equivalenceᵉ kᵉ fᵉ
  is-truncation-equivalence-right-factorᵉ egᵉ =
    is-equiv-right-factorᵉ
      ( map-truncᵉ kᵉ gᵉ)
      ( map-truncᵉ kᵉ fᵉ)
      ( egᵉ)
      ( is-equiv-htpyᵉ
        ( map-truncᵉ kᵉ (gᵉ ∘ᵉ fᵉ))
        ( inv-htpyᵉ (preserves-comp-map-truncᵉ kᵉ gᵉ fᵉ))
        ( eᵉ))
```

### Composing `k`-equivalences with equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  is-truncation-equivalence-is-equiv-is-truncation-equivalenceᵉ :
    (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ) →
    is-truncation-equivalenceᵉ kᵉ gᵉ →
    is-equivᵉ fᵉ →
    is-truncation-equivalenceᵉ kᵉ (gᵉ ∘ᵉ fᵉ)
  is-truncation-equivalence-is-equiv-is-truncation-equivalenceᵉ gᵉ fᵉ egᵉ efᵉ =
    is-truncation-equivalence-compᵉ gᵉ fᵉ
      ( is-truncation-equivalence-is-equivᵉ fᵉ efᵉ)
      ( egᵉ)

  is-truncation-equivalence-is-truncation-equivalence-is-equivᵉ :
    (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ) →
    is-equivᵉ gᵉ →
    is-truncation-equivalenceᵉ kᵉ fᵉ →
    is-truncation-equivalenceᵉ kᵉ (gᵉ ∘ᵉ fᵉ)
  is-truncation-equivalence-is-truncation-equivalence-is-equivᵉ gᵉ fᵉ egᵉ efᵉ =
    is-truncation-equivalence-compᵉ gᵉ fᵉ
      ( efᵉ)
      ( is-truncation-equivalence-is-equivᵉ gᵉ egᵉ)

  is-truncation-equivalence-equiv-is-truncation-equivalenceᵉ :
    (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ ≃ᵉ Bᵉ) →
    is-truncation-equivalenceᵉ kᵉ gᵉ →
    is-truncation-equivalenceᵉ kᵉ (gᵉ ∘ᵉ map-equivᵉ fᵉ)
  is-truncation-equivalence-equiv-is-truncation-equivalenceᵉ gᵉ fᵉ egᵉ =
    is-truncation-equivalence-is-equiv-is-truncation-equivalenceᵉ gᵉ
      ( map-equivᵉ fᵉ)
      ( egᵉ)
      ( is-equiv-map-equivᵉ fᵉ)

  is-truncation-equivalence-is-truncation-equivalence-equivᵉ :
    (gᵉ : Bᵉ ≃ᵉ Cᵉ) (fᵉ : Aᵉ → Bᵉ) →
    is-truncation-equivalenceᵉ kᵉ fᵉ →
    is-truncation-equivalenceᵉ kᵉ (map-equivᵉ gᵉ ∘ᵉ fᵉ)
  is-truncation-equivalence-is-truncation-equivalence-equivᵉ gᵉ fᵉ efᵉ =
    is-truncation-equivalence-is-truncation-equivalence-is-equivᵉ
      ( map-equivᵉ gᵉ)
      ( fᵉ)
      ( is-equiv-map-equivᵉ gᵉ)
      ( efᵉ)
```

### The map on dependent pair types induced by the unit of the `(k+1)`-truncation is a `k`-equivalence

Thisᵉ isᵉ anᵉ instance ofᵉ Lemmaᵉ 2.27ᵉ in {{#citeᵉ CORS20ᵉ}} listedᵉ below.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ}
  {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : (type-truncᵉ (succ-𝕋ᵉ kᵉ) Xᵉ) → UUᵉ l2ᵉ)
  where

  map-Σ-map-base-unit-truncᵉ :
    Σᵉ Xᵉ (Pᵉ ∘ᵉ unit-truncᵉ) → Σᵉ (type-truncᵉ (succ-𝕋ᵉ kᵉ) Xᵉ) Pᵉ
  map-Σ-map-base-unit-truncᵉ = map-Σ-map-baseᵉ unit-truncᵉ Pᵉ

  is-truncation-equivalence-map-Σ-map-base-unit-truncᵉ :
    is-truncation-equivalenceᵉ kᵉ map-Σ-map-base-unit-truncᵉ
  is-truncation-equivalence-map-Σ-map-base-unit-truncᵉ =
    is-truncation-equivalence-is-equiv-precompᵉ kᵉ
      ( map-Σ-map-base-unit-truncᵉ)
      ( λ lᵉ Xᵉ →
        is-equiv-equivᵉ
          ( equiv-ev-pairᵉ)
          ( equiv-ev-pairᵉ)
          ( refl-htpyᵉ)
          ( dependent-universal-property-truncᵉ
            ( λ tᵉ →
              ( ( Pᵉ tᵉ → type-Truncated-Typeᵉ Xᵉ) ,ᵉ
                ( is-trunc-succ-is-truncᵉ kᵉ
                  ( is-trunc-function-typeᵉ kᵉ
                    ( is-trunc-type-Truncated-Typeᵉ Xᵉ)))))))
```

### There is an `k`-equivalence between the fiber of a map and the fiber of its `(k+1)`-truncation

Thisᵉ isᵉ anᵉ instance ofᵉ Corollaryᵉ 2.29ᵉ in {{#citeᵉ CORS20}}.ᵉ

Weᵉ considerᵉ theᵉ followingᵉ compositionᵉ ofᵉ mapsᵉ

```text
   fiberᵉ fᵉ bᵉ = Σᵉ Aᵉ (λ aᵉ → fᵉ aᵉ = bᵉ)
             → Σᵉ Aᵉ (λ aᵉ → ∥ᵉ fᵉ aᵉ ＝ᵉ bᵉ ∥ᵉ)
             ≃ᵉ Σᵉ Aᵉ (λ aᵉ → | fᵉ aᵉ | = | bᵉ |
             ≃ᵉ Σᵉ Aᵉ (λ aᵉ → ∥ᵉ fᵉ ∥ᵉ | aᵉ | = | bᵉ |ᵉ)
             → Σᵉ ∥ᵉ Aᵉ ∥ᵉ (λ tᵉ → ∥ᵉ fᵉ ∥ᵉ tᵉ = | bᵉ |ᵉ)
             = fiberᵉ ∥ᵉ fᵉ ∥ᵉ | bᵉ |
```

where theᵉ firstᵉ andᵉ lastᵉ mapsᵉ areᵉ `k`-equivalences.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (bᵉ : Bᵉ)
  where

  fiber-map-trunc-fiberᵉ :
    fiberᵉ fᵉ bᵉ → fiberᵉ (map-truncᵉ (succ-𝕋ᵉ kᵉ) fᵉ) (unit-truncᵉ bᵉ)
  fiber-map-trunc-fiberᵉ =
    ( map-Σ-map-base-unit-truncᵉ
      ( λ tᵉ → map-truncᵉ (succ-𝕋ᵉ kᵉ) fᵉ tᵉ ＝ᵉ unit-truncᵉ bᵉ)) ∘ᵉ
    ( totᵉ
      ( λ aᵉ →
        ( concatᵉ (naturality-unit-truncᵉ (succ-𝕋ᵉ kᵉ) fᵉ aᵉ) (unit-truncᵉ bᵉ)) ∘ᵉ
        ( map-effectiveness-truncᵉ kᵉ (fᵉ aᵉ) bᵉ) ∘ᵉ
        ( unit-truncᵉ)))

  is-truncation-equivalence-fiber-map-trunc-fiberᵉ :
    is-truncation-equivalenceᵉ kᵉ fiber-map-trunc-fiberᵉ
  is-truncation-equivalence-fiber-map-trunc-fiberᵉ =
    is-truncation-equivalence-compᵉ
      ( map-Σ-map-base-unit-truncᵉ
        ( λ tᵉ → map-truncᵉ (succ-𝕋ᵉ kᵉ) fᵉ tᵉ ＝ᵉ unit-truncᵉ bᵉ))
      ( totᵉ
        ( λ aᵉ →
          ( concatᵉ (naturality-unit-truncᵉ (succ-𝕋ᵉ kᵉ) fᵉ aᵉ) (unit-truncᵉ bᵉ)) ∘ᵉ
          ( map-effectiveness-truncᵉ kᵉ (fᵉ aᵉ) bᵉ) ∘ᵉ
          ( unit-truncᵉ)))
      ( is-truncation-equivalence-is-truncation-equivalence-equivᵉ
        ( equiv-totᵉ
          ( λ aᵉ →
            ( equiv-concatᵉ
              ( naturality-unit-truncᵉ (succ-𝕋ᵉ kᵉ) fᵉ aᵉ)
              ( unit-truncᵉ bᵉ)) ∘eᵉ
            ( effectiveness-truncᵉ kᵉ (fᵉ aᵉ) bᵉ)))
        ( λ (aᵉ ,ᵉ pᵉ) → aᵉ ,ᵉ unit-truncᵉ pᵉ)
        ( is-equiv-map-equivᵉ (equiv-trunc-Σᵉ kᵉ)))
      ( is-truncation-equivalence-map-Σ-map-base-unit-truncᵉ
        ( λ tᵉ → map-truncᵉ (succ-𝕋ᵉ kᵉ) fᵉ tᵉ ＝ᵉ unit-truncᵉ bᵉ))

  truncation-equivalence-fiber-map-trunc-fiberᵉ :
    truncation-equivalenceᵉ kᵉ
      ( fiberᵉ fᵉ bᵉ)
      ( fiberᵉ (map-truncᵉ (succ-𝕋ᵉ kᵉ) fᵉ) (unit-truncᵉ bᵉ))
  pr1ᵉ truncation-equivalence-fiber-map-trunc-fiberᵉ = fiber-map-trunc-fiberᵉ
  pr2ᵉ truncation-equivalence-fiber-map-trunc-fiberᵉ =
    is-truncation-equivalence-fiber-map-trunc-fiberᵉ
```

### Being `k`-connected is invariant under `k`-equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-connected-is-truncation-equivalence-is-connectedᵉ :
    (fᵉ : Aᵉ → Bᵉ) → is-truncation-equivalenceᵉ kᵉ fᵉ →
    is-connectedᵉ kᵉ Bᵉ → is-connectedᵉ kᵉ Aᵉ
  is-connected-is-truncation-equivalence-is-connectedᵉ fᵉ eᵉ =
    is-contr-equivᵉ (type-truncᵉ kᵉ Bᵉ) (map-truncᵉ kᵉ fᵉ ,ᵉ eᵉ)

  is-connected-truncation-equivalence-is-connectedᵉ :
    truncation-equivalenceᵉ kᵉ Aᵉ Bᵉ → is-connectedᵉ kᵉ Bᵉ → is-connectedᵉ kᵉ Aᵉ
  is-connected-truncation-equivalence-is-connectedᵉ fᵉ =
    is-connected-is-truncation-equivalence-is-connectedᵉ
      ( map-truncation-equivalenceᵉ kᵉ fᵉ)
      ( is-truncation-equivalence-truncation-equivalenceᵉ kᵉ fᵉ)
```

### Every `(k+1)`-equivalence is `k`-connected

Thisᵉ isᵉ anᵉ instance ofᵉ Propositionᵉ 2.30ᵉ in {{#citeᵉ CORS20}}.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-connected-map-is-succ-truncation-equivalenceᵉ :
    is-truncation-equivalenceᵉ (succ-𝕋ᵉ kᵉ) fᵉ → is-connected-mapᵉ kᵉ fᵉ
  is-connected-map-is-succ-truncation-equivalenceᵉ eᵉ bᵉ =
    is-connected-truncation-equivalence-is-connectedᵉ
      ( truncation-equivalence-fiber-map-trunc-fiberᵉ fᵉ bᵉ)
      ( is-connected-is-contrᵉ kᵉ (is-contr-map-is-equivᵉ eᵉ (unit-truncᵉ bᵉ)))
```

### The codomain of a `k`-connected map is `(k+1)`-connected if its domain is `(k+1)`-connected

Thisᵉ followsᵉ partᵉ ofᵉ theᵉ proofᵉ ofᵉ Propositionᵉ 2.31ᵉ in {{#citeᵉ CORS20}}.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-trunc-fiber-map-trunc-is-succ-connectedᵉ :
    is-connectedᵉ (succ-𝕋ᵉ kᵉ) Aᵉ →
    (bᵉ : Bᵉ) →
    is-truncᵉ kᵉ (fiberᵉ (map-truncᵉ (succ-𝕋ᵉ kᵉ) fᵉ) (unit-truncᵉ bᵉ))
  is-trunc-fiber-map-trunc-is-succ-connectedᵉ cᵉ bᵉ =
    is-trunc-equivᵉ kᵉ
      ( map-truncᵉ (succ-𝕋ᵉ kᵉ) fᵉ (centerᵉ cᵉ) ＝ᵉ unit-truncᵉ bᵉ)
      ( left-unit-law-Σ-is-contrᵉ cᵉ (centerᵉ cᵉ))
      ( is-trunc-type-truncᵉ (map-truncᵉ (succ-𝕋ᵉ kᵉ) fᵉ (centerᵉ cᵉ)) (unit-truncᵉ bᵉ))

  is-succ-connected-is-connected-map-is-succ-connectedᵉ :
    is-connectedᵉ (succ-𝕋ᵉ kᵉ) Aᵉ →
    is-connected-mapᵉ kᵉ fᵉ →
    is-connectedᵉ (succ-𝕋ᵉ kᵉ) Bᵉ
  is-succ-connected-is-connected-map-is-succ-connectedᵉ cAᵉ cfᵉ =
    is-contr-is-equiv'ᵉ
      ( type-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ)
      ( map-truncᵉ (succ-𝕋ᵉ kᵉ) fᵉ)
      ( is-equiv-is-contr-mapᵉ
        ( λ tᵉ →
          apply-universal-property-trunc-Propᵉ
            ( is-surjective-is-truncationᵉ
              ( truncᵉ (succ-𝕋ᵉ kᵉ) Bᵉ)
              ( is-truncation-truncᵉ)
              ( tᵉ))
            ( is-contr-Propᵉ (fiberᵉ (map-truncᵉ (succ-𝕋ᵉ kᵉ) fᵉ) tᵉ))
            ( λ (bᵉ ,ᵉ pᵉ) →
              trᵉ
                ( λ sᵉ → is-contrᵉ (fiberᵉ (map-truncᵉ (succ-𝕋ᵉ kᵉ) fᵉ) sᵉ))
                ( pᵉ)
                ( is-contr-equiv'ᵉ
                  ( type-truncᵉ kᵉ (fiberᵉ fᵉ bᵉ))
                  ( ( inv-equivᵉ
                      ( equiv-unit-truncᵉ
                        ( fiberᵉ (map-truncᵉ (succ-𝕋ᵉ kᵉ) fᵉ) (unit-truncᵉ bᵉ) ,ᵉ
                          is-trunc-fiber-map-trunc-is-succ-connectedᵉ cAᵉ bᵉ))) ∘eᵉ
                    ( map-truncᵉ kᵉ (fiber-map-trunc-fiberᵉ fᵉ bᵉ) ,ᵉ
                      is-truncation-equivalence-fiber-map-trunc-fiberᵉ fᵉ bᵉ))
                  ( cfᵉ bᵉ)))))
      ( cAᵉ)
```

### If `g ∘ f` is `(k+1)`-connected, then `f` is `k`-connected if and only if `g` is `(k+1)`-connected

Thisᵉ isᵉ anᵉ instance ofᵉ Propositionᵉ 2.31ᵉ in {{#citeᵉ CORS20}}.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ) (cgfᵉ : is-connected-mapᵉ (succ-𝕋ᵉ kᵉ) (gᵉ ∘ᵉ fᵉ))
  where

  is-connected-map-right-factor-is-succ-connected-map-left-factorᵉ :
    is-connected-mapᵉ (succ-𝕋ᵉ kᵉ) gᵉ → is-connected-mapᵉ kᵉ fᵉ
  is-connected-map-right-factor-is-succ-connected-map-left-factorᵉ cgᵉ =
    is-connected-map-is-succ-truncation-equivalenceᵉ fᵉ
      ( is-truncation-equivalence-right-factorᵉ gᵉ fᵉ
        ( is-truncation-equivalence-is-connected-mapᵉ (gᵉ ∘ᵉ fᵉ) cgfᵉ)
        ( is-truncation-equivalence-is-connected-mapᵉ gᵉ cgᵉ))

  is-connected-map-right-factor-is-succ-connected-map-right-factorᵉ :
    is-connected-mapᵉ kᵉ fᵉ → is-connected-mapᵉ (succ-𝕋ᵉ kᵉ) gᵉ
  is-connected-map-right-factor-is-succ-connected-map-right-factorᵉ cfᵉ cᵉ =
    is-succ-connected-is-connected-map-is-succ-connectedᵉ
      ( pr1ᵉ)
      ( is-connected-equiv'ᵉ (compute-fiber-compᵉ gᵉ fᵉ cᵉ) (cgfᵉ cᵉ))
      ( λ pᵉ →
        is-connected-equivᵉ
          ( equiv-fiber-pr1ᵉ (fiberᵉ fᵉ ∘ᵉ pr1ᵉ) pᵉ)
          ( cfᵉ (pr1ᵉ pᵉ)))
```

### A `k`-equivalence with a section is `k`-connected

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-connected-map-is-truncation-equivalence-sectionᵉ :
    (kᵉ : 𝕋ᵉ) →
    sectionᵉ fᵉ → is-truncation-equivalenceᵉ kᵉ fᵉ → is-connected-mapᵉ kᵉ fᵉ
  is-connected-map-is-truncation-equivalence-sectionᵉ neg-two-𝕋ᵉ (sᵉ ,ᵉ hᵉ) eᵉ =
    is-neg-two-connected-mapᵉ fᵉ
  is-connected-map-is-truncation-equivalence-sectionᵉ (succ-𝕋ᵉ kᵉ) (sᵉ ,ᵉ hᵉ) eᵉ =
    is-connected-map-right-factor-is-succ-connected-map-right-factorᵉ fᵉ sᵉ
      ( is-connected-map-is-equivᵉ (is-equiv-htpyᵉ idᵉ hᵉ is-equiv-idᵉ))
      ( is-connected-map-is-succ-truncation-equivalenceᵉ sᵉ
        ( is-truncation-equivalence-right-factorᵉ fᵉ sᵉ
          ( is-truncation-equivalence-is-equivᵉ
            ( fᵉ ∘ᵉ sᵉ)
            ( is-equiv-htpyᵉ idᵉ hᵉ is-equiv-idᵉ))
          ( eᵉ)))
```

## References

-ᵉ Theᵉ notionᵉ ofᵉ `k`-equivalenceᵉ isᵉ aᵉ specialᵉ caseᵉ ofᵉ theᵉ notionᵉ ofᵉ
  `L`-equivalence,ᵉ where `L`ᵉ isᵉ aᵉ reflectiveᵉ subuniverse.ᵉ Theyᵉ wereᵉ studiedᵉ in
  theᵉ paperᵉ {{#citeᵉ CORS20}}.ᵉ
-ᵉ Theᵉ classᵉ ofᵉ `k`-equivalencesᵉ isᵉ leftᵉ orthogonalᵉ to theᵉ classᵉ ofᵉ `k`-étaleᵉ
  maps.ᵉ Thisᵉ wasᵉ shownᵉ in {{#citeᵉ CR21}}.ᵉ

{{#bibliographyᵉ}}