# Epimorphisms with respect to truncated types

```agda
module foundation.epimorphisms-with-respect-to-truncated-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.connected-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-truncationᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.sectionsᵉ
open import foundation.truncation-equivalencesᵉ
open import foundation.truncationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.codiagonals-of-mapsᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ saidᵉ to beᵉ aᵉ **`k`-epimorphism**ᵉ ifᵉ theᵉ precompositionᵉ
functionᵉ

```text
  -ᵉ ∘ᵉ fᵉ : (Bᵉ → Xᵉ) → (Aᵉ → Xᵉ)
```

isᵉ anᵉ embeddingᵉ forᵉ everyᵉ `k`-truncatedᵉ typeᵉ `X`.ᵉ

## Definitions

### `k`-epimorphisms

```agda
is-epimorphism-Truncated-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (Aᵉ → Bᵉ) → UUωᵉ
is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ =
  {lᵉ : Level} (Xᵉ : Truncated-Typeᵉ lᵉ kᵉ) →
  is-embᵉ (precompᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))
```

## Properties

### Every `k+1`-epimorphism is a `k`-epimorphism

```agda
is-epimorphism-is-epimorphism-succ-Truncated-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-epimorphism-Truncated-Typeᵉ (succ-𝕋ᵉ kᵉ) fᵉ →
  is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ
is-epimorphism-is-epimorphism-succ-Truncated-Typeᵉ kᵉ fᵉ Hᵉ Xᵉ =
  Hᵉ (truncated-type-succ-Truncated-Typeᵉ kᵉ Xᵉ)
```

### Every map is a `-1`-epimorphism

```agda
is-neg-one-epimorphismᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-epimorphism-Truncated-Typeᵉ neg-one-𝕋ᵉ fᵉ
is-neg-one-epimorphismᵉ fᵉ Pᵉ =
  is-emb-is-propᵉ
    ( is-prop-function-typeᵉ (is-prop-type-Propᵉ Pᵉ))
    ( is-prop-function-typeᵉ (is-prop-type-Propᵉ Pᵉ))
```

### Every `k`-equivalence is a `k`-epimorphism

```agda
is-epimorphism-is-truncation-equivalence-Truncated-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-truncation-equivalenceᵉ kᵉ fᵉ →
  is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ
is-epimorphism-is-truncation-equivalence-Truncated-Typeᵉ kᵉ fᵉ Hᵉ Xᵉ =
  is-emb-is-equivᵉ (is-equiv-precomp-is-truncation-equivalenceᵉ kᵉ fᵉ Hᵉ Xᵉ)
```

### A map is a `k`-epimorphism if and only if its `k`-truncation is a `k`-epimorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-epimorphism-is-epimorphism-map-trunc-Truncated-Typeᵉ :
    is-epimorphism-Truncated-Typeᵉ kᵉ (map-truncᵉ kᵉ fᵉ) →
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ
  is-epimorphism-is-epimorphism-map-trunc-Truncated-Typeᵉ Hᵉ Xᵉ =
    is-emb-bottom-is-emb-top-is-equiv-coherence-square-mapsᵉ
      ( precompᵉ (map-truncᵉ kᵉ fᵉ) (type-Truncated-Typeᵉ Xᵉ))
      ( precompᵉ unit-truncᵉ (type-Truncated-Typeᵉ Xᵉ))
      ( precompᵉ unit-truncᵉ (type-Truncated-Typeᵉ Xᵉ))
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
      ( Hᵉ Xᵉ)

  is-epimorphism-map-trunc-is-epimorphism-Truncated-Typeᵉ :
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ →
    is-epimorphism-Truncated-Typeᵉ kᵉ (map-truncᵉ kᵉ fᵉ)
  is-epimorphism-map-trunc-is-epimorphism-Truncated-Typeᵉ Hᵉ Xᵉ =
    is-emb-top-is-emb-bottom-is-equiv-coherence-square-mapsᵉ
      ( precompᵉ (map-truncᵉ kᵉ fᵉ) (type-Truncated-Typeᵉ Xᵉ))
      ( precompᵉ unit-truncᵉ (type-Truncated-Typeᵉ Xᵉ))
      ( precompᵉ unit-truncᵉ (type-Truncated-Typeᵉ Xᵉ))
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
      ( Hᵉ Xᵉ)
```

### The class of `k`-epimorphisms is closed under composition and has the right cancellation property

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ)
  where

  is-epimorphism-comp-Truncated-Typeᵉ :
    is-epimorphism-Truncated-Typeᵉ kᵉ gᵉ →
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ →
    is-epimorphism-Truncated-Typeᵉ kᵉ (gᵉ ∘ᵉ fᵉ)
  is-epimorphism-comp-Truncated-Typeᵉ egᵉ efᵉ Xᵉ =
    is-emb-compᵉ
      ( precompᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))
      ( precompᵉ gᵉ (type-Truncated-Typeᵉ Xᵉ))
      ( efᵉ Xᵉ)
      ( egᵉ Xᵉ)

  is-epimorphism-left-factor-Truncated-Typeᵉ :
    is-epimorphism-Truncated-Typeᵉ kᵉ (gᵉ ∘ᵉ fᵉ) →
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ →
    is-epimorphism-Truncated-Typeᵉ kᵉ gᵉ
  is-epimorphism-left-factor-Truncated-Typeᵉ ecᵉ efᵉ Xᵉ =
    is-emb-right-factorᵉ
      ( precompᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))
      ( precompᵉ gᵉ (type-Truncated-Typeᵉ Xᵉ))
      ( efᵉ Xᵉ)
      ( ecᵉ Xᵉ)
```

### A map `f` is a `k`-epimorphism if and only if the horizontal/vertical projections from `cocone {X} f f` are equivalences for all `k`-types `X`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-equiv-diagonal-into-fibers-precomp-is-epimorphism-Truncated-Typeᵉ :
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ →
    {lᵉ : Level} (Xᵉ : Truncated-Typeᵉ lᵉ kᵉ) →
    is-equivᵉ (diagonal-into-fibers-precompᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))
  is-equiv-diagonal-into-fibers-precomp-is-epimorphism-Truncated-Typeᵉ eᵉ Xᵉ =
    is-equiv-map-section-familyᵉ
      ( λ gᵉ → gᵉ ,ᵉ reflᵉ)
      ( λ gᵉ →
        is-proof-irrelevant-is-propᵉ
          ( is-prop-map-is-embᵉ (eᵉ Xᵉ) (gᵉ ∘ᵉ fᵉ))
          ( gᵉ ,ᵉ reflᵉ))

  is-equiv-diagonal-into-cocone-is-epimorphism-Truncated-Typeᵉ :
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ →
    {lᵉ : Level} (Xᵉ : Truncated-Typeᵉ lᵉ kᵉ) →
    is-equivᵉ (diagonal-into-coconeᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))
  is-equiv-diagonal-into-cocone-is-epimorphism-Truncated-Typeᵉ eᵉ Xᵉ =
    is-equiv-compᵉ
      ( map-equivᵉ (compute-total-fiber-precompᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ)))
      ( diagonal-into-fibers-precompᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))
      ( is-equiv-diagonal-into-fibers-precomp-is-epimorphism-Truncated-Typeᵉ eᵉ Xᵉ)
      ( is-equiv-map-equivᵉ
        ( compute-total-fiber-precompᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ)))

  is-equiv-horizontal-map-cocone-is-epimorphism-Truncated-Typeᵉ :
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ →
    {lᵉ : Level} (Xᵉ : Truncated-Typeᵉ lᵉ kᵉ) →
    is-equivᵉ (horizontal-map-coconeᵉ {Xᵉ = type-Truncated-Typeᵉ Xᵉ} fᵉ fᵉ)
  is-equiv-horizontal-map-cocone-is-epimorphism-Truncated-Typeᵉ eᵉ Xᵉ =
    is-equiv-left-factorᵉ
      ( horizontal-map-coconeᵉ fᵉ fᵉ)
      ( diagonal-into-coconeᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))
      ( is-equiv-idᵉ)
      ( is-equiv-diagonal-into-cocone-is-epimorphism-Truncated-Typeᵉ eᵉ Xᵉ)

  is-equiv-vertical-map-cocone-is-epimorphism-Truncated-Typeᵉ :
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ →
    {lᵉ : Level} (Xᵉ : Truncated-Typeᵉ lᵉ kᵉ) →
    is-equivᵉ (vertical-map-coconeᵉ {Xᵉ = type-Truncated-Typeᵉ Xᵉ} fᵉ fᵉ)
  is-equiv-vertical-map-cocone-is-epimorphism-Truncated-Typeᵉ eᵉ Xᵉ =
    is-equiv-left-factorᵉ
      ( vertical-map-coconeᵉ fᵉ fᵉ)
      ( diagonal-into-coconeᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))
      ( is-equiv-idᵉ)
      ( is-equiv-diagonal-into-cocone-is-epimorphism-Truncated-Typeᵉ eᵉ Xᵉ)

  is-epimorphism-is-equiv-horizontal-map-cocone-Truncated-Typeᵉ :
    ( {lᵉ : Level} (Xᵉ : Truncated-Typeᵉ lᵉ kᵉ) →
      is-equivᵉ (horizontal-map-coconeᵉ {Xᵉ = type-Truncated-Typeᵉ Xᵉ} fᵉ fᵉ)) →
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ
  is-epimorphism-is-equiv-horizontal-map-cocone-Truncated-Typeᵉ hᵉ Xᵉ =
    is-emb-is-contr-fibers-valuesᵉ
      ( precompᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))
      ( λ gᵉ →
        is-contr-equivᵉ
          ( Σᵉ ( Bᵉ → (type-Truncated-Typeᵉ Xᵉ))
              ( λ hᵉ → coherence-square-mapsᵉ fᵉ fᵉ hᵉ gᵉ))
          ( compute-fiber-precompᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ) gᵉ)
          ( is-contr-is-equiv-pr1ᵉ (hᵉ Xᵉ) gᵉ))

  is-epimorphism-is-equiv-vertical-map-cocone-Truncated-Typeᵉ :
    ( {lᵉ : Level} (Xᵉ : Truncated-Typeᵉ lᵉ kᵉ) →
      is-equivᵉ (vertical-map-coconeᵉ {Xᵉ = type-Truncated-Typeᵉ Xᵉ} fᵉ fᵉ)) →
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ
  is-epimorphism-is-equiv-vertical-map-cocone-Truncated-Typeᵉ hᵉ =
    is-epimorphism-is-equiv-horizontal-map-cocone-Truncated-Typeᵉ
      ( λ Xᵉ →
        is-equiv-compᵉ
          ( vertical-map-coconeᵉ fᵉ fᵉ)
          ( swap-coconeᵉ fᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))
          ( is-equiv-swap-coconeᵉ fᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))
          ( hᵉ Xᵉ))
```

### The codiagonal of a `k`-epimorphism is a `k`-equivalence

Weᵉ considerᵉ theᵉ commutativeᵉ diagramᵉ forᵉ anyᵉ `k`-typeᵉ `X`ᵉ:

```text
             horizontal-map-coconeᵉ
 (Bᵉ → Xᵉ) <----------------------------ᵉ coconeᵉ fᵉ fᵉ Xᵉ
    |                  ≃ᵉ                  ∧ᵉ
 idᵉ | ≃ᵉ                                 ≃ᵉ | (universalᵉ propertyᵉ)
    ∨ᵉ                                     |
 (Bᵉ → Xᵉ) ------------------------>ᵉ (pushoutᵉ fᵉ fᵉ → Xᵉ)
          precompᵉ (codiagonalᵉ fᵉ)
```

Sinceᵉ theᵉ topᵉ (inᵉ caseᵉ `f`ᵉ isᵉ epic),ᵉ leftᵉ andᵉ rightᵉ mapsᵉ areᵉ allᵉ equivalences,ᵉ
soᵉ isᵉ theᵉ bottomᵉ map.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-truncation-equivalence-codiagonal-map-is-epimorphism-Truncated-Typeᵉ :
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ →
    is-truncation-equivalenceᵉ kᵉ (codiagonal-mapᵉ fᵉ)
  is-truncation-equivalence-codiagonal-map-is-epimorphism-Truncated-Typeᵉ eᵉ =
    is-truncation-equivalence-is-equiv-precompᵉ kᵉ
      ( codiagonal-mapᵉ fᵉ)
      ( λ lᵉ Xᵉ →
        is-equiv-right-factorᵉ
          ( ( horizontal-map-coconeᵉ fᵉ fᵉ) ∘ᵉ
            ( map-equivᵉ (equiv-up-pushoutᵉ fᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))))
          ( precompᵉ (codiagonal-mapᵉ fᵉ) (type-Truncated-Typeᵉ Xᵉ))
          ( is-equiv-compᵉ
            ( horizontal-map-coconeᵉ fᵉ fᵉ)
            ( map-equivᵉ (equiv-up-pushoutᵉ fᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ)))
            ( is-equiv-map-equivᵉ (equiv-up-pushoutᵉ fᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ)))
            ( is-equiv-horizontal-map-cocone-is-epimorphism-Truncated-Typeᵉ
              ( kᵉ)
              ( fᵉ)
              ( eᵉ)
              ( Xᵉ)))
          ( is-equiv-htpyᵉ
            ( idᵉ)
            ( λ gᵉ → eq-htpyᵉ (λ bᵉ → apᵉ gᵉ (compute-inl-codiagonal-mapᵉ fᵉ bᵉ)))
            ( is-equiv-idᵉ)))
```

### A map is a `k`-epimorphism if its codiagonal is a `k`-equivalence

Weᵉ useᵉ theᵉ sameᵉ diagramᵉ asᵉ above.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-equiv-horizontal-map-cocone-is-truncation-equivalence-codiagonal-mapᵉ :
    is-truncation-equivalenceᵉ kᵉ (codiagonal-mapᵉ fᵉ) →
    {lᵉ : Level} (Xᵉ : Truncated-Typeᵉ lᵉ kᵉ) →
    is-equivᵉ (horizontal-map-coconeᵉ {Xᵉ = type-Truncated-Typeᵉ Xᵉ} fᵉ fᵉ)
  is-equiv-horizontal-map-cocone-is-truncation-equivalence-codiagonal-mapᵉ eᵉ Xᵉ =
    is-equiv-left-factorᵉ
      ( horizontal-map-coconeᵉ fᵉ fᵉ)
      ( ( map-equivᵉ (equiv-up-pushoutᵉ fᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))) ∘ᵉ
        ( precompᵉ (codiagonal-mapᵉ fᵉ) (type-Truncated-Typeᵉ Xᵉ)))
      ( is-equiv-htpyᵉ
        ( idᵉ)
        ( λ gᵉ → eq-htpyᵉ (λ bᵉ → apᵉ gᵉ (compute-inl-codiagonal-mapᵉ fᵉ bᵉ)))
        ( is-equiv-idᵉ))
      ( is-equiv-compᵉ
        ( map-equivᵉ (equiv-up-pushoutᵉ fᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ)))
        ( precompᵉ (codiagonal-mapᵉ fᵉ) (type-Truncated-Typeᵉ Xᵉ))
        ( is-equiv-precomp-is-truncation-equivalenceᵉ kᵉ (codiagonal-mapᵉ fᵉ) eᵉ Xᵉ)
        ( is-equiv-map-equivᵉ (equiv-up-pushoutᵉ fᵉ fᵉ (type-Truncated-Typeᵉ Xᵉ))))

  is-epimorphism-is-truncation-equivalence-codiagonal-map-Truncated-Typeᵉ :
    is-truncation-equivalenceᵉ kᵉ (codiagonal-mapᵉ fᵉ) →
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ
  is-epimorphism-is-truncation-equivalence-codiagonal-map-Truncated-Typeᵉ eᵉ Xᵉ =
    is-epimorphism-is-equiv-horizontal-map-cocone-Truncated-Typeᵉ kᵉ fᵉ
      ( is-equiv-horizontal-map-cocone-is-truncation-equivalence-codiagonal-mapᵉ
        ( eᵉ))
      ( Xᵉ)
```

### A map is a `k`-epimorphism if and only if its codiagonal is `k`-connected

Thisᵉ strengthensᵉ theᵉ aboveᵉ resultᵉ aboutᵉ theᵉ codiagonalᵉ beingᵉ aᵉ `k`-equivalence.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-epimorphism-is-connected-codiagonal-map-Truncated-Typeᵉ :
    is-connected-mapᵉ kᵉ (codiagonal-mapᵉ fᵉ) → is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ
  is-epimorphism-is-connected-codiagonal-map-Truncated-Typeᵉ cᵉ =
    is-epimorphism-is-truncation-equivalence-codiagonal-map-Truncated-Typeᵉ kᵉ fᵉ
      ( is-truncation-equivalence-is-connected-mapᵉ (codiagonal-mapᵉ fᵉ) cᵉ)

  is-connected-codiagonal-map-is-epimorphism-Truncated-Typeᵉ :
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ → is-connected-mapᵉ kᵉ (codiagonal-mapᵉ fᵉ)
  is-connected-codiagonal-map-is-epimorphism-Truncated-Typeᵉ eᵉ =
    is-connected-map-is-truncation-equivalence-sectionᵉ
      ( codiagonal-mapᵉ fᵉ)
      ( kᵉ)
      ( inl-pushoutᵉ fᵉ fᵉ ,ᵉ compute-inl-codiagonal-mapᵉ fᵉ)
      ( is-truncation-equivalence-codiagonal-map-is-epimorphism-Truncated-Typeᵉ
        ( kᵉ)
        ( fᵉ)
        ( eᵉ))
```

## See also

-ᵉ [Acyclicᵉ maps](synthetic-homotopy-theory.acyclic-maps.mdᵉ)
-ᵉ [Dependentᵉ epimorphisms](foundation.dependent-epimorphisms.mdᵉ)
-ᵉ [Epimorphisms](foundation.epimorphisms.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to sets](foundation.epimorphisms-with-respect-to-sets.mdᵉ)