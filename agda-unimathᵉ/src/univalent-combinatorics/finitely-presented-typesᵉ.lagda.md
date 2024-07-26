# Finitely presented types

```agda
module univalent-combinatorics.finitely-presented-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.set-presented-typesᵉ
open import foundation.set-truncationsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.finite-choiceᵉ
open import univalent-combinatorics.finite-connected-componentsᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ saidᵉ to beᵉ finitelyᵉ presentedᵉ ifᵉ itᵉ isᵉ presentedᵉ byᵉ aᵉ standardᵉ finiteᵉ
type.ᵉ

## Definition

### To have a presentation of cardinality `k`

```agda
has-presentation-of-cardinality-Propᵉ :
  {l1ᵉ : Level} (kᵉ : ℕᵉ) (Aᵉ : UUᵉ l1ᵉ) → Propᵉ l1ᵉ
has-presentation-of-cardinality-Propᵉ kᵉ Aᵉ =
  has-set-presentation-Propᵉ (Fin-Setᵉ kᵉ) Aᵉ

has-presentation-of-cardinalityᵉ : {l1ᵉ : Level} (kᵉ : ℕᵉ) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ l1ᵉ
has-presentation-of-cardinalityᵉ kᵉ Aᵉ =
  type-Propᵉ (has-presentation-of-cardinality-Propᵉ kᵉ Aᵉ)
```

### Finitely presented types

```agda
is-finitely-presentedᵉ : {l1ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l1ᵉ
is-finitely-presentedᵉ Aᵉ =
  Σᵉ ℕᵉ (λ kᵉ → has-presentation-of-cardinalityᵉ kᵉ Aᵉ)
```

## Properties

### A type has finitely many connected components if and only if it has a finite presentation

```agda
has-presentation-of-cardinality-has-cardinality-componentsᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} → has-cardinality-componentsᵉ kᵉ Aᵉ →
  has-presentation-of-cardinalityᵉ kᵉ Aᵉ
has-presentation-of-cardinality-has-cardinality-componentsᵉ {lᵉ} kᵉ {Aᵉ} Hᵉ =
  apply-universal-property-trunc-Propᵉ Hᵉ
    ( has-presentation-of-cardinality-Propᵉ kᵉ Aᵉ)
    ( λ eᵉ →
      apply-universal-property-trunc-Propᵉ
        ( P2ᵉ eᵉ)
        ( has-presentation-of-cardinality-Propᵉ kᵉ Aᵉ)
        ( λ gᵉ →
          unit-trunc-Propᵉ
            ( pairᵉ
              ( λ xᵉ → pr1ᵉ (gᵉ xᵉ))
              ( is-equiv-htpy-equivᵉ eᵉ (λ xᵉ → pr2ᵉ (gᵉ xᵉ))))))
  where
  P1ᵉ :
    (eᵉ : Finᵉ kᵉ ≃ᵉ type-trunc-Setᵉ Aᵉ) (xᵉ : Finᵉ kᵉ) →
    type-trunc-Propᵉ (fiberᵉ unit-trunc-Setᵉ (map-equivᵉ eᵉ xᵉ))
  P1ᵉ eᵉ xᵉ = is-surjective-unit-trunc-Setᵉ Aᵉ (map-equivᵉ eᵉ xᵉ)
  P2ᵉ :
    (eᵉ : Finᵉ kᵉ ≃ᵉ type-trunc-Setᵉ Aᵉ) →
    type-trunc-Propᵉ ((xᵉ : Finᵉ kᵉ) → fiberᵉ unit-trunc-Setᵉ (map-equivᵉ eᵉ xᵉ))
  P2ᵉ eᵉ = finite-choice-Finᵉ kᵉ (P1ᵉ eᵉ)

has-cardinality-components-has-presentation-of-cardinalityᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} → has-presentation-of-cardinalityᵉ kᵉ Aᵉ →
  has-cardinality-componentsᵉ kᵉ Aᵉ
has-cardinality-components-has-presentation-of-cardinalityᵉ {lᵉ} kᵉ {Aᵉ} Hᵉ =
  apply-universal-property-trunc-Propᵉ Hᵉ
    ( has-cardinality-components-Propᵉ kᵉ Aᵉ)
    ( λ (fᵉ ,ᵉ Eᵉ) → unit-trunc-Propᵉ (unit-trunc-Setᵉ ∘ᵉ fᵉ ,ᵉ Eᵉ))
```

### To be finitely presented is a property

```agda
all-elements-equal-is-finitely-presentedᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → all-elements-equalᵉ (is-finitely-presentedᵉ Aᵉ)
all-elements-equal-is-finitely-presentedᵉ {l1ᵉ} {Aᵉ} (pairᵉ kᵉ Kᵉ) (pairᵉ lᵉ Lᵉ) =
  eq-type-subtypeᵉ
    ( λ nᵉ → has-set-presentation-Propᵉ (Fin-Setᵉ nᵉ) Aᵉ)
    ( eq-cardinalityᵉ
      ( has-cardinality-components-has-presentation-of-cardinalityᵉ kᵉ Kᵉ)
      ( has-cardinality-components-has-presentation-of-cardinalityᵉ lᵉ Lᵉ))

is-prop-is-finitely-presentedᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-propᵉ (is-finitely-presentedᵉ Aᵉ)
is-prop-is-finitely-presentedᵉ =
  is-prop-all-elements-equalᵉ all-elements-equal-is-finitely-presentedᵉ

is-finitely-presented-Propᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → Propᵉ lᵉ
pr1ᵉ (is-finitely-presented-Propᵉ Aᵉ) = is-finitely-presentedᵉ Aᵉ
pr2ᵉ (is-finitely-presented-Propᵉ Aᵉ) = is-prop-is-finitely-presentedᵉ
```