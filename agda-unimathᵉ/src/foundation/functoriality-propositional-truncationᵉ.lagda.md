# Functoriality of propositional truncations

```agda
module foundation.functoriality-propositional-truncationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Theᵉ universalᵉ propertyᵉ ofᵉ propositionalᵉ truncationsᵉ canᵉ beᵉ usedᵉ to defineᵉ theᵉ
functorialᵉ actionᵉ ofᵉ propositionalᵉ truncations.ᵉ

## Definition

```agda
abstract
  unique-map-trunc-Propᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-contrᵉ
      ( Σᵉ ( type-hom-Propᵉ (trunc-Propᵉ Aᵉ) (trunc-Propᵉ Bᵉ))
          ( λ hᵉ → (hᵉ ∘ᵉ unit-trunc-Propᵉ) ~ᵉ (unit-trunc-Propᵉ ∘ᵉ fᵉ)))
  unique-map-trunc-Propᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} fᵉ =
    universal-property-trunc-Propᵉ Aᵉ (trunc-Propᵉ Bᵉ) (unit-trunc-Propᵉ ∘ᵉ fᵉ)

abstract
  map-trunc-Propᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    (Aᵉ → Bᵉ) → type-hom-Propᵉ (trunc-Propᵉ Aᵉ) (trunc-Propᵉ Bᵉ)
  map-trunc-Propᵉ fᵉ =
    pr1ᵉ (centerᵉ (unique-map-trunc-Propᵉ fᵉ))
```

## Properties

### Propositional truncations of homotopic maps are homotopic

```agda
  htpy-map-trunc-Propᵉ :
    { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    ( (map-trunc-Propᵉ fᵉ) ∘ᵉ unit-trunc-Propᵉ) ~ᵉ (unit-trunc-Propᵉ ∘ᵉ fᵉ)
  htpy-map-trunc-Propᵉ fᵉ =
    pr2ᵉ (centerᵉ (unique-map-trunc-Propᵉ fᵉ))

  htpy-uniqueness-map-trunc-Propᵉ :
    { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    ( hᵉ : type-hom-Propᵉ (trunc-Propᵉ Aᵉ) (trunc-Propᵉ Bᵉ)) →
    ( ( hᵉ ∘ᵉ unit-trunc-Propᵉ) ~ᵉ (unit-trunc-Propᵉ ∘ᵉ fᵉ)) →
    (map-trunc-Propᵉ fᵉ) ~ᵉ hᵉ
  htpy-uniqueness-map-trunc-Propᵉ fᵉ hᵉ Hᵉ =
    htpy-eqᵉ (apᵉ pr1ᵉ (contractionᵉ (unique-map-trunc-Propᵉ fᵉ) (pairᵉ hᵉ Hᵉ)))
```

### The propositional truncation of the identity map is the identity map

```agda
abstract
  id-map-trunc-Propᵉ :
    { l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → map-trunc-Propᵉ (idᵉ {Aᵉ = Aᵉ}) ~ᵉ idᵉ
  id-map-trunc-Propᵉ {l1ᵉ} {Aᵉ} =
    htpy-uniqueness-map-trunc-Propᵉ idᵉ idᵉ refl-htpyᵉ
```

### The propositional truncation of a composite is the composite of the propositional truncations

```agda
abstract
  preserves-comp-map-trunc-Propᵉ :
    { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
    ( gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ) →
    ( map-trunc-Propᵉ (gᵉ ∘ᵉ fᵉ)) ~ᵉ
    ( (map-trunc-Propᵉ gᵉ) ∘ᵉ (map-trunc-Propᵉ fᵉ))
  preserves-comp-map-trunc-Propᵉ gᵉ fᵉ =
    htpy-uniqueness-map-trunc-Propᵉ
      ( gᵉ ∘ᵉ fᵉ)
      ( (map-trunc-Propᵉ gᵉ) ∘ᵉ (map-trunc-Propᵉ fᵉ))
      ( ( (map-trunc-Propᵉ gᵉ) ·lᵉ (htpy-map-trunc-Propᵉ fᵉ)) ∙hᵉ
        ( ( htpy-map-trunc-Propᵉ gᵉ) ·rᵉ fᵉ))
```

### The functorial action of propositional truncations preserves equivalences

```agda
abstract
  map-equiv-trunc-Propᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    (Aᵉ ≃ᵉ Bᵉ) → type-trunc-Propᵉ Aᵉ → type-trunc-Propᵉ Bᵉ
  map-equiv-trunc-Propᵉ eᵉ = map-trunc-Propᵉ (map-equivᵉ eᵉ)

abstract
  map-inv-equiv-trunc-Propᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    (Aᵉ ≃ᵉ Bᵉ) → type-trunc-Propᵉ Bᵉ → type-trunc-Propᵉ Aᵉ
  map-inv-equiv-trunc-Propᵉ eᵉ = map-equiv-trunc-Propᵉ (inv-equivᵉ eᵉ)

abstract
  equiv-trunc-Propᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    (Aᵉ ≃ᵉ Bᵉ) → (type-trunc-Propᵉ Aᵉ ≃ᵉ type-trunc-Propᵉ Bᵉ)
  pr1ᵉ (equiv-trunc-Propᵉ eᵉ) = map-equiv-trunc-Propᵉ eᵉ
  pr2ᵉ (equiv-trunc-Propᵉ eᵉ) =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-type-trunc-Propᵉ)
      ( is-prop-type-trunc-Propᵉ)
      ( map-inv-equiv-trunc-Propᵉ eᵉ)
```