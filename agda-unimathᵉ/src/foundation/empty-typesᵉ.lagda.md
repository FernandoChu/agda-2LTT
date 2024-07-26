# Empty types

```agda
module foundation.empty-typesᵉ where

open import foundation-core.empty-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.subuniversesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Anᵉ emptyᵉ typeᵉ isᵉ aᵉ typeᵉ with noᵉ elements.ᵉ Theᵉ (standardᵉ) emptyᵉ typeᵉ isᵉ
introducedᵉ asᵉ anᵉ inductive typeᵉ with noᵉ constructors.ᵉ Withᵉ theᵉ standardᵉ emptyᵉ
typeᵉ available,ᵉ weᵉ willᵉ sayᵉ thatᵉ aᵉ typeᵉ isᵉ emptyᵉ ifᵉ itᵉ mapsᵉ intoᵉ theᵉ standardᵉ
emptyᵉ type.ᵉ

## Definitions

### We raise the empty type to an arbitrary universe level

```agda
raise-emptyᵉ : (lᵉ : Level) → UUᵉ lᵉ
raise-emptyᵉ lᵉ = raiseᵉ lᵉ emptyᵉ

compute-raise-emptyᵉ : (lᵉ : Level) → emptyᵉ ≃ᵉ raise-emptyᵉ lᵉ
compute-raise-emptyᵉ lᵉ = compute-raiseᵉ lᵉ emptyᵉ

raise-ex-falsoᵉ :
  (l1ᵉ : Level) {l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} →
  raise-emptyᵉ l1ᵉ → Aᵉ
raise-ex-falsoᵉ lᵉ = ex-falsoᵉ ∘ᵉ map-inv-equivᵉ (compute-raise-emptyᵉ lᵉ)
```

### The predicate that a subuniverse contains the empty type

```agda
contains-empty-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) → UUᵉ l2ᵉ
contains-empty-subuniverseᵉ {l1ᵉ} Pᵉ = is-in-subuniverseᵉ Pᵉ (raise-emptyᵉ l1ᵉ)
```

### The predicate that a subuniverse contains any empty type

```agda
contains-empty-types-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
contains-empty-types-subuniverseᵉ {l1ᵉ} Pᵉ =
  (Xᵉ : UUᵉ l1ᵉ) → is-emptyᵉ Xᵉ → is-in-subuniverseᵉ Pᵉ Xᵉ
```

### The predicate that a subuniverse is closed under the `is-empty` predicate

```agda
is-closed-under-is-empty-subuniversesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : subuniverseᵉ l1ᵉ l3ᵉ) →
  UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
is-closed-under-is-empty-subuniversesᵉ Pᵉ Qᵉ =
  (Xᵉ : type-subuniverseᵉ Pᵉ) →
  is-in-subuniverseᵉ Qᵉ (is-emptyᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ))
```

## Properties

### The map `ex-falso` is an embedding

```agda
raise-ex-falso-embᵉ :
  (l1ᵉ : Level) {l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} →
  raise-emptyᵉ l1ᵉ ↪ᵉ Aᵉ
raise-ex-falso-embᵉ lᵉ =
  comp-embᵉ ex-falso-embᵉ (emb-equivᵉ (inv-equivᵉ (compute-raise-emptyᵉ lᵉ)))
```

### Being empty is a proposition

```agda
is-property-is-emptyᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-propᵉ (is-emptyᵉ Aᵉ)
is-property-is-emptyᵉ = is-prop-function-typeᵉ is-prop-emptyᵉ

is-empty-Propᵉ : {l1ᵉ : Level} → UUᵉ l1ᵉ → Propᵉ l1ᵉ
pr1ᵉ (is-empty-Propᵉ Aᵉ) = is-emptyᵉ Aᵉ
pr2ᵉ (is-empty-Propᵉ Aᵉ) = is-property-is-emptyᵉ

is-nonempty-Propᵉ : {l1ᵉ : Level} → UUᵉ l1ᵉ → Propᵉ l1ᵉ
pr1ᵉ (is-nonempty-Propᵉ Aᵉ) = is-nonemptyᵉ Aᵉ
pr2ᵉ (is-nonempty-Propᵉ Aᵉ) = is-property-is-emptyᵉ
```

```agda
abstract
  is-empty-type-trunc-Propᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → is-emptyᵉ Xᵉ → is-emptyᵉ (type-trunc-Propᵉ Xᵉ)
  is-empty-type-trunc-Propᵉ fᵉ =
    map-universal-property-trunc-Propᵉ empty-Propᵉ fᵉ

abstract
  is-empty-type-trunc-Prop'ᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → is-emptyᵉ (type-trunc-Propᵉ Xᵉ) → is-emptyᵉ Xᵉ
  is-empty-type-trunc-Prop'ᵉ fᵉ = fᵉ ∘ᵉ unit-trunc-Propᵉ
```

### Any inhabited type is nonempty

```agda
abstract
  is-nonempty-is-inhabitedᵉ :
    {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → type-trunc-Propᵉ Xᵉ → is-nonemptyᵉ Xᵉ
  is-nonempty-is-inhabitedᵉ {lᵉ} {Xᵉ} =
    map-universal-property-trunc-Propᵉ (is-nonempty-Propᵉ Xᵉ) (λ xᵉ fᵉ → fᵉ xᵉ)
```

```agda
abstract
  is-prop-raise-emptyᵉ :
    {l1ᵉ : Level} → is-propᵉ (raise-emptyᵉ l1ᵉ)
  is-prop-raise-emptyᵉ {l1ᵉ} =
    is-prop-equiv'ᵉ
      ( compute-raiseᵉ l1ᵉ emptyᵉ)
      ( is-prop-emptyᵉ)

raise-empty-Propᵉ :
  (l1ᵉ : Level) → Propᵉ l1ᵉ
pr1ᵉ (raise-empty-Propᵉ l1ᵉ) = raise-emptyᵉ l1ᵉ
pr2ᵉ (raise-empty-Propᵉ l1ᵉ) = is-prop-raise-emptyᵉ

abstract
  is-empty-raise-emptyᵉ :
    {l1ᵉ : Level} → is-emptyᵉ (raise-emptyᵉ l1ᵉ)
  is-empty-raise-emptyᵉ {l1ᵉ} = map-inv-equivᵉ (compute-raise-emptyᵉ l1ᵉ)
```

### The type of all empty types of a given universe is contractible

```agda
is-contr-type-is-emptyᵉ :
  (lᵉ : Level) →
  is-contrᵉ (type-subuniverseᵉ is-empty-Propᵉ)
pr1ᵉ (is-contr-type-is-emptyᵉ lᵉ) = raise-emptyᵉ lᵉ ,ᵉ is-empty-raise-emptyᵉ
pr2ᵉ (is-contr-type-is-emptyᵉ lᵉ) xᵉ =
  eq-pair-Σᵉ
    ( eq-equivᵉ
      ( equiv-is-emptyᵉ
        ( is-empty-raise-emptyᵉ)
        ( is-in-subuniverse-inclusion-subuniverseᵉ is-empty-Propᵉ xᵉ)))
    ( eq-is-propᵉ is-property-is-emptyᵉ)
```