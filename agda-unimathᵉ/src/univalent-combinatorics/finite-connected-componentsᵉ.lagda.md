# Finiteness of the type of connected components

```agda
module univalent-combinatorics.finite-connected-componentsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.propositionsᵉ
open import foundation.set-truncationsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ saidᵉ to haveᵉ finitelyᵉ manyᵉ connectedᵉ componentsᵉ ifᵉ itsᵉ setᵉ truncationᵉ
isᵉ aᵉ finiteᵉ type.ᵉ

## Definition

```agda
has-finitely-many-components-Propᵉ : {lᵉ : Level} → UUᵉ lᵉ → Propᵉ lᵉ
has-finitely-many-components-Propᵉ Aᵉ = is-finite-Propᵉ (type-trunc-Setᵉ Aᵉ)

has-finitely-many-componentsᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
has-finitely-many-componentsᵉ Aᵉ = type-Propᵉ (has-finitely-many-components-Propᵉ Aᵉ)

has-cardinality-components-Propᵉ : {lᵉ : Level} (kᵉ : ℕᵉ) → UUᵉ lᵉ → Propᵉ lᵉ
has-cardinality-components-Propᵉ kᵉ Aᵉ =
  has-cardinality-Propᵉ kᵉ (type-trunc-Setᵉ Aᵉ)

has-cardinality-componentsᵉ : {lᵉ : Level} (kᵉ : ℕᵉ) → UUᵉ lᵉ → UUᵉ lᵉ
has-cardinality-componentsᵉ kᵉ Aᵉ =
  type-Propᵉ (has-cardinality-components-Propᵉ kᵉ Aᵉ)
```