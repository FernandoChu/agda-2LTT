# Empty types

```agda
module foundation.exo-empty-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.exo-universes
```

</details>

## Idea

An empty type is a type with no elements. The (standard) empty type is
introduced as an inductive type with no constructors. With the standard empty
type available, we will say that a type is empty if it maps into the standard
empty type.

## Definition

### Empty types

```agda
data emptyᵉ : UUᵉ lzero where

ind-emptyᵉ : {l : Level} {P : emptyᵉ → UUᵉ l} → ((x : emptyᵉ) → P x)
ind-emptyᵉ ()

ex-falsoᵉ : {l : Level} {A : UUᵉ l} → emptyᵉ → A
ex-falsoᵉ = ind-emptyᵉ

is-emptyᵉ : {l : Level} → UUᵉ l → UUᵉ l
is-emptyᵉ A = A → emptyᵉ

is-nonemptyᵉ : {l : Level} → UUᵉ l → UUᵉ l
is-nonemptyᵉ A = is-emptyᵉ (is-emptyᵉ A)
```
