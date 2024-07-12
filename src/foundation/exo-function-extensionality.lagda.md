# Function extensionality

```agda
module foundation.exo-function-extensionality where
```

<details><summary>Imports</summary>

```agda
open import foundation.exo-function-types
open import foundation.exo-homotopies
open import foundation.exo-identity-types
open import foundation.exo-universes
```

</details>

## Idea

The function extensionality axiom asserts that identifications of (dependent)
functions are equivalently described as pointwise equalities between them. In
other words, a function is completely determined by its values.

In this file, we define the statement of the axiom. The axiom itself is
postulated in
[`foundation.function-extensionality`](foundation.function-extensionality.md) as
`funext`.

## Statement

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2}
  where

  htpy-eq : {f g : (x : A) → B x} → (f ＝ᵉ g) → (f ~ᵉ  g)
  htpy-eq reflᵉ = refl-htpyᵉ

  postulate
    eq-htpy : {f g : (x : A) → B x} → f ~ᵉ g → f ＝ᵉ g
```
