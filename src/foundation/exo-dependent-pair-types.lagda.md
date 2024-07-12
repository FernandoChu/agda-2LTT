# Dependent pairᵉ types

```agda
module foundation.exo-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.exo-universes
```

</details>

## Idea

When `B` is a family of types over `A`, then we can form the type of pairs
`pairᵉ a b` consisting of an element `a : A` and an element `b : B a`. Such pairs
are called dependent pairs, since the type of the second component depends on
the first component.

## Definition

```agda
record Σᵉ {l1 l2 : Level} (A : UUᵉ l1) (B : A → UUᵉ l2) : UUᵉ (l1 ⊔ l2) where
  constructor pairᵉ
  field
    pr1ᵉ : A
    pr2ᵉ : B pr1ᵉ

open Σᵉ public

infixr 10 _,ᵉ_
pattern _,ᵉ_ a b = pairᵉ a b
```

## Constructions

```agda
ind-Σᵉ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {C : Σᵉ A B → UUᵉ l3} →
  ((x : A) (y : B x) → C (pairᵉ x y)) → ((t : Σᵉ A B) → C t)
ind-Σᵉ f (pairᵉ x y) = f x y

ev-pairᵉ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {C : Σᵉ A B → UUᵉ l3} →
  ((t : Σᵉ A B) → C t) → (x : A) (y : B x) → C (pairᵉ x y)
ev-pairᵉ f x y = f (pairᵉ x y)
```

### Families on dependent pairᵉ types

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2}
  where

  fam-Σᵉ : ((x : A) → B x → UUᵉ l3) → Σᵉ A B → UUᵉ l3
  fam-Σᵉ C (pairᵉ x y) = C x y
```
