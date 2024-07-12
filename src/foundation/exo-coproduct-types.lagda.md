# Coproduct types

```agda
module foundation.exo-coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.exo-universes
```

</details>

## Idea

The coproduct of two types `A` and `B` can be thought of as the disjoint union
of `A` and `B`.

## Definition

```agda
data _+ᵉ_ {l1 l2 : Level} (A : UUᵉ l1) (B : UUᵉ l2) : UUᵉ (l1 ⊔ l2)
  where
  inlᵉ : A → A +ᵉ B
  inrᵉ : B → A +ᵉ B

ind-coprodᵉ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (C : A +ᵉ B → UUᵉ l3) →
  ((x : A) → C (inlᵉ x)) → ((y : B) → C (inrᵉ y)) →
  (t : A +ᵉ B) → C t
ind-coprodᵉ C f g (inlᵉ x) = f x
ind-coprodᵉ C f g (inrᵉ x) = g x
```
