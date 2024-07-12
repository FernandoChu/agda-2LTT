# Exo-cartesian product types

```agda
module foundation.exo-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.exo-dependent-pair-types
open import foundation.exo-universes
```

</details>

## Definition

Cartesian products of types are defined as dependent pair types, using a
constant type family.

```agda
prodᵉ : {l1 l2 : Level} (A : UUᵉ l1) (B : UUᵉ l2) → UUᵉ (l1 ⊔ l2)
prodᵉ A B = Σᵉ A (λ a → B)

pair'ᵉ :
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} → A → B → prodᵉ A B
pair'ᵉ = pairᵉ

_×ᵉ_ : {l1 l2 : Level} (A : UUᵉ l1) (B : UUᵉ l2) → UUᵉ (l1 ⊔ l2)
A ×ᵉ B = prodᵉ A B
```

## Fibrant
