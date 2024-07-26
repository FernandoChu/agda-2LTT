# Unordered tuples of elements in commutative monoids

```agda
module group-theory.unordered-tuples-of-elements-commutative-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ
open import foundation.unordered-tuplesᵉ

open import group-theory.commutative-monoidsᵉ
```

</details>

## Definition

```agda
unordered-tuple-Commutative-Monoidᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Mᵉ : Commutative-Monoidᵉ lᵉ) → UUᵉ (lsuc lzero ⊔ lᵉ)
unordered-tuple-Commutative-Monoidᵉ nᵉ Mᵉ =
  unordered-tupleᵉ nᵉ (type-Commutative-Monoidᵉ Mᵉ)

module _
  {lᵉ : Level} {nᵉ : ℕᵉ} (Mᵉ : Commutative-Monoidᵉ lᵉ)
  (xᵉ : unordered-tuple-Commutative-Monoidᵉ nᵉ Mᵉ)
  where

  type-unordered-tuple-Commutative-Monoidᵉ : UUᵉ lzero
  type-unordered-tuple-Commutative-Monoidᵉ = type-unordered-tupleᵉ nᵉ xᵉ

  element-unordered-tuple-Commutative-Monoidᵉ :
    type-unordered-tuple-Commutative-Monoidᵉ → type-Commutative-Monoidᵉ Mᵉ
  element-unordered-tuple-Commutative-Monoidᵉ =
    element-unordered-tupleᵉ nᵉ xᵉ
```