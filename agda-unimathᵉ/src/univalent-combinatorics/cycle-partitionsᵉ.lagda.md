# Cycle partitions of finite types

```agda
module univalent-combinatorics.cycle-partitionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.cyclic-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ cycleᵉ partitionᵉ ofᵉ aᵉ finiteᵉ typeᵉ `A`ᵉ isᵉ aᵉ finiteᵉ familyᵉ ofᵉ cyclicᵉ finiteᵉ typesᵉ
equippedᵉ with anᵉ equivalenceᵉ fromᵉ `A`ᵉ to theᵉ totalᵉ spaceᵉ ofᵉ theᵉ underlyingᵉ typesᵉ
ofᵉ theᵉ family.ᵉ Theᵉ typeᵉ ofᵉ cyclicᵉ partitionsᵉ ofᵉ `A`ᵉ isᵉ equivalentᵉ to theᵉ typeᵉ ofᵉ
permutationsᵉ ofᵉ `A`.ᵉ

## Definition

```agda
cyclic-partition-𝔽ᵉ :
  {lᵉ : Level} (l2ᵉ l3ᵉ : Level) → 𝔽ᵉ lᵉ → UUᵉ (lᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
cyclic-partition-𝔽ᵉ l2ᵉ l3ᵉ Xᵉ =
  Σᵉ ( 𝔽ᵉ l2ᵉ)
    ( λ Yᵉ →
      Σᵉ ( type-𝔽ᵉ Yᵉ → Σᵉ ℕᵉ (λ nᵉ → Cyclic-Typeᵉ l3ᵉ (succ-ℕᵉ nᵉ)))
        ( λ Cᵉ →
          type-𝔽ᵉ Xᵉ ≃ᵉ
          Σᵉ ( type-𝔽ᵉ Yᵉ)
            ( λ yᵉ → type-Cyclic-Typeᵉ (succ-ℕᵉ (pr1ᵉ (Cᵉ yᵉ))) (pr2ᵉ (Cᵉ yᵉ)))))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Cᵉ : cyclic-partition-𝔽ᵉ l2ᵉ l3ᵉ Xᵉ)
  where

  finite-indexing-type-cyclic-partition-𝔽ᵉ : 𝔽ᵉ l2ᵉ
  finite-indexing-type-cyclic-partition-𝔽ᵉ = pr1ᵉ Cᵉ

  indexing-type-cyclic-partition-𝔽ᵉ : UUᵉ l2ᵉ
  indexing-type-cyclic-partition-𝔽ᵉ =
    type-𝔽ᵉ finite-indexing-type-cyclic-partition-𝔽ᵉ

  order-cycle-cyclic-partition-𝔽ᵉ :
    indexing-type-cyclic-partition-𝔽ᵉ → ℕᵉ
  order-cycle-cyclic-partition-𝔽ᵉ yᵉ = succ-ℕᵉ (pr1ᵉ (pr1ᵉ (pr2ᵉ Cᵉ) yᵉ))

  cycle-cyclic-partition-𝔽ᵉ :
    (yᵉ : indexing-type-cyclic-partition-𝔽ᵉ) →
    Cyclic-Typeᵉ l3ᵉ (order-cycle-cyclic-partition-𝔽ᵉ yᵉ)
  cycle-cyclic-partition-𝔽ᵉ yᵉ =
    pr2ᵉ (pr1ᵉ (pr2ᵉ Cᵉ) yᵉ)

  type-cycle-cyclic-partition-𝔽ᵉ :
    indexing-type-cyclic-partition-𝔽ᵉ → UUᵉ l3ᵉ
  type-cycle-cyclic-partition-𝔽ᵉ yᵉ =
    type-Cyclic-Typeᵉ
      ( order-cycle-cyclic-partition-𝔽ᵉ yᵉ)
      ( cycle-cyclic-partition-𝔽ᵉ yᵉ)

  equiv-cyclic-partition-𝔽ᵉ :
    type-𝔽ᵉ Xᵉ ≃ᵉ Σᵉ indexing-type-cyclic-partition-𝔽ᵉ type-cycle-cyclic-partition-𝔽ᵉ
  equiv-cyclic-partition-𝔽ᵉ = pr2ᵉ (pr2ᵉ Cᵉ)
```