# Cycle index series of species

```agda
module species.cycle-index-series-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.cyclic-finite-typesᵉ
```

</details>

## Idea

Theᵉ cycleᵉ indexᵉ seriesᵉ ofᵉ aᵉ speciesᵉ ofᵉ typesᵉ `F`ᵉ isᵉ aᵉ typeᵉ familyᵉ indexedᵉ byᵉ
finiteᵉ familiesᵉ ofᵉ cyclicᵉ types.ᵉ Noteᵉ thatᵉ aᵉ finiteᵉ familyᵉ ofᵉ cyclicᵉ typesᵉ `Cᵢ`ᵉ
uniquelyᵉ determinesᵉ aᵉ permutationᵉ `e`ᵉ onᵉ theᵉ disjointᵉ unionᵉ `Cᵉ :=ᵉ Σᵢᵉ Cᵢ`ᵉ ofᵉ theᵉ
underlyingᵉ typesᵉ ofᵉ theᵉ `Cᵢ`.ᵉ Thisᵉ permutationᵉ determinesᵉ anᵉ actionᵉ `Fᵉ e`ᵉ onᵉ
`Fᵉ C`.ᵉ Theᵉ cycleᵉ indexᵉ seriesᵉ ofᵉ `F`ᵉ atᵉ theᵉ familyᵉ `Cᵢ`ᵉ isᵉ theᵉ typeᵉ `Fixᵉ (Fᵉ e)`ᵉ
ofᵉ fixedᵉ pointsᵉ ofᵉ `Fᵉ e`.ᵉ

## Definition

```agda
total-type-family-of-cyclic-typesᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Cᵉ : Xᵉ → Σᵉ ℕᵉ (Cyclic-Typeᵉ l2ᵉ)) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
total-type-family-of-cyclic-typesᵉ Xᵉ Cᵉ =
  Σᵉ Xᵉ (λ xᵉ → type-Cyclic-Typeᵉ (pr1ᵉ (Cᵉ xᵉ)) (pr2ᵉ (Cᵉ xᵉ)))

{-ᵉ
permutation-family-of-cyclic-typesᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Cᵉ : type-𝔽ᵉ Xᵉ → Σᵉ ℕᵉ (Cyclic-Typeᵉ l2ᵉ)) →
  Autᵉ (total-type-family-of-cyclic-typesᵉ Xᵉ Cᵉ)
permutation-family-of-cyclic-typesᵉ Xᵉ Cᵉ = {!!ᵉ}

cycle-index-series-species-typesᵉ :
  {l1ᵉ l2ᵉ : Level} (Fᵉ : species-typesᵉ l1ᵉ l2ᵉ) (Xᵉ : 𝔽ᵉ l1ᵉ) →
  (type-𝔽ᵉ Xᵉ → Σᵉ ℕᵉ (Cyclic-Typeᵉ {!!ᵉ} ∘ᵉ succ-ℕᵉ)) →
  UUᵉ {!!ᵉ}
cycle-index-series-species-typesᵉ Fᵉ Xᵉ Cᵉ =
  Σᵉ {!Fᵉ (total-type-family-of-cyclic-typesᵉ Xᵉ C)!ᵉ} {!!ᵉ}
  -ᵉ}
```