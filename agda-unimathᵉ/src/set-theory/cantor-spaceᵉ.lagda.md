# Cantor space

```agda
module set-theory.cantor-spaceᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.tight-apartness-relationsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ Cantorᵉ spaceᵉ isᵉ theᵉ typeᵉ ofᵉ functionsᵉ `ℕᵉ → Finᵉ 2`.ᵉ

## Definition

```agda
cantor-spaceᵉ : UUᵉ lzero
cantor-spaceᵉ = ℕᵉ → Finᵉ 2
```

## Properties

### The cantor space has a tight apartness relation

```agda
cantor-space-Type-With-Tight-Apartnessᵉ : Type-With-Tight-Apartnessᵉ lzero lzero
cantor-space-Type-With-Tight-Apartnessᵉ =
  exp-Type-With-Tight-Apartnessᵉ ℕᵉ (Fin-Type-With-Tight-Apartnessᵉ 2ᵉ)
```