# The lesser limited principle of omniscience

```agda
module foundation.lesser-limited-principle-of-omniscienceᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.parity-natural-numbersᵉ

open import foundation.disjunctionᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Statement

Theᵉ **lesserᵉ limitedᵉ principleᵉ ofᵉ omniscience**ᵉ assertsᵉ thatᵉ forᵉ anyᵉ sequenceᵉ
`fᵉ : ℕᵉ → Finᵉ 2`ᵉ containingᵉ atᵉ mostᵉ oneᵉ `1`,ᵉ eitherᵉ `fᵉ nᵉ ＝ᵉ 0`ᵉ forᵉ allᵉ evenᵉ `n`ᵉ
orᵉ `fᵉ nᵉ ＝ᵉ 0`ᵉ forᵉ allᵉ oddᵉ `n`.ᵉ

```agda
LLPOᵉ : UUᵉ lzero
LLPOᵉ =
  (fᵉ : ℕᵉ → Finᵉ 2ᵉ) → is-propᵉ (fiberᵉ fᵉ (one-Finᵉ 1ᵉ)) →
  type-disjunction-Propᵉ
    ( Π-Propᵉ ℕᵉ
      ( λ nᵉ →
        function-Propᵉ (is-even-ℕᵉ nᵉ) (Id-Propᵉ (Fin-Setᵉ 2ᵉ) (fᵉ nᵉ) (zero-Finᵉ 1ᵉ))))
    ( Π-Propᵉ ℕᵉ
      ( λ nᵉ →
        function-Propᵉ (is-odd-ℕᵉ nᵉ) (Id-Propᵉ (Fin-Setᵉ 2ᵉ) (fᵉ nᵉ) (zero-Finᵉ 1ᵉ))))
```

## See also

-ᵉ [Theᵉ principleᵉ ofᵉ omniscience](foundation.principle-of-omniscience.mdᵉ)
-ᵉ [Theᵉ limitedᵉ principleᵉ ofᵉ omniscience](foundation.limited-principle-of-omniscience.mdᵉ)
-ᵉ [Theᵉ weakᵉ limitedᵉ principleᵉ ofᵉ omniscience](foundation.weak-limited-principle-of-omniscience.mdᵉ)