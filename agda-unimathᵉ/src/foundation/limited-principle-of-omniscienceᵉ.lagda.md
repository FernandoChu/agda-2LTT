# The limited principle of omniscience

```agda
module foundation.limited-principle-of-omniscienceᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.disjunctionᵉ
open import foundation.existential-quantificationᵉ
open import foundation.universal-quantificationᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Statement

Theᵉ
{{#conceptᵉ "limitedᵉ principleᵉ ofᵉ omniscience"ᵉ WDID=Q6549544ᵉ WD="limitedᵉ principleᵉ ofᵉ omniscience"ᵉ Agda=LPOᵉ}}
(LPOᵉ) assertsᵉ thatᵉ forᵉ everyᵉ [sequence](foundation.sequences.mdᵉ) `fᵉ : ℕᵉ → Finᵉ 2`ᵉ
thereᵉ eitherᵉ [exists](foundation.existential-quantification.mdᵉ) anᵉ `n`ᵉ suchᵉ thatᵉ
`fᵉ nᵉ ＝ᵉ 1`ᵉ orᵉ forᵉ allᵉ `n`ᵉ weᵉ haveᵉ `fᵉ nᵉ ＝ᵉ 0`.ᵉ

```agda
LPOᵉ : UUᵉ lzero
LPOᵉ =
  (fᵉ : ℕᵉ → Finᵉ 2ᵉ) →
  type-disjunction-Propᵉ
    ( ∃ᵉ ℕᵉ (λ nᵉ → Id-Propᵉ (Fin-Setᵉ 2ᵉ) (fᵉ nᵉ) (one-Finᵉ 1ᵉ)))
    ( ∀'ᵉ ℕᵉ (λ nᵉ → Id-Propᵉ (Fin-Setᵉ 2ᵉ) (fᵉ nᵉ) (zero-Finᵉ 1ᵉ)))
```

## See also

-ᵉ [Theᵉ principleᵉ ofᵉ omniscience](foundation.principle-of-omniscience.mdᵉ)
-ᵉ [Theᵉ lesserᵉ limitedᵉ principleᵉ ofᵉ omniscience](foundation.lesser-limited-principle-of-omniscience.mdᵉ)
-ᵉ [Theᵉ weakᵉ limitedᵉ principleᵉ ofᵉ omniscience](foundation.weak-limited-principle-of-omniscience.mdᵉ)