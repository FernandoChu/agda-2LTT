# The weak limited principle of omniscience

```agda
module foundation.weak-limited-principle-of-omniscienceᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.disjunctionᵉ
open import foundation.negationᵉ
open import foundation.universal-quantificationᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Statement

Theᵉ {{#conceptᵉ "Weakᵉ Limitedᵉ Principleᵉ ofᵉ Omniscience"ᵉ}} assertsᵉ thatᵉ forᵉ anyᵉ
[sequence](foundation.sequences.mdᵉ) `fᵉ : ℕᵉ → Finᵉ 2`ᵉ eitherᵉ `fᵉ nᵉ ＝ᵉ 0`ᵉ forᵉ allᵉ
`nᵉ : ℕ`ᵉ orᵉ not.ᵉ Inᵉ particular,ᵉ itᵉ isᵉ aᵉ restrictedᵉ formᵉ ofᵉ theᵉ
[lawᵉ ofᵉ excludedᵉ middle](foundation.law-of-excluded-middle.md).ᵉ

```agda
WLPO-Propᵉ : Propᵉ lzero
WLPO-Propᵉ =
  ∀'ᵉ
    ( ℕᵉ → Finᵉ 2ᵉ)
    ( λ fᵉ →
      disjunction-Propᵉ
        ( ∀'ᵉ ℕᵉ (λ nᵉ → Id-Propᵉ (Fin-Setᵉ 2ᵉ) (fᵉ nᵉ) (zero-Finᵉ 1ᵉ)))
        ( ¬'ᵉ (∀'ᵉ ℕᵉ (λ nᵉ → Id-Propᵉ (Fin-Setᵉ 2ᵉ) (fᵉ nᵉ) (zero-Finᵉ 1ᵉ)))))

WLPOᵉ : UUᵉ lzero
WLPOᵉ = type-Propᵉ WLPO-Propᵉ
```

## See also

-ᵉ [Theᵉ principleᵉ ofᵉ omniscience](foundation.principle-of-omniscience.mdᵉ)
-ᵉ [Theᵉ limitedᵉ principleᵉ ofᵉ omniscience](foundation.limited-principle-of-omniscience.mdᵉ)
-ᵉ [Theᵉ lesserᵉ limitedᵉ principleᵉ ofᵉ omniscience](foundation.lesser-limited-principle-of-omniscience.mdᵉ)