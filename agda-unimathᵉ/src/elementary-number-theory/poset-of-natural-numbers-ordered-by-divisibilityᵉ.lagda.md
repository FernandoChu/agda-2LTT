# The poset of natural numbers ordered by divisibility

```agda
module
  elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibilityᵉ
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
```

</details>

## Idea

Theᵉ **posetᵉ ofᵉ naturalᵉ numbersᵉ orderedᵉ byᵉ divisibility**ᵉ consistsᵉ ofᵉ theᵉ
[naturalᵉ numbers](elementary-number-theory.natural-numbers.mdᵉ) andᵉ itsᵉ orderingᵉ
isᵉ definedᵉ byᵉ `mᵉ ≤ᵉ nᵉ :=ᵉ mᵉ | n`,ᵉ i.e.,ᵉ byᵉ
[divisibility](elementary-number-theory.divisibility-natural-numbers.md).ᵉ

Theᵉ divisibilityᵉ relationᵉ `mᵉ | n`ᵉ onᵉ theᵉ naturalᵉ numbers,ᵉ however,ᵉ isᵉ onlyᵉ
valuedᵉ in theᵉ [propositions](foundation.propositions.mdᵉ) whenᵉ bothᵉ `m`ᵉ andᵉ `n`ᵉ
areᵉ [nonzero](elementary-number-theory.nonzero-natural-numbers.md).ᵉ Weᵉ thereforeᵉ
redefineᵉ theᵉ divisibilityᵉ relationᵉ in theᵉ followingᵉ wayᵉ: Aᵉ numberᵉ `m`ᵉ isᵉ saidᵉ to
**divide**ᵉ aᵉ numberᵉ `n`ᵉ ifᵉ thereᵉ
[merelyᵉ exists](foundation.existential-quantification.mdᵉ) aᵉ numberᵉ `k`ᵉ suchᵉ thatᵉ
`kmᵉ ＝ᵉ n`.ᵉ Sinceᵉ mereᵉ existenceᵉ isᵉ definedᵉ viaᵉ theᵉ
[propoositionalᵉ truncation](foundation.propositional-truncations.md),ᵉ thisᵉ canᵉ
beᵉ statedᵉ alternativelyᵉ asᵉ theᵉ propositionᵉ

```text
  trunc-Propᵉ (div-ℕᵉ mᵉ n).ᵉ
```

Inᵉ otherᵉ words,ᵉ weᵉ simplyᵉ forceᵉ theᵉ divisibilityᵉ relationᵉ to takeᵉ valuesᵉ in
propositionsᵉ byᵉ identifyingᵉ allᵉ witnessesᵉ ofᵉ divisibility.ᵉ

## Definition

```agda
leq-prop-ℕ-Divᵉ : ℕᵉ → ℕᵉ → Propᵉ lzero
leq-prop-ℕ-Divᵉ mᵉ nᵉ = trunc-Propᵉ (div-ℕᵉ mᵉ nᵉ)

leq-ℕ-Divᵉ : ℕᵉ → ℕᵉ → UUᵉ lzero
leq-ℕ-Divᵉ mᵉ nᵉ = type-Propᵉ (leq-prop-ℕ-Divᵉ mᵉ nᵉ)

refl-leq-ℕ-Divᵉ : (nᵉ : ℕᵉ) → leq-ℕ-Divᵉ nᵉ nᵉ
refl-leq-ℕ-Divᵉ nᵉ = unit-trunc-Propᵉ (refl-div-ℕᵉ nᵉ)

antisymmetric-leq-ℕ-Divᵉ : (mᵉ nᵉ : ℕᵉ) → leq-ℕ-Divᵉ mᵉ nᵉ → leq-ℕ-Divᵉ nᵉ mᵉ → mᵉ ＝ᵉ nᵉ
antisymmetric-leq-ℕ-Divᵉ mᵉ nᵉ Hᵉ Kᵉ =
  apply-twice-universal-property-trunc-Propᵉ Hᵉ Kᵉ
    ( Id-Propᵉ ℕ-Setᵉ _ _)
    ( antisymmetric-div-ℕᵉ mᵉ nᵉ)

transitive-leq-ℕ-Divᵉ :
  (mᵉ nᵉ oᵉ : ℕᵉ) → leq-ℕ-Divᵉ nᵉ oᵉ → leq-ℕ-Divᵉ mᵉ nᵉ → leq-ℕ-Divᵉ mᵉ oᵉ
transitive-leq-ℕ-Divᵉ mᵉ nᵉ oᵉ Hᵉ Kᵉ =
  apply-twice-universal-property-trunc-Propᵉ Hᵉ Kᵉ
    ( leq-prop-ℕ-Divᵉ mᵉ oᵉ)
    ( λ H'ᵉ K'ᵉ → unit-trunc-Propᵉ (transitive-div-ℕᵉ mᵉ nᵉ oᵉ H'ᵉ K'ᵉ))

ℕ-Div-Preorderᵉ : Preorderᵉ lzero lzero
pr1ᵉ ℕ-Div-Preorderᵉ = ℕᵉ
pr1ᵉ (pr2ᵉ ℕ-Div-Preorderᵉ) = leq-prop-ℕ-Divᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ ℕ-Div-Preorderᵉ)) = refl-leq-ℕ-Divᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ ℕ-Div-Preorderᵉ)) = transitive-leq-ℕ-Divᵉ

ℕ-Div-Posetᵉ : Posetᵉ lzero lzero
pr1ᵉ ℕ-Div-Posetᵉ = ℕ-Div-Preorderᵉ
pr2ᵉ ℕ-Div-Posetᵉ = antisymmetric-leq-ℕ-Divᵉ
```