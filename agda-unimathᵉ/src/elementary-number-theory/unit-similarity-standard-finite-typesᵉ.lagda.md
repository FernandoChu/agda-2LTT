# Unit similarity on the standard finite types

```agda
module elementary-number-theory.unit-similarity-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.congruence-natural-numbersᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.unit-elements-standard-finite-typesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Twoᵉ elementsᵉ `xᵉ yᵉ : Finᵉ k`ᵉ areᵉ saidᵉ to beᵉ unitᵉ similarᵉ ifᵉ thereᵉ isᵉ aᵉ unitᵉ
elementᵉ `uᵉ : Finᵉ k`ᵉ suchᵉ thatᵉ `mul-Finᵉ uᵉ xᵉ = y`.ᵉ Thisᵉ relationᵉ givesᵉ aᵉ groupoidᵉ
structureᵉ onᵉ `Finᵉ k`.ᵉ

## Definition

### Unit similarity in `Fin k`

```agda
sim-unit-Finᵉ :
  (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ → UUᵉ lzero
sim-unit-Finᵉ kᵉ xᵉ yᵉ = Σᵉ (unit-Finᵉ kᵉ) (λ uᵉ → mul-Finᵉ kᵉ (pr1ᵉ uᵉ) xᵉ ＝ᵉ yᵉ)
```

### Unit similarity on `ℕ`

```agda
sim-unit-ℕᵉ :
  (kᵉ : ℕᵉ) → ℕᵉ → ℕᵉ → UUᵉ lzero
sim-unit-ℕᵉ kᵉ xᵉ yᵉ =
  Σᵉ (Σᵉ ℕᵉ (λ lᵉ → cong-ℕᵉ kᵉ lᵉ 1ᵉ)) (λ lᵉ → cong-ℕᵉ kᵉ ((pr1ᵉ lᵉ) *ℕᵉ xᵉ) yᵉ)
```

### Congruence to `1`

```agda
sim-unit-one-ℕᵉ : (kᵉ xᵉ : ℕᵉ) → UUᵉ lzero
sim-unit-one-ℕᵉ kᵉ xᵉ = Σᵉ ℕᵉ (λ lᵉ → cong-ℕᵉ kᵉ (lᵉ *ℕᵉ xᵉ) 1ᵉ)
```

## Properties

### Unit similarity is an equivalence relation

```agda
refl-sim-unit-Finᵉ : {kᵉ : ℕᵉ} → is-reflexiveᵉ (sim-unit-Finᵉ kᵉ)
pr1ᵉ (refl-sim-unit-Finᵉ {succ-ℕᵉ kᵉ} xᵉ) = one-unit-Finᵉ
pr2ᵉ (refl-sim-unit-Finᵉ {succ-ℕᵉ kᵉ} xᵉ) = left-unit-law-mul-Finᵉ kᵉ xᵉ

symmetric-sim-unit-Finᵉ : {kᵉ : ℕᵉ} → is-symmetricᵉ (sim-unit-Finᵉ kᵉ)
pr1ᵉ (symmetric-sim-unit-Finᵉ {succ-ℕᵉ kᵉ} xᵉ yᵉ (pairᵉ (pairᵉ uᵉ (pairᵉ vᵉ qᵉ)) pᵉ)) =
  inv-unit-Finᵉ (pairᵉ uᵉ (pairᵉ vᵉ qᵉ))
pr2ᵉ (symmetric-sim-unit-Finᵉ {succ-ℕᵉ kᵉ} xᵉ yᵉ (pairᵉ (pairᵉ uᵉ (pairᵉ vᵉ qᵉ)) pᵉ)) =
  ( ( ( apᵉ (mul-Finᵉ (succ-ℕᵉ kᵉ) vᵉ) (invᵉ pᵉ)) ∙ᵉ
        ( invᵉ (associative-mul-Finᵉ (succ-ℕᵉ kᵉ) vᵉ uᵉ xᵉ))) ∙ᵉ
      ( apᵉ (mul-Fin'ᵉ (succ-ℕᵉ kᵉ) xᵉ) qᵉ)) ∙ᵉ
    ( left-unit-law-mul-Finᵉ kᵉ xᵉ)

transitive-sim-unit-Finᵉ : {kᵉ : ℕᵉ} → is-transitiveᵉ (sim-unit-Finᵉ kᵉ)
pr1ᵉ (transitive-sim-unit-Finᵉ {succ-ℕᵉ kᵉ} xᵉ yᵉ zᵉ (pairᵉ vᵉ qᵉ) (pairᵉ uᵉ pᵉ)) =
  mul-unit-Finᵉ (succ-ℕᵉ kᵉ) vᵉ uᵉ
pr2ᵉ (transitive-sim-unit-Finᵉ {succ-ℕᵉ kᵉ} xᵉ yᵉ zᵉ (pairᵉ vᵉ qᵉ) (pairᵉ uᵉ pᵉ)) =
  ( associative-mul-Finᵉ (succ-ℕᵉ kᵉ) (pr1ᵉ vᵉ) (pr1ᵉ uᵉ) xᵉ) ∙ᵉ
  ( apᵉ (mul-Finᵉ (succ-ℕᵉ kᵉ) (pr1ᵉ vᵉ)) pᵉ ∙ᵉ qᵉ)
```

### A natural number `x` is congruent to `1` modulo `k+1` if and only if `[x]_{k+1}` is unit similar to `1`

```agda
is-unit-similar-one-sim-unit-mod-succ-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) → sim-unit-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ) (one-Finᵉ kᵉ) →
  sim-unit-one-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ
pr1ᵉ (is-unit-similar-one-sim-unit-mod-succ-ℕᵉ kᵉ xᵉ (pairᵉ uᵉ pᵉ)) =
  nat-Finᵉ (succ-ℕᵉ kᵉ) (pr1ᵉ uᵉ)
pr2ᵉ (is-unit-similar-one-sim-unit-mod-succ-ℕᵉ kᵉ xᵉ (pairᵉ uᵉ pᵉ)) =
  cong-eq-mod-succ-ℕᵉ kᵉ
    ( (nat-Finᵉ (succ-ℕᵉ kᵉ) (pr1ᵉ uᵉ)) *ℕᵉ xᵉ)
    ( 1ᵉ)
    ( ( eq-mod-succ-cong-ℕᵉ kᵉ
        ( (nat-Finᵉ (succ-ℕᵉ kᵉ) (pr1ᵉ uᵉ)) *ℕᵉ xᵉ)
        ( (nat-Finᵉ (succ-ℕᵉ kᵉ) (pr1ᵉ uᵉ)) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ)))
        ( scalar-invariant-cong-ℕᵉ
          ( succ-ℕᵉ kᵉ)
          ( xᵉ)
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) (pr1ᵉ uᵉ))
          ( symmetric-cong-ℕᵉ
            ( succ-ℕᵉ kᵉ)
            ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))
            ( xᵉ)
            ( cong-nat-mod-succ-ℕᵉ kᵉ xᵉ)))) ∙ᵉ
      ( pᵉ))
```