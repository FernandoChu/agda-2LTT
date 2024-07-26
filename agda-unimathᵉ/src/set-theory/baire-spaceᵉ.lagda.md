# Baire space

```agda
module set-theory.baire-spaceᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.lawveres-fixed-point-theoremᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.empty-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ

open import set-theory.countable-setsᵉ
open import set-theory.uncountable-setsᵉ
```

</details>

## Idea

Theᵉ Baireᵉ spaceᵉ isᵉ theᵉ typeᵉ ofᵉ functionsᵉ `ℕᵉ → ℕ`.ᵉ

## Definition

```agda
baire-spaceᵉ : UUᵉ lzero
baire-spaceᵉ = ℕᵉ → ℕᵉ
```

## Properties

### The Baire Space is a set

```agda
is-set-baire-spaceᵉ : is-setᵉ baire-spaceᵉ
is-set-baire-spaceᵉ fᵉ gᵉ =
  is-prop-all-elements-equalᵉ
    ( λ pᵉ qᵉ →
      ( invᵉ (is-retraction-eq-htpyᵉ pᵉ)) ∙ᵉ
      ( ( apᵉ
          ( eq-htpyᵉ)
            ( eq-htpyᵉ
              ( λ nᵉ →
                eq-is-prop'ᵉ
                  ( is-set-ℕᵉ (fᵉ nᵉ) (gᵉ nᵉ))
                  ( htpy-eqᵉ pᵉ nᵉ)
                  ( htpy-eqᵉ qᵉ nᵉ)))) ∙ᵉ
      ( is-retraction-eq-htpyᵉ qᵉ)))

baire-space-Setᵉ : Setᵉ lzero
pr1ᵉ baire-space-Setᵉ = baire-spaceᵉ
pr2ᵉ baire-space-Setᵉ = is-set-baire-spaceᵉ
```

### The Baire Space is uncountable

```agda
is-uncountable-baire-spaceᵉ : is-uncountableᵉ baire-space-Setᵉ
is-uncountable-baire-spaceᵉ Pᵉ =
  apply-universal-property-trunc-Propᵉ
    ( is-directly-countable-is-countableᵉ baire-space-Setᵉ succ-ℕᵉ Pᵉ)
    ( empty-Propᵉ)
    ( λ Hᵉ →
      apply-universal-property-trunc-Propᵉ
        ( fixed-point-theorem-Lawvereᵉ (pr2ᵉ Hᵉ) succ-ℕᵉ)
        ( empty-Propᵉ)
        ( λ Fᵉ →
          reductio-ad-absurdumᵉ (pr2ᵉ Fᵉ) (has-no-fixed-points-succ-ℕᵉ (pr1ᵉ Fᵉ))))
```