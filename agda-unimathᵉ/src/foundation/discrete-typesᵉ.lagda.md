# Discrete types

```agda
module foundation.discrete-typesᵉ where

open import foundation-core.discrete-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relationsᵉ
open import foundation.binary-relationsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.tight-apartness-relationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.coproduct-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Aᵉ discreteᵉ typeᵉ isᵉ aᵉ typeᵉ thatᵉ hasᵉ decidableᵉ equality.ᵉ

## Properties

### The apartness relation on a discrete type is negated equality

```agda
module _
  {lᵉ : Level} (Xᵉ : Discrete-Typeᵉ lᵉ)
  where

  rel-apart-Discrete-Typeᵉ : Relation-Propᵉ lᵉ (type-Discrete-Typeᵉ Xᵉ)
  rel-apart-Discrete-Typeᵉ xᵉ yᵉ = neg-type-Propᵉ (xᵉ ＝ᵉ yᵉ)

  apart-Discrete-Typeᵉ : (xᵉ yᵉ : type-Discrete-Typeᵉ Xᵉ) → UUᵉ lᵉ
  apart-Discrete-Typeᵉ xᵉ yᵉ = type-Propᵉ (rel-apart-Discrete-Typeᵉ xᵉ yᵉ)

  antireflexive-apart-Discrete-Typeᵉ : is-antireflexiveᵉ rel-apart-Discrete-Typeᵉ
  antireflexive-apart-Discrete-Typeᵉ xᵉ rᵉ = rᵉ reflᵉ

  symmetric-apart-Discrete-Typeᵉ : is-symmetricᵉ apart-Discrete-Typeᵉ
  symmetric-apart-Discrete-Typeᵉ xᵉ yᵉ Hᵉ pᵉ = Hᵉ (invᵉ pᵉ)

  cotransitive-apart-Discrete-Typeᵉ : is-cotransitiveᵉ rel-apart-Discrete-Typeᵉ
  cotransitive-apart-Discrete-Typeᵉ xᵉ yᵉ zᵉ rᵉ
    with has-decidable-equality-type-Discrete-Typeᵉ Xᵉ xᵉ zᵉ
  ... | inlᵉ reflᵉ = unit-trunc-Propᵉ (inrᵉ (λ sᵉ → rᵉ (invᵉ sᵉ)))
  ... | inrᵉ npᵉ = unit-trunc-Propᵉ (inlᵉ npᵉ)

  is-tight-apart-Discrete-Typeᵉ :
    is-tightᵉ rel-apart-Discrete-Typeᵉ
  is-tight-apart-Discrete-Typeᵉ xᵉ yᵉ =
    double-negation-elim-is-decidableᵉ
      ( has-decidable-equality-type-Discrete-Typeᵉ Xᵉ xᵉ yᵉ)

  apartness-relation-Discrete-Typeᵉ :
    Apartness-Relationᵉ lᵉ (type-Discrete-Typeᵉ Xᵉ)
  pr1ᵉ apartness-relation-Discrete-Typeᵉ = rel-apart-Discrete-Typeᵉ
  pr1ᵉ (pr2ᵉ apartness-relation-Discrete-Typeᵉ) = antireflexive-apart-Discrete-Typeᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ apartness-relation-Discrete-Typeᵉ)) =
    symmetric-apart-Discrete-Typeᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ apartness-relation-Discrete-Typeᵉ)) =
    cotransitive-apart-Discrete-Typeᵉ

  type-with-apartness-Discrete-Typeᵉ : Type-With-Apartnessᵉ lᵉ lᵉ
  pr1ᵉ type-with-apartness-Discrete-Typeᵉ = type-Discrete-Typeᵉ Xᵉ
  pr2ᵉ type-with-apartness-Discrete-Typeᵉ = apartness-relation-Discrete-Typeᵉ

  tight-apartness-relation-Discrete-Typeᵉ :
    Tight-Apartness-Relationᵉ lᵉ (type-Discrete-Typeᵉ Xᵉ)
  pr1ᵉ tight-apartness-relation-Discrete-Typeᵉ =
    apartness-relation-Discrete-Typeᵉ
  pr2ᵉ tight-apartness-relation-Discrete-Typeᵉ =
    is-tight-apart-Discrete-Typeᵉ

  type-with-tight-apartness-Discrete-Typeᵉ : Type-With-Tight-Apartnessᵉ lᵉ lᵉ
  pr1ᵉ type-with-tight-apartness-Discrete-Typeᵉ =
    type-with-apartness-Discrete-Typeᵉ
  pr2ᵉ type-with-tight-apartness-Discrete-Typeᵉ =
    is-tight-apart-Discrete-Typeᵉ
```