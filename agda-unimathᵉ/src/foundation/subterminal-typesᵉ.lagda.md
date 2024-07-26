# Subterminal types

```agda
module foundation.subterminal-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ saidᵉ to beᵉ {{#conceptᵉ "subterminal"ᵉ Agda=is-subterminalᵉ}} ifᵉ itᵉ
[embeds](foundation-core.embeddings.mdᵉ) intoᵉ theᵉ
[unitᵉ type](foundation.unit-type.md).ᵉ Aᵉ typeᵉ isᵉ subterminalᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ isᵉ
aᵉ [proposition](foundation-core.propositions.md).ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  is-subterminalᵉ : UUᵉ lᵉ
  is-subterminalᵉ = is-embᵉ (terminal-mapᵉ Aᵉ)
```

## Properties

### A type is subterminal if and only if it is a proposition

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  abstract
    is-subterminal-is-proof-irrelevantᵉ :
      is-proof-irrelevantᵉ Aᵉ → is-subterminalᵉ Aᵉ
    is-subterminal-is-proof-irrelevantᵉ Hᵉ =
      is-emb-is-embᵉ
        ( λ xᵉ → is-emb-is-equivᵉ (is-equiv-is-contrᵉ _ (Hᵉ xᵉ) is-contr-unitᵉ))

  abstract
    is-subterminal-all-elements-equalᵉ : all-elements-equalᵉ Aᵉ → is-subterminalᵉ Aᵉ
    is-subterminal-all-elements-equalᵉ =
      is-subterminal-is-proof-irrelevantᵉ ∘ᵉ
      is-proof-irrelevant-all-elements-equalᵉ

  abstract
    is-subterminal-is-propᵉ : is-propᵉ Aᵉ → is-subterminalᵉ Aᵉ
    is-subterminal-is-propᵉ = is-subterminal-all-elements-equalᵉ ∘ᵉ eq-is-prop'ᵉ

  abstract
    is-prop-is-subterminalᵉ : is-subterminalᵉ Aᵉ → is-propᵉ Aᵉ
    is-prop-is-subterminalᵉ Hᵉ xᵉ yᵉ =
      is-contr-is-equivᵉ
        ( starᵉ ＝ᵉ starᵉ)
        ( apᵉ (terminal-mapᵉ Aᵉ))
        ( Hᵉ xᵉ yᵉ)
        ( is-prop-unitᵉ starᵉ starᵉ)

  abstract
    eq-is-subterminalᵉ : is-subterminalᵉ Aᵉ → all-elements-equalᵉ Aᵉ
    eq-is-subterminalᵉ = eq-is-prop'ᵉ ∘ᵉ is-prop-is-subterminalᵉ

  abstract
    is-proof-irrelevant-is-subterminalᵉ :
      is-subterminalᵉ Aᵉ → is-proof-irrelevantᵉ Aᵉ
    is-proof-irrelevant-is-subterminalᵉ Hᵉ =
      is-proof-irrelevant-all-elements-equalᵉ (eq-is-subterminalᵉ Hᵉ)
```

## Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}