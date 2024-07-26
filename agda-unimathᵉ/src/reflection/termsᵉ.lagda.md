# Terms

```agda
module reflection.termsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.universe-levelsᵉ

open import lists.listsᵉ

open import primitives.stringsᵉ

open import reflection.abstractionsᵉ
open import reflection.argumentsᵉ
open import reflection.literalsᵉ
open import reflection.metavariablesᵉ
open import reflection.namesᵉ
```

</details>

## Idea

Inᵉ thisᵉ module weᵉ representᵉ theᵉ termsᵉ ofᵉ agdaᵉ byᵉ anᵉ inductive definitionᵉ ofᵉ theᵉ
typeᵉ `Term-Agda`.ᵉ Seeᵉ theᵉ commentsᵉ forᵉ detailsᵉ onᵉ theᵉ constructors.ᵉ

Weᵉ canᵉ obtainᵉ aᵉ `Term-Agda`ᵉ fromᵉ anᵉ agdaᵉ termᵉ throughᵉ theᵉ keywordᵉ `quoteTerm`.ᵉ

Forᵉ concreteᵉ examples,ᵉ seeᵉ
[`reflection.definitions`](reflection.definitions.md).ᵉ

## Definition

```agda
data Term-Agdaᵉ : UUᵉ lzero
data Sort-Agdaᵉ : UUᵉ lzero
data Pattern-Agdaᵉ : UUᵉ lzero
data Clause-Agdaᵉ : UUᵉ lzero
Telescope-Agdaᵉ = listᵉ (Stringᵉ ×ᵉ Argument-Agdaᵉ Term-Agdaᵉ)

data Term-Agdaᵉ where
  --ᵉ Variables,ᵉ where theᵉ naturalᵉ numberᵉ isᵉ aᵉ deᵉ Bruijnᵉ indexᵉ
  variable-Term-Agdaᵉ : ℕᵉ → listᵉ (Argument-Agdaᵉ Term-Agdaᵉ) → Term-Agdaᵉ
  --ᵉ Anᵉ applicationᵉ ofᵉ aᵉ constructor orᵉ definitionᵉ
  constructor-Term-Agdaᵉ : Name-Agdaᵉ → listᵉ (Argument-Agdaᵉ Term-Agdaᵉ) → Term-Agdaᵉ
  definition-Term-Agdaᵉ : Name-Agdaᵉ → listᵉ (Argument-Agdaᵉ Term-Agdaᵉ) → Term-Agdaᵉ
  --ᵉ Aᵉ lambdaᵉ abstractionᵉ
  lambda-Term-Agdaᵉ :
    Visibility-Argument-Agdaᵉ → Abstraction-Agdaᵉ Term-Agdaᵉ → Term-Agdaᵉ
  pattern-lambda-Term-Agdaᵉ :
    listᵉ Clause-Agdaᵉ → listᵉ (Argument-Agdaᵉ Term-Agdaᵉ) → Term-Agdaᵉ
  --ᵉ Aᵉ Piᵉ termᵉ
  dependent-product-Term-Agdaᵉ :
    Argument-Agdaᵉ Term-Agdaᵉ → Abstraction-Agdaᵉ Term-Agdaᵉ → Term-Agdaᵉ
  --ᵉ Aᵉ sort,ᵉ alsoᵉ calledᵉ aᵉ universeᵉ
  sort-Term-Agdaᵉ : Sort-Agdaᵉ → Term-Agdaᵉ
  --ᵉ Aᵉ literal,ᵉ e.g.ᵉ `3`ᵉ
  literal-Term-Agdaᵉ : Literal-Agdaᵉ → Term-Agdaᵉ
  --ᵉ Aᵉ metavariableᵉ
  metavariable-Term-Agdaᵉ :
    Metavariable-Agdaᵉ → listᵉ (Argument-Agdaᵉ Term-Agdaᵉ) → Term-Agdaᵉ
  --ᵉ Aᵉ holeᵉ
  unknown-Term-Agdaᵉ : Term-Agdaᵉ

data Sort-Agdaᵉ where
  --ᵉ Aᵉ universeᵉ ofᵉ aᵉ givenᵉ (possiblyᵉ neutralᵉ) levelᵉ
  universe-Sort-Agdaᵉ : Term-Agdaᵉ → Sort-Agdaᵉ
  --ᵉ Aᵉ universeᵉ ofᵉ aᵉ givenᵉ concreteᵉ levelᵉ
  fixed-universe-Sort-Agdaᵉ : ℕᵉ → Sort-Agdaᵉ
  --ᵉ Aᵉ Propᵉ ofᵉ aᵉ givenᵉ (possiblyᵉ neutralᵉ) levelᵉ
  prop-Sort-Agdaᵉ : Term-Agdaᵉ → Sort-Agdaᵉ
  --ᵉ Aᵉ Propᵉ ofᵉ aᵉ givenᵉ concreteᵉ levelᵉ
  fixed-prop-Sort-Agdaᵉ : ℕᵉ → Sort-Agdaᵉ
  --ᵉ UUωiᵉ ofᵉ aᵉ givenᵉ concreteᵉ levelᵉ i.ᵉ
  fixed-large-universe-Sort-Agdaᵉ : ℕᵉ → Sort-Agdaᵉ
  --ᵉ Aᵉ holeᵉ
  unknown-Sort-Agdaᵉ : Sort-Agdaᵉ

data Pattern-Agdaᵉ where
  constructor-Term-Agdaᵉ :
    Name-Agdaᵉ → listᵉ (Argument-Agdaᵉ Pattern-Agdaᵉ) → Pattern-Agdaᵉ
  dot-Pattern-Agdaᵉ : Term-Agdaᵉ → Pattern-Agdaᵉ
  variable-Term-Agdaᵉ : ℕᵉ → Pattern-Agdaᵉ
  literal-Term-Agdaᵉ : Literal-Agdaᵉ → Pattern-Agdaᵉ
  projection-Pattern-Agdaᵉ : Name-Agdaᵉ → Pattern-Agdaᵉ
  --ᵉ Absurdᵉ pattern with aᵉ deᵉ Bruijnᵉ indexᵉ
  absurd-Pattern-Agdaᵉ : ℕᵉ → Pattern-Agdaᵉ

--ᵉ Aᵉ clause-Clause-Agdaᵉ onᵉ aᵉ pattern matchingᵉ lambdaᵉ
data Clause-Agdaᵉ where
  clause-Clause-Agdaᵉ :
    Telescope-Agdaᵉ → listᵉ (Argument-Agdaᵉ Pattern-Agdaᵉ) → Term-Agdaᵉ → Clause-Agdaᵉ
  absurd-Clause-Agdaᵉ :
    Telescope-Agdaᵉ → listᵉ (Argument-Agdaᵉ Pattern-Agdaᵉ) → Clause-Agdaᵉ
```

## Bindings

```agda
































```

## Helpers

```agda
replicate-hidden-Argument-Agdaᵉ : ℕᵉ → listᵉ (Argument-Agdaᵉ Term-Agdaᵉ)
replicate-hidden-Argument-Agdaᵉ zero-ℕᵉ =
  nilᵉ
replicate-hidden-Argument-Agdaᵉ (succ-ℕᵉ nᵉ) =
  consᵉ
    ( hidden-Argument-Agdaᵉ (unknown-Term-Agdaᵉ))
    ( replicate-hidden-Argument-Agdaᵉ nᵉ)
```