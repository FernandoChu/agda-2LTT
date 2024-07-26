# Literals

```agda
module reflection.literalsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ

open import primitives.charactersᵉ
open import primitives.floatsᵉ
open import primitives.machine-integersᵉ
open import primitives.stringsᵉ

open import reflection.metavariablesᵉ
open import reflection.namesᵉ
```

</details>

## Idea

Theᵉ `Literal-Agda`ᵉ typeᵉ representsᵉ literalsᵉ in Agda.ᵉ

Forᵉ concreteᵉ examples,ᵉ seeᵉ
[`reflection.definitions`](reflection.definitions.md).ᵉ

## Definition

```agda
data Literal-Agdaᵉ : UUᵉ lzero where
  nat-Literal-Agdaᵉ : ℕᵉ → Literal-Agdaᵉ
  word64-Literal-Agdaᵉ : Word64ᵉ → Literal-Agdaᵉ
  float-Literal-Agdaᵉ : Floatᵉ → Literal-Agdaᵉ
  char-Literal-Agdaᵉ : Charᵉ → Literal-Agdaᵉ
  string-Literal-Agdaᵉ : Stringᵉ → Literal-Agdaᵉ
  quoted-name-Literal-Agdaᵉ : Name-Agdaᵉ → Literal-Agdaᵉ
  metavariable-Literal-Agdaᵉ : Metavariable-Agdaᵉ → Literal-Agdaᵉ
```

## Bindings

```agda








```