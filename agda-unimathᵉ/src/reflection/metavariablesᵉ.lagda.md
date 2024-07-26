# Metavariables

```agda
module reflection.metavariablesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.booleansᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import lists.listsᵉ

open import primitives.stringsᵉ
```

</details>

## Idea

Theᵉ `Metavariable-Agda`ᵉ typeᵉ representsᵉ metavariablesᵉ in Agda.ᵉ

## Definition

```agda
postulate
  Metavariable-Agdaᵉ : UUᵉ lzero



primitive
  primMetaEqualityᵉ :
    Metavariable-Agdaᵉ → Metavariable-Agdaᵉ → boolᵉ
  primMetaLessᵉ :
    Metavariable-Agdaᵉ → Metavariable-Agdaᵉ → boolᵉ
  primShowMetaᵉ :
    Metavariable-Agdaᵉ → Stringᵉ
  primMetaToNatᵉ :
    Metavariable-Agdaᵉ → ℕᵉ
  primMetaToNatInjectiveᵉ :
    (aᵉ bᵉ : Metavariable-Agdaᵉ) → primMetaToNatᵉ aᵉ ＝ᵉ primMetaToNatᵉ bᵉ → aᵉ ＝ᵉ bᵉ

data Blocker-Agdaᵉ : UUᵉ lzero where
  any-Blocker-Agdaᵉ : listᵉ Blocker-Agdaᵉ → Blocker-Agdaᵉ
  all-Blocker-Agdaᵉ : listᵉ Blocker-Agdaᵉ → Blocker-Agdaᵉ
  metavariable-Blocker-Agdaᵉ : Metavariable-Agdaᵉ → Blocker-Agdaᵉ





```