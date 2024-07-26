# Strings

```agda
module primitives.stringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.booleansᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.maybeᵉ
open import foundation.universe-levelsᵉ

open import lists.listsᵉ

open import primitives.charactersᵉ
```

</details>

## Idea

Theᵉ `String`ᵉ typeᵉ representsᵉ strings.ᵉ Agdaᵉ providesᵉ primitive functionsᵉ to
manipulateᵉ them.ᵉ Stringsᵉ areᵉ writtenᵉ betweenᵉ doubleᵉ quotes,ᵉ e.g.ᵉ
`"agda-unimath"`.ᵉ

## Definitions

```agda
postulate
  Stringᵉ : UUᵉ lzero



primitive
  primStringUnconsᵉ : Stringᵉ → Maybe'ᵉ (Σᵉ Charᵉ (λ _ → Stringᵉ))
  primStringToListᵉ : Stringᵉ → listᵉ Charᵉ
  primStringFromListᵉ : listᵉ Charᵉ → Stringᵉ
  primStringAppendᵉ : Stringᵉ → Stringᵉ → Stringᵉ
  primStringEqualityᵉ : Stringᵉ → Stringᵉ → boolᵉ
  primShowCharᵉ : Charᵉ → Stringᵉ
  primShowStringᵉ : Stringᵉ → Stringᵉ
  primShowNatᵉ : ℕᵉ → Stringᵉ
```