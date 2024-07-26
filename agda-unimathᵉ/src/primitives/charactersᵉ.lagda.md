# Characters

```agda
module primitives.charactersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.booleansᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ `Char`ᵉ typeᵉ representsᵉ aᵉ character.ᵉ Agdaᵉ providesᵉ primitive functionsᵉ to
manipulateᵉ them.ᵉ Charactersᵉ areᵉ writtenᵉ betweenᵉ singleᵉ quotes,ᵉ e.g.ᵉ `'a'`.ᵉ

## Definitions

```agda
postulate
  Charᵉ : UUᵉ lzero



primitive
  primIsLowerᵉ primIsDigitᵉ primIsAlphaᵉ primIsSpaceᵉ primIsAsciiᵉ
    primIsLatin1ᵉ primIsPrintᵉ primIsHexDigitᵉ : Charᵉ → boolᵉ
  primToUpperᵉ primToLowerᵉ : Charᵉ → Charᵉ
  primCharToNatᵉ : Charᵉ → ℕᵉ
  primNatToCharᵉ : ℕᵉ → Charᵉ
  primCharEqualityᵉ : Charᵉ → Charᵉ → boolᵉ
```