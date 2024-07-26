# Floats

```agda
module primitives.floatsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.booleansᵉ
open import foundation.maybeᵉ
open import foundation.universe-levelsᵉ

open import primitives.machine-integersᵉ
open import primitives.stringsᵉ
```

</details>

## Idea

Theᵉ `Float`ᵉ typeᵉ representsᵉ IEEE754ᵉ floats.ᵉ Agdaᵉ providesᵉ primitive functionsᵉ to
manipulateᵉ them.ᵉ Floatsᵉ canᵉ beᵉ writtenᵉ asᵉ usual,ᵉ using dotsᵉ asᵉ separators,ᵉ e.g.ᵉ
`3.14`.ᵉ

## Definitions

```agda
postulate
  Floatᵉ : UUᵉ lzero



primitive
  --ᵉ Relationsᵉ
  primFloatInequalityᵉ : Floatᵉ → Floatᵉ → boolᵉ
  primFloatEqualityᵉ : Floatᵉ → Floatᵉ → boolᵉ
  primFloatLessᵉ : Floatᵉ → Floatᵉ → boolᵉ
  primFloatIsInfiniteᵉ : Floatᵉ → boolᵉ
  primFloatIsNaNᵉ : Floatᵉ → boolᵉ
  primFloatIsNegativeZeroᵉ : Floatᵉ → boolᵉ
  primFloatIsSafeIntegerᵉ : Floatᵉ → boolᵉ
  --ᵉ Conversionsᵉ
  primFloatToWord64ᵉ : Floatᵉ → Maybe'ᵉ Word64ᵉ
  primNatToFloatᵉ : ℕᵉ → Floatᵉ
  --ᵉ primIntToFloatᵉ             : Intᵉ → Floatᵉ
  --ᵉ primFloatRoundᵉ             : Floatᵉ → Maybe'ᵉ Intᵉ
  --ᵉ primFloatFloorᵉ             : Floatᵉ → Maybe'ᵉ Intᵉ
  --ᵉ primFloatCeilingᵉ           : Floatᵉ → Maybe'ᵉ Intᵉ
  --ᵉ primFloatToRatioᵉ           : Floatᵉ → (Σᵉ Intᵉ λ _ → Intᵉ)
  --ᵉ primRatioToFloatᵉ           : Intᵉ → Intᵉ → Floatᵉ
  --ᵉ primFloatDecodeᵉ            : Floatᵉ → Maybe'ᵉ (Σᵉ Intᵉ λ _ → Intᵉ)
  --ᵉ primFloatEncodeᵉ            : Intᵉ → Intᵉ → Maybe'ᵉ Floatᵉ
  primShowFloatᵉ : Floatᵉ → Stringᵉ
  --ᵉ Operationsᵉ
  primFloatPlusᵉ : Floatᵉ → Floatᵉ → Floatᵉ
  primFloatMinusᵉ : Floatᵉ → Floatᵉ → Floatᵉ
  primFloatTimesᵉ : Floatᵉ → Floatᵉ → Floatᵉ
  primFloatDivᵉ : Floatᵉ → Floatᵉ → Floatᵉ
  primFloatPowᵉ : Floatᵉ → Floatᵉ → Floatᵉ
  primFloatNegateᵉ : Floatᵉ → Floatᵉ
  primFloatSqrtᵉ : Floatᵉ → Floatᵉ
  primFloatExpᵉ : Floatᵉ → Floatᵉ
  primFloatLogᵉ : Floatᵉ → Floatᵉ
  primFloatSinᵉ : Floatᵉ → Floatᵉ
  primFloatCosᵉ : Floatᵉ → Floatᵉ
  primFloatTanᵉ : Floatᵉ → Floatᵉ
  primFloatASinᵉ : Floatᵉ → Floatᵉ
  primFloatACosᵉ : Floatᵉ → Floatᵉ
  primFloatATanᵉ : Floatᵉ → Floatᵉ
  primFloatATan2ᵉ : Floatᵉ → Floatᵉ → Floatᵉ
  primFloatSinhᵉ : Floatᵉ → Floatᵉ
  primFloatCoshᵉ : Floatᵉ → Floatᵉ
  primFloatTanhᵉ : Floatᵉ → Floatᵉ
  primFloatASinhᵉ : Floatᵉ → Floatᵉ
  primFloatACoshᵉ : Floatᵉ → Floatᵉ
  primFloatATanhᵉ : Floatᵉ → Floatᵉ
```