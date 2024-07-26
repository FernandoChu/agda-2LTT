# Names

```agda
module reflection.namesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleansᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import primitives.machine-integersᵉ
open import primitives.stringsᵉ
```

</details>

## Idea

Theᵉ `Name-Agda`ᵉ typeᵉ representsᵉ quotedᵉ names,ᵉ i.e.ᵉ theyᵉ areᵉ anᵉ abstract
syntacticᵉ representationᵉ ofᵉ terms.ᵉ Agdaᵉ providesᵉ primitive functionsᵉ to
manipulateᵉ them,ᵉ givingᵉ themᵉ anᵉ equalityᵉ andᵉ ordering.ᵉ Aᵉ closedᵉ termᵉ canᵉ beᵉ
convertedᵉ to aᵉ quotedᵉ nameᵉ byᵉ meansᵉ ofᵉ theᵉ `quote`ᵉ keyword,ᵉ e.g.ᵉ `quoteᵉ bool`.ᵉ

## Definition

```agda
postulate
  Name-Agdaᵉ : UUᵉ lzero



primitive
  primQNameEqualityᵉ : Name-Agdaᵉ → Name-Agdaᵉ → boolᵉ
  primQNameLessᵉ : Name-Agdaᵉ → Name-Agdaᵉ → boolᵉ
  primShowQNameᵉ : Name-Agdaᵉ → Stringᵉ
  primQNameToWord64sᵉ : Name-Agdaᵉ → Word64ᵉ ×ᵉ Word64ᵉ
  primQNameToWord64sInjectiveᵉ :
    (aᵉ bᵉ : Name-Agdaᵉ) → primQNameToWord64sᵉ aᵉ ＝ᵉ primQNameToWord64sᵉ bᵉ → aᵉ ＝ᵉ bᵉ
```

## Examples

```agda
_ : primQNameLessᵉ (quoteᵉ boolᵉ) (quoteᵉ unitᵉ) ＝ᵉ trueᵉ
_ = reflᵉ

_ : primShowQNameᵉ (quoteᵉ boolᵉ) ＝ᵉ "foundation.booleans.bool"ᵉ
_ = reflᵉ
```