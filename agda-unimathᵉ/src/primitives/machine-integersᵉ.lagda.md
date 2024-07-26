# Machine integers

```agda
module primitives.machine-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ `Word64`ᵉ typeᵉ representsᵉ 64-bitᵉ machineᵉ words.ᵉ Agdaᵉ providesᵉ primitive
functionsᵉ to manipulateᵉ them.ᵉ

## Definitions

```agda
postulate
  Word64ᵉ : UUᵉ lzero



primitive
  primWord64ToNatᵉ : Word64ᵉ → ℕᵉ
  primWord64FromNatᵉ : ℕᵉ → Word64ᵉ
  primWord64ToNatInjectiveᵉ :
    (aᵉ bᵉ : Word64ᵉ) → primWord64ToNatᵉ aᵉ ＝ᵉ primWord64ToNatᵉ bᵉ → aᵉ ＝ᵉ bᵉ
```