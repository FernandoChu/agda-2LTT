# Binary operations on unordered pairs of types

```agda
module foundation.binary-operations-unordered-pairs-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.products-unordered-pairs-of-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ
```

</details>

## Idea

Aᵉ binaryᵉ operationᵉ onᵉ anᵉ unorderedᵉ pairᵉ ofᵉ typesᵉ Aᵉ indexedᵉ byᵉ aᵉ 2-elementᵉ typeᵉ Iᵉ
isᵉ aᵉ mapᵉ `((iᵉ : Iᵉ) → Aᵉ iᵉ) → B`.ᵉ

## Definition

```agda
binary-operation-unordered-pair-typesᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : unordered-pairᵉ (UUᵉ l1ᵉ)) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
binary-operation-unordered-pair-typesᵉ Aᵉ Bᵉ = product-unordered-pair-typesᵉ Aᵉ → Bᵉ
```