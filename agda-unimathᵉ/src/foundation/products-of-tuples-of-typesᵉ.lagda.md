# Products of tuples of types

```agda
module foundation.products-of-tuples-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.tuples-of-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ productᵉ ofᵉ anᵉ `n`-tupleᵉ ofᵉ typesᵉ isᵉ theirᵉ dependentᵉ product.ᵉ

## Definition

### Products of `n`-tuples of types

```agda
product-tuple-typesᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) → tuple-typesᵉ lᵉ nᵉ → UUᵉ lᵉ
product-tuple-typesᵉ nᵉ Aᵉ = (iᵉ : Finᵉ nᵉ) → Aᵉ iᵉ
```

### The projection maps

```agda
pr-product-tuple-typesᵉ :
  {lᵉ : Level} {nᵉ : ℕᵉ} (Aᵉ : tuple-typesᵉ lᵉ nᵉ) (iᵉ : Finᵉ nᵉ) →
  product-tuple-typesᵉ nᵉ Aᵉ → Aᵉ iᵉ
pr-product-tuple-typesᵉ Aᵉ iᵉ fᵉ = fᵉ iᵉ
```