# Binary equivalences on unordered pairs of types

```agda
module foundation.binary-equivalences-unordered-pairs-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-operations-unordered-pairs-of-typesᵉ
open import foundation.products-unordered-pairs-of-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
```

</details>

## Idea

Aᵉ binaryᵉ operationᵉ `fᵉ : ((iᵉ : Iᵉ) → Aᵉ iᵉ) → B`ᵉ isᵉ aᵉ binaryᵉ equivalenceᵉ ifᵉ forᵉ eachᵉ
`iᵉ : I`ᵉ andᵉ eachᵉ `xᵉ : Aᵉ i`ᵉ theᵉ mapᵉ `fᵉ ∘ᵉ pairᵉ xᵉ : Aᵉ (swapᵉ iᵉ) → B`ᵉ isᵉ anᵉ
equivalence.ᵉ

## Definition

```agda
is-binary-equiv-unordered-pair-typesᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : unordered-pairᵉ (UUᵉ l1ᵉ)) {Bᵉ : UUᵉ l2ᵉ}
  (fᵉ : binary-operation-unordered-pair-typesᵉ Aᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-binary-equiv-unordered-pair-typesᵉ Aᵉ fᵉ =
  (iᵉ : type-unordered-pairᵉ Aᵉ) (xᵉ : element-unordered-pairᵉ Aᵉ iᵉ) →
  is-equivᵉ (fᵉ ∘ᵉ pair-product-unordered-pair-typesᵉ Aᵉ iᵉ xᵉ)
```