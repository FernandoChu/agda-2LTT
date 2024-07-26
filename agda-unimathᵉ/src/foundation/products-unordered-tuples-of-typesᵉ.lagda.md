# Products of unordered tuples of types

```agda
module foundation.products-unordered-tuples-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.universal-property-maybeᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-tuplesᵉ
open import foundation.unordered-tuples-of-typesᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ

open import univalent-combinatorics.complements-isolated-elementsᵉ
```

</details>

## Idea

Givenᵉ anᵉ unorderedᵉ pairᵉ ofᵉ types,ᵉ weᵉ canᵉ takeᵉ theirᵉ product.ᵉ Thisᵉ isᵉ aᵉ
commutativeᵉ versionᵉ ofᵉ theᵉ cartesianᵉ productᵉ operationᵉ onᵉ types.ᵉ

## Definition

```agda
product-unordered-tuple-typesᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) → unordered-tupleᵉ nᵉ (UUᵉ lᵉ) → (UUᵉ lᵉ)
product-unordered-tuple-typesᵉ nᵉ pᵉ =
  (xᵉ : type-unordered-tupleᵉ nᵉ pᵉ) → element-unordered-tupleᵉ nᵉ pᵉ xᵉ

pr-product-unordered-tuple-typesᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : unordered-tuple-typesᵉ lᵉ nᵉ)
  (iᵉ : type-unordered-tupleᵉ nᵉ Aᵉ) →
  product-unordered-tuple-typesᵉ nᵉ Aᵉ → element-unordered-tupleᵉ nᵉ Aᵉ iᵉ
pr-product-unordered-tuple-typesᵉ nᵉ Aᵉ iᵉ fᵉ = fᵉ iᵉ

equiv-pr-product-unordered-tuple-typesᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : unordered-tuple-typesᵉ lᵉ (succ-ℕᵉ nᵉ))
  (iᵉ : type-unordered-tupleᵉ (succ-ℕᵉ nᵉ) Aᵉ) →
  ( ( product-unordered-tuple-typesᵉ nᵉ
      ( unordered-tuple-complement-point-type-unordered-tupleᵉ nᵉ Aᵉ iᵉ)) ×ᵉ
    ( element-unordered-tupleᵉ (succ-ℕᵉ nᵉ) Aᵉ iᵉ)) ≃ᵉ
  product-unordered-tuple-typesᵉ (succ-ℕᵉ nᵉ) Aᵉ
equiv-pr-product-unordered-tuple-typesᵉ nᵉ Aᵉ iᵉ =
  ( equiv-Πᵉ
    ( element-unordered-tupleᵉ (succ-ℕᵉ nᵉ) Aᵉ)
    ( equiv-maybe-structure-element-UU-Finᵉ nᵉ
      ( type-unordered-tuple-UU-Finᵉ (succ-ℕᵉ nᵉ) Aᵉ) iᵉ)
    ( λ xᵉ → id-equivᵉ)) ∘eᵉ
  ( inv-equivᵉ
    ( equiv-dependent-universal-property-Maybeᵉ
      ( λ jᵉ →
        element-unordered-tupleᵉ (succ-ℕᵉ nᵉ) Aᵉ
          ( map-equivᵉ (equiv-maybe-structure-element-UU-Finᵉ nᵉ
            ( type-unordered-tuple-UU-Finᵉ (succ-ℕᵉ nᵉ) Aᵉ) iᵉ)
            ( jᵉ)))))

map-equiv-pr-product-unordered-tuple-typesᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : unordered-tuple-typesᵉ lᵉ (succ-ℕᵉ nᵉ))
  (iᵉ : type-unordered-tupleᵉ (succ-ℕᵉ nᵉ) Aᵉ) →
  product-unordered-tuple-typesᵉ nᵉ
    ( unordered-tuple-complement-point-type-unordered-tupleᵉ nᵉ Aᵉ iᵉ) →
  element-unordered-tupleᵉ (succ-ℕᵉ nᵉ) Aᵉ iᵉ →
  product-unordered-tuple-typesᵉ (succ-ℕᵉ nᵉ) Aᵉ
map-equiv-pr-product-unordered-tuple-typesᵉ nᵉ Aᵉ iᵉ fᵉ aᵉ =
  map-equivᵉ (equiv-pr-product-unordered-tuple-typesᵉ nᵉ Aᵉ iᵉ) (pairᵉ fᵉ aᵉ)
```

### Equivalences of products of unordered pairs of types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {nᵉ : ℕᵉ} (Aᵉ : unordered-tuple-typesᵉ l1ᵉ nᵉ)
  (Bᵉ : unordered-tuple-typesᵉ l2ᵉ nᵉ)
  where

  equiv-product-unordered-tuple-typesᵉ :
    equiv-unordered-tuple-typesᵉ nᵉ Aᵉ Bᵉ →
    product-unordered-tuple-typesᵉ nᵉ Aᵉ ≃ᵉ product-unordered-tuple-typesᵉ nᵉ Bᵉ
  equiv-product-unordered-tuple-typesᵉ eᵉ =
    equiv-Πᵉ
      ( element-unordered-tupleᵉ nᵉ Bᵉ)
      ( equiv-type-equiv-unordered-tuple-typesᵉ nᵉ Aᵉ Bᵉ eᵉ)
      ( equiv-element-equiv-unordered-tuple-typesᵉ nᵉ Aᵉ Bᵉ eᵉ)
```