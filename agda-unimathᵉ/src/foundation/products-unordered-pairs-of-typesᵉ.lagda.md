# Products of unordered pairs of types

```agda
module foundation.products-unordered-pairs-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.symmetric-operationsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ
open import foundation.unordered-pairs-of-typesᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ

open import univalent-combinatorics.2-element-typesᵉ
open import univalent-combinatorics.universal-property-standard-finite-typesᵉ
```

</details>

## Idea

Givenᵉ anᵉ unorderedᵉ pairᵉ ofᵉ types,ᵉ weᵉ canᵉ takeᵉ theirᵉ product.ᵉ Thisᵉ isᵉ aᵉ symmetricᵉ
versionᵉ ofᵉ theᵉ cartesianᵉ productᵉ operationᵉ onᵉ types.ᵉ

## Definition

```agda
product-unordered-pair-typesᵉ :
  {lᵉ : Level} → symmetric-operationᵉ (UUᵉ lᵉ) (UUᵉ lᵉ)
product-unordered-pair-typesᵉ pᵉ =
  (xᵉ : type-unordered-pairᵉ pᵉ) → element-unordered-pairᵉ pᵉ xᵉ

pr-product-unordered-pair-typesᵉ :
  {lᵉ : Level} (pᵉ : unordered-pair-typesᵉ lᵉ) (iᵉ : type-unordered-pairᵉ pᵉ) →
  product-unordered-pair-typesᵉ pᵉ → element-unordered-pairᵉ pᵉ iᵉ
pr-product-unordered-pair-typesᵉ pᵉ iᵉ fᵉ = fᵉ iᵉ

equiv-pr-product-unordered-pair-typesᵉ :
  {lᵉ : Level} (Aᵉ : unordered-pair-typesᵉ lᵉ) (iᵉ : type-unordered-pairᵉ Aᵉ) →
  product-unordered-pair-typesᵉ Aᵉ ≃ᵉ
  (element-unordered-pairᵉ Aᵉ iᵉ ×ᵉ other-element-unordered-pairᵉ Aᵉ iᵉ)
equiv-pr-product-unordered-pair-typesᵉ Aᵉ iᵉ =
  ( ( equiv-productᵉ
      ( equiv-trᵉ
        ( element-unordered-pairᵉ Aᵉ)
        ( compute-map-equiv-point-2-Element-Typeᵉ
          ( 2-element-type-unordered-pairᵉ Aᵉ)
          ( iᵉ)))
      ( equiv-trᵉ
        ( element-unordered-pairᵉ Aᵉ)
        ( compute-map-equiv-point-2-Element-Type'ᵉ
          ( 2-element-type-unordered-pairᵉ Aᵉ)
          ( iᵉ)))) ∘eᵉ
    ( equiv-dependent-universal-property-Fin-two-ℕᵉ
      ( ( element-unordered-pairᵉ Aᵉ) ∘ᵉ
        ( map-equiv-point-2-Element-Typeᵉ
          ( 2-element-type-unordered-pairᵉ Aᵉ)
          ( iᵉ))))) ∘eᵉ
  ( equiv-precomp-Πᵉ
    ( equiv-point-2-Element-Typeᵉ (2-element-type-unordered-pairᵉ Aᵉ) (iᵉ))
    ( element-unordered-pairᵉ Aᵉ))

equiv-pair-product-unordered-pair-typesᵉ :
  {lᵉ : Level} (Aᵉ : unordered-pair-typesᵉ lᵉ) (iᵉ : type-unordered-pairᵉ Aᵉ) →
  (element-unordered-pairᵉ Aᵉ iᵉ ×ᵉ other-element-unordered-pairᵉ Aᵉ iᵉ) ≃ᵉ
  product-unordered-pair-typesᵉ Aᵉ
equiv-pair-product-unordered-pair-typesᵉ Aᵉ iᵉ =
  inv-equivᵉ (equiv-pr-product-unordered-pair-typesᵉ Aᵉ iᵉ)

pair-product-unordered-pair-typesᵉ :
  {lᵉ : Level} (Aᵉ : unordered-pair-typesᵉ lᵉ) (iᵉ : type-unordered-pairᵉ Aᵉ) →
  element-unordered-pairᵉ Aᵉ iᵉ → other-element-unordered-pairᵉ Aᵉ iᵉ →
  product-unordered-pair-typesᵉ Aᵉ
pair-product-unordered-pair-typesᵉ Aᵉ iᵉ xᵉ yᵉ =
  map-equivᵉ (equiv-pair-product-unordered-pair-typesᵉ Aᵉ iᵉ) (pairᵉ xᵉ yᵉ)
```

### Equivalences of products of unordered pairs of types

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : unordered-pair-typesᵉ l1ᵉ) (Bᵉ : unordered-pair-typesᵉ l2ᵉ)
  where

  equiv-product-unordered-pair-typesᵉ :
    equiv-unordered-pair-typesᵉ Aᵉ Bᵉ →
    product-unordered-pair-typesᵉ Aᵉ ≃ᵉ product-unordered-pair-typesᵉ Bᵉ
  equiv-product-unordered-pair-typesᵉ eᵉ =
    equiv-Πᵉ
      ( element-unordered-pairᵉ Bᵉ)
      ( equiv-type-equiv-unordered-pair-typesᵉ Aᵉ Bᵉ eᵉ)
      ( equiv-element-equiv-unordered-pair-typesᵉ Aᵉ Bᵉ eᵉ)
```