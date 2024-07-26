# The universal property of the standard finite types

```agda
module univalent-combinatorics.universal-property-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-contractible-typesᵉ
open import foundation.universal-property-empty-typeᵉ
open import foundation.universal-property-maybeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ universalᵉ propertyᵉ ofᵉ theᵉ standardᵉ finiteᵉ typesᵉ assertsᵉ thatᵉ forᵉ anyᵉ familyᵉ
`A`ᵉ ofᵉ typesᵉ overᵉ `Finᵉ n`,ᵉ theᵉ typeᵉ `Πᵉ (iᵉ : Finᵉ n),ᵉ Aᵉ i`ᵉ isᵉ equivalentᵉ to theᵉ
iteratedᵉ Cartesianᵉ productᵉ `Aᵉ 0 ×ᵉ ... ×ᵉ Aᵉ (n-1)`.ᵉ

## Definitions

### Iterated cartesian products

```agda
iterated-productᵉ : {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : Finᵉ nᵉ → UUᵉ lᵉ) → UUᵉ lᵉ
iterated-productᵉ zero-ℕᵉ Aᵉ = raise-unitᵉ _
iterated-productᵉ (succ-ℕᵉ zero-ℕᵉ) Aᵉ = Aᵉ (zero-Finᵉ 0ᵉ)
iterated-productᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) Aᵉ =
  ( iterated-productᵉ (succ-ℕᵉ nᵉ) (Aᵉ ∘ᵉ inl-Finᵉ (succ-ℕᵉ nᵉ))) ×ᵉ
  ( Aᵉ (neg-one-Finᵉ (succ-ℕᵉ nᵉ)))
```

## Properties

### The dependent universal property of the standard finite types

```agda
equiv-dependent-universal-property-Finᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : Finᵉ nᵉ → UUᵉ lᵉ) →
  ((iᵉ : Finᵉ nᵉ) → Aᵉ iᵉ) ≃ᵉ iterated-productᵉ nᵉ Aᵉ
equiv-dependent-universal-property-Finᵉ zero-ℕᵉ Aᵉ =
  equiv-is-contrᵉ
    ( dependent-universal-property-empty'ᵉ Aᵉ)
    ( is-contr-raise-unitᵉ)
equiv-dependent-universal-property-Finᵉ (succ-ℕᵉ zero-ℕᵉ) Aᵉ =
  equiv-dependent-universal-property-contrᵉ (zero-Finᵉ 0ᵉ) is-contr-Fin-one-ℕᵉ Aᵉ
equiv-dependent-universal-property-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) Aᵉ =
  ( equiv-productᵉ
    ( equiv-dependent-universal-property-Finᵉ (succ-ℕᵉ nᵉ) (Aᵉ ∘ᵉ inlᵉ))
    ( id-equivᵉ)) ∘eᵉ
  ( equiv-dependent-universal-property-Maybeᵉ Aᵉ)
```

### The dependent universal property of the standard 2-element type

```agda
module _
  {lᵉ : Level} (Aᵉ : Finᵉ 2 → UUᵉ lᵉ)
  where

  ev-zero-one-Fin-two-ℕᵉ :
    ((iᵉ : Finᵉ 2ᵉ) → Aᵉ iᵉ) → Aᵉ (zero-Finᵉ 1ᵉ) ×ᵉ Aᵉ (one-Finᵉ 1ᵉ)
  pr1ᵉ (ev-zero-one-Fin-two-ℕᵉ fᵉ) = fᵉ (zero-Finᵉ 1ᵉ)
  pr2ᵉ (ev-zero-one-Fin-two-ℕᵉ fᵉ) = fᵉ (one-Finᵉ 1ᵉ)

  map-inv-ev-zero-one-Fin-two-ℕᵉ :
    Aᵉ (zero-Finᵉ 1ᵉ) ×ᵉ Aᵉ (one-Finᵉ 1ᵉ) → (iᵉ : Finᵉ 2ᵉ) → Aᵉ iᵉ
  map-inv-ev-zero-one-Fin-two-ℕᵉ (xᵉ ,ᵉ yᵉ) (inlᵉ (inrᵉ starᵉ)) = xᵉ
  map-inv-ev-zero-one-Fin-two-ℕᵉ (xᵉ ,ᵉ yᵉ) (inrᵉ starᵉ) = yᵉ

  is-section-map-inv-ev-zero-one-Fin-two-ℕᵉ :
    ev-zero-one-Fin-two-ℕᵉ ∘ᵉ map-inv-ev-zero-one-Fin-two-ℕᵉ ~ᵉ idᵉ
  is-section-map-inv-ev-zero-one-Fin-two-ℕᵉ (xᵉ ,ᵉ yᵉ) = reflᵉ

  abstract
    is-retraction-map-inv-ev-zero-one-Fin-two-ℕᵉ :
      map-inv-ev-zero-one-Fin-two-ℕᵉ ∘ᵉ ev-zero-one-Fin-two-ℕᵉ ~ᵉ idᵉ
    is-retraction-map-inv-ev-zero-one-Fin-two-ℕᵉ fᵉ =
      eq-htpyᵉ (λ { (inlᵉ (inrᵉ starᵉ)) → reflᵉ ; (inrᵉ starᵉ) → reflᵉ})

  dependent-universal-property-Fin-two-ℕᵉ :
    is-equivᵉ ev-zero-one-Fin-two-ℕᵉ
  dependent-universal-property-Fin-two-ℕᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-ev-zero-one-Fin-two-ℕᵉ
      is-section-map-inv-ev-zero-one-Fin-two-ℕᵉ
      is-retraction-map-inv-ev-zero-one-Fin-two-ℕᵉ

  is-equiv-map-inv-dependent-universal-proeprty-Fin-two-ℕᵉ :
    is-equivᵉ map-inv-ev-zero-one-Fin-two-ℕᵉ
  is-equiv-map-inv-dependent-universal-proeprty-Fin-two-ℕᵉ =
    is-equiv-is-invertibleᵉ
      ev-zero-one-Fin-two-ℕᵉ
      is-retraction-map-inv-ev-zero-one-Fin-two-ℕᵉ
      is-section-map-inv-ev-zero-one-Fin-two-ℕᵉ

  equiv-dependent-universal-property-Fin-two-ℕᵉ :
    ((iᵉ : Finᵉ 2ᵉ) → Aᵉ iᵉ) ≃ᵉ (Aᵉ (zero-Finᵉ 1ᵉ) ×ᵉ Aᵉ (one-Finᵉ 1ᵉ))
  pr1ᵉ equiv-dependent-universal-property-Fin-two-ℕᵉ =
    ev-zero-one-Fin-two-ℕᵉ
  pr2ᵉ equiv-dependent-universal-property-Fin-two-ℕᵉ =
    dependent-universal-property-Fin-two-ℕᵉ
```

### The universal property of the standard finite types

```agda
equiv-universal-property-Finᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {Xᵉ : UUᵉ lᵉ} →
  (Finᵉ nᵉ → Xᵉ) ≃ᵉ iterated-productᵉ nᵉ (λ _ → Xᵉ)
equiv-universal-property-Finᵉ nᵉ =
  equiv-dependent-universal-property-Finᵉ nᵉ (λ _ → _)
```

### The universal property of the standard 2-element type

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  universal-property-Fin-two-ℕᵉ :
    is-equivᵉ (ev-zero-one-Fin-two-ℕᵉ (λ _ → Xᵉ))
  universal-property-Fin-two-ℕᵉ =
    dependent-universal-property-Fin-two-ℕᵉ (λ _ → Xᵉ)

  equiv-universal-property-Fin-two-ℕᵉ :
    (Finᵉ 2 → Xᵉ) ≃ᵉ Xᵉ ×ᵉ Xᵉ
  equiv-universal-property-Fin-two-ℕᵉ =
    equiv-dependent-universal-property-Fin-two-ℕᵉ (λ _ → Xᵉ)
```