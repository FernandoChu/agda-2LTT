# Intersections of subtypes

```agda
module foundation.intersections-subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunctionᵉ
open import foundation.decidable-subtypesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.large-locale-of-subtypesᵉ
open import foundation.powersetsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.decidable-propositionsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ

open import order-theory.greatest-lower-bounds-large-posetsᵉ
```

</details>

## Idea

Theᵉ intersectionᵉ ofᵉ twoᵉ subtypesᵉ `A`ᵉ andᵉ `B`ᵉ isᵉ theᵉ subtypeᵉ thatᵉ containsᵉ theᵉ
elementsᵉ thatᵉ areᵉ in `A`ᵉ andᵉ in `B`.ᵉ

## Definition

### The intersection of two subtypes

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l2ᵉ Xᵉ) (Qᵉ : subtypeᵉ l3ᵉ Xᵉ)
  where

  intersection-subtypeᵉ : subtypeᵉ (l2ᵉ ⊔ l3ᵉ) Xᵉ
  intersection-subtypeᵉ = meet-powerset-Large-Localeᵉ Pᵉ Qᵉ

  is-greatest-binary-lower-bound-intersection-subtypeᵉ :
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( powerset-Large-Posetᵉ Xᵉ)
      ( Pᵉ)
      ( Qᵉ)
      ( intersection-subtypeᵉ)
  pr1ᵉ
    ( pr1ᵉ
      ( is-greatest-binary-lower-bound-intersection-subtypeᵉ Rᵉ)
      ( pᵉ ,ᵉ qᵉ) xᵉ rᵉ) =
    pᵉ xᵉ rᵉ
  pr2ᵉ
    ( pr1ᵉ
      ( is-greatest-binary-lower-bound-intersection-subtypeᵉ Rᵉ)
      ( pᵉ ,ᵉ qᵉ) xᵉ rᵉ) = qᵉ xᵉ rᵉ
  pr1ᵉ (pr2ᵉ (is-greatest-binary-lower-bound-intersection-subtypeᵉ Rᵉ) pᵉ) xᵉ rᵉ =
    pr1ᵉ (pᵉ xᵉ rᵉ)
  pr2ᵉ (pr2ᵉ (is-greatest-binary-lower-bound-intersection-subtypeᵉ Rᵉ) pᵉ) xᵉ rᵉ =
    pr2ᵉ (pᵉ xᵉ rᵉ)
```

### The intersection of two decidable subtypes

```agda
module _
  {lᵉ l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  intersection-decidable-subtypeᵉ :
    decidable-subtypeᵉ l1ᵉ Xᵉ → decidable-subtypeᵉ l2ᵉ Xᵉ →
    decidable-subtypeᵉ (l1ᵉ ⊔ l2ᵉ) Xᵉ
  intersection-decidable-subtypeᵉ Pᵉ Qᵉ xᵉ = conjunction-Decidable-Propᵉ (Pᵉ xᵉ) (Qᵉ xᵉ)
```

### The intersection of a family of subtypes

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ}
  where

  intersection-family-of-subtypesᵉ :
    {Iᵉ : UUᵉ l2ᵉ} (Pᵉ : Iᵉ → subtypeᵉ l3ᵉ Xᵉ) → subtypeᵉ (l2ᵉ ⊔ l3ᵉ) Xᵉ
  intersection-family-of-subtypesᵉ {Iᵉ} Pᵉ xᵉ = Π-Propᵉ Iᵉ (λ iᵉ → Pᵉ iᵉ xᵉ)
```