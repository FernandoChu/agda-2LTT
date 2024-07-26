# Type arithmetic with the empty type

```agda
module foundation.type-arithmetic-empty-typeᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Weᵉ proveᵉ arithmeticalᵉ lawsᵉ involvingᵉ theᵉ emptyᵉ type.ᵉ

## Laws

### Left zero law for cartesian products

```agda
module _
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ)
  where

  inv-pr1-product-emptyᵉ : emptyᵉ → emptyᵉ ×ᵉ Xᵉ
  inv-pr1-product-emptyᵉ ()

  is-section-inv-pr1-product-emptyᵉ : (pr1ᵉ ∘ᵉ inv-pr1-product-emptyᵉ) ~ᵉ idᵉ
  is-section-inv-pr1-product-emptyᵉ ()

  is-retraction-inv-pr1-product-emptyᵉ : (inv-pr1-product-emptyᵉ ∘ᵉ pr1ᵉ) ~ᵉ idᵉ
  is-retraction-inv-pr1-product-emptyᵉ (pairᵉ () xᵉ)

  is-equiv-pr1-product-emptyᵉ : is-equivᵉ (pr1ᵉ {Aᵉ = emptyᵉ} {Bᵉ = λ tᵉ → Xᵉ})
  is-equiv-pr1-product-emptyᵉ =
    is-equiv-is-invertibleᵉ
      inv-pr1-product-emptyᵉ
      is-section-inv-pr1-product-emptyᵉ
      is-retraction-inv-pr1-product-emptyᵉ

  left-zero-law-productᵉ : (emptyᵉ ×ᵉ Xᵉ) ≃ᵉ emptyᵉ
  pr1ᵉ left-zero-law-productᵉ = pr1ᵉ
  pr2ᵉ left-zero-law-productᵉ = is-equiv-pr1-product-emptyᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) (is-empty-Aᵉ : is-emptyᵉ Aᵉ)
  where
  inv-pr1-product-is-emptyᵉ : Aᵉ → Aᵉ ×ᵉ Bᵉ
  inv-pr1-product-is-emptyᵉ aᵉ = ex-falsoᵉ (is-empty-Aᵉ aᵉ)

  is-section-inv-pr1-product-is-emptyᵉ : (pr1ᵉ ∘ᵉ inv-pr1-product-is-emptyᵉ) ~ᵉ idᵉ
  is-section-inv-pr1-product-is-emptyᵉ aᵉ = ex-falsoᵉ (is-empty-Aᵉ aᵉ)

  is-retraction-inv-pr1-product-is-emptyᵉ : (inv-pr1-product-is-emptyᵉ ∘ᵉ pr1ᵉ) ~ᵉ idᵉ
  is-retraction-inv-pr1-product-is-emptyᵉ (pairᵉ aᵉ bᵉ) = ex-falsoᵉ (is-empty-Aᵉ aᵉ)

  is-equiv-pr1-product-is-emptyᵉ : is-equivᵉ (pr1ᵉ {Aᵉ = Aᵉ} {Bᵉ = λ aᵉ → Bᵉ})
  is-equiv-pr1-product-is-emptyᵉ =
    is-equiv-is-invertibleᵉ
      inv-pr1-product-is-emptyᵉ
      is-section-inv-pr1-product-is-emptyᵉ
      is-retraction-inv-pr1-product-is-emptyᵉ

  left-zero-law-product-is-emptyᵉ : (Aᵉ ×ᵉ Bᵉ) ≃ᵉ Aᵉ
  pr1ᵉ left-zero-law-product-is-emptyᵉ = pr1ᵉ
  pr2ᵉ left-zero-law-product-is-emptyᵉ = is-equiv-pr1-product-is-emptyᵉ
```

### Right zero law for cartesian products

```agda
module _
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ)
  where

  inv-pr2-product-emptyᵉ : emptyᵉ → (Xᵉ ×ᵉ emptyᵉ)
  inv-pr2-product-emptyᵉ ()

  is-section-inv-pr2-product-emptyᵉ : (pr2ᵉ ∘ᵉ inv-pr2-product-emptyᵉ) ~ᵉ idᵉ
  is-section-inv-pr2-product-emptyᵉ ()

  is-retraction-inv-pr2-product-emptyᵉ : (inv-pr2-product-emptyᵉ ∘ᵉ pr2ᵉ) ~ᵉ idᵉ
  is-retraction-inv-pr2-product-emptyᵉ (pairᵉ xᵉ ())

  is-equiv-pr2-product-emptyᵉ : is-equivᵉ (pr2ᵉ {Aᵉ = Xᵉ} {Bᵉ = λ xᵉ → emptyᵉ})
  is-equiv-pr2-product-emptyᵉ =
    is-equiv-is-invertibleᵉ
      inv-pr2-product-emptyᵉ
      is-section-inv-pr2-product-emptyᵉ
      is-retraction-inv-pr2-product-emptyᵉ

  right-zero-law-productᵉ : (Xᵉ ×ᵉ emptyᵉ) ≃ᵉ emptyᵉ
  pr1ᵉ right-zero-law-productᵉ = pr2ᵉ
  pr2ᵉ right-zero-law-productᵉ = is-equiv-pr2-product-emptyᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) (is-empty-Bᵉ : is-emptyᵉ Bᵉ)
  where
  inv-pr2-product-is-emptyᵉ : Bᵉ → Aᵉ ×ᵉ Bᵉ
  inv-pr2-product-is-emptyᵉ bᵉ = ex-falsoᵉ (is-empty-Bᵉ bᵉ)

  is-section-inv-pr2-product-is-emptyᵉ : (pr2ᵉ ∘ᵉ inv-pr2-product-is-emptyᵉ) ~ᵉ idᵉ
  is-section-inv-pr2-product-is-emptyᵉ bᵉ = ex-falsoᵉ (is-empty-Bᵉ bᵉ)

  is-retraction-inv-pr2-product-is-emptyᵉ : (inv-pr2-product-is-emptyᵉ ∘ᵉ pr2ᵉ) ~ᵉ idᵉ
  is-retraction-inv-pr2-product-is-emptyᵉ (pairᵉ aᵉ bᵉ) = ex-falsoᵉ (is-empty-Bᵉ bᵉ)

  is-equiv-pr2-product-is-emptyᵉ : is-equivᵉ (pr2ᵉ {Aᵉ = Aᵉ} {Bᵉ = λ aᵉ → Bᵉ})
  is-equiv-pr2-product-is-emptyᵉ =
    is-equiv-is-invertibleᵉ
      inv-pr2-product-is-emptyᵉ
      is-section-inv-pr2-product-is-emptyᵉ
      is-retraction-inv-pr2-product-is-emptyᵉ

  right-zero-law-product-is-emptyᵉ : (Aᵉ ×ᵉ Bᵉ) ≃ᵉ Bᵉ
  pr1ᵉ right-zero-law-product-is-emptyᵉ = pr2ᵉ
  pr2ᵉ right-zero-law-product-is-emptyᵉ = is-equiv-pr2-product-is-emptyᵉ
```

### Right absorption law for dependent pair types and for cartesian products

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  map-right-absorption-Σᵉ : Σᵉ Aᵉ (λ xᵉ → emptyᵉ) → emptyᵉ
  map-right-absorption-Σᵉ (pairᵉ xᵉ ())

  is-equiv-map-right-absorption-Σᵉ : is-equivᵉ map-right-absorption-Σᵉ
  is-equiv-map-right-absorption-Σᵉ = is-equiv-is-empty'ᵉ map-right-absorption-Σᵉ

  right-absorption-Σᵉ : Σᵉ Aᵉ (λ xᵉ → emptyᵉ) ≃ᵉ emptyᵉ
  right-absorption-Σᵉ =
    pairᵉ map-right-absorption-Σᵉ is-equiv-map-right-absorption-Σᵉ
```

### Left absorption law for dependent pair types

```agda
module _
  {lᵉ : Level} (Aᵉ : emptyᵉ → UUᵉ lᵉ)
  where

  map-left-absorption-Σᵉ : Σᵉ emptyᵉ Aᵉ → emptyᵉ
  map-left-absorption-Σᵉ = pr1ᵉ

  is-equiv-map-left-absorption-Σᵉ : is-equivᵉ map-left-absorption-Σᵉ
  is-equiv-map-left-absorption-Σᵉ =
    is-equiv-is-empty'ᵉ map-left-absorption-Σᵉ

  left-absorption-Σᵉ : Σᵉ emptyᵉ Aᵉ ≃ᵉ emptyᵉ
  pr1ᵉ left-absorption-Σᵉ = map-left-absorption-Σᵉ
  pr2ᵉ left-absorption-Σᵉ = is-equiv-map-left-absorption-Σᵉ
```

### Right absorption law for cartesian product types

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  map-right-absorption-productᵉ : Aᵉ ×ᵉ emptyᵉ → emptyᵉ
  map-right-absorption-productᵉ = map-right-absorption-Σᵉ Aᵉ

  is-equiv-map-right-absorption-productᵉ : is-equivᵉ map-right-absorption-productᵉ
  is-equiv-map-right-absorption-productᵉ = is-equiv-map-right-absorption-Σᵉ Aᵉ

  right-absorption-productᵉ : (Aᵉ ×ᵉ emptyᵉ) ≃ᵉ emptyᵉ
  right-absorption-productᵉ = right-absorption-Σᵉ Aᵉ

is-empty-right-factor-is-empty-productᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → is-emptyᵉ (Aᵉ ×ᵉ Bᵉ) → Aᵉ → is-emptyᵉ Bᵉ
is-empty-right-factor-is-empty-productᵉ fᵉ aᵉ bᵉ = fᵉ (pairᵉ aᵉ bᵉ)
```

### Left absorption law for cartesian products

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  map-left-absorption-productᵉ : emptyᵉ ×ᵉ Aᵉ → emptyᵉ
  map-left-absorption-productᵉ = map-left-absorption-Σᵉ (λ xᵉ → Aᵉ)

  is-equiv-map-left-absorption-productᵉ : is-equivᵉ map-left-absorption-productᵉ
  is-equiv-map-left-absorption-productᵉ =
    is-equiv-map-left-absorption-Σᵉ (λ xᵉ → Aᵉ)

  left-absorption-productᵉ : (emptyᵉ ×ᵉ Aᵉ) ≃ᵉ emptyᵉ
  left-absorption-productᵉ = left-absorption-Σᵉ (λ xᵉ → Aᵉ)

is-empty-left-factor-is-empty-productᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → is-emptyᵉ (Aᵉ ×ᵉ Bᵉ) → Bᵉ → is-emptyᵉ Aᵉ
is-empty-left-factor-is-empty-productᵉ fᵉ bᵉ aᵉ = fᵉ (pairᵉ aᵉ bᵉ)
```

### Left unit law for coproducts

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) (Hᵉ : is-emptyᵉ Aᵉ)
  where

  map-left-unit-law-coproduct-is-emptyᵉ : Aᵉ +ᵉ Bᵉ → Bᵉ
  map-left-unit-law-coproduct-is-emptyᵉ (inlᵉ aᵉ) = ex-falsoᵉ (Hᵉ aᵉ)
  map-left-unit-law-coproduct-is-emptyᵉ (inrᵉ bᵉ) = bᵉ

  map-inv-left-unit-law-coproduct-is-emptyᵉ : Bᵉ → Aᵉ +ᵉ Bᵉ
  map-inv-left-unit-law-coproduct-is-emptyᵉ = inrᵉ

  is-section-map-inv-left-unit-law-coproduct-is-emptyᵉ :
    ( map-left-unit-law-coproduct-is-emptyᵉ ∘ᵉ
      map-inv-left-unit-law-coproduct-is-emptyᵉ) ~ᵉ idᵉ
  is-section-map-inv-left-unit-law-coproduct-is-emptyᵉ = refl-htpyᵉ

  is-retraction-map-inv-left-unit-law-coproduct-is-emptyᵉ :
    ( map-inv-left-unit-law-coproduct-is-emptyᵉ ∘ᵉ
      map-left-unit-law-coproduct-is-emptyᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-left-unit-law-coproduct-is-emptyᵉ (inlᵉ aᵉ) =
    ex-falsoᵉ (Hᵉ aᵉ)
  is-retraction-map-inv-left-unit-law-coproduct-is-emptyᵉ (inrᵉ bᵉ) = reflᵉ

  is-equiv-map-left-unit-law-coproduct-is-emptyᵉ :
    is-equivᵉ map-left-unit-law-coproduct-is-emptyᵉ
  is-equiv-map-left-unit-law-coproduct-is-emptyᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-left-unit-law-coproduct-is-emptyᵉ
      is-section-map-inv-left-unit-law-coproduct-is-emptyᵉ
      is-retraction-map-inv-left-unit-law-coproduct-is-emptyᵉ

  left-unit-law-coproduct-is-emptyᵉ : (Aᵉ +ᵉ Bᵉ) ≃ᵉ Bᵉ
  pr1ᵉ left-unit-law-coproduct-is-emptyᵉ = map-left-unit-law-coproduct-is-emptyᵉ
  pr2ᵉ left-unit-law-coproduct-is-emptyᵉ =
    is-equiv-map-left-unit-law-coproduct-is-emptyᵉ

  is-equiv-inr-is-emptyᵉ :
    is-equivᵉ inrᵉ
  is-equiv-inr-is-emptyᵉ =
    is-equiv-is-invertibleᵉ
      ( map-left-unit-law-coproduct-is-emptyᵉ)
      ( is-retraction-map-inv-left-unit-law-coproduct-is-emptyᵉ)
      ( is-section-map-inv-left-unit-law-coproduct-is-emptyᵉ)

  inv-left-unit-law-coproduct-is-emptyᵉ : Bᵉ ≃ᵉ (Aᵉ +ᵉ Bᵉ)
  pr1ᵉ inv-left-unit-law-coproduct-is-emptyᵉ =
    map-inv-left-unit-law-coproduct-is-emptyᵉ
  pr2ᵉ inv-left-unit-law-coproduct-is-emptyᵉ = is-equiv-inr-is-emptyᵉ

  is-contr-map-left-unit-law-coproduct-is-emptyᵉ :
    is-contr-mapᵉ map-left-unit-law-coproduct-is-emptyᵉ
  is-contr-map-left-unit-law-coproduct-is-emptyᵉ =
    is-contr-map-is-equivᵉ is-equiv-map-left-unit-law-coproduct-is-emptyᵉ

  is-contr-map-inr-is-emptyᵉ :
    is-contr-mapᵉ map-inv-left-unit-law-coproduct-is-emptyᵉ
  is-contr-map-inr-is-emptyᵉ = is-contr-map-is-equivᵉ is-equiv-inr-is-emptyᵉ

  is-right-coproduct-is-emptyᵉ : (xᵉ : Aᵉ +ᵉ Bᵉ) → Σᵉ Bᵉ (λ bᵉ → inrᵉ bᵉ ＝ᵉ xᵉ)
  is-right-coproduct-is-emptyᵉ xᵉ = centerᵉ (is-contr-map-inr-is-emptyᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-empty-left-summand-is-equivᵉ : is-equivᵉ (inrᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ}) → is-emptyᵉ Aᵉ
  is-empty-left-summand-is-equivᵉ Hᵉ aᵉ =
    neq-inr-inlᵉ (is-section-map-inv-is-equivᵉ Hᵉ (inlᵉ aᵉ))

module _
  {lᵉ : Level} (Bᵉ : UUᵉ lᵉ)
  where

  map-left-unit-law-coproductᵉ : emptyᵉ +ᵉ Bᵉ → Bᵉ
  map-left-unit-law-coproductᵉ = map-left-unit-law-coproduct-is-emptyᵉ emptyᵉ Bᵉ idᵉ

  map-inv-left-unit-law-coproductᵉ : Bᵉ → emptyᵉ +ᵉ Bᵉ
  map-inv-left-unit-law-coproductᵉ = inrᵉ

  is-section-map-inv-left-unit-law-coproductᵉ :
    ( map-left-unit-law-coproductᵉ ∘ᵉ map-inv-left-unit-law-coproductᵉ) ~ᵉ idᵉ
  is-section-map-inv-left-unit-law-coproductᵉ =
    is-section-map-inv-left-unit-law-coproduct-is-emptyᵉ emptyᵉ Bᵉ idᵉ

  is-retraction-map-inv-left-unit-law-coproductᵉ :
    ( map-inv-left-unit-law-coproductᵉ ∘ᵉ map-left-unit-law-coproductᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-left-unit-law-coproductᵉ =
    is-retraction-map-inv-left-unit-law-coproduct-is-emptyᵉ emptyᵉ Bᵉ idᵉ

  is-equiv-map-left-unit-law-coproductᵉ : is-equivᵉ map-left-unit-law-coproductᵉ
  is-equiv-map-left-unit-law-coproductᵉ =
    is-equiv-map-left-unit-law-coproduct-is-emptyᵉ emptyᵉ Bᵉ idᵉ

  left-unit-law-coproductᵉ : (emptyᵉ +ᵉ Bᵉ) ≃ᵉ Bᵉ
  left-unit-law-coproductᵉ = left-unit-law-coproduct-is-emptyᵉ emptyᵉ Bᵉ idᵉ

  inv-left-unit-law-coproductᵉ : Bᵉ ≃ᵉ (emptyᵉ +ᵉ Bᵉ)
  inv-left-unit-law-coproductᵉ = inv-left-unit-law-coproduct-is-emptyᵉ emptyᵉ Bᵉ idᵉ
```

### Right unit law for coproducts

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) (Hᵉ : is-emptyᵉ Bᵉ)
  where

  map-right-unit-law-coproduct-is-emptyᵉ : Aᵉ +ᵉ Bᵉ → Aᵉ
  map-right-unit-law-coproduct-is-emptyᵉ (inlᵉ aᵉ) = aᵉ
  map-right-unit-law-coproduct-is-emptyᵉ (inrᵉ bᵉ) = ex-falsoᵉ (Hᵉ bᵉ)

  map-inv-right-unit-law-coproduct-is-emptyᵉ : Aᵉ → Aᵉ +ᵉ Bᵉ
  map-inv-right-unit-law-coproduct-is-emptyᵉ = inlᵉ

  is-section-map-inv-right-unit-law-coproduct-is-emptyᵉ :
    ( map-right-unit-law-coproduct-is-emptyᵉ ∘ᵉ
      map-inv-right-unit-law-coproduct-is-emptyᵉ) ~ᵉ idᵉ
  is-section-map-inv-right-unit-law-coproduct-is-emptyᵉ aᵉ = reflᵉ

  is-retraction-map-inv-right-unit-law-coproduct-is-emptyᵉ :
    ( map-inv-right-unit-law-coproduct-is-emptyᵉ ∘ᵉ
      map-right-unit-law-coproduct-is-emptyᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-right-unit-law-coproduct-is-emptyᵉ (inlᵉ aᵉ) = reflᵉ
  is-retraction-map-inv-right-unit-law-coproduct-is-emptyᵉ (inrᵉ bᵉ) =
    ex-falsoᵉ (Hᵉ bᵉ)

  is-equiv-map-right-unit-law-coproduct-is-emptyᵉ :
    is-equivᵉ map-right-unit-law-coproduct-is-emptyᵉ
  is-equiv-map-right-unit-law-coproduct-is-emptyᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-right-unit-law-coproduct-is-emptyᵉ
      is-section-map-inv-right-unit-law-coproduct-is-emptyᵉ
      is-retraction-map-inv-right-unit-law-coproduct-is-emptyᵉ

  is-equiv-inl-is-emptyᵉ : is-equivᵉ (inlᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ})
  is-equiv-inl-is-emptyᵉ =
    is-equiv-is-invertibleᵉ
      ( map-right-unit-law-coproduct-is-emptyᵉ)
      ( is-retraction-map-inv-right-unit-law-coproduct-is-emptyᵉ)
      ( is-section-map-inv-right-unit-law-coproduct-is-emptyᵉ)

  right-unit-law-coproduct-is-emptyᵉ : (Aᵉ +ᵉ Bᵉ) ≃ᵉ Aᵉ
  pr1ᵉ right-unit-law-coproduct-is-emptyᵉ = map-right-unit-law-coproduct-is-emptyᵉ
  pr2ᵉ right-unit-law-coproduct-is-emptyᵉ =
    is-equiv-map-right-unit-law-coproduct-is-emptyᵉ

  inv-right-unit-law-coproduct-is-emptyᵉ : Aᵉ ≃ᵉ (Aᵉ +ᵉ Bᵉ)
  pr1ᵉ inv-right-unit-law-coproduct-is-emptyᵉ = inlᵉ
  pr2ᵉ inv-right-unit-law-coproduct-is-emptyᵉ = is-equiv-inl-is-emptyᵉ

  is-contr-map-right-unit-law-coproduct-is-emptyᵉ :
    is-contr-mapᵉ map-right-unit-law-coproduct-is-emptyᵉ
  is-contr-map-right-unit-law-coproduct-is-emptyᵉ =
    is-contr-map-is-equivᵉ is-equiv-map-right-unit-law-coproduct-is-emptyᵉ

  is-contr-map-inl-is-emptyᵉ : is-contr-mapᵉ inlᵉ
  is-contr-map-inl-is-emptyᵉ = is-contr-map-is-equivᵉ is-equiv-inl-is-emptyᵉ

  is-left-coproduct-is-emptyᵉ :
    (xᵉ : Aᵉ +ᵉ Bᵉ) → Σᵉ Aᵉ (λ aᵉ → inlᵉ aᵉ ＝ᵉ xᵉ)
  is-left-coproduct-is-emptyᵉ xᵉ = centerᵉ (is-contr-map-inl-is-emptyᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-empty-right-summand-is-equivᵉ : is-equivᵉ (inlᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ}) → is-emptyᵉ Bᵉ
  is-empty-right-summand-is-equivᵉ Hᵉ bᵉ =
    neq-inl-inrᵉ (is-section-map-inv-is-equivᵉ Hᵉ (inrᵉ bᵉ))

module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  map-right-unit-law-coproductᵉ : Aᵉ +ᵉ emptyᵉ → Aᵉ
  map-right-unit-law-coproductᵉ =
    map-right-unit-law-coproduct-is-emptyᵉ Aᵉ emptyᵉ idᵉ

  map-inv-right-unit-law-coproductᵉ : Aᵉ → Aᵉ +ᵉ emptyᵉ
  map-inv-right-unit-law-coproductᵉ = inlᵉ

  is-section-map-inv-right-unit-law-coproductᵉ :
    ( map-right-unit-law-coproductᵉ ∘ᵉ map-inv-right-unit-law-coproductᵉ) ~ᵉ idᵉ
  is-section-map-inv-right-unit-law-coproductᵉ =
    is-section-map-inv-right-unit-law-coproduct-is-emptyᵉ Aᵉ emptyᵉ idᵉ

  is-retraction-map-inv-right-unit-law-coproductᵉ :
    ( map-inv-right-unit-law-coproductᵉ ∘ᵉ map-right-unit-law-coproductᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-right-unit-law-coproductᵉ =
    is-retraction-map-inv-right-unit-law-coproduct-is-emptyᵉ Aᵉ emptyᵉ idᵉ

  is-equiv-map-right-unit-law-coproductᵉ : is-equivᵉ map-right-unit-law-coproductᵉ
  is-equiv-map-right-unit-law-coproductᵉ =
    is-equiv-map-right-unit-law-coproduct-is-emptyᵉ Aᵉ emptyᵉ idᵉ

  right-unit-law-coproductᵉ : (Aᵉ +ᵉ emptyᵉ) ≃ᵉ Aᵉ
  right-unit-law-coproductᵉ = right-unit-law-coproduct-is-emptyᵉ Aᵉ emptyᵉ idᵉ

  inv-right-unit-law-coproductᵉ : Aᵉ ≃ᵉ (Aᵉ +ᵉ emptyᵉ)
  inv-right-unit-law-coproductᵉ =
    inv-right-unit-law-coproduct-is-emptyᵉ Aᵉ emptyᵉ idᵉ
```

## See also

-ᵉ Inᵉ
  [`foundation.universal-property-empty-type`](foundation.universal-property-empty-type.mdᵉ)
  weᵉ showᵉ thatᵉ `empty`ᵉ isᵉ theᵉ initialᵉ type,ᵉ whichᵉ canᵉ beᵉ consideredᵉ aᵉ _leftᵉ zeroᵉ
  lawᵉ forᵉ functionᵉ typesᵉ_ (`(emptyᵉ → Aᵉ) ≃ᵉ unit`).ᵉ