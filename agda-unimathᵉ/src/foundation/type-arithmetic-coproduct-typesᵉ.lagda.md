# Type arithmetic for coproduct types

```agda
module foundation.type-arithmetic-coproduct-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-coproduct-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Weᵉ proveᵉ lawsᵉ forᵉ theᵉ manipulationᵉ ofᵉ coproductᵉ typesᵉ with respectᵉ to
themselves,ᵉ cartesianᵉ products,ᵉ andᵉ dependentᵉ pairᵉ types.ᵉ

## Laws

### Commutativity of coproducts

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  map-commutative-coproductᵉ : Aᵉ +ᵉ Bᵉ → Bᵉ +ᵉ Aᵉ
  map-commutative-coproductᵉ (inlᵉ aᵉ) = inrᵉ aᵉ
  map-commutative-coproductᵉ (inrᵉ bᵉ) = inlᵉ bᵉ

  map-inv-commutative-coproductᵉ : Bᵉ +ᵉ Aᵉ → Aᵉ +ᵉ Bᵉ
  map-inv-commutative-coproductᵉ (inlᵉ bᵉ) = inrᵉ bᵉ
  map-inv-commutative-coproductᵉ (inrᵉ aᵉ) = inlᵉ aᵉ

  is-section-map-inv-commutative-coproductᵉ :
    ( map-commutative-coproductᵉ ∘ᵉ map-inv-commutative-coproductᵉ) ~ᵉ idᵉ
  is-section-map-inv-commutative-coproductᵉ (inlᵉ bᵉ) = reflᵉ
  is-section-map-inv-commutative-coproductᵉ (inrᵉ aᵉ) = reflᵉ

  is-retraction-map-inv-commutative-coproductᵉ :
    ( map-inv-commutative-coproductᵉ ∘ᵉ map-commutative-coproductᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-commutative-coproductᵉ (inlᵉ aᵉ) = reflᵉ
  is-retraction-map-inv-commutative-coproductᵉ (inrᵉ bᵉ) = reflᵉ

  is-equiv-map-commutative-coproductᵉ : is-equivᵉ map-commutative-coproductᵉ
  is-equiv-map-commutative-coproductᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-commutative-coproductᵉ
      is-section-map-inv-commutative-coproductᵉ
      is-retraction-map-inv-commutative-coproductᵉ

  commutative-coproductᵉ : (Aᵉ +ᵉ Bᵉ) ≃ᵉ (Bᵉ +ᵉ Aᵉ)
  pr1ᵉ commutative-coproductᵉ = map-commutative-coproductᵉ
  pr2ᵉ commutative-coproductᵉ = is-equiv-map-commutative-coproductᵉ
```

### Associativity of coproducts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  map-associative-coproductᵉ : (Aᵉ +ᵉ Bᵉ) +ᵉ Cᵉ → Aᵉ +ᵉ (Bᵉ +ᵉ Cᵉ)
  map-associative-coproductᵉ (inlᵉ (inlᵉ xᵉ)) = inlᵉ xᵉ
  map-associative-coproductᵉ (inlᵉ (inrᵉ xᵉ)) = inrᵉ (inlᵉ xᵉ)
  map-associative-coproductᵉ (inrᵉ xᵉ) = inrᵉ (inrᵉ xᵉ)

  map-inv-associative-coproductᵉ : Aᵉ +ᵉ (Bᵉ +ᵉ Cᵉ) → (Aᵉ +ᵉ Bᵉ) +ᵉ Cᵉ
  map-inv-associative-coproductᵉ (inlᵉ xᵉ) = inlᵉ (inlᵉ xᵉ)
  map-inv-associative-coproductᵉ (inrᵉ (inlᵉ xᵉ)) = inlᵉ (inrᵉ xᵉ)
  map-inv-associative-coproductᵉ (inrᵉ (inrᵉ xᵉ)) = inrᵉ xᵉ

  is-section-map-inv-associative-coproductᵉ :
    (map-associative-coproductᵉ ∘ᵉ map-inv-associative-coproductᵉ) ~ᵉ idᵉ
  is-section-map-inv-associative-coproductᵉ (inlᵉ xᵉ) = reflᵉ
  is-section-map-inv-associative-coproductᵉ (inrᵉ (inlᵉ xᵉ)) = reflᵉ
  is-section-map-inv-associative-coproductᵉ (inrᵉ (inrᵉ xᵉ)) = reflᵉ

  is-retraction-map-inv-associative-coproductᵉ :
    (map-inv-associative-coproductᵉ ∘ᵉ map-associative-coproductᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-associative-coproductᵉ (inlᵉ (inlᵉ xᵉ)) = reflᵉ
  is-retraction-map-inv-associative-coproductᵉ (inlᵉ (inrᵉ xᵉ)) = reflᵉ
  is-retraction-map-inv-associative-coproductᵉ (inrᵉ xᵉ) = reflᵉ

  is-equiv-map-associative-coproductᵉ : is-equivᵉ map-associative-coproductᵉ
  is-equiv-map-associative-coproductᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-associative-coproductᵉ
      is-section-map-inv-associative-coproductᵉ
      is-retraction-map-inv-associative-coproductᵉ

  is-equiv-map-inv-associative-coproductᵉ :
    is-equivᵉ map-inv-associative-coproductᵉ
  is-equiv-map-inv-associative-coproductᵉ =
    is-equiv-is-invertibleᵉ
      map-associative-coproductᵉ
      is-retraction-map-inv-associative-coproductᵉ
      is-section-map-inv-associative-coproductᵉ

  associative-coproductᵉ : ((Aᵉ +ᵉ Bᵉ) +ᵉ Cᵉ) ≃ᵉ (Aᵉ +ᵉ (Bᵉ +ᵉ Cᵉ))
  pr1ᵉ associative-coproductᵉ = map-associative-coproductᵉ
  pr2ᵉ associative-coproductᵉ = is-equiv-map-associative-coproductᵉ

  inv-associative-coproductᵉ : (Aᵉ +ᵉ (Bᵉ +ᵉ Cᵉ)) ≃ᵉ ((Aᵉ +ᵉ Bᵉ) +ᵉ Cᵉ)
  pr1ᵉ inv-associative-coproductᵉ = map-inv-associative-coproductᵉ
  pr2ᵉ inv-associative-coproductᵉ = is-equiv-map-inv-associative-coproductᵉ
```

### Right distributivity of Σ over coproducts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) (Cᵉ : Aᵉ +ᵉ Bᵉ → UUᵉ l3ᵉ)
  where

  map-right-distributive-Σ-coproductᵉ :
    Σᵉ (Aᵉ +ᵉ Bᵉ) Cᵉ → (Σᵉ Aᵉ (λ xᵉ → Cᵉ (inlᵉ xᵉ))) +ᵉ (Σᵉ Bᵉ (λ yᵉ → Cᵉ (inrᵉ yᵉ)))
  map-right-distributive-Σ-coproductᵉ (inlᵉ xᵉ ,ᵉ zᵉ) = inlᵉ (xᵉ ,ᵉ zᵉ)
  map-right-distributive-Σ-coproductᵉ (inrᵉ yᵉ ,ᵉ zᵉ) = inrᵉ (yᵉ ,ᵉ zᵉ)

  map-inv-right-distributive-Σ-coproductᵉ :
    (Σᵉ Aᵉ (λ xᵉ → Cᵉ (inlᵉ xᵉ))) +ᵉ (Σᵉ Bᵉ (λ yᵉ → Cᵉ (inrᵉ yᵉ))) → Σᵉ (Aᵉ +ᵉ Bᵉ) Cᵉ
  pr1ᵉ (map-inv-right-distributive-Σ-coproductᵉ (inlᵉ (xᵉ ,ᵉ zᵉ))) = inlᵉ xᵉ
  pr2ᵉ (map-inv-right-distributive-Σ-coproductᵉ (inlᵉ (xᵉ ,ᵉ zᵉ))) = zᵉ
  pr1ᵉ (map-inv-right-distributive-Σ-coproductᵉ (inrᵉ (yᵉ ,ᵉ zᵉ))) = inrᵉ yᵉ
  pr2ᵉ (map-inv-right-distributive-Σ-coproductᵉ (inrᵉ (yᵉ ,ᵉ zᵉ))) = zᵉ

  is-section-map-inv-right-distributive-Σ-coproductᵉ :
    ( map-right-distributive-Σ-coproductᵉ ∘ᵉ
      map-inv-right-distributive-Σ-coproductᵉ) ~ᵉ
    ( idᵉ)
  is-section-map-inv-right-distributive-Σ-coproductᵉ (inlᵉ (xᵉ ,ᵉ zᵉ)) = reflᵉ
  is-section-map-inv-right-distributive-Σ-coproductᵉ (inrᵉ (yᵉ ,ᵉ zᵉ)) = reflᵉ

  is-retraction-map-inv-right-distributive-Σ-coproductᵉ :
    ( map-inv-right-distributive-Σ-coproductᵉ ∘ᵉ
      map-right-distributive-Σ-coproductᵉ) ~ᵉ
    ( idᵉ)
  is-retraction-map-inv-right-distributive-Σ-coproductᵉ (inlᵉ xᵉ ,ᵉ zᵉ) = reflᵉ
  is-retraction-map-inv-right-distributive-Σ-coproductᵉ (inrᵉ yᵉ ,ᵉ zᵉ) = reflᵉ

  abstract
    is-equiv-map-right-distributive-Σ-coproductᵉ :
      is-equivᵉ map-right-distributive-Σ-coproductᵉ
    is-equiv-map-right-distributive-Σ-coproductᵉ =
      is-equiv-is-invertibleᵉ
        map-inv-right-distributive-Σ-coproductᵉ
        is-section-map-inv-right-distributive-Σ-coproductᵉ
        is-retraction-map-inv-right-distributive-Σ-coproductᵉ

  right-distributive-Σ-coproductᵉ :
    Σᵉ (Aᵉ +ᵉ Bᵉ) Cᵉ ≃ᵉ ((Σᵉ Aᵉ (λ xᵉ → Cᵉ (inlᵉ xᵉ))) +ᵉ (Σᵉ Bᵉ (λ yᵉ → Cᵉ (inrᵉ yᵉ))))
  pr1ᵉ right-distributive-Σ-coproductᵉ = map-right-distributive-Σ-coproductᵉ
  pr2ᵉ right-distributive-Σ-coproductᵉ =
    is-equiv-map-right-distributive-Σ-coproductᵉ
```

### Left distributivity of Σ over coproducts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  map-left-distributive-Σ-coproductᵉ :
    Σᵉ Aᵉ (λ xᵉ → Bᵉ xᵉ +ᵉ Cᵉ xᵉ) → (Σᵉ Aᵉ Bᵉ) +ᵉ (Σᵉ Aᵉ Cᵉ)
  map-left-distributive-Σ-coproductᵉ (xᵉ ,ᵉ inlᵉ yᵉ) = inlᵉ (xᵉ ,ᵉ yᵉ)
  map-left-distributive-Σ-coproductᵉ (xᵉ ,ᵉ inrᵉ zᵉ) = inrᵉ (xᵉ ,ᵉ zᵉ)

  map-inv-left-distributive-Σ-coproductᵉ :
    (Σᵉ Aᵉ Bᵉ) +ᵉ (Σᵉ Aᵉ Cᵉ) → Σᵉ Aᵉ (λ xᵉ → Bᵉ xᵉ +ᵉ Cᵉ xᵉ)
  pr1ᵉ (map-inv-left-distributive-Σ-coproductᵉ (inlᵉ (xᵉ ,ᵉ yᵉ))) = xᵉ
  pr2ᵉ (map-inv-left-distributive-Σ-coproductᵉ (inlᵉ (xᵉ ,ᵉ yᵉ))) = inlᵉ yᵉ
  pr1ᵉ (map-inv-left-distributive-Σ-coproductᵉ (inrᵉ (xᵉ ,ᵉ zᵉ))) = xᵉ
  pr2ᵉ (map-inv-left-distributive-Σ-coproductᵉ (inrᵉ (xᵉ ,ᵉ zᵉ))) = inrᵉ zᵉ

  is-section-map-inv-left-distributive-Σ-coproductᵉ :
    ( map-left-distributive-Σ-coproductᵉ ∘ᵉ
      map-inv-left-distributive-Σ-coproductᵉ) ~ᵉ
    ( idᵉ)
  is-section-map-inv-left-distributive-Σ-coproductᵉ (inlᵉ (xᵉ ,ᵉ yᵉ)) = reflᵉ
  is-section-map-inv-left-distributive-Σ-coproductᵉ (inrᵉ (xᵉ ,ᵉ zᵉ)) = reflᵉ

  is-retraction-map-inv-left-distributive-Σ-coproductᵉ :
    ( map-inv-left-distributive-Σ-coproductᵉ ∘ᵉ
      map-left-distributive-Σ-coproductᵉ) ~ᵉ
    ( idᵉ)
  is-retraction-map-inv-left-distributive-Σ-coproductᵉ (xᵉ ,ᵉ inlᵉ yᵉ) = reflᵉ
  is-retraction-map-inv-left-distributive-Σ-coproductᵉ (xᵉ ,ᵉ inrᵉ zᵉ) = reflᵉ

  is-equiv-map-left-distributive-Σ-coproductᵉ :
    is-equivᵉ map-left-distributive-Σ-coproductᵉ
  is-equiv-map-left-distributive-Σ-coproductᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-left-distributive-Σ-coproductᵉ
      is-section-map-inv-left-distributive-Σ-coproductᵉ
      is-retraction-map-inv-left-distributive-Σ-coproductᵉ

  left-distributive-Σ-coproductᵉ :
    Σᵉ Aᵉ (λ xᵉ → Bᵉ xᵉ +ᵉ Cᵉ xᵉ) ≃ᵉ ((Σᵉ Aᵉ Bᵉ) +ᵉ (Σᵉ Aᵉ Cᵉ))
  pr1ᵉ left-distributive-Σ-coproductᵉ = map-left-distributive-Σ-coproductᵉ
  pr2ᵉ left-distributive-Σ-coproductᵉ = is-equiv-map-left-distributive-Σ-coproductᵉ
```

### Right distributivity of products over coproducts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) (Cᵉ : UUᵉ l3ᵉ)
  where

  map-right-distributive-product-coproductᵉ : (Aᵉ +ᵉ Bᵉ) ×ᵉ Cᵉ → (Aᵉ ×ᵉ Cᵉ) +ᵉ (Bᵉ ×ᵉ Cᵉ)
  map-right-distributive-product-coproductᵉ =
    map-right-distributive-Σ-coproductᵉ Aᵉ Bᵉ (λ _ → Cᵉ)

  map-inv-right-distributive-product-coproductᵉ :
    (Aᵉ ×ᵉ Cᵉ) +ᵉ (Bᵉ ×ᵉ Cᵉ) → (Aᵉ +ᵉ Bᵉ) ×ᵉ Cᵉ
  map-inv-right-distributive-product-coproductᵉ =
    map-inv-right-distributive-Σ-coproductᵉ Aᵉ Bᵉ (λ _ → Cᵉ)

  is-section-map-inv-right-distributive-product-coproductᵉ :
    map-right-distributive-product-coproductᵉ ∘ᵉ
    map-inv-right-distributive-product-coproductᵉ ~ᵉ idᵉ
  is-section-map-inv-right-distributive-product-coproductᵉ =
    is-section-map-inv-right-distributive-Σ-coproductᵉ Aᵉ Bᵉ (λ _ → Cᵉ)

  is-retraction-map-inv-right-distributive-product-coproductᵉ :
    map-inv-right-distributive-product-coproductᵉ ∘ᵉ
    map-right-distributive-product-coproductᵉ ~ᵉ idᵉ
  is-retraction-map-inv-right-distributive-product-coproductᵉ =
    is-retraction-map-inv-right-distributive-Σ-coproductᵉ Aᵉ Bᵉ (λ _ → Cᵉ)

  abstract
    is-equiv-map-right-distributive-product-coproductᵉ :
      is-equivᵉ map-right-distributive-product-coproductᵉ
    is-equiv-map-right-distributive-product-coproductᵉ =
      is-equiv-map-right-distributive-Σ-coproductᵉ Aᵉ Bᵉ (λ _ → Cᵉ)

  right-distributive-product-coproductᵉ : ((Aᵉ +ᵉ Bᵉ) ×ᵉ Cᵉ) ≃ᵉ ((Aᵉ ×ᵉ Cᵉ) +ᵉ (Bᵉ ×ᵉ Cᵉ))
  right-distributive-product-coproductᵉ =
    right-distributive-Σ-coproductᵉ Aᵉ Bᵉ (λ _ → Cᵉ)
```

### Left distributivity of products over coproducts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) (Cᵉ : UUᵉ l3ᵉ)
  where

  map-left-distributive-product-coproductᵉ : Aᵉ ×ᵉ (Bᵉ +ᵉ Cᵉ) → (Aᵉ ×ᵉ Bᵉ) +ᵉ (Aᵉ ×ᵉ Cᵉ)
  map-left-distributive-product-coproductᵉ =
    map-left-distributive-Σ-coproductᵉ Aᵉ (λ _ → Bᵉ) (λ _ → Cᵉ)

  map-inv-left-distributive-product-coproductᵉ :
    (Aᵉ ×ᵉ Bᵉ) +ᵉ (Aᵉ ×ᵉ Cᵉ) → Aᵉ ×ᵉ (Bᵉ +ᵉ Cᵉ)
  map-inv-left-distributive-product-coproductᵉ =
    map-inv-left-distributive-Σ-coproductᵉ Aᵉ (λ _ → Bᵉ) (λ _ → Cᵉ)

  is-section-map-inv-left-distributive-product-coproductᵉ :
    map-left-distributive-product-coproductᵉ ∘ᵉ
    map-inv-left-distributive-product-coproductᵉ ~ᵉ idᵉ
  is-section-map-inv-left-distributive-product-coproductᵉ =
    is-section-map-inv-left-distributive-Σ-coproductᵉ Aᵉ (λ _ → Bᵉ) (λ _ → Cᵉ)

  is-retraction-map-inv-left-distributive-product-coproductᵉ :
    map-inv-left-distributive-product-coproductᵉ ∘ᵉ
    map-left-distributive-product-coproductᵉ ~ᵉ idᵉ
  is-retraction-map-inv-left-distributive-product-coproductᵉ =
    is-retraction-map-inv-left-distributive-Σ-coproductᵉ Aᵉ (λ _ → Bᵉ) (λ _ → Cᵉ)

  is-equiv-map-left-distributive-product-coproductᵉ :
    is-equivᵉ map-left-distributive-product-coproductᵉ
  is-equiv-map-left-distributive-product-coproductᵉ =
    is-equiv-map-left-distributive-Σ-coproductᵉ Aᵉ (λ _ → Bᵉ) (λ _ → Cᵉ)

  left-distributive-product-coproductᵉ : (Aᵉ ×ᵉ (Bᵉ +ᵉ Cᵉ)) ≃ᵉ ((Aᵉ ×ᵉ Bᵉ) +ᵉ (Aᵉ ×ᵉ Cᵉ))
  left-distributive-product-coproductᵉ =
    left-distributive-Σ-coproductᵉ Aᵉ (λ _ → Bᵉ) (λ _ → Cᵉ)
```

### If a coproduct is contractible then one summand is contractible and the other is empty

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-contr-left-summandᵉ :
    is-contrᵉ (Aᵉ +ᵉ Bᵉ) → Aᵉ → is-contrᵉ Aᵉ
  pr1ᵉ (is-contr-left-summandᵉ Hᵉ aᵉ) = aᵉ
  pr2ᵉ (is-contr-left-summandᵉ Hᵉ aᵉ) xᵉ =
    is-injective-inlᵉ (eq-is-contrᵉ Hᵉ {inlᵉ aᵉ} {inlᵉ xᵉ})

  is-contr-left-summand-is-emptyᵉ :
    is-contrᵉ (Aᵉ +ᵉ Bᵉ) → is-emptyᵉ Bᵉ → is-contrᵉ Aᵉ
  pr1ᵉ (is-contr-left-summand-is-emptyᵉ (inlᵉ aᵉ ,ᵉ Hᵉ) Kᵉ) = aᵉ
  pr2ᵉ (is-contr-left-summand-is-emptyᵉ (inlᵉ aᵉ ,ᵉ Hᵉ) Kᵉ) xᵉ =
    is-injective-inlᵉ (Hᵉ (inlᵉ xᵉ))
  is-contr-left-summand-is-emptyᵉ (inrᵉ bᵉ ,ᵉ Hᵉ) Kᵉ = ex-falsoᵉ (Kᵉ bᵉ)

  is-contr-right-summandᵉ :
    is-contrᵉ (Aᵉ +ᵉ Bᵉ) → Bᵉ → is-contrᵉ Bᵉ
  pr1ᵉ (is-contr-right-summandᵉ Hᵉ bᵉ) = bᵉ
  pr2ᵉ (is-contr-right-summandᵉ Hᵉ bᵉ) xᵉ =
    is-injective-inrᵉ (eq-is-contrᵉ Hᵉ {inrᵉ bᵉ} {inrᵉ xᵉ})

  is-contr-right-summand-is-emptyᵉ :
    is-contrᵉ (Aᵉ +ᵉ Bᵉ) → is-emptyᵉ Aᵉ → is-contrᵉ Bᵉ
  is-contr-right-summand-is-emptyᵉ (inlᵉ aᵉ ,ᵉ Hᵉ) Kᵉ = ex-falsoᵉ (Kᵉ aᵉ)
  pr1ᵉ (is-contr-right-summand-is-emptyᵉ (inrᵉ bᵉ ,ᵉ Hᵉ) Kᵉ) = bᵉ
  pr2ᵉ (is-contr-right-summand-is-emptyᵉ (inrᵉ bᵉ ,ᵉ Hᵉ) Kᵉ) xᵉ =
    is-injective-inrᵉ (Hᵉ (inrᵉ xᵉ))

  is-empty-left-summand-is-contr-coproductᵉ :
    is-contrᵉ (Aᵉ +ᵉ Bᵉ) → Bᵉ → is-emptyᵉ Aᵉ
  is-empty-left-summand-is-contr-coproductᵉ Hᵉ bᵉ aᵉ =
    ex-falsoᵉ (is-empty-eq-coproduct-inl-inrᵉ aᵉ bᵉ (eq-is-contrᵉ Hᵉ))

  is-empty-right-summand-is-contr-coproductᵉ :
    is-contrᵉ (Aᵉ +ᵉ Bᵉ) → Aᵉ → is-emptyᵉ Bᵉ
  is-empty-right-summand-is-contr-coproductᵉ Hᵉ aᵉ bᵉ =
    ex-falsoᵉ (is-empty-eq-coproduct-inl-inrᵉ aᵉ bᵉ (eq-is-contrᵉ Hᵉ))
```

## See also

-ᵉ Functorialᵉ propertiesᵉ ofᵉ coproductsᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-coproduct-types`](foundation.functoriality-coproduct-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in coproductᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-coproduct-types`](foundation.equality-coproduct-types.md).ᵉ
-ᵉ Theᵉ universalᵉ propertyᵉ ofᵉ coproductsᵉ isᵉ treatedᵉ in
  [`foundation.universal-property-coproduct-types`](foundation.universal-property-coproduct-types.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ dependentᵉ pairᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-dependent-pair-types`](foundation.type-arithmetic-dependent-pair-types.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ cartesian-productᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-cartesian-product-types`](foundation.type-arithmetic-cartesian-product-types.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ theᵉ unitᵉ typeᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-unit-type`](foundation.type-arithmetic-unit-type.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ theᵉ emptyᵉ typeᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-empty-type`](foundation.type-arithmetic-empty-type.md).ᵉ