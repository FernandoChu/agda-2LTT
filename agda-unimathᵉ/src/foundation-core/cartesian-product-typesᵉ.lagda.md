# Cartesian product types

```agda
module foundation-core.cartesian-product-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Definitions

Cartesianᵉ productsᵉ ofᵉ typesᵉ areᵉ definedᵉ asᵉ dependentᵉ pairᵉ types,ᵉ using aᵉ
constantᵉ typeᵉ family.ᵉ

### The cartesian product type

```agda
productᵉ : {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
productᵉ Aᵉ Bᵉ = Σᵉ Aᵉ (λ _ → Bᵉ)

pair'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → Aᵉ → Bᵉ → productᵉ Aᵉ Bᵉ
pair'ᵉ = pairᵉ

infixr 15 _×ᵉ_
_×ᵉ_ : {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
_×ᵉ_ = productᵉ
```

### The induction principle for the cartesian product type

```agda
ind-productᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ ×ᵉ Bᵉ → UUᵉ l3ᵉ} →
  ((xᵉ : Aᵉ) (yᵉ : Bᵉ) → Cᵉ (xᵉ ,ᵉ yᵉ)) → (tᵉ : Aᵉ ×ᵉ Bᵉ) → Cᵉ tᵉ
ind-productᵉ = ind-Σᵉ
```

### The recursion principle for the cartesian product type

```agda
rec-productᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} →
  (Aᵉ → Bᵉ → Cᵉ) → (Aᵉ ×ᵉ Bᵉ) → Cᵉ
rec-productᵉ = ind-productᵉ
```