# The precategory of posets

```agda
module order-theory.precategory-of-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.universe-levelsᵉ

open import order-theory.order-preserving-maps-posetsᵉ
open import order-theory.posetsᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "(largeᵉ) precategoryᵉ ofᵉ posets"ᵉ Agda=Poset-Large-Precategoryᵉ}}
consistsᵉ ofᵉ [posets](order-theory.posets.mdᵉ) andᵉ
[orderᵉ preservingᵉ maps](order-theory.order-preserving-maps-posets.md).ᵉ

## Definitions

### The large precategory of posets

```agda
parametric-Poset-Large-Precategoryᵉ :
  (αᵉ βᵉ : Level → Level) →
  Large-Precategoryᵉ
    ( λ lᵉ → lsuc (αᵉ lᵉ) ⊔ lsuc (βᵉ lᵉ))
    ( λ l1ᵉ l2ᵉ → αᵉ l1ᵉ ⊔ βᵉ l1ᵉ ⊔ αᵉ l2ᵉ ⊔ βᵉ l2ᵉ)
parametric-Poset-Large-Precategoryᵉ αᵉ βᵉ =
  λ where
    .obj-Large-Precategoryᵉ lᵉ →
      Posetᵉ (αᵉ lᵉ) (βᵉ lᵉ)
    .hom-set-Large-Precategoryᵉ →
      hom-set-Posetᵉ
    .comp-hom-Large-Precategoryᵉ {Xᵉ = Xᵉ} {Yᵉ} {Zᵉ} →
      comp-hom-Posetᵉ Xᵉ Yᵉ Zᵉ
    .id-hom-Large-Precategoryᵉ {Xᵉ = Xᵉ} →
      id-hom-Posetᵉ Xᵉ
    .involutive-eq-associative-comp-hom-Large-Precategoryᵉ {Xᵉ = Xᵉ} {Yᵉ} {Zᵉ} {Wᵉ} →
      involutive-eq-associative-comp-hom-Posetᵉ Xᵉ Yᵉ Zᵉ Wᵉ
    .left-unit-law-comp-hom-Large-Precategoryᵉ {Xᵉ = Xᵉ} {Yᵉ} →
      left-unit-law-comp-hom-Posetᵉ Xᵉ Yᵉ
    .right-unit-law-comp-hom-Large-Precategoryᵉ {Xᵉ = Xᵉ} {Yᵉ} →
      right-unit-law-comp-hom-Posetᵉ Xᵉ Yᵉ

Poset-Large-Precategoryᵉ : Large-Precategoryᵉ lsuc (_⊔ᵉ_)
Poset-Large-Precategoryᵉ = parametric-Poset-Large-Precategoryᵉ (λ lᵉ → lᵉ) (λ lᵉ → lᵉ)
```

### The precategory or posets of universe level `l`

```agda
Poset-Precategoryᵉ : (lᵉ : Level) → Precategoryᵉ (lsuc lᵉ) lᵉ
Poset-Precategoryᵉ = precategory-Large-Precategoryᵉ Poset-Large-Precategoryᵉ
```