# The precategory of rings

```agda
module ring-theory.precategory-of-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.universe-levelsᵉ

open import ring-theory.homomorphisms-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Theᵉ **(largeᵉ) precategoryᵉ ofᵉ rings**ᵉ consistsᵉ ofᵉ [rings](ring-theory.rings.mdᵉ)
andᵉ [ringᵉ homomorphisms](ring-theory.homomorphisms-rings.md).ᵉ

## Definitions

### The large precategory of rings

```agda
Ring-Large-Precategoryᵉ : Large-Precategoryᵉ (lsucᵉ) (_⊔ᵉ_)
Ring-Large-Precategoryᵉ =
  make-Large-Precategoryᵉ
    ( Ringᵉ)
    ( hom-set-Ringᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Rᵉ} {Sᵉ} {Tᵉ} → comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ)
    ( λ {lᵉ} {Rᵉ} → id-hom-Ringᵉ Rᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {l3ᵉ} {l4ᵉ} {Rᵉ} {Sᵉ} {Tᵉ} {Uᵉ} → associative-comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ Uᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {Rᵉ} {Sᵉ} → left-unit-law-comp-hom-Ringᵉ Rᵉ Sᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {Rᵉ} {Sᵉ} → right-unit-law-comp-hom-Ringᵉ Rᵉ Sᵉ)
```

### The precategory or rings of universe level `l`

```agda
Ring-Precategoryᵉ : (lᵉ : Level) → Precategoryᵉ (lsuc lᵉ) lᵉ
Ring-Precategoryᵉ = precategory-Large-Precategoryᵉ Ring-Large-Precategoryᵉ
```