# The precategory of semirings

```agda
module ring-theory.precategory-of-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.universe-levelsᵉ

open import ring-theory.homomorphisms-semiringsᵉ
open import ring-theory.semiringsᵉ
```

</details>

## Idea

Theᵉ {{#concetᵉ "precategoryᵉ ofᵉ semirings"ᵉ Agda=Semiring-Large-Precategoryᵉ}}
consistsᵉ ofᵉ [semirings](ring-theory.semirings.mdᵉ) andᵉ
[homomorphismsᵉ ofᵉ semirings](ring-theory.homomorphisms-semirings.md).ᵉ

## Definitions

### The large precategory of semirings

```agda
Semiring-Large-Precategoryᵉ : Large-Precategoryᵉ lsuc (_⊔ᵉ_)
Semiring-Large-Precategoryᵉ =
  make-Large-Precategoryᵉ
    ( Semiringᵉ)
    ( hom-set-Semiringᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Rᵉ} {Sᵉ} {Tᵉ} → comp-hom-Semiringᵉ Rᵉ Sᵉ Tᵉ)
    ( λ {lᵉ} {Rᵉ} → id-hom-Semiringᵉ Rᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {l3ᵉ} {l4ᵉ} {Rᵉ} {Sᵉ} {Tᵉ} {Uᵉ} →
      associative-comp-hom-Semiringᵉ Rᵉ Sᵉ Tᵉ Uᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {Rᵉ} {Sᵉ} → left-unit-law-comp-hom-Semiringᵉ Rᵉ Sᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {Rᵉ} {Sᵉ} → right-unit-law-comp-hom-Semiringᵉ Rᵉ Sᵉ)
```

### The precategory of small semirings

```agda
Semiring-Precategoryᵉ : (lᵉ : Level) → Precategoryᵉ (lsuc lᵉ) lᵉ
Semiring-Precategoryᵉ = precategory-Large-Precategoryᵉ Semiring-Large-Precategoryᵉ
```