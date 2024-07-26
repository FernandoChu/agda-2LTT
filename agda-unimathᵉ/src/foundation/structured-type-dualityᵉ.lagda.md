# Structured type duality

```agda
module foundation.structured-type-dualityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.structureᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-dualityᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Theorem

### Structured type duality

```agda
Slice-structureᵉ :
  {l1ᵉ l2ᵉ : Level} (lᵉ : Level) (Pᵉ : UUᵉ (l1ᵉ ⊔ lᵉ) → UUᵉ l2ᵉ) (Bᵉ : UUᵉ l1ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
Slice-structureᵉ lᵉ Pᵉ Bᵉ = Σᵉ (UUᵉ lᵉ) (λ Aᵉ → hom-structureᵉ Pᵉ Aᵉ Bᵉ)

equiv-Fiber-structureᵉ :
  {l1ᵉ l2ᵉ : Level} (lᵉ : Level) (Pᵉ : UUᵉ (l1ᵉ ⊔ lᵉ) → UUᵉ l2ᵉ) (Bᵉ : UUᵉ l1ᵉ) →
  Slice-structureᵉ (l1ᵉ ⊔ lᵉ) Pᵉ Bᵉ ≃ᵉ fam-structureᵉ Pᵉ Bᵉ
equiv-Fiber-structureᵉ {l1ᵉ} {l3ᵉ} lᵉ Pᵉ Bᵉ =
  ( ( inv-distributive-Π-Σᵉ) ∘eᵉ
    ( equiv-Σᵉ
      ( λ Cᵉ → (bᵉ : Bᵉ) → Pᵉ (Cᵉ bᵉ))
      ( equiv-Fiberᵉ lᵉ Bᵉ)
      ( λ fᵉ → equiv-Π-equiv-familyᵉ (λ bᵉ → id-equivᵉ)))) ∘eᵉ
  ( inv-associative-Σᵉ
    ( UUᵉ (l1ᵉ ⊔ lᵉ))
    ( λ Aᵉ → Aᵉ → Bᵉ)
    ( λ fᵉ → structure-mapᵉ Pᵉ (pr2ᵉ fᵉ)))
```

```agda
equiv-fixed-Slice-structureᵉ :
  {lᵉ : Level} (Pᵉ : UUᵉ lᵉ → UUᵉ lᵉ) (Xᵉ : UUᵉ lᵉ) (Aᵉ : UUᵉ lᵉ) →
  ( hom-structureᵉ Pᵉ Xᵉ Aᵉ) ≃ᵉ
  ( Σᵉ (Aᵉ → Σᵉ (UUᵉ lᵉ) (λ Zᵉ → Pᵉ (Zᵉ))) ( λ Yᵉ → Xᵉ ≃ᵉ (Σᵉ Aᵉ (pr1ᵉ ∘ᵉ Yᵉ))))
equiv-fixed-Slice-structureᵉ {lᵉ} Pᵉ Xᵉ Aᵉ =
  ( ( equiv-Σᵉ
      ( λ Yᵉ → Xᵉ ≃ᵉ Σᵉ Aᵉ (pr1ᵉ ∘ᵉ Yᵉ))
      ( equiv-Fiber-structureᵉ lᵉ Pᵉ Aᵉ)
      ( λ sᵉ →
        inv-equivᵉ
          ( equiv-postcomp-equivᵉ (equiv-total-fiberᵉ (pr1ᵉ (pr2ᵉ sᵉ))) Xᵉ))) ∘eᵉ
    ( ( equiv-right-swap-Σᵉ) ∘eᵉ
      ( ( inv-left-unit-law-Σ-is-contrᵉ
          ( is-torsorial-equivᵉ Xᵉ)
          ( Xᵉ ,ᵉ id-equivᵉ)))))
```