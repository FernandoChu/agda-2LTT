# Subtype duality

```agda
module foundation.subtype-dualityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.propositional-mapsᵉ
open import foundation.structured-type-dualityᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Theorem

### Subtype duality

```agda
Slice-embᵉ : (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
Slice-embᵉ lᵉ Aᵉ = Σᵉ (UUᵉ lᵉ) (λ Xᵉ → Xᵉ ↪ᵉ Aᵉ)

equiv-Fiber-Propᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) →
  Slice-embᵉ (l1ᵉ ⊔ lᵉ) Aᵉ ≃ᵉ (Aᵉ → Propᵉ (l1ᵉ ⊔ lᵉ))
equiv-Fiber-Propᵉ lᵉ Aᵉ =
  ( equiv-Fiber-structureᵉ lᵉ is-propᵉ Aᵉ) ∘eᵉ
  ( equiv-totᵉ (λ Xᵉ → equiv-totᵉ equiv-is-prop-map-is-embᵉ))

Slice-surjectionᵉ : (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
Slice-surjectionᵉ lᵉ Aᵉ = Σᵉ (UUᵉ lᵉ) (λ Xᵉ → Xᵉ ↠ᵉ Aᵉ)

equiv-Fiber-trunc-Propᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) →
  Slice-surjectionᵉ (l1ᵉ ⊔ lᵉ) Aᵉ ≃ᵉ (Aᵉ → Inhabited-Typeᵉ (l1ᵉ ⊔ lᵉ))
equiv-Fiber-trunc-Propᵉ lᵉ Aᵉ =
  ( equiv-Fiber-structureᵉ lᵉ is-inhabitedᵉ Aᵉ)
```