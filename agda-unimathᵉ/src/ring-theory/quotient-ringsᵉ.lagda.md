# Quotient rings

```agda
module ring-theory.quotient-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.homomorphisms-ringsᵉ
open import ring-theory.ideals-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Definitions

### The universal property of quotient rings

```agda
precomp-quotient-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ)
  (Sᵉ : Ringᵉ l3ᵉ) (Tᵉ : Ringᵉ l4ᵉ) →
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ)
  ( Hᵉ : (xᵉ : type-Ringᵉ Rᵉ) → is-in-ideal-Ringᵉ Rᵉ Iᵉ xᵉ →
        map-hom-Ringᵉ Rᵉ Sᵉ fᵉ xᵉ ＝ᵉ zero-Ringᵉ Sᵉ) →
  hom-Ringᵉ Sᵉ Tᵉ →
  Σᵉ ( hom-Ringᵉ Rᵉ Tᵉ)
    ( λ gᵉ →
      (xᵉ : type-Ringᵉ Rᵉ) →
      is-in-ideal-Ringᵉ Rᵉ Iᵉ xᵉ → map-hom-Ringᵉ Rᵉ Tᵉ gᵉ xᵉ ＝ᵉ zero-Ringᵉ Tᵉ)
pr1ᵉ (precomp-quotient-Ringᵉ Rᵉ Iᵉ Sᵉ Tᵉ fᵉ Hᵉ hᵉ) = comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ hᵉ fᵉ
pr2ᵉ (precomp-quotient-Ringᵉ Rᵉ Iᵉ Sᵉ Tᵉ fᵉ Hᵉ hᵉ) xᵉ Kᵉ =
  apᵉ (map-hom-Ringᵉ Sᵉ Tᵉ hᵉ) (Hᵉ xᵉ Kᵉ) ∙ᵉ preserves-zero-hom-Ringᵉ Sᵉ Tᵉ hᵉ

universal-property-quotient-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (lᵉ : Level) (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ)
  (Sᵉ : Ringᵉ l3ᵉ) (fᵉ : hom-Ringᵉ Rᵉ Sᵉ)
  ( Hᵉ : (xᵉ : type-Ringᵉ Rᵉ) → is-in-ideal-Ringᵉ Rᵉ Iᵉ xᵉ →
        map-hom-Ringᵉ Rᵉ Sᵉ fᵉ xᵉ ＝ᵉ zero-Ringᵉ Sᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ lsuc lᵉ)
universal-property-quotient-Ringᵉ lᵉ Rᵉ Iᵉ Sᵉ fᵉ Hᵉ =
  (Tᵉ : Ringᵉ lᵉ) → is-equivᵉ (precomp-quotient-Ringᵉ Rᵉ Iᵉ Sᵉ Tᵉ fᵉ Hᵉ)
```