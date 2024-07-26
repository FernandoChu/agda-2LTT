# Fibers of pointed maps

```agda
module structured-types.fibers-of-pointed-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Definition

```agda
fiber-Pointed-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} →
  (Aᵉ →∗ᵉ Bᵉ) → Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (fiber-Pointed-Typeᵉ fᵉ) = fiberᵉ (map-pointed-mapᵉ fᵉ) (point-Pointed-Typeᵉ _)
pr1ᵉ (pr2ᵉ (fiber-Pointed-Typeᵉ fᵉ)) = point-Pointed-Typeᵉ _
pr2ᵉ (pr2ᵉ (fiber-Pointed-Typeᵉ fᵉ)) = preserves-point-pointed-mapᵉ fᵉ
```