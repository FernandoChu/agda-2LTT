# Unpointed maps between pointed types

```agda
module structured-types.unpointed-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ unpointedᵉ mapsᵉ betweenᵉ pointedᵉ typesᵉ isᵉ aᵉ pointedᵉ type,ᵉ pointedᵉ atᵉ
theᵉ constantᵉ function.ᵉ

## Definition

```agda
unpointed-map-Pointed-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} → Pointed-Typeᵉ l1ᵉ → Pointed-Typeᵉ l2ᵉ → Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (unpointed-map-Pointed-Typeᵉ Aᵉ Bᵉ) = type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Bᵉ
pr2ᵉ (unpointed-map-Pointed-Typeᵉ Aᵉ Bᵉ) xᵉ = point-Pointed-Typeᵉ Bᵉ
```