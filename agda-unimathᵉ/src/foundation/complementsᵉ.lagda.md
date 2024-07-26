# Complements of type families

```agda
module foundation.complementsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.empty-typesᵉ
open import foundation-core.function-typesᵉ
```

</details>

## Idea

Theᵉ **complement**ᵉ ofᵉ aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`ᵉ consistsᵉ ofᵉ theᵉ typeᵉ ofᵉ pointsᵉ
in `A`ᵉ atᵉ whichᵉ `Bᵉ x`ᵉ isᵉ [empty](foundation-core.empty-types.md).ᵉ

```agda
complementᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
complementᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} Bᵉ = Σᵉ Aᵉ (is-emptyᵉ ∘ᵉ Bᵉ)
```