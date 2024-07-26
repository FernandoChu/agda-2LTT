# Σ-closed subuniverses

```agda
module foundation.sigma-closed-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
```

</details>

## Idea

Aᵉ [subuniverse](foundation.subuniverses.mdᵉ) `P`ᵉ isᵉ **Σ-closed**ᵉ ifᵉ itᵉ isᵉ closedᵉ
underᵉ theᵉ formationᵉ ofᵉ [Σ-types](foundation.dependent-pair-types.md).ᵉ Meaningᵉ
`P`ᵉ isᵉ Σ-closedᵉ ifᵉ `Σᵉ Aᵉ B`ᵉ isᵉ in `P`ᵉ wheneverᵉ `B`ᵉ isᵉ aᵉ familyᵉ ofᵉ typesᵉ in `P`ᵉ
overᵉ aᵉ typeᵉ `A`ᵉ in `P`.ᵉ

## Definition

Weᵉ stateᵉ aᵉ generalᵉ formᵉ involvingᵉ threeᵉ universes,ᵉ andᵉ aᵉ moreᵉ traditionalᵉ formᵉ
using aᵉ singleᵉ universeᵉ

```agda
is-closed-under-Σ-subuniversesᵉ :
  {l1ᵉ l2ᵉ lPᵉ lQᵉ lRᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ lPᵉ)
  (Qᵉ : subuniverseᵉ l2ᵉ lQᵉ)
  (Rᵉ : subuniverseᵉ (l1ᵉ ⊔ l2ᵉ) lRᵉ) →
  UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lPᵉ ⊔ lQᵉ ⊔ lRᵉ)
is-closed-under-Σ-subuniversesᵉ Pᵉ Qᵉ Rᵉ =
  (Xᵉ : type-subuniverseᵉ Pᵉ)
  (Yᵉ : inclusion-subuniverseᵉ Pᵉ Xᵉ → type-subuniverseᵉ Qᵉ) →
  is-in-subuniverseᵉ Rᵉ
    ( Σᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ) (inclusion-subuniverseᵉ Qᵉ ∘ᵉ Yᵉ))

is-closed-under-Σ-subuniverseᵉ :
  {lᵉ lPᵉ : Level} → subuniverseᵉ lᵉ lPᵉ → UUᵉ (lsuc lᵉ ⊔ lPᵉ)
is-closed-under-Σ-subuniverseᵉ Pᵉ = is-closed-under-Σ-subuniversesᵉ Pᵉ Pᵉ Pᵉ

closed-under-Σ-subuniverseᵉ :
  (lᵉ lPᵉ : Level) → UUᵉ (lsuc lᵉ ⊔ lsuc lPᵉ)
closed-under-Σ-subuniverseᵉ lᵉ lPᵉ =
  Σᵉ (subuniverseᵉ lᵉ lPᵉ) (is-closed-under-Σ-subuniverseᵉ)
```

## See also

-ᵉ [Σ-closedᵉ reflectiveᵉ subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.mdᵉ)