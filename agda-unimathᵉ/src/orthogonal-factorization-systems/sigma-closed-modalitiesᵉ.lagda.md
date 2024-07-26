# Σ-closed modalities

```agda
module orthogonal-factorization-systems.sigma-closed-modalitiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.sigma-closed-subuniversesᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.modal-operatorsᵉ
```

</details>

## Idea

Aᵉ [modalᵉ operator](orthogonal-factorization-systems.modal-operators.mdᵉ) with
unitᵉ isᵉ **Σ-closed**ᵉ ifᵉ itsᵉ [subuniverse](foundation.subuniverses.mdᵉ) ofᵉ modalᵉ
typesᵉ isᵉ [Σ-closed](foundation.sigma-closed-subuniverses.md).ᵉ I.e.ᵉ ifᵉ `Σᵉ Aᵉ B`ᵉ isᵉ
modalᵉ wheneverᵉ `B`ᵉ isᵉ aᵉ familyᵉ ofᵉ modalᵉ typesᵉ overᵉ modalᵉ baseᵉ `A`.ᵉ

## Definition

```agda
is-closed-under-Σ-modalityᵉ :
  {lᵉ : Level} {○ᵉ : operator-modalityᵉ lᵉ lᵉ} → unit-modalityᵉ ○ᵉ → UUᵉ (lsuc lᵉ)
is-closed-under-Σ-modalityᵉ =
  is-closed-under-Σ-subuniverseᵉ ∘ᵉ modal-type-subuniverseᵉ

closed-under-Σ-modalityᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
closed-under-Σ-modalityᵉ lᵉ =
  Σᵉ ( operator-modalityᵉ lᵉ lᵉ)
    ( λ ○ᵉ → Σᵉ (unit-modalityᵉ ○ᵉ) (is-closed-under-Σ-modalityᵉ))
```

## See also

-ᵉ [Reflectiveᵉ modalities](orthogonal-factorization-systems.reflective-modalities.mdᵉ)