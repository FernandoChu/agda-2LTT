# Σ-closed reflective modalities

```agda
module orthogonal-factorization-systems.sigma-closed-reflective-modalitiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.modal-operatorsᵉ
open import orthogonal-factorization-systems.reflective-modalitiesᵉ
open import orthogonal-factorization-systems.sigma-closed-modalitiesᵉ
```

</details>

## Idea

Aᵉ [modality](orthogonal-factorization-systems.modal-operators.mdᵉ) isᵉ **Σ-closedᵉ
reflective**ᵉ ifᵉ itᵉ isᵉ
[reflective](orthogonal-factorization-systems.reflective-modalities.mdᵉ) andᵉ
[Σ-closed](orthogonal-factorization-systems.sigma-closed-modalities.md).ᵉ

## Definition

```agda
is-closed-under-Σ-reflective-modalityᵉ :
  {lᵉ : Level} {○ᵉ : operator-modalityᵉ lᵉ lᵉ} →
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ) → UUᵉ (lsuc lᵉ)
is-closed-under-Σ-reflective-modalityᵉ unit-○ᵉ =
  (is-reflective-modalityᵉ unit-○ᵉ) ×ᵉ (is-closed-under-Σ-modalityᵉ unit-○ᵉ)

closed-under-Σ-reflective-modalityᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
closed-under-Σ-reflective-modalityᵉ lᵉ =
  Σᵉ ( operator-modalityᵉ lᵉ lᵉ)
    ( λ ○ᵉ →
      Σᵉ ( unit-modalityᵉ ○ᵉ)
        ( is-closed-under-Σ-reflective-modalityᵉ))
```

## See also

Theᵉ equivalentᵉ notionsᵉ ofᵉ

-ᵉ [Higherᵉ modalities](orthogonal-factorization-systems.higher-modalities.mdᵉ)
-ᵉ [Uniquelyᵉ eliminatingᵉ modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.mdᵉ)
-ᵉ [Σ-closedᵉ reflectiveᵉ subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.mdᵉ)
-ᵉ [Stableᵉ orthogonalᵉ factorizationᵉ systems](orthogonal-factorization-systems.stable-orthogonal-factorization-systems.mdᵉ)