# Σ-closed reflective subuniverses

```agda
module orthogonal-factorization-systems.sigma-closed-reflective-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.sigma-closed-subuniversesᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.reflective-subuniversesᵉ
```

</details>

## Idea

Aᵉ
[reflectiveᵉ subuniverse](orthogonal-factorization-systems.reflective-subuniverses.mdᵉ)
isᵉ **Σ-closed**ᵉ ifᵉ itᵉ isᵉ closedᵉ underᵉ theᵉ formationᵉ ofᵉ
[Σ-types](foundation.dependent-pair-types.md).ᵉ

## Definition

```agda
is-closed-under-Σ-reflective-subuniverseᵉ :
  {lᵉ lPᵉ : Level} → reflective-subuniverseᵉ lᵉ lPᵉ → UUᵉ (lsuc lᵉ ⊔ lPᵉ)
is-closed-under-Σ-reflective-subuniverseᵉ (Pᵉ ,ᵉ _) =
  is-closed-under-Σ-subuniverseᵉ Pᵉ

closed-under-Σ-reflective-subuniverseᵉ :
  (lᵉ lPᵉ : Level) → UUᵉ (lsuc lᵉ ⊔ lsuc lPᵉ)
closed-under-Σ-reflective-subuniverseᵉ lᵉ lPᵉ =
  Σᵉ ( reflective-subuniverseᵉ lᵉ lPᵉ)
    ( is-closed-under-Σ-reflective-subuniverseᵉ)
```

## See also

Theᵉ equivalentᵉ notionsᵉ ofᵉ

-ᵉ [Higherᵉ modalities](orthogonal-factorization-systems.higher-modalities.mdᵉ)
-ᵉ [Uniquelyᵉ eliminatingᵉ modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.mdᵉ)
-ᵉ [Stableᵉ orthogonalᵉ factorizationᵉ systems](orthogonal-factorization-systems.stable-orthogonal-factorization-systems.mdᵉ)
-ᵉ [Σ-closedᵉ reflectiveᵉ modalities](orthogonal-factorization-systems.sigma-closed-reflective-modalities.mdᵉ)

## References

{{#bibliographyᵉ}} {{#referenceᵉ RSS20ᵉ}}