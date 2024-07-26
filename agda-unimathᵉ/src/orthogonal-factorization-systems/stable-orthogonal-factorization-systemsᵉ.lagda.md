# Stable orthogonal factorization systems

```agda
module orthogonal-factorization-systems.stable-orthogonal-factorization-systemsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.function-classesᵉ
open import orthogonal-factorization-systems.orthogonal-factorization-systemsᵉ
```

</details>

## Idea

Aᵉ **stableᵉ orthogonalᵉ factorizationᵉ system**,ᵉ orᵉ **stableᵉ factorizationᵉ system**ᵉ
forᵉ short,ᵉ isᵉ anᵉ
[orthogonalᵉ factorizationᵉ system](orthogonal-factorization-systems.orthogonal-factorization-systems.mdᵉ)
whoseᵉ leftᵉ classᵉ isᵉ stableᵉ underᵉ [pullbacks](foundation.pullbacks.md).ᵉ Theᵉ rightᵉ
classᵉ ofᵉ anᵉ orthogonalᵉ factorizationᵉ system,ᵉ however,ᵉ isᵉ alwaysᵉ stableᵉ underᵉ
pullbacks.ᵉ

## Definition

```agda
is-stable-orthogonal-factorization-systemᵉ :
  {l1ᵉ lLᵉ lRᵉ : Level} →
  orthogonal-factorization-systemᵉ l1ᵉ lLᵉ lRᵉ → UUᵉ (lsuc l1ᵉ ⊔ lLᵉ)
is-stable-orthogonal-factorization-systemᵉ OFSᵉ =
  is-pullback-stable-function-classᵉ
    ( left-class-orthogonal-factorization-systemᵉ OFSᵉ)
```

## See also

Theᵉ equivalentᵉ notionsᵉ ofᵉ

-ᵉ [Higherᵉ modalities](orthogonal-factorization-systems.higher-modalities.mdᵉ)
-ᵉ [Uniquelyᵉ eliminatingᵉ modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.mdᵉ)
-ᵉ [Σ-closedᵉ reflectiveᵉ modalities](orthogonal-factorization-systems.sigma-closed-reflective-modalities.mdᵉ)
-ᵉ [Σ-closedᵉ reflectiveᵉ subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.mdᵉ)

## References

{{#bibliographyᵉ}} {{#referenceᵉ RSS20ᵉ}}