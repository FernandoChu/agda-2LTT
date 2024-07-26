# Reflective modalities

```agda
module orthogonal-factorization-systems.reflective-modalitiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.modal-operatorsᵉ
open import orthogonal-factorization-systems.reflective-subuniversesᵉ
```

</details>

## Idea

Aᵉ [modalᵉ operator](orthogonal-factorization-systems.modal-operators.mdᵉ) with
unitᵉ isᵉ **reflective**ᵉ ifᵉ itsᵉ [subuniverse](foundation.subuniverses.mdᵉ) ofᵉ modalᵉ
typesᵉ isᵉ
[reflective](orthogonal-factorization-systems.reflective-subuniverses.md).ᵉ

## Definitions

### Reflective subuniverses

```agda
is-reflective-modalityᵉ :
  {lᵉ : Level} {○ᵉ : operator-modalityᵉ lᵉ lᵉ} → unit-modalityᵉ ○ᵉ → UUᵉ (lsuc lᵉ)
is-reflective-modalityᵉ unit-○ᵉ =
  is-reflective-subuniverseᵉ (modal-type-subuniverseᵉ unit-○ᵉ)

reflective-modalityᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
reflective-modalityᵉ lᵉ =
  Σᵉ (operator-modalityᵉ lᵉ lᵉ) (λ ○ᵉ → Σᵉ (unit-modalityᵉ ○ᵉ) (is-reflective-modalityᵉ))
```

## See also

-ᵉ [Localizationsᵉ with respectᵉ to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.mdᵉ)