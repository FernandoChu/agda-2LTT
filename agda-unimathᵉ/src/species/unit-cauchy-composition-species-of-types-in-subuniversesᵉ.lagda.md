# The unit of Cauchy composition of species of types in subuniverses

```agda
module species.unit-cauchy-composition-species-of-types-in-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.global-subuniversesᵉ
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-types-in-subuniversesᵉ
```

</details>

## Idea

Givenᵉ aᵉ globalᵉ subuniverseᵉ closedᵉ underᵉ `is-contr`,ᵉ weᵉ defineᵉ theᵉ unitᵉ ofᵉ theᵉ
Cauchyᵉ compositionᵉ ofᵉ speciesᵉ ofᵉ typesᵉ in aᵉ subuniverseᵉ byᵉ

```text
  Xᵉ ↦ᵉ is-contrᵉ X.ᵉ
```

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (C4ᵉ :
    is-closed-under-is-contr-subuniversesᵉ Pᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ))
  where

  cauchy-composition-unit-species-subuniverseᵉ :
    species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l1ᵉ)
  cauchy-composition-unit-species-subuniverseᵉ Xᵉ =
    (is-contrᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ) ,ᵉ C4ᵉ Xᵉ)
```