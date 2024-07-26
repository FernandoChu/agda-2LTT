# Wild groups

```agda
module structured-types.wild-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-equivalencesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.wild-monoidsᵉ
```

</details>

```agda
is-wild-group-Wild-Monoidᵉ :
  {lᵉ : Level} (Mᵉ : Wild-Monoidᵉ lᵉ) → UUᵉ lᵉ
is-wild-group-Wild-Monoidᵉ Mᵉ = is-binary-equivᵉ (mul-Wild-Monoidᵉ Mᵉ)

Wild-Groupᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Wild-Groupᵉ lᵉ = Σᵉ (Wild-Monoidᵉ lᵉ) is-wild-group-Wild-Monoidᵉ
```