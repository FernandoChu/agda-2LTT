# Proper subsets

```agda
module foundation.proper-subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.complements-subtypesᵉ
open import foundation.inhabited-subtypesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
```

</details>

## Idea

Aᵉ subtypeᵉ ofᵉ aᵉ typeᵉ isᵉ saidᵉ to beᵉ **proper**ᵉ ifᵉ itsᵉ complementᵉ isᵉ inhabited.ᵉ

```agda
is-proper-subtype-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → subtypeᵉ l2ᵉ Aᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-proper-subtype-Propᵉ Pᵉ =
  is-inhabited-subtype-Propᵉ (complement-subtypeᵉ Pᵉ)
```