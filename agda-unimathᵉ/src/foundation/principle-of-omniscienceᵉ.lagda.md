# The principle of omniscience

```agda
module foundation.principle-of-omniscienceᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-subtypesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.decidable-propositionsᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Aᵉ typeᵉ `X`ᵉ isᵉ saidᵉ to satisfyᵉ theᵉ **principleᵉ ofᵉ omniscience**ᵉ ifᵉ everyᵉ
[decidableᵉ subtype](foundation.decidable-subtypes.mdᵉ) ofᵉ `X`ᵉ isᵉ eitherᵉ
[inhabited](foundation.inhabited-types.mdᵉ) orᵉ
[empty](foundation-core.empty-types.md).ᵉ

## Definition

```agda
is-omniscient-Propᵉ : {lᵉ : Level} → UUᵉ lᵉ → Propᵉ (lsuc lzero ⊔ lᵉ)
is-omniscient-Propᵉ Xᵉ =
  Π-Propᵉ
    ( decidable-subtypeᵉ lzero Xᵉ)
    ( λ Pᵉ → is-decidable-Propᵉ (trunc-Propᵉ (type-decidable-subtypeᵉ Pᵉ)))

is-omniscientᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ (lsuc lzero ⊔ lᵉ)
is-omniscientᵉ Xᵉ = type-Propᵉ (is-omniscient-Propᵉ Xᵉ)
```

## See also

-ᵉ [Theᵉ limitedᵉ principleᵉ ofᵉ omniscience](foundation.limited-principle-of-omniscience.mdᵉ)
-ᵉ [Theᵉ lesserᵉ limitedᵉ principleᵉ ofᵉ omniscience](foundation.lesser-limited-principle-of-omniscience.mdᵉ)
-ᵉ [Theᵉ weakᵉ limitedᵉ principleᵉ ofᵉ omniscience](foundation.weak-limited-principle-of-omniscience.mdᵉ)