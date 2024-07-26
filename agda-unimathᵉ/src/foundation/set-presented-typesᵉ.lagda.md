# Set presented types

```agda
module foundation.set-presented-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalencesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.set-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
```

</details>

## Idea

Aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "setᵉ presented"ᵉ Agda=has-set-presentation-Propᵉ}} ifᵉ thereᵉ
[exists](foundation.existential-quantification.mdᵉ) aᵉ mapᵉ `fᵉ : Xᵉ → A`ᵉ fromᵉ aᵉ
[set](foundation-core.sets.mdᵉ) `X`ᵉ suchᵉ thatᵉ theᵉ compositeᵉ
`Xᵉ → Aᵉ → type-trunc-Setᵉ A`ᵉ isᵉ anᵉ [equivalence](foundation.equivalences.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  has-set-presentation-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  has-set-presentation-Propᵉ =
    ∃ᵉ (type-Setᵉ Aᵉ → Bᵉ) (λ fᵉ → is-equiv-Propᵉ (unit-trunc-Setᵉ ∘ᵉ fᵉ))
```