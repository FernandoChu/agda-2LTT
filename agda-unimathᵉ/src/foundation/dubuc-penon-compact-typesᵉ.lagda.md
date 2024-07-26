# Dubuc-Penon compact types

```agda
module foundation.dubuc-penon-compact-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.disjunctionᵉ
open import foundation.universal-quantificationᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "Dubuc-Penonᵉ compact"ᵉ Agda=is-dubuc-penon-compactᵉ}} ifᵉ forᵉ everyᵉ
[proposition](foundation-core.propositions.mdᵉ) `P`ᵉ andᵉ everyᵉ
[subtype](foundation-core.subtypes.mdᵉ) `Q`ᵉ ofᵉ `X`ᵉ suchᵉ thatᵉ theᵉ
[disjunction](foundation.disjunction.mdᵉ) `Pᵉ ∨ᵉ Qᵉ x`ᵉ holdsᵉ forᵉ allᵉ `x`,ᵉ thenᵉ
eitherᵉ `P`ᵉ isᵉ trueᵉ orᵉ `Q`ᵉ containsᵉ everyᵉ elementᵉ ofᵉ `X`.ᵉ

## Definition

```agda
is-dubuc-penon-compact-Propᵉ :
  {lᵉ : Level} (l1ᵉ l2ᵉ : Level) → UUᵉ lᵉ → Propᵉ (lᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ)
is-dubuc-penon-compact-Propᵉ l1ᵉ l2ᵉ Xᵉ =
  ∀'ᵉ
    ( Propᵉ l1ᵉ)
    ( λ Pᵉ →
      ∀'ᵉ
        ( subtypeᵉ l2ᵉ Xᵉ)
        ( λ Qᵉ → (∀'ᵉ Xᵉ (λ xᵉ → Pᵉ ∨ᵉ Qᵉ xᵉ)) ⇒ᵉ (Pᵉ ∨ᵉ (∀'ᵉ Xᵉ Qᵉ))))

is-dubuc-penon-compactᵉ :
  {lᵉ : Level} (l1ᵉ l2ᵉ : Level) → UUᵉ lᵉ → UUᵉ (lᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ)
is-dubuc-penon-compactᵉ l1ᵉ l2ᵉ Xᵉ = type-Propᵉ (is-dubuc-penon-compact-Propᵉ l1ᵉ l2ᵉ Xᵉ)
```