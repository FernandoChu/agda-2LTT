# Directed complete posets

```agda
module order-theory.directed-complete-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.directed-familiesᵉ
open import order-theory.least-upper-bounds-posetsᵉ
open import order-theory.posetsᵉ
```

</details>

## Idea

Aᵉ **DCPO**,ᵉ i.e.,ᵉ aᵉ **directedᵉ completeᵉ partiallyᵉ orderedᵉ set**,ᵉ isᵉ aᵉ posetᵉ in
whichᵉ eachᵉ directedᵉ familyᵉ ofᵉ elementsᵉ hasᵉ aᵉ leastᵉ upperᵉ bound.ᵉ

## Definition

```agda
is-directed-complete-Poset-Propᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
is-directed-complete-Poset-Propᵉ l3ᵉ Pᵉ =
  Π-Propᵉ
    ( directed-family-Posetᵉ l3ᵉ Pᵉ)
    ( λ xᵉ →
      has-least-upper-bound-family-of-elements-Poset-Propᵉ Pᵉ
        ( family-directed-family-Posetᵉ Pᵉ xᵉ))

DCPOᵉ : (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
DCPOᵉ l1ᵉ l2ᵉ l3ᵉ = type-subtypeᵉ (is-directed-complete-Poset-Propᵉ {l1ᵉ} {l2ᵉ} l3ᵉ)
```