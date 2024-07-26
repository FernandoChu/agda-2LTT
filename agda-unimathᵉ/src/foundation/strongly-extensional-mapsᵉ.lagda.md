# Strongly extensional maps

```agda
module foundation.strongly-extensional-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Considerᵉ aᵉ functionᵉ `fᵉ : Aᵉ → B`ᵉ betweenᵉ typesᵉ equippedᵉ with apartnessᵉ relations.ᵉ
Thenᵉ weᵉ sayᵉ thatᵉ `f`ᵉ isᵉ **stronglyᵉ extensional**ᵉ ifᵉ

```text
  fᵉ xᵉ #ᵉ fᵉ yᵉ → xᵉ #ᵉ yᵉ
```

## Definition

```agda
strongly-extensionalᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Type-With-Apartnessᵉ l1ᵉ l2ᵉ)
  (Bᵉ : Type-With-Apartnessᵉ l3ᵉ l4ᵉ) →
  (type-Type-With-Apartnessᵉ Aᵉ → type-Type-With-Apartnessᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
strongly-extensionalᵉ Aᵉ Bᵉ fᵉ =
  (xᵉ yᵉ : type-Type-With-Apartnessᵉ Aᵉ) →
  apart-Type-With-Apartnessᵉ Bᵉ (fᵉ xᵉ) (fᵉ yᵉ) → apart-Type-With-Apartnessᵉ Aᵉ xᵉ yᵉ
```

## Properties

```text
is-strongly-extensionalᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Type-With-Apartnessᵉ l1ᵉ l2ᵉ)
  (Bᵉ : Type-With-Apartnessᵉ l3ᵉ l4ᵉ) →
  (fᵉ : type-Type-With-Apartnessᵉ Aᵉ → type-Type-With-Apartnessᵉ Bᵉ) →
  strongly-extensionalᵉ Aᵉ Bᵉ fᵉ
is-strongly-extensionalᵉ Aᵉ Bᵉ fᵉ xᵉ yᵉ Hᵉ = {!!ᵉ}
```