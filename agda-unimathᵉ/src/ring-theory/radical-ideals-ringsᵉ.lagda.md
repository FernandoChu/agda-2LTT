# Radical ideals of rings

```agda
module ring-theory.radical-ideals-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.ideals-ringsᵉ
open import ring-theory.invertible-elements-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Aᵉ radicalᵉ idealᵉ in aᵉ ringᵉ Rᵉ isᵉ anᵉ idealᵉ Iᵉ suchᵉ thatᵉ `1ᵉ +ᵉ x`ᵉ isᵉ aᵉ multiplicativeᵉ
unitᵉ forᵉ everyᵉ `xᵉ ∈ᵉ I`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  is-radical-ideal-prop-Ringᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-radical-ideal-prop-Ringᵉ =
    Π-Propᵉ
      ( type-ideal-Ringᵉ Rᵉ Iᵉ)
      ( λ xᵉ →
        is-invertible-element-prop-Ringᵉ Rᵉ
          ( add-Ringᵉ Rᵉ (one-Ringᵉ Rᵉ) (inclusion-ideal-Ringᵉ Rᵉ Iᵉ xᵉ)))

  is-radical-ideal-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-radical-ideal-Ringᵉ =
    type-Propᵉ is-radical-ideal-prop-Ringᵉ

  is-prop-is-radical-ideal-Ringᵉ :
    is-propᵉ is-radical-ideal-Ringᵉ
  is-prop-is-radical-ideal-Ringᵉ =
    is-prop-type-Propᵉ is-radical-ideal-prop-Ringᵉ
```