# Preimages of subtypes

```agda
module foundation.preimages-of-subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.subtypesᵉ
```

</details>

## Idea

Theᵉ preimageᵉ ofᵉ aᵉ subtypeᵉ `Sᵉ ⊆ᵉ B`ᵉ underᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ theᵉ subtypeᵉ ofᵉ `A`ᵉ
consistingᵉ ofᵉ elementsᵉ `a`ᵉ suchᵉ thatᵉ `fᵉ aᵉ ∈ᵉ S`.ᵉ

## Definition

```agda
preimage-subtypeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  subtypeᵉ l3ᵉ Bᵉ → subtypeᵉ l3ᵉ Aᵉ
preimage-subtypeᵉ fᵉ Sᵉ aᵉ = Sᵉ (fᵉ aᵉ)
```