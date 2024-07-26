# Petri-nets

```agda
module univalent-combinatorics.petri-netsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Weᵉ giveᵉ aᵉ definitionᵉ ofᵉ Petriᵉ netsᵉ dueᵉ to Joachimᵉ Kockᵉ [[1]][1ᵉ]

## Definition

```agda
Petri-Netᵉ : (l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ)
Petri-Netᵉ l1ᵉ l2ᵉ l3ᵉ l4ᵉ =
  Σᵉ ( 𝔽ᵉ l1ᵉ)
    ( λ Sᵉ →
      Σᵉ ( 𝔽ᵉ l2ᵉ)
        ( λ Tᵉ →
          ( type-𝔽ᵉ Sᵉ → type-𝔽ᵉ Tᵉ → 𝔽ᵉ l3ᵉ) ×ᵉ
          ( type-𝔽ᵉ Tᵉ → type-𝔽ᵉ Sᵉ → 𝔽ᵉ l4ᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Petri-Netᵉ l1ᵉ l2ᵉ l3ᵉ l4ᵉ)
  where

  place-Petri-Net-𝔽ᵉ : 𝔽ᵉ l1ᵉ
  place-Petri-Net-𝔽ᵉ = pr1ᵉ Pᵉ

  place-Petri-Netᵉ : UUᵉ l1ᵉ
  place-Petri-Netᵉ = type-𝔽ᵉ place-Petri-Net-𝔽ᵉ

  transition-Petri-Net-𝔽ᵉ : 𝔽ᵉ l2ᵉ
  transition-Petri-Net-𝔽ᵉ = pr1ᵉ (pr2ᵉ Pᵉ)

  transition-Petri-Netᵉ : UUᵉ l2ᵉ
  transition-Petri-Netᵉ = type-𝔽ᵉ transition-Petri-Net-𝔽ᵉ

  incoming-arc-Petri-Net-𝔽ᵉ : place-Petri-Netᵉ → transition-Petri-Netᵉ → 𝔽ᵉ l3ᵉ
  incoming-arc-Petri-Net-𝔽ᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Pᵉ))

  incoming-arc-Petri-Netᵉ : place-Petri-Netᵉ → transition-Petri-Netᵉ → UUᵉ l3ᵉ
  incoming-arc-Petri-Netᵉ sᵉ tᵉ = type-𝔽ᵉ (incoming-arc-Petri-Net-𝔽ᵉ sᵉ tᵉ)

  outgoing-arc-Petri-Net-𝔽ᵉ : transition-Petri-Netᵉ → place-Petri-Netᵉ → 𝔽ᵉ l4ᵉ
  outgoing-arc-Petri-Net-𝔽ᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ Pᵉ))

  outgoing-arc-Petri-Netᵉ : transition-Petri-Netᵉ → place-Petri-Netᵉ → UUᵉ l4ᵉ
  outgoing-arc-Petri-Netᵉ tᵉ sᵉ = type-𝔽ᵉ (outgoing-arc-Petri-Net-𝔽ᵉ tᵉ sᵉ)
```

[1ᵉ]: https://arxiv.org/abs/2005.05108ᵉ