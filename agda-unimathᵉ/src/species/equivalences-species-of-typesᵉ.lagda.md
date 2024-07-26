# Equivalences of species of types

```agda
module species.equivalences-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-typesᵉ
```

</details>

## Idea

Anᵉ equivalenceᵉ ofᵉ speciesᵉ ofᵉ typesᵉ fromᵉ `F`ᵉ to `G`ᵉ isᵉ aᵉ pointwiseᵉ equivalence.ᵉ

## Definition

```agda
equiv-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} → species-typesᵉ l1ᵉ l2ᵉ → species-typesᵉ l1ᵉ l3ᵉ →
  UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
equiv-species-typesᵉ {l1ᵉ} Fᵉ Gᵉ = (Xᵉ : UUᵉ l1ᵉ) → Fᵉ Xᵉ ≃ᵉ Gᵉ Xᵉ
```

## Properties

### The identity type of two species of types is equivalent to the type of equivalences between them

```agda
extensionality-species-typesᵉ :
  {l1ᵉ l2ᵉ : Level} (Fᵉ : species-typesᵉ l1ᵉ l2ᵉ) (Gᵉ : species-typesᵉ l1ᵉ l2ᵉ) →
  (Idᵉ Fᵉ Gᵉ) ≃ᵉ (equiv-species-typesᵉ Fᵉ Gᵉ)
extensionality-species-typesᵉ = extensionality-famᵉ
```