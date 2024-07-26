# Equivalences of species of types in subuniverses

```agda
module species.equivalences-species-of-types-in-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-types-in-subuniversesᵉ
```

</details>

## Idea

Anᵉ equivalenceᵉ ofᵉ speciesᵉ ofᵉ typesᵉ fromᵉ `F`ᵉ to `G`ᵉ isᵉ aᵉ pointwiseᵉ equivalence.ᵉ

## Definition

```agda
equiv-species-subuniverseᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : subuniverseᵉ l1ᵉ l3ᵉ) →
  species-subuniverseᵉ Pᵉ Qᵉ → species-subuniverseᵉ Pᵉ Qᵉ →
  UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
equiv-species-subuniverseᵉ {l1ᵉ} Pᵉ Qᵉ Sᵉ Tᵉ =
  (Xᵉ : type-subuniverseᵉ Pᵉ) →
  inclusion-subuniverseᵉ Qᵉ (Sᵉ Xᵉ) ≃ᵉ inclusion-subuniverseᵉ Qᵉ (Tᵉ Xᵉ)
```

## Properties

### The identity type of two species of types is equivalent to the type of equivalences between them

```agda
extensionality-species-subuniverseᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : subuniverseᵉ l1ᵉ l3ᵉ) →
  (Sᵉ : species-subuniverseᵉ Pᵉ Qᵉ) → (Tᵉ : species-subuniverseᵉ Pᵉ Qᵉ) →
  (Idᵉ Sᵉ Tᵉ) ≃ᵉ (equiv-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ)
extensionality-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ =
  extensionality-fam-subuniverseᵉ Qᵉ Sᵉ Tᵉ
```