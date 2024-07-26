# Dependent homotopies

```agda
module foundation.dependent-homotopiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.dependent-identificationsᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Considerᵉ aᵉ [homotopy](foundation-core.homotopies.mdᵉ) `Hᵉ : fᵉ ~ᵉ g`ᵉ betweenᵉ twoᵉ
functionsᵉ `fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ x`.ᵉ Furthermore,ᵉ considerᵉ aᵉ typeᵉ familyᵉ
`Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → 𝒰`ᵉ andᵉ twoᵉ functionsᵉ

```text
  f'ᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ (fᵉ xᵉ)
  g'ᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ (gᵉ xᵉ)
```

Aᵉ {{#conceptᵉ "dependentᵉ homotopy"ᵉ Agda=dependent-homotopyᵉ}} fromᵉ `f'`ᵉ to `g'`ᵉ
overᵉ `H`ᵉ isᵉ aᵉ familyᵉ ofᵉ
[dependentᵉ identifications](foundation-core.dependent-identifications.mdᵉ) fromᵉ
`f'ᵉ x`ᵉ to `g'ᵉ x`ᵉ overᵉ `Hᵉ x`.ᵉ

## Definitions

### Dependent homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ)
  {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ)
  where

  dependent-homotopyᵉ :
    ((xᵉ : Aᵉ) → Cᵉ xᵉ (fᵉ xᵉ)) → ((xᵉ : Aᵉ) → Cᵉ xᵉ (gᵉ xᵉ)) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  dependent-homotopyᵉ f'ᵉ g'ᵉ =
    (xᵉ : Aᵉ) → dependent-identificationᵉ (Cᵉ xᵉ) (Hᵉ xᵉ) (f'ᵉ xᵉ) (g'ᵉ xᵉ)
```

### The reflexive dependent homotopy

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ)
  {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  refl-dependent-homotopyᵉ :
    {f'ᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ (fᵉ xᵉ)} → dependent-homotopyᵉ Cᵉ refl-htpyᵉ f'ᵉ f'ᵉ
  refl-dependent-homotopyᵉ = refl-htpyᵉ
```

### Iterated dependent homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ)
  {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} {Hᵉ Kᵉ : fᵉ ~ᵉ gᵉ} (Lᵉ : Hᵉ ~ᵉ Kᵉ)
  where

  dependent-homotopy²ᵉ :
    {f'ᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ (fᵉ xᵉ)} {g'ᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ (gᵉ xᵉ)} →
    dependent-homotopyᵉ Cᵉ Hᵉ f'ᵉ g'ᵉ →
    dependent-homotopyᵉ Cᵉ Kᵉ f'ᵉ g'ᵉ → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  dependent-homotopy²ᵉ {f'ᵉ} {g'ᵉ} H'ᵉ K'ᵉ =
    (xᵉ : Aᵉ) → dependent-identification²ᵉ (Cᵉ xᵉ) (Lᵉ xᵉ) (H'ᵉ xᵉ) (K'ᵉ xᵉ)
```