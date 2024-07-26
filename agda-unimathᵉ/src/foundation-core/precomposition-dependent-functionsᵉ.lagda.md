# Precomposition of dependent functions

```agda
module foundation-core.precomposition-dependent-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.dependent-homotopiesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Givenᵉ aᵉ functionᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ aᵉ typeᵉ familyᵉ `X`ᵉ overᵉ `B`,ᵉ theᵉ
**precompositionᵉ function**ᵉ

```text
  -ᵉ ∘ᵉ fᵉ : ((yᵉ : Bᵉ) → Xᵉ bᵉ) → ((xᵉ : Aᵉ) → Xᵉ (fᵉ xᵉ))
```

isᵉ definedᵉ byᵉ `λᵉ hᵉ xᵉ → hᵉ (fᵉ x)`.ᵉ

## Definitions

### The precomposition operation on dependent function

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Cᵉ : Bᵉ → UUᵉ l3ᵉ)
  where

  precomp-Πᵉ : ((bᵉ : Bᵉ) → Cᵉ bᵉ) → ((aᵉ : Aᵉ) → Cᵉ (fᵉ aᵉ))
  precomp-Πᵉ hᵉ aᵉ = hᵉ (fᵉ aᵉ)
```

## Properties

### The action of dependent precomposition on homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  {fᵉ gᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) (Cᵉ : Bᵉ → UUᵉ l3ᵉ) (hᵉ : (yᵉ : Bᵉ) → Cᵉ yᵉ)
  where

  htpy-precomp-Πᵉ :
    dependent-homotopyᵉ (λ _ → Cᵉ) Hᵉ (precomp-Πᵉ fᵉ Cᵉ hᵉ) (precomp-Πᵉ gᵉ Cᵉ hᵉ)
  htpy-precomp-Πᵉ xᵉ = apdᵉ hᵉ (Hᵉ xᵉ)
```