# Dependent binary homotopies

```agda
module foundation.dependent-binary-homotopiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-homotopiesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.dependent-identificationsᵉ
```

</details>

## Idea

Considerᵉ aᵉ [binaryᵉ homotopy](foundation-core.homotopies.mdᵉ) `Hᵉ : fᵉ ~ᵉ g`ᵉ betweenᵉ
twoᵉ functionsᵉ `fᵉ gᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ y`.ᵉ Furthermore,ᵉ considerᵉ aᵉ typeᵉ
familyᵉ `Dᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) (zᵉ : Cᵉ xᵉ yᵉ) → 𝒰`ᵉ andᵉ twoᵉ functionsᵉ

```text
  f'ᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Dᵉ xᵉ yᵉ (fᵉ xᵉ yᵉ)
  g'ᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Dᵉ xᵉ yᵉ (gᵉ xᵉ yᵉ)
```

Aᵉ **dependentᵉ binaryᵉ homotopy**ᵉ fromᵉ `f'`ᵉ to `g'`ᵉ overᵉ `H`ᵉ isᵉ aᵉ familyᵉ ofᵉ
[dependentᵉ identifications](foundation-core.dependent-identifications.mdᵉ) fromᵉ
`f'ᵉ xᵉ y`ᵉ to `g'ᵉ xᵉ y`ᵉ overᵉ `Hᵉ xᵉ y`.ᵉ

## Definitions

### Dependent homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ}
  (Dᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) (zᵉ : Cᵉ xᵉ yᵉ) → UUᵉ l4ᵉ)
  {fᵉ gᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ} (Hᵉ : binary-htpyᵉ fᵉ gᵉ)
  where

  dependent-binary-homotopyᵉ :
    ((xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Dᵉ xᵉ yᵉ (fᵉ xᵉ yᵉ)) →
    ((xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Dᵉ xᵉ yᵉ (gᵉ xᵉ yᵉ)) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  dependent-binary-homotopyᵉ f'ᵉ g'ᵉ =
    (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) →
    dependent-identificationᵉ (Dᵉ xᵉ yᵉ) (Hᵉ xᵉ yᵉ) (f'ᵉ xᵉ yᵉ) (g'ᵉ xᵉ yᵉ)
```

### The reflexive dependent binary homotopy

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ}
  (Dᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) (zᵉ : Cᵉ xᵉ yᵉ) → UUᵉ l4ᵉ)
  {fᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ}
  where

  refl-dependent-binary-homotopyᵉ :
    {f'ᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Dᵉ xᵉ yᵉ (fᵉ xᵉ yᵉ)} →
    dependent-binary-homotopyᵉ Dᵉ (refl-binary-htpyᵉ fᵉ) f'ᵉ f'ᵉ
  refl-dependent-binary-homotopyᵉ {f'ᵉ} = refl-binary-htpyᵉ f'ᵉ
```