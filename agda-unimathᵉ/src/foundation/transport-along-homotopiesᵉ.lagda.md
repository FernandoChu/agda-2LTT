# Transport along homotopies

```agda
module foundation.transport-along-homotopiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.transport-along-higher-identificationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Ifᵉ `Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → 𝒰`ᵉ isᵉ aᵉ typeᵉ family,ᵉ andᵉ `Hᵉ : fᵉ ~ᵉ g`ᵉ isᵉ aᵉ homotopyᵉ
betweenᵉ functionsᵉ `fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ x`,ᵉ thenᵉ thereᵉ isᵉ aᵉ naturalᵉ transportᵉ
operationᵉ thatᵉ transportsᵉ anᵉ elementᵉ `zᵉ : Cᵉ xᵉ (fᵉ x)`ᵉ alongᵉ theᵉ homotopyᵉ `H`ᵉ to
anᵉ elementᵉ ofᵉ typeᵉ `Cᵉ xᵉ (gᵉ x)`.ᵉ

## Definitions

### Transporting along homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ)
  {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  tr-htpyᵉ :
    (fᵉ ~ᵉ gᵉ) → ((xᵉ : Aᵉ) → Cᵉ xᵉ (fᵉ xᵉ)) → ((xᵉ : Aᵉ) → Cᵉ xᵉ (gᵉ xᵉ))
  tr-htpyᵉ Hᵉ f'ᵉ xᵉ = trᵉ (Cᵉ xᵉ) (Hᵉ xᵉ) (f'ᵉ xᵉ)

  tr-htpy²ᵉ :
    {Hᵉ Kᵉ : fᵉ ~ᵉ gᵉ} (Lᵉ : Hᵉ ~ᵉ Kᵉ) (f'ᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ (fᵉ xᵉ)) →
    tr-htpyᵉ Hᵉ f'ᵉ ~ᵉ tr-htpyᵉ Kᵉ f'ᵉ
  tr-htpy²ᵉ Lᵉ f'ᵉ xᵉ = tr²ᵉ (Cᵉ xᵉ) (Lᵉ xᵉ) (f'ᵉ xᵉ)
```

## Properties

### Transport along a homotopy `H` is homotopic to transport along the identification `eq-htpy H`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ)
  where

  statement-compute-tr-htpyᵉ :
    {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  statement-compute-tr-htpyᵉ Hᵉ =
    trᵉ (λ uᵉ → (xᵉ : Aᵉ) → Cᵉ xᵉ (uᵉ xᵉ)) (eq-htpyᵉ Hᵉ) ~ᵉ tr-htpyᵉ Cᵉ Hᵉ

  base-case-compute-tr-htpyᵉ :
    {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} → statement-compute-tr-htpyᵉ (refl-htpy'ᵉ fᵉ)
  base-case-compute-tr-htpyᵉ =
    htpy-eqᵉ (apᵉ (trᵉ (λ uᵉ → (xᵉ : Aᵉ) → Cᵉ xᵉ (uᵉ xᵉ))) (eq-htpy-refl-htpyᵉ _))

  abstract
    compute-tr-htpyᵉ :
      {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) → statement-compute-tr-htpyᵉ Hᵉ
    compute-tr-htpyᵉ {fᵉ} {gᵉ} =
      ind-htpyᵉ fᵉ
        ( λ _ → statement-compute-tr-htpyᵉ)
        ( base-case-compute-tr-htpyᵉ)

    compute-tr-htpy-refl-htpyᵉ :
      {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} →
      compute-tr-htpyᵉ (refl-htpy'ᵉ fᵉ) ＝ᵉ base-case-compute-tr-htpyᵉ
    compute-tr-htpy-refl-htpyᵉ {fᵉ} =
      compute-ind-htpyᵉ fᵉ
        ( λ _ → statement-compute-tr-htpyᵉ)
        ( base-case-compute-tr-htpyᵉ)
```