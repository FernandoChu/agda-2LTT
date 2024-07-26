# Structure

```agda
module foundation.structureᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Givenᵉ aᵉ typeᵉ familyᵉ `P`ᵉ onᵉ theᵉ universe,ᵉ aᵉ **`P`-structuredᵉ type**ᵉ consistsᵉ ofᵉ aᵉ
typeᵉ `A`ᵉ equippedᵉ with anᵉ elementᵉ ofᵉ typeᵉ `Pᵉ A`.ᵉ

## Definition

```agda
structureᵉ : {l1ᵉ l2ᵉ : Level} (Pᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
structureᵉ {l1ᵉ} Pᵉ = Σᵉ (UUᵉ l1ᵉ) Pᵉ

fam-structureᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ) (Aᵉ : UUᵉ l3ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
fam-structureᵉ Pᵉ Aᵉ = Aᵉ → structureᵉ Pᵉ

structure-mapᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ) → UUᵉ l3ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → Bᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
structure-mapᵉ Pᵉ {Aᵉ} {Bᵉ} fᵉ = (bᵉ : Bᵉ) → Pᵉ (fiberᵉ fᵉ bᵉ)

hom-structureᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ) → UUᵉ l3ᵉ) →
  UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
hom-structureᵉ Pᵉ Aᵉ Bᵉ = Σᵉ (Aᵉ → Bᵉ) (structure-mapᵉ Pᵉ)
```

## Properties

### Having structure is closed under equivalences

```agda
has-structure-equivᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ) {Xᵉ Yᵉ : UUᵉ l1ᵉ} → Xᵉ ≃ᵉ Yᵉ → Pᵉ Xᵉ → Pᵉ Yᵉ
has-structure-equivᵉ Pᵉ eᵉ = trᵉ Pᵉ (eq-equivᵉ eᵉ)

has-structure-equiv'ᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ) {Xᵉ Yᵉ : UUᵉ l1ᵉ} → Xᵉ ≃ᵉ Yᵉ → Pᵉ Yᵉ → Pᵉ Xᵉ
has-structure-equiv'ᵉ Pᵉ eᵉ = trᵉ Pᵉ (invᵉ (eq-equivᵉ eᵉ))
```