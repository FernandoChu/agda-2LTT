# Π-types in precategories with families

```agda
module type-theories.pi-types-precategories-with-familiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import type-theories.precategories-with-familiesᵉ
```

</details>

## Idea

Aᵉ [precategoryᵉ with families](type-theories.precategories-with-families.mdᵉ) `𝒯`ᵉ
isᵉ saidᵉ to haveᵉ **Π-types**ᵉ ifᵉ itᵉ comesᵉ equippedᵉ with theᵉ followingᵉ structureᵉ:

-ᵉ Anᵉ operationᵉ `Πᵉ : (Aᵉ : Tyᵉ Γᵉ) → Tyᵉ (extᵉ Γᵉ Aᵉ) → Tyᵉ Γ`ᵉ forᵉ everyᵉ contextᵉ `Γ`,ᵉ
-ᵉ Aᵉ familyᵉ ofᵉ equivalencesᵉ `Tmᵉ Γᵉ (Πᵉ Aᵉ Bᵉ) ≃ᵉ Tmᵉ (extᵉ Γᵉ Aᵉ) B`,ᵉ

thatᵉ areᵉ compatibleᵉ with theᵉ substitutionᵉ structureᵉ onᵉ `𝒯`.ᵉ

## Definitions

### The structure of `Π`-types on a precategory with families

```agda
record
  Π-structure-Precategory-With-Familiesᵉ
    (l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level) (cwfᵉ : Precategory-With-Familiesᵉ l1ᵉ l2ᵉ l3ᵉ l4ᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  where

  open Precategory-With-Familiesᵉ cwfᵉ

  field
    Πᵉ : {Γᵉ : Ctxᵉ} (Aᵉ : Tyᵉ Γᵉ) (Bᵉ : Tyᵉ (extᵉ Γᵉ Aᵉ)) → Tyᵉ Γᵉ
    iso-Πᵉ :
      {Γᵉ : Ctxᵉ} (Aᵉ : Tyᵉ Γᵉ) (Bᵉ : Tyᵉ (extᵉ Γᵉ Aᵉ)) → Tmᵉ Γᵉ (Πᵉ Aᵉ Bᵉ) ≃ᵉ Tmᵉ (extᵉ Γᵉ Aᵉ) Bᵉ

  appᵉ : {Γᵉ : Ctxᵉ} (Aᵉ : Tyᵉ Γᵉ) (Bᵉ : Tyᵉ (extᵉ Γᵉ Aᵉ)) → Tmᵉ Γᵉ (Πᵉ Aᵉ Bᵉ) → Tmᵉ (extᵉ Γᵉ Aᵉ) Bᵉ
  appᵉ Aᵉ Bᵉ = map-equivᵉ (iso-Πᵉ Aᵉ Bᵉ)

  lamᵉ : {Γᵉ : Ctxᵉ} (Aᵉ : Tyᵉ Γᵉ) (Bᵉ : Tyᵉ (extᵉ Γᵉ Aᵉ)) → Tmᵉ (extᵉ Γᵉ Aᵉ) Bᵉ → Tmᵉ Γᵉ (Πᵉ Aᵉ Bᵉ)
  lamᵉ Aᵉ Bᵉ = map-inv-equivᵉ (iso-Πᵉ Aᵉ Bᵉ)

  field
    substitution-law-Πᵉ :
      {Γᵉ Δᵉ : Ctxᵉ} (Aᵉ : Tyᵉ Δᵉ) (Bᵉ : Tyᵉ (extᵉ Δᵉ Aᵉ)) (σᵉ : Subᵉ Γᵉ Δᵉ) →
      (Πᵉ Aᵉ Bᵉ) ·ᵉ σᵉ ＝ᵉ Πᵉ (Aᵉ ·ᵉ σᵉ) (Bᵉ ·ᵉ ⟨ᵉ σᵉ ,ᵉ Aᵉ ⟩ᵉ)
    substitution-law-iso-Πᵉ :
      {Γᵉ Δᵉ : Ctxᵉ} (Aᵉ : Tyᵉ Δᵉ) (Bᵉ : Tyᵉ (extᵉ Δᵉ Aᵉ)) (σᵉ : Subᵉ Γᵉ Δᵉ) →
      (tᵉ : Tmᵉ Δᵉ (Πᵉ Aᵉ Bᵉ)) →
      appᵉ
        ( Aᵉ ·ᵉ σᵉ)
        ( Bᵉ ·ᵉ ⟨ᵉ σᵉ ,ᵉ Aᵉ ⟩ᵉ)
        ( trᵉ (Tmᵉ Γᵉ) (substitution-law-Πᵉ Aᵉ Bᵉ σᵉ) (tᵉ [ σᵉ ])) ＝ᵉ
      appᵉ Aᵉ Bᵉ tᵉ [ ⟨ᵉ σᵉ ,ᵉ Aᵉ ⟩ᵉ ]
```