# Isomorphism induction in precategories

```agda
module category-theory.isomorphism-induction-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-systemsᵉ
open import foundation.identity-typesᵉ
open import foundation.sectionsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

**Isomorphismᵉ induction**ᵉ in aᵉ precategoryᵉ `𝒞`ᵉ isᵉ theᵉ principleᵉ assertingᵉ that,ᵉ
givenᵉ anᵉ objectᵉ `Aᵉ : 𝒞`ᵉ andᵉ anyᵉ typeᵉ familyᵉ

```text
  Pᵉ : (Bᵉ : 𝒞ᵉ) (ϕᵉ : Aᵉ ≅ᵉ Bᵉ) → 𝒰ᵉ
```

ofᵉ typesᵉ indexedᵉ byᵉ allᵉ
[isomorphisms](category-theory.isomorphisms-in-categories.mdᵉ) with domainᵉ `A`,ᵉ
thereᵉ isᵉ aᵉ [section](foundation.sections.mdᵉ) ofᵉ theᵉ evaluationᵉ mapᵉ

```text
  ((Bᵉ : 𝒞ᵉ) (ϕᵉ : Aᵉ ≅ᵉ Bᵉ) → Pᵉ Bᵉ ϕᵉ) → Pᵉ Aᵉ id-iso.ᵉ
```

Theᵉ principleᵉ ofᵉ isomorphismᵉ inductionᵉ isᵉ equivalentᵉ to theᵉ univalenceᵉ axiomᵉ forᵉ
categories,ᵉ henceᵉ thisᵉ isᵉ oneᵉ approachᵉ to provingᵉ thatᵉ aᵉ precategoryᵉ isᵉ aᵉ
category.ᵉ

## Statement

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) {Aᵉ : obj-Precategoryᵉ Cᵉ}
  where

  ev-id-iso-Precategoryᵉ :
    {lᵉ : Level} (Pᵉ : (Bᵉ : obj-Precategoryᵉ Cᵉ) → (iso-Precategoryᵉ Cᵉ Aᵉ Bᵉ) → UUᵉ lᵉ) →
    ((Bᵉ : obj-Precategoryᵉ Cᵉ) (eᵉ : iso-Precategoryᵉ Cᵉ Aᵉ Bᵉ) → Pᵉ Bᵉ eᵉ) →
    Pᵉ Aᵉ (id-iso-Precategoryᵉ Cᵉ)
  ev-id-iso-Precategoryᵉ Pᵉ fᵉ = fᵉ Aᵉ (id-iso-Precategoryᵉ Cᵉ)

  induction-principle-iso-Precategoryᵉ :
    {lᵉ : Level} (Pᵉ : (Bᵉ : obj-Precategoryᵉ Cᵉ) → iso-Precategoryᵉ Cᵉ Aᵉ Bᵉ → UUᵉ lᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lᵉ)
  induction-principle-iso-Precategoryᵉ Pᵉ = sectionᵉ (ev-id-iso-Precategoryᵉ Pᵉ)

  triangle-ev-id-iso-Precategoryᵉ :
    {lᵉ : Level}
    (Pᵉ : (Bᵉ : obj-Precategoryᵉ Cᵉ) → iso-Precategoryᵉ Cᵉ Aᵉ Bᵉ → UUᵉ lᵉ) →
    coherence-triangle-mapsᵉ
      ( ev-pointᵉ (Aᵉ ,ᵉ id-iso-Precategoryᵉ Cᵉ))
      ( ev-id-iso-Precategoryᵉ Pᵉ)
      ( ev-pairᵉ)
  triangle-ev-id-iso-Precategoryᵉ Pᵉ fᵉ = reflᵉ
```

## Properties

### Contractibility of the total space of isomorphisms implies isomorphism induction

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) {Aᵉ : obj-Precategoryᵉ Cᵉ}
  where

  abstract
    is-identity-system-is-torsorial-iso-Precategoryᵉ :
      is-torsorialᵉ (iso-Precategoryᵉ Cᵉ Aᵉ) →
      is-identity-systemᵉ (iso-Precategoryᵉ Cᵉ Aᵉ) Aᵉ (id-iso-Precategoryᵉ Cᵉ)
    is-identity-system-is-torsorial-iso-Precategoryᵉ =
      is-identity-system-is-torsorialᵉ Aᵉ (id-iso-Precategoryᵉ Cᵉ)
```

### Isomorphism induction implies contractibility of the total space of isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) {Aᵉ : obj-Precategoryᵉ Cᵉ}
  where

  is-torsorial-equiv-induction-principle-iso-Precategoryᵉ :
    is-identity-systemᵉ (iso-Precategoryᵉ Cᵉ Aᵉ) Aᵉ (id-iso-Precategoryᵉ Cᵉ) →
    is-torsorialᵉ (iso-Precategoryᵉ Cᵉ Aᵉ)
  is-torsorial-equiv-induction-principle-iso-Precategoryᵉ =
    is-torsorial-is-identity-systemᵉ Aᵉ (id-iso-Precategoryᵉ Cᵉ)
```