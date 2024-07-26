# Isomorphism induction in categories

```agda
module category-theory.isomorphism-induction-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.isomorphism-induction-precategoriesᵉ
open import category-theory.isomorphisms-in-categoriesᵉ

open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.sectionsᵉ
open import foundation.universal-property-identity-systemsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

**Isomorphismᵉ induction**ᵉ in aᵉ [category](category-theory.categories.mdᵉ) `𝒞`ᵉ isᵉ
theᵉ principleᵉ assertingᵉ that,ᵉ givenᵉ anᵉ objectᵉ `Aᵉ : 𝒞`ᵉ andᵉ anyᵉ typeᵉ familyᵉ

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
categories.ᵉ

## Statement

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) {Aᵉ : obj-Categoryᵉ Cᵉ}
  where

  ev-id-iso-Categoryᵉ :
    {lᵉ : Level} (Pᵉ : (Bᵉ : obj-Categoryᵉ Cᵉ) → (iso-Categoryᵉ Cᵉ Aᵉ Bᵉ) → UUᵉ lᵉ) →
    ((Bᵉ : obj-Categoryᵉ Cᵉ) (eᵉ : iso-Categoryᵉ Cᵉ Aᵉ Bᵉ) → Pᵉ Bᵉ eᵉ) →
    Pᵉ Aᵉ (id-iso-Categoryᵉ Cᵉ)
  ev-id-iso-Categoryᵉ = ev-id-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  induction-principle-iso-Categoryᵉ :
    {lᵉ : Level} (Pᵉ : (Bᵉ : obj-Categoryᵉ Cᵉ) (eᵉ : iso-Categoryᵉ Cᵉ Aᵉ Bᵉ) → UUᵉ lᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lᵉ)
  induction-principle-iso-Categoryᵉ =
    induction-principle-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  triangle-ev-id-iso-Categoryᵉ :
    {lᵉ : Level}
    (Pᵉ : (Bᵉ : obj-Categoryᵉ Cᵉ) → iso-Categoryᵉ Cᵉ Aᵉ Bᵉ → UUᵉ lᵉ) →
    coherence-triangle-mapsᵉ
      ( ev-pointᵉ (Aᵉ ,ᵉ id-iso-Categoryᵉ Cᵉ))
      ( ev-id-iso-Categoryᵉ Pᵉ)
      ( ev-pairᵉ)
  triangle-ev-id-iso-Categoryᵉ =
    triangle-ev-id-iso-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

## Properties

### Isomorphism induction in a category

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) {Aᵉ : obj-Categoryᵉ Cᵉ}
  (Pᵉ : (Bᵉ : obj-Categoryᵉ Cᵉ) (eᵉ : iso-Categoryᵉ Cᵉ Aᵉ Bᵉ) → UUᵉ l3ᵉ)
  where

  abstract
    is-identity-system-iso-Categoryᵉ : sectionᵉ (ev-id-iso-Categoryᵉ Cᵉ Pᵉ)
    is-identity-system-iso-Categoryᵉ =
      is-identity-system-is-torsorial-iso-Precategoryᵉ
        ( precategory-Categoryᵉ Cᵉ)
        ( is-torsorial-iso-Categoryᵉ Cᵉ Aᵉ)
        ( Pᵉ)

  ind-iso-Categoryᵉ :
    Pᵉ Aᵉ (id-iso-Categoryᵉ Cᵉ) →
    {Bᵉ : obj-Categoryᵉ Cᵉ} (eᵉ : iso-Categoryᵉ Cᵉ Aᵉ Bᵉ) → Pᵉ Bᵉ eᵉ
  ind-iso-Categoryᵉ pᵉ {Bᵉ} = pr1ᵉ is-identity-system-iso-Categoryᵉ pᵉ Bᵉ

  compute-ind-iso-Categoryᵉ :
    (uᵉ : Pᵉ Aᵉ (id-iso-Categoryᵉ Cᵉ)) → ind-iso-Categoryᵉ uᵉ (id-iso-Categoryᵉ Cᵉ) ＝ᵉ uᵉ
  compute-ind-iso-Categoryᵉ = pr2ᵉ is-identity-system-iso-Categoryᵉ
```

### The evaluation map `ev-id-iso-Category` is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) {Aᵉ : obj-Categoryᵉ Cᵉ}
  (Pᵉ : (Bᵉ : obj-Categoryᵉ Cᵉ) (eᵉ : iso-Categoryᵉ Cᵉ Aᵉ Bᵉ) → UUᵉ l3ᵉ)
  where

  is-equiv-ev-id-iso-Categoryᵉ : is-equivᵉ (ev-id-iso-Categoryᵉ Cᵉ Pᵉ)
  is-equiv-ev-id-iso-Categoryᵉ =
    dependent-universal-property-identity-system-is-torsorialᵉ
      ( id-iso-Categoryᵉ Cᵉ)
      ( is-torsorial-iso-Categoryᵉ Cᵉ Aᵉ)
      ( Pᵉ)

  is-contr-map-ev-id-iso-Categoryᵉ :
    is-contr-mapᵉ (ev-id-iso-Categoryᵉ Cᵉ Pᵉ)
  is-contr-map-ev-id-iso-Categoryᵉ =
    is-contr-map-is-equivᵉ is-equiv-ev-id-iso-Categoryᵉ
```