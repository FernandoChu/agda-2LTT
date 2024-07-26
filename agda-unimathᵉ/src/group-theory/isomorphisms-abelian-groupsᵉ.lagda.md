# Isomorphisms of abelian groups

```agda
module group-theory.isomorphisms-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.homomorphisms-abelian-groupsᵉ
open import group-theory.isomorphisms-groupsᵉ
```

</details>

## Idea

**Isomorphisms**ᵉ betweenᵉ [abelianᵉ groups](group-theory.abelian-groups.mdᵉ) areᵉ
justᵉ [isomorphisms](group-theory.isomorphisms-groups.mdᵉ) betweenᵉ theirᵉ
underlyingᵉ [groups](group-theory.groups.md).ᵉ

## Definitions

### The predicate of being an isomorphism of abelian groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ) (fᵉ : hom-Abᵉ Aᵉ Bᵉ)
  where

  is-iso-Abᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-Abᵉ = is-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  is-prop-is-iso-Abᵉ : is-propᵉ is-iso-Abᵉ
  is-prop-is-iso-Abᵉ =
    is-prop-is-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  is-iso-prop-Abᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-prop-Abᵉ = is-iso-prop-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  hom-inv-is-iso-Abᵉ : is-iso-Abᵉ → hom-Abᵉ Bᵉ Aᵉ
  hom-inv-is-iso-Abᵉ = hom-inv-is-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  map-inv-is-iso-Abᵉ : is-iso-Abᵉ → type-Abᵉ Bᵉ → type-Abᵉ Aᵉ
  map-inv-is-iso-Abᵉ =
    map-inv-is-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  is-section-hom-inv-is-iso-Abᵉ :
    (Hᵉ : is-iso-Abᵉ) →
    comp-hom-Abᵉ Bᵉ Aᵉ Bᵉ fᵉ (hom-inv-is-iso-Abᵉ Hᵉ) ＝ᵉ id-hom-Abᵉ Bᵉ
  is-section-hom-inv-is-iso-Abᵉ =
    is-section-hom-inv-is-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  is-section-map-inv-is-iso-Abᵉ :
    (Hᵉ : is-iso-Abᵉ) →
    ( map-hom-Abᵉ Aᵉ Bᵉ fᵉ ∘ᵉ map-hom-Abᵉ Bᵉ Aᵉ (hom-inv-is-iso-Abᵉ Hᵉ)) ~ᵉ idᵉ
  is-section-map-inv-is-iso-Abᵉ =
    is-section-map-inv-is-iso-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( group-Abᵉ Bᵉ)
      ( fᵉ)

  is-retraction-hom-inv-is-iso-Abᵉ :
    (Hᵉ : is-iso-Abᵉ) →
    comp-hom-Abᵉ Aᵉ Bᵉ Aᵉ (hom-inv-is-iso-Abᵉ Hᵉ) fᵉ ＝ᵉ id-hom-Abᵉ Aᵉ
  is-retraction-hom-inv-is-iso-Abᵉ Hᵉ = pr2ᵉ (pr2ᵉ Hᵉ)

  is-retraction-map-inv-is-iso-Abᵉ :
    (Hᵉ : is-iso-Abᵉ) →
    ( map-inv-is-iso-Abᵉ Hᵉ ∘ᵉ map-hom-Abᵉ Aᵉ Bᵉ fᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-is-iso-Abᵉ =
    is-retraction-map-inv-is-iso-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( group-Abᵉ Bᵉ)
      ( fᵉ)
```

### The predicate of being an equivalence of abelian groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  is-equiv-hom-Abᵉ : hom-Abᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-equiv-hom-Abᵉ =
    is-equiv-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  equiv-Abᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-Abᵉ = equiv-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)
```

### The type of isomorphisms of abelian groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  iso-Abᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  iso-Abᵉ = iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  hom-iso-Abᵉ : iso-Abᵉ → hom-Abᵉ Aᵉ Bᵉ
  hom-iso-Abᵉ = hom-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  map-iso-Abᵉ : iso-Abᵉ → type-Abᵉ Aᵉ → type-Abᵉ Bᵉ
  map-iso-Abᵉ = map-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  preserves-add-iso-Abᵉ :
    (fᵉ : iso-Abᵉ) {xᵉ yᵉ : type-Abᵉ Aᵉ} →
    map-iso-Abᵉ fᵉ (add-Abᵉ Aᵉ xᵉ yᵉ) ＝ᵉ add-Abᵉ Bᵉ (map-iso-Abᵉ fᵉ xᵉ) (map-iso-Abᵉ fᵉ yᵉ)
  preserves-add-iso-Abᵉ =
    preserves-mul-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  is-iso-iso-Abᵉ : (fᵉ : iso-Abᵉ) → is-iso-Abᵉ Aᵉ Bᵉ (hom-iso-Abᵉ fᵉ)
  is-iso-iso-Abᵉ = is-iso-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  hom-inv-iso-Abᵉ : iso-Abᵉ → hom-Abᵉ Bᵉ Aᵉ
  hom-inv-iso-Abᵉ = hom-inv-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  map-inv-iso-Abᵉ : iso-Abᵉ → type-Abᵉ Bᵉ → type-Abᵉ Aᵉ
  map-inv-iso-Abᵉ = map-inv-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  preserves-add-inv-iso-Abᵉ :
    (fᵉ : iso-Abᵉ) {xᵉ yᵉ : type-Abᵉ Bᵉ} →
    map-inv-iso-Abᵉ fᵉ (add-Abᵉ Bᵉ xᵉ yᵉ) ＝ᵉ
    add-Abᵉ Aᵉ (map-inv-iso-Abᵉ fᵉ xᵉ) (map-inv-iso-Abᵉ fᵉ yᵉ)
  preserves-add-inv-iso-Abᵉ =
    preserves-mul-inv-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  is-section-hom-inv-iso-Abᵉ :
    (fᵉ : iso-Abᵉ) →
    comp-hom-Abᵉ Bᵉ Aᵉ Bᵉ (hom-iso-Abᵉ fᵉ) (hom-inv-iso-Abᵉ fᵉ) ＝ᵉ id-hom-Abᵉ Bᵉ
  is-section-hom-inv-iso-Abᵉ =
    is-section-hom-inv-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  is-section-map-inv-iso-Abᵉ :
    (fᵉ : iso-Abᵉ) → (map-iso-Abᵉ fᵉ ∘ᵉ map-inv-iso-Abᵉ fᵉ) ~ᵉ idᵉ
  is-section-map-inv-iso-Abᵉ =
    is-section-map-inv-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  is-retraction-hom-inv-iso-Abᵉ :
    (fᵉ : iso-Abᵉ) →
    comp-hom-Abᵉ Aᵉ Bᵉ Aᵉ (hom-inv-iso-Abᵉ fᵉ) (hom-iso-Abᵉ fᵉ) ＝ᵉ id-hom-Abᵉ Aᵉ
  is-retraction-hom-inv-iso-Abᵉ =
    is-retraction-hom-inv-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  is-retraction-map-inv-iso-Abᵉ :
    (fᵉ : iso-Abᵉ) → (map-inv-iso-Abᵉ fᵉ ∘ᵉ map-iso-Abᵉ fᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-iso-Abᵉ =
    is-retraction-map-inv-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)
```

### The identity isomorphism of abelian groups

```agda
id-iso-Abᵉ : {lᵉ : Level} (Aᵉ : Abᵉ lᵉ) → iso-Abᵉ Aᵉ Aᵉ
id-iso-Abᵉ Aᵉ = id-iso-Groupᵉ (group-Abᵉ Aᵉ)
```

## Properties

### Isomorphisms characterize identifications of abelian groups

```agda
iso-eq-Abᵉ :
  {lᵉ : Level} (Aᵉ Bᵉ : Abᵉ lᵉ) → Idᵉ Aᵉ Bᵉ → iso-Abᵉ Aᵉ Bᵉ
iso-eq-Abᵉ Aᵉ Bᵉ pᵉ = iso-eq-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) (apᵉ pr1ᵉ pᵉ)

abstract
  equiv-iso-eq-Ab'ᵉ :
    {lᵉ : Level} (Aᵉ Bᵉ : Abᵉ lᵉ) → Idᵉ Aᵉ Bᵉ ≃ᵉ iso-Abᵉ Aᵉ Bᵉ
  equiv-iso-eq-Ab'ᵉ Aᵉ Bᵉ =
    ( extensionality-Group'ᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)) ∘eᵉ
    ( equiv-ap-inclusion-subtypeᵉ is-abelian-prop-Groupᵉ {Aᵉ} {Bᵉ})

abstract
  is-torsorial-iso-Abᵉ :
    {lᵉ : Level} (Aᵉ : Abᵉ lᵉ) → is-torsorialᵉ (λ (Bᵉ : Abᵉ lᵉ) → iso-Abᵉ Aᵉ Bᵉ)
  is-torsorial-iso-Abᵉ {lᵉ} Aᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (Abᵉ lᵉ) (Idᵉ Aᵉ))
      ( equiv-totᵉ (equiv-iso-eq-Ab'ᵉ Aᵉ))
      ( is-torsorial-Idᵉ Aᵉ)

is-equiv-iso-eq-Abᵉ :
  {lᵉ : Level} (Aᵉ Bᵉ : Abᵉ lᵉ) → is-equivᵉ (iso-eq-Abᵉ Aᵉ Bᵉ)
is-equiv-iso-eq-Abᵉ Aᵉ =
  fundamental-theorem-idᵉ
    ( is-torsorial-iso-Abᵉ Aᵉ)
    ( iso-eq-Abᵉ Aᵉ)

eq-iso-Abᵉ :
  {lᵉ : Level} (Aᵉ Bᵉ : Abᵉ lᵉ) → iso-Abᵉ Aᵉ Bᵉ → Idᵉ Aᵉ Bᵉ
eq-iso-Abᵉ Aᵉ Bᵉ = map-inv-is-equivᵉ (is-equiv-iso-eq-Abᵉ Aᵉ Bᵉ)
```

### A homomorphism of abelian groups is an isomorphism if and only if its underlying map is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  is-iso-is-equiv-hom-Abᵉ :
    (fᵉ : hom-Abᵉ Aᵉ Bᵉ) → is-equiv-hom-Abᵉ Aᵉ Bᵉ fᵉ → is-iso-Abᵉ Aᵉ Bᵉ fᵉ
  is-iso-is-equiv-hom-Abᵉ = is-iso-is-equiv-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  is-equiv-is-iso-Abᵉ :
    (fᵉ : hom-Abᵉ Aᵉ Bᵉ) → is-iso-Abᵉ Aᵉ Bᵉ fᵉ → is-equiv-hom-Abᵉ Aᵉ Bᵉ fᵉ
  is-equiv-is-iso-Abᵉ = is-equiv-is-iso-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  equiv-iso-equiv-Abᵉ : equiv-Abᵉ Aᵉ Bᵉ ≃ᵉ iso-Abᵉ Aᵉ Bᵉ
  equiv-iso-equiv-Abᵉ = equiv-iso-equiv-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  iso-equiv-Abᵉ : equiv-Abᵉ Aᵉ Bᵉ → iso-Abᵉ Aᵉ Bᵉ
  iso-equiv-Abᵉ = iso-equiv-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)
```