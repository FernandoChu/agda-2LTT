# Isomorphisms of semigroups

```agda
module group-theory.isomorphisms-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.equivalences-semigroupsᵉ
open import group-theory.homomorphisms-semigroupsᵉ
open import group-theory.precategory-of-semigroupsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Isomorphismsᵉ ofᵉ semigroupsᵉ areᵉ homomorphismsᵉ thatᵉ haveᵉ aᵉ two-sidedᵉ inverse.ᵉ

## Definition

### The predicate of being an isomorphism of semigroups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ)
  (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ)
  where

  is-iso-Semigroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-Semigroupᵉ =
    is-iso-Large-Precategoryᵉ Semigroup-Large-Precategoryᵉ {Xᵉ = Gᵉ} {Yᵉ = Hᵉ} fᵉ

  hom-inv-is-iso-Semigroupᵉ :
    is-iso-Semigroupᵉ → hom-Semigroupᵉ Hᵉ Gᵉ
  hom-inv-is-iso-Semigroupᵉ =
    hom-inv-is-iso-Large-Precategoryᵉ
      ( Semigroup-Large-Precategoryᵉ)
      { Xᵉ = Gᵉ}
      { Yᵉ = Hᵉ}
      ( fᵉ)

  map-inv-is-iso-Semigroupᵉ :
    is-iso-Semigroupᵉ → type-Semigroupᵉ Hᵉ → type-Semigroupᵉ Gᵉ
  map-inv-is-iso-Semigroupᵉ Uᵉ =
    map-hom-Semigroupᵉ Hᵉ Gᵉ (hom-inv-is-iso-Semigroupᵉ Uᵉ)

  is-section-hom-inv-is-iso-Semigroupᵉ :
    (Uᵉ : is-iso-Semigroupᵉ) →
    comp-hom-Semigroupᵉ Hᵉ Gᵉ Hᵉ fᵉ (hom-inv-is-iso-Semigroupᵉ Uᵉ) ＝ᵉ
    id-hom-Semigroupᵉ Hᵉ
  is-section-hom-inv-is-iso-Semigroupᵉ =
    is-section-hom-inv-is-iso-Large-Precategoryᵉ
      ( Semigroup-Large-Precategoryᵉ)
      { Xᵉ = Gᵉ}
      { Yᵉ = Hᵉ}
      ( fᵉ)

  is-section-map-inv-is-iso-Semigroupᵉ :
    (Uᵉ : is-iso-Semigroupᵉ) →
    ( map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ ∘ᵉ map-inv-is-iso-Semigroupᵉ Uᵉ) ~ᵉ idᵉ
  is-section-map-inv-is-iso-Semigroupᵉ Uᵉ =
    htpy-eq-hom-Semigroupᵉ Hᵉ Hᵉ
      ( comp-hom-Semigroupᵉ Hᵉ Gᵉ Hᵉ fᵉ (hom-inv-is-iso-Semigroupᵉ Uᵉ))
      ( id-hom-Semigroupᵉ Hᵉ)
      ( is-section-hom-inv-is-iso-Semigroupᵉ Uᵉ)

  is-retraction-hom-inv-is-iso-Semigroupᵉ :
    (Uᵉ : is-iso-Semigroupᵉ) →
    comp-hom-Semigroupᵉ Gᵉ Hᵉ Gᵉ (hom-inv-is-iso-Semigroupᵉ Uᵉ) fᵉ ＝ᵉ
    id-hom-Semigroupᵉ Gᵉ
  is-retraction-hom-inv-is-iso-Semigroupᵉ =
    is-retraction-hom-inv-is-iso-Large-Precategoryᵉ
      ( Semigroup-Large-Precategoryᵉ)
      { Xᵉ = Gᵉ}
      { Yᵉ = Hᵉ}
      ( fᵉ)

  is-retraction-map-inv-is-iso-Semigroupᵉ :
    (Uᵉ : is-iso-Semigroupᵉ) →
    ( map-inv-is-iso-Semigroupᵉ Uᵉ ∘ᵉ map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-is-iso-Semigroupᵉ Uᵉ =
    htpy-eq-hom-Semigroupᵉ Gᵉ Gᵉ
      ( comp-hom-Semigroupᵉ Gᵉ Hᵉ Gᵉ (hom-inv-is-iso-Semigroupᵉ Uᵉ) fᵉ)
      ( id-hom-Semigroupᵉ Gᵉ)
      ( is-retraction-hom-inv-is-iso-Semigroupᵉ Uᵉ)
```

### Isomorphisms of semigroups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ)
  where

  iso-Semigroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  iso-Semigroupᵉ = iso-Large-Precategoryᵉ Semigroup-Large-Precategoryᵉ Gᵉ Hᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ) (fᵉ : iso-Semigroupᵉ Gᵉ Hᵉ)
  where

  hom-iso-Semigroupᵉ : hom-Semigroupᵉ Gᵉ Hᵉ
  hom-iso-Semigroupᵉ =
    hom-iso-Large-Precategoryᵉ Semigroup-Large-Precategoryᵉ {Xᵉ = Gᵉ} {Yᵉ = Hᵉ} fᵉ

  map-iso-Semigroupᵉ : type-Semigroupᵉ Gᵉ → type-Semigroupᵉ Hᵉ
  map-iso-Semigroupᵉ = map-hom-Semigroupᵉ Gᵉ Hᵉ hom-iso-Semigroupᵉ

  preserves-mul-iso-Semigroupᵉ :
    {xᵉ yᵉ : type-Semigroupᵉ Gᵉ} →
    map-iso-Semigroupᵉ (mul-Semigroupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    mul-Semigroupᵉ Hᵉ (map-iso-Semigroupᵉ xᵉ) (map-iso-Semigroupᵉ yᵉ)
  preserves-mul-iso-Semigroupᵉ =
    preserves-mul-hom-Semigroupᵉ Gᵉ Hᵉ hom-iso-Semigroupᵉ

  is-iso-iso-Semigroupᵉ : is-iso-Semigroupᵉ Gᵉ Hᵉ hom-iso-Semigroupᵉ
  is-iso-iso-Semigroupᵉ =
    is-iso-iso-Large-Precategoryᵉ Semigroup-Large-Precategoryᵉ {Xᵉ = Gᵉ} {Yᵉ = Hᵉ} fᵉ

  inv-iso-Semigroupᵉ : iso-Semigroupᵉ Hᵉ Gᵉ
  inv-iso-Semigroupᵉ =
    inv-iso-Large-Precategoryᵉ Semigroup-Large-Precategoryᵉ {Xᵉ = Gᵉ} {Yᵉ = Hᵉ} fᵉ

  hom-inv-iso-Semigroupᵉ : hom-Semigroupᵉ Hᵉ Gᵉ
  hom-inv-iso-Semigroupᵉ =
    hom-inv-iso-Large-Precategoryᵉ Semigroup-Large-Precategoryᵉ {Xᵉ = Gᵉ} {Yᵉ = Hᵉ} fᵉ

  map-inv-iso-Semigroupᵉ : type-Semigroupᵉ Hᵉ → type-Semigroupᵉ Gᵉ
  map-inv-iso-Semigroupᵉ =
    map-hom-Semigroupᵉ Hᵉ Gᵉ hom-inv-iso-Semigroupᵉ

  preserves-mul-inv-iso-Semigroupᵉ :
    {xᵉ yᵉ : type-Semigroupᵉ Hᵉ} →
    map-inv-iso-Semigroupᵉ (mul-Semigroupᵉ Hᵉ xᵉ yᵉ) ＝ᵉ
    mul-Semigroupᵉ Gᵉ (map-inv-iso-Semigroupᵉ xᵉ) (map-inv-iso-Semigroupᵉ yᵉ)
  preserves-mul-inv-iso-Semigroupᵉ =
    preserves-mul-hom-Semigroupᵉ Hᵉ Gᵉ hom-inv-iso-Semigroupᵉ

  is-section-hom-inv-iso-Semigroupᵉ :
    comp-hom-Semigroupᵉ Hᵉ Gᵉ Hᵉ hom-iso-Semigroupᵉ hom-inv-iso-Semigroupᵉ ＝ᵉ
    id-hom-Semigroupᵉ Hᵉ
  is-section-hom-inv-iso-Semigroupᵉ =
    is-section-hom-inv-iso-Large-Precategoryᵉ
      ( Semigroup-Large-Precategoryᵉ)
      { Xᵉ = Gᵉ}
      { Yᵉ = Hᵉ}
      ( fᵉ)

  is-section-map-inv-iso-Semigroupᵉ :
    map-iso-Semigroupᵉ ∘ᵉ map-inv-iso-Semigroupᵉ ~ᵉ idᵉ
  is-section-map-inv-iso-Semigroupᵉ =
    htpy-eq-hom-Semigroupᵉ Hᵉ Hᵉ
      ( comp-hom-Semigroupᵉ Hᵉ Gᵉ Hᵉ
        ( hom-iso-Semigroupᵉ)
        ( hom-inv-iso-Semigroupᵉ))
      ( id-hom-Semigroupᵉ Hᵉ)
      ( is-section-hom-inv-iso-Semigroupᵉ)

  is-retraction-hom-inv-iso-Semigroupᵉ :
    comp-hom-Semigroupᵉ Gᵉ Hᵉ Gᵉ hom-inv-iso-Semigroupᵉ hom-iso-Semigroupᵉ ＝ᵉ
    id-hom-Semigroupᵉ Gᵉ
  is-retraction-hom-inv-iso-Semigroupᵉ =
    is-retraction-hom-inv-iso-Large-Precategoryᵉ
      ( Semigroup-Large-Precategoryᵉ)
      { Xᵉ = Gᵉ}
      { Yᵉ = Hᵉ}
      ( fᵉ)

  is-retraction-map-inv-iso-Semigroupᵉ :
    map-inv-iso-Semigroupᵉ ∘ᵉ map-iso-Semigroupᵉ ~ᵉ idᵉ
  is-retraction-map-inv-iso-Semigroupᵉ =
    htpy-eq-hom-Semigroupᵉ Gᵉ Gᵉ
      ( comp-hom-Semigroupᵉ Gᵉ Hᵉ Gᵉ
        ( hom-inv-iso-Semigroupᵉ)
        ( hom-iso-Semigroupᵉ))
      ( id-hom-Semigroupᵉ Gᵉ)
      ( is-retraction-hom-inv-iso-Semigroupᵉ)
```

## Properties

### Being an isomorphism is a property

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ)
  where

  abstract
    is-prop-is-iso-Semigroupᵉ :
      (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ) → is-propᵉ (is-iso-Semigroupᵉ Gᵉ Hᵉ fᵉ)
    is-prop-is-iso-Semigroupᵉ =
      is-prop-is-iso-Large-Precategoryᵉ
        ( Semigroup-Large-Precategoryᵉ)
        { Xᵉ = Gᵉ}
        { Yᵉ = Hᵉ}

  is-iso-prop-Semigroupᵉ :
    hom-Semigroupᵉ Gᵉ Hᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-prop-Semigroupᵉ =
    is-iso-prop-Large-Precategoryᵉ
      ( Semigroup-Large-Precategoryᵉ)
      { Xᵉ = Gᵉ}
      { Yᵉ = Hᵉ}
```

### The inverse of an equivalence of semigroups preserves the binary operation

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ)
  where

  abstract
    preserves-mul-map-inv-is-equiv-Semigroupᵉ :
      ( fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ)
      ( Uᵉ : is-equivᵉ (map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ)) →
      preserves-mul-Semigroupᵉ Hᵉ Gᵉ (map-inv-is-equivᵉ Uᵉ)
    preserves-mul-map-inv-is-equiv-Semigroupᵉ (fᵉ ,ᵉ μ-fᵉ) Uᵉ {xᵉ} {yᵉ} =
      map-inv-is-equivᵉ
        ( is-emb-is-equivᵉ Uᵉ
          ( map-inv-is-equivᵉ Uᵉ (mul-Semigroupᵉ Hᵉ xᵉ yᵉ))
          ( mul-Semigroupᵉ Gᵉ
            ( map-inv-is-equivᵉ Uᵉ xᵉ)
            ( map-inv-is-equivᵉ Uᵉ yᵉ)))
        ( ( is-section-map-inv-is-equivᵉ Uᵉ (mul-Semigroupᵉ Hᵉ xᵉ yᵉ)) ∙ᵉ
          ( apᵉ
            ( λ tᵉ → mul-Semigroupᵉ Hᵉ tᵉ yᵉ)
            ( invᵉ (is-section-map-inv-is-equivᵉ Uᵉ xᵉ))) ∙ᵉ
          ( apᵉ
            ( mul-Semigroupᵉ Hᵉ (fᵉ (map-inv-is-equivᵉ Uᵉ xᵉ)))
            ( invᵉ (is-section-map-inv-is-equivᵉ Uᵉ yᵉ))) ∙ᵉ
          ( invᵉ μ-fᵉ))
```

### A homomorphism of semigroups is an equivalence of semigroups if and only if it is an isomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ)
  where

  abstract
    is-iso-is-equiv-hom-Semigroupᵉ :
      (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ) →
      is-equiv-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ → is-iso-Semigroupᵉ Gᵉ Hᵉ fᵉ
    pr1ᵉ (pr1ᵉ (is-iso-is-equiv-hom-Semigroupᵉ (fᵉ ,ᵉ μ-fᵉ) Uᵉ)) =
      map-inv-is-equivᵉ Uᵉ
    pr2ᵉ (pr1ᵉ (is-iso-is-equiv-hom-Semigroupᵉ (fᵉ ,ᵉ μ-fᵉ) Uᵉ)) =
      preserves-mul-map-inv-is-equiv-Semigroupᵉ Gᵉ Hᵉ (fᵉ ,ᵉ μ-fᵉ) Uᵉ
    pr1ᵉ (pr2ᵉ (is-iso-is-equiv-hom-Semigroupᵉ (fᵉ ,ᵉ μ-fᵉ) Uᵉ)) =
      eq-htpy-hom-Semigroupᵉ Hᵉ Hᵉ (is-section-map-inv-is-equivᵉ Uᵉ)
    pr2ᵉ (pr2ᵉ (is-iso-is-equiv-hom-Semigroupᵉ (fᵉ ,ᵉ μ-fᵉ) Uᵉ)) =
      eq-htpy-hom-Semigroupᵉ Gᵉ Gᵉ (is-retraction-map-inv-is-equivᵉ Uᵉ)

  abstract
    is-equiv-is-iso-Semigroupᵉ :
      (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ) →
      is-iso-Semigroupᵉ Gᵉ Hᵉ fᵉ → is-equiv-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ
    is-equiv-is-iso-Semigroupᵉ (fᵉ ,ᵉ μ-fᵉ) ((gᵉ ,ᵉ μ-gᵉ) ,ᵉ Sᵉ ,ᵉ Rᵉ) =
      is-equiv-is-invertibleᵉ gᵉ
        ( htpy-eqᵉ (apᵉ pr1ᵉ Sᵉ))
        ( htpy-eqᵉ (apᵉ pr1ᵉ Rᵉ))

  equiv-iso-equiv-Semigroupᵉ : equiv-Semigroupᵉ Gᵉ Hᵉ ≃ᵉ iso-Semigroupᵉ Gᵉ Hᵉ
  equiv-iso-equiv-Semigroupᵉ =
    ( equiv-type-subtypeᵉ
      ( λ fᵉ → is-property-is-equivᵉ (map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ))
      ( is-prop-is-iso-Semigroupᵉ Gᵉ Hᵉ)
      ( is-iso-is-equiv-hom-Semigroupᵉ)
      ( is-equiv-is-iso-Semigroupᵉ)) ∘eᵉ
    ( equiv-right-swap-Σᵉ)

  iso-equiv-Semigroupᵉ : equiv-Semigroupᵉ Gᵉ Hᵉ → iso-Semigroupᵉ Gᵉ Hᵉ
  iso-equiv-Semigroupᵉ = map-equivᵉ equiv-iso-equiv-Semigroupᵉ
```

### Two semigroups are equal if and only if they are isomorphic

```agda
module _
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ)
  where

  is-torsorial-iso-Semigroupᵉ :
    is-torsorialᵉ (iso-Semigroupᵉ Gᵉ)
  is-torsorial-iso-Semigroupᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (Semigroupᵉ lᵉ) (equiv-Semigroupᵉ Gᵉ))
      ( equiv-totᵉ (equiv-iso-equiv-Semigroupᵉ Gᵉ))
      ( is-torsorial-equiv-Semigroupᵉ Gᵉ)

  id-iso-Semigroupᵉ : iso-Semigroupᵉ Gᵉ Gᵉ
  id-iso-Semigroupᵉ =
    id-iso-Large-Precategoryᵉ Semigroup-Large-Precategoryᵉ {Xᵉ = Gᵉ}

  iso-eq-Semigroupᵉ : (Hᵉ : Semigroupᵉ lᵉ) → Idᵉ Gᵉ Hᵉ → iso-Semigroupᵉ Gᵉ Hᵉ
  iso-eq-Semigroupᵉ = iso-eq-Large-Precategoryᵉ Semigroup-Large-Precategoryᵉ Gᵉ
```