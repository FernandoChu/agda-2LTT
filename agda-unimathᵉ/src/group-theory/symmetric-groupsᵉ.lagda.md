# Symmetric groups

```agda
module group-theory.symmetric-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.automorphismsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.homomorphisms-semigroupsᵉ
open import group-theory.isomorphisms-groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.opposite-groupsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.symmetric-concrete-groupsᵉ
```

</details>

## Definitions

```agda
set-symmetric-Groupᵉ : {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) → Setᵉ lᵉ
set-symmetric-Groupᵉ Xᵉ = Aut-Setᵉ Xᵉ

type-symmetric-Groupᵉ : {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) → UUᵉ lᵉ
type-symmetric-Groupᵉ Xᵉ = type-Setᵉ (set-symmetric-Groupᵉ Xᵉ)

is-set-type-symmetric-Groupᵉ :
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) → is-setᵉ (type-symmetric-Groupᵉ Xᵉ)
is-set-type-symmetric-Groupᵉ Xᵉ = is-set-type-Setᵉ (set-symmetric-Groupᵉ Xᵉ)

has-associative-mul-aut-Setᵉ :
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) → has-associative-mul-Setᵉ (Aut-Setᵉ Xᵉ)
pr1ᵉ (has-associative-mul-aut-Setᵉ Xᵉ) fᵉ eᵉ = fᵉ ∘eᵉ eᵉ
pr2ᵉ (has-associative-mul-aut-Setᵉ Xᵉ) eᵉ fᵉ gᵉ = associative-comp-equivᵉ gᵉ fᵉ eᵉ

symmetric-Semigroupᵉ :
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) → Semigroupᵉ lᵉ
pr1ᵉ (symmetric-Semigroupᵉ Xᵉ) = set-symmetric-Groupᵉ Xᵉ
pr2ᵉ (symmetric-Semigroupᵉ Xᵉ) = has-associative-mul-aut-Setᵉ Xᵉ

is-unital-Semigroup-symmetric-Semigroupᵉ :
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) → is-unital-Semigroupᵉ (symmetric-Semigroupᵉ Xᵉ)
pr1ᵉ (is-unital-Semigroup-symmetric-Semigroupᵉ Xᵉ) = id-equivᵉ
pr1ᵉ (pr2ᵉ (is-unital-Semigroup-symmetric-Semigroupᵉ Xᵉ)) = left-unit-law-equivᵉ
pr2ᵉ (pr2ᵉ (is-unital-Semigroup-symmetric-Semigroupᵉ Xᵉ)) = right-unit-law-equivᵉ

is-group-symmetric-Semigroup'ᵉ :
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) →
  is-group-is-unital-Semigroupᵉ
    ( symmetric-Semigroupᵉ Xᵉ)
    ( is-unital-Semigroup-symmetric-Semigroupᵉ Xᵉ)
pr1ᵉ (is-group-symmetric-Semigroup'ᵉ Xᵉ) = inv-equivᵉ
pr1ᵉ (pr2ᵉ (is-group-symmetric-Semigroup'ᵉ Xᵉ)) = left-inverse-law-equivᵉ
pr2ᵉ (pr2ᵉ (is-group-symmetric-Semigroup'ᵉ Xᵉ)) = right-inverse-law-equivᵉ

symmetric-Groupᵉ :
  {lᵉ : Level} → Setᵉ lᵉ → Groupᵉ lᵉ
pr1ᵉ (symmetric-Groupᵉ Xᵉ) = symmetric-Semigroupᵉ Xᵉ
pr1ᵉ (pr2ᵉ (symmetric-Groupᵉ Xᵉ)) = is-unital-Semigroup-symmetric-Semigroupᵉ Xᵉ
pr2ᵉ (pr2ᵉ (symmetric-Groupᵉ Xᵉ)) = is-group-symmetric-Semigroup'ᵉ Xᵉ
```

## Properties

### If two sets are equivalent, then their symmetric groups are isomorphic

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Setᵉ l1ᵉ) (Yᵉ : Setᵉ l2ᵉ) (eᵉ : type-Setᵉ Xᵉ ≃ᵉ type-Setᵉ Yᵉ)
  where

  hom-symmetric-group-equiv-Setᵉ :
    hom-Groupᵉ (symmetric-Groupᵉ Xᵉ) (symmetric-Groupᵉ Yᵉ)
  pr1ᵉ hom-symmetric-group-equiv-Setᵉ fᵉ = eᵉ ∘eᵉ (fᵉ ∘eᵉ inv-equivᵉ eᵉ)
  pr2ᵉ hom-symmetric-group-equiv-Setᵉ {fᵉ} {gᵉ} =
    ( eq-equiv-eq-map-equivᵉ reflᵉ) ∙ᵉ
    ( apᵉ
      ( λ hᵉ → eᵉ ∘eᵉ fᵉ ∘eᵉ hᵉ ∘eᵉ gᵉ ∘eᵉ inv-equivᵉ eᵉ)
      ( invᵉ (left-inverse-law-equivᵉ eᵉ))) ∙ᵉ
    ( eq-equiv-eq-map-equivᵉ reflᵉ)

  hom-inv-symmetric-group-equiv-Setᵉ :
    hom-Groupᵉ (symmetric-Groupᵉ Yᵉ) (symmetric-Groupᵉ Xᵉ)
  pr1ᵉ hom-inv-symmetric-group-equiv-Setᵉ fᵉ = inv-equivᵉ eᵉ ∘eᵉ fᵉ ∘eᵉ eᵉ
  pr2ᵉ hom-inv-symmetric-group-equiv-Setᵉ {fᵉ} {gᵉ} =
    ( eq-equiv-eq-map-equivᵉ reflᵉ) ∙ᵉ
    ( apᵉ
      ( λ hᵉ → inv-equivᵉ eᵉ ∘eᵉ fᵉ ∘eᵉ hᵉ ∘eᵉ gᵉ ∘eᵉ eᵉ)
      ( invᵉ (right-inverse-law-equivᵉ eᵉ))) ∙ᵉ
    ( eq-equiv-eq-map-equivᵉ reflᵉ)

  is-section-hom-inv-symmetric-group-equiv-Setᵉ :
    Idᵉ
      ( comp-hom-Groupᵉ
        ( symmetric-Groupᵉ Yᵉ)
        ( symmetric-Groupᵉ Xᵉ)
        ( symmetric-Groupᵉ Yᵉ)
        ( hom-symmetric-group-equiv-Setᵉ)
        ( hom-inv-symmetric-group-equiv-Setᵉ))
      ( id-hom-Groupᵉ (symmetric-Groupᵉ Yᵉ))
  is-section-hom-inv-symmetric-group-equiv-Setᵉ =
    eq-type-subtypeᵉ
      ( preserves-mul-prop-Semigroupᵉ
        ( semigroup-Groupᵉ (symmetric-Groupᵉ Yᵉ))
        ( semigroup-Groupᵉ (symmetric-Groupᵉ Yᵉ)))
      ( eq-htpyᵉ
        ( λ fᵉ →
          ( eq-equiv-eq-map-equivᵉ reflᵉ) ∙ᵉ
          ( apᵉ (λ hᵉ → hᵉ ∘eᵉ fᵉ ∘eᵉ hᵉ) (right-inverse-law-equivᵉ eᵉ)) ∙ᵉ
          ( eq-equiv-eq-map-equivᵉ reflᵉ)))

  is-retraction-hom-inv-symmetric-group-equiv-Setᵉ :
    Idᵉ
      ( comp-hom-Groupᵉ
        ( symmetric-Groupᵉ Xᵉ)
        ( symmetric-Groupᵉ Yᵉ)
        ( symmetric-Groupᵉ Xᵉ)
        ( hom-inv-symmetric-group-equiv-Setᵉ)
        ( hom-symmetric-group-equiv-Setᵉ))
      ( id-hom-Groupᵉ (symmetric-Groupᵉ Xᵉ))
  is-retraction-hom-inv-symmetric-group-equiv-Setᵉ =
    eq-type-subtypeᵉ
      ( preserves-mul-prop-Semigroupᵉ
        ( semigroup-Groupᵉ (symmetric-Groupᵉ Xᵉ))
        ( semigroup-Groupᵉ (symmetric-Groupᵉ Xᵉ)))
      ( eq-htpyᵉ
        ( λ fᵉ →
          ( eq-equiv-eq-map-equivᵉ reflᵉ) ∙ᵉ
          ( apᵉ (λ hᵉ → hᵉ ∘eᵉ fᵉ ∘eᵉ hᵉ) (left-inverse-law-equivᵉ eᵉ)) ∙ᵉ
          ( eq-equiv-eq-map-equivᵉ reflᵉ)))

  iso-symmetric-group-equiv-Setᵉ :
    iso-Groupᵉ (symmetric-Groupᵉ Xᵉ) (symmetric-Groupᵉ Yᵉ)
  pr1ᵉ iso-symmetric-group-equiv-Setᵉ =
    hom-symmetric-group-equiv-Setᵉ
  pr1ᵉ (pr2ᵉ iso-symmetric-group-equiv-Setᵉ) =
    hom-inv-symmetric-group-equiv-Setᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ iso-symmetric-group-equiv-Setᵉ)) =
    is-section-hom-inv-symmetric-group-equiv-Setᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ iso-symmetric-group-equiv-Setᵉ)) =
    is-retraction-hom-inv-symmetric-group-equiv-Setᵉ
```

### The symmetric group and the abstract automorphism group of a set are isomorphic

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ)
  where

  equiv-compute-symmetric-Concrete-Groupᵉ :
    type-Concrete-Groupᵉ (symmetric-Concrete-Groupᵉ Aᵉ) ≃ᵉ type-symmetric-Groupᵉ Aᵉ
  equiv-compute-symmetric-Concrete-Groupᵉ =
    extensionality-classifying-type-symmetric-Concrete-Groupᵉ Aᵉ
      ( shape-symmetric-Concrete-Groupᵉ Aᵉ)
      ( shape-symmetric-Concrete-Groupᵉ Aᵉ)

  map-compute-symmetric-Concrete-Groupᵉ :
    type-Concrete-Groupᵉ (symmetric-Concrete-Groupᵉ Aᵉ) → type-symmetric-Groupᵉ Aᵉ
  map-compute-symmetric-Concrete-Groupᵉ =
    equiv-eq-classifying-type-symmetric-Concrete-Groupᵉ Aᵉ
      ( shape-symmetric-Concrete-Groupᵉ Aᵉ)
      ( shape-symmetric-Concrete-Groupᵉ Aᵉ)

  preserves-mul-compute-symmetric-Concrete-Groupᵉ :
    preserves-mul-Groupᵉ
      ( op-group-Concrete-Groupᵉ (symmetric-Concrete-Groupᵉ Aᵉ))
      ( symmetric-Groupᵉ Aᵉ)
      ( map-compute-symmetric-Concrete-Groupᵉ)
  preserves-mul-compute-symmetric-Concrete-Groupᵉ {xᵉ} {yᵉ} =
    preserves-mul-equiv-eq-classifying-type-symmetric-Concrete-Groupᵉ Aᵉ
      ( shape-symmetric-Concrete-Groupᵉ Aᵉ)
      ( shape-symmetric-Concrete-Groupᵉ Aᵉ)
      ( shape-symmetric-Concrete-Groupᵉ Aᵉ)
      ( xᵉ)
      ( yᵉ)

  equiv-group-compute-symmetric-Concrete-Groupᵉ :
    equiv-Groupᵉ
      ( op-group-Concrete-Groupᵉ (symmetric-Concrete-Groupᵉ Aᵉ))
      ( symmetric-Groupᵉ Aᵉ)
  pr1ᵉ equiv-group-compute-symmetric-Concrete-Groupᵉ =
    equiv-compute-symmetric-Concrete-Groupᵉ
  pr2ᵉ equiv-group-compute-symmetric-Concrete-Groupᵉ {xᵉ} {yᵉ} =
    preserves-mul-compute-symmetric-Concrete-Groupᵉ {xᵉ} {yᵉ}

  compute-symmetric-Concrete-Group'ᵉ :
    iso-Groupᵉ
      ( op-group-Concrete-Groupᵉ (symmetric-Concrete-Groupᵉ Aᵉ))
      ( symmetric-Groupᵉ Aᵉ)
  compute-symmetric-Concrete-Group'ᵉ =
    iso-equiv-Groupᵉ
      ( op-group-Concrete-Groupᵉ (symmetric-Concrete-Groupᵉ Aᵉ))
      ( symmetric-Groupᵉ Aᵉ)
      ( equiv-group-compute-symmetric-Concrete-Groupᵉ)

  compute-symmetric-Concrete-Groupᵉ :
    iso-Groupᵉ
      ( group-Concrete-Groupᵉ (symmetric-Concrete-Groupᵉ Aᵉ))
      ( symmetric-Groupᵉ Aᵉ)
  compute-symmetric-Concrete-Groupᵉ =
    comp-iso-Groupᵉ
      ( group-Concrete-Groupᵉ (symmetric-Concrete-Groupᵉ Aᵉ))
      ( op-group-Concrete-Groupᵉ (symmetric-Concrete-Groupᵉ Aᵉ))
      ( symmetric-Groupᵉ Aᵉ)
      ( compute-symmetric-Concrete-Group'ᵉ)
      ( iso-inv-Groupᵉ (group-Concrete-Groupᵉ (symmetric-Concrete-Groupᵉ Aᵉ)))
```