# Concrete automorphism groups on sets

```agda
module group-theory.loop-groups-setsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.identity-truncated-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import group-theory.automorphism-groupsᵉ
open import group-theory.concrete-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.homomorphisms-semigroupsᵉ
open import group-theory.isomorphisms-groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.symmetric-groupsᵉ
```

</details>

## Definitions

```agda
module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ)
  where

  type-loop-Setᵉ : UUᵉ (lsuc lᵉ)
  type-loop-Setᵉ = Idᵉ (type-Setᵉ Xᵉ) (type-Setᵉ Xᵉ)

  is-set-type-loop-Setᵉ : is-setᵉ type-loop-Setᵉ
  is-set-type-loop-Setᵉ =
    is-trunc-id-is-truncᵉ zero-𝕋ᵉ (is-set-type-Setᵉ Xᵉ) (is-set-type-Setᵉ Xᵉ)

  set-loop-Setᵉ : Setᵉ (lsuc lᵉ)
  pr1ᵉ set-loop-Setᵉ = type-loop-Setᵉ
  pr2ᵉ set-loop-Setᵉ = is-set-type-loop-Setᵉ

  has-associative-mul-loop-Setᵉ : has-associative-mul-Setᵉ (set-loop-Setᵉ)
  pr1ᵉ has-associative-mul-loop-Setᵉ = _∙ᵉ_
  pr2ᵉ has-associative-mul-loop-Setᵉ = assocᵉ

  loop-semigroup-Setᵉ : Semigroupᵉ (lsuc lᵉ)
  pr1ᵉ loop-semigroup-Setᵉ = set-loop-Setᵉ
  pr2ᵉ loop-semigroup-Setᵉ = has-associative-mul-loop-Setᵉ

  is-unital-Semigroup-loop-semigroup-Setᵉ :
    is-unital-Semigroupᵉ loop-semigroup-Setᵉ
  pr1ᵉ is-unital-Semigroup-loop-semigroup-Setᵉ = reflᵉ
  pr1ᵉ (pr2ᵉ is-unital-Semigroup-loop-semigroup-Setᵉ) yᵉ = left-unitᵉ
  pr2ᵉ (pr2ᵉ is-unital-Semigroup-loop-semigroup-Setᵉ) xᵉ = right-unitᵉ

  is-group-loop-semigroup-Set'ᵉ :
    is-group-is-unital-Semigroupᵉ
      ( loop-semigroup-Setᵉ)
      ( is-unital-Semigroup-loop-semigroup-Setᵉ)
  pr1ᵉ is-group-loop-semigroup-Set'ᵉ = invᵉ
  pr1ᵉ (pr2ᵉ is-group-loop-semigroup-Set'ᵉ) = left-invᵉ
  pr2ᵉ (pr2ᵉ is-group-loop-semigroup-Set'ᵉ) = right-invᵉ

  loop-group-Setᵉ : Groupᵉ (lsuc lᵉ)
  pr1ᵉ loop-group-Setᵉ = loop-semigroup-Setᵉ
  pr1ᵉ (pr2ᵉ loop-group-Setᵉ) = is-unital-Semigroup-loop-semigroup-Setᵉ
  pr2ᵉ (pr2ᵉ loop-group-Setᵉ) = is-group-loop-semigroup-Set'ᵉ
```

## Properties

### The symmetry group and the loop group of a set are isomorphic

```agda
module _
  {lᵉ : Level}
  where

  map-hom-symmetric-group-loop-group-Setᵉ :
    (Xᵉ Yᵉ : Setᵉ lᵉ) →
    Idᵉ (type-Setᵉ Xᵉ) (type-Setᵉ Yᵉ) → (type-Setᵉ Yᵉ) ≃ᵉ (type-Setᵉ Xᵉ)
  map-hom-symmetric-group-loop-group-Setᵉ Xᵉ Yᵉ pᵉ = equiv-eqᵉ (invᵉ pᵉ)

  map-hom-inv-symmetric-group-loop-group-Setᵉ :
    (Xᵉ Yᵉ : Setᵉ lᵉ) →
    (type-Setᵉ Xᵉ) ≃ᵉ (type-Setᵉ Yᵉ) → Idᵉ (type-Setᵉ Yᵉ) (type-Setᵉ Xᵉ)
  map-hom-inv-symmetric-group-loop-group-Setᵉ Xᵉ Yᵉ fᵉ = invᵉ (eq-equivᵉ fᵉ)

  commutative-inv-map-hom-symmetric-group-loop-group-Setᵉ :
    (Xᵉ Yᵉ : UUᵉ lᵉ) (pᵉ : Idᵉ Xᵉ Yᵉ) (sXᵉ : is-setᵉ Xᵉ) (sYᵉ : is-setᵉ Yᵉ) →
    Idᵉ
      ( map-hom-symmetric-group-loop-group-Setᵉ (Yᵉ ,ᵉ sYᵉ) (Xᵉ ,ᵉ sXᵉ) (invᵉ pᵉ))
      ( inv-equivᵉ
        ( map-hom-symmetric-group-loop-group-Setᵉ (Xᵉ ,ᵉ sXᵉ) (Yᵉ ,ᵉ sYᵉ) pᵉ))
  commutative-inv-map-hom-symmetric-group-loop-group-Setᵉ Xᵉ .Xᵉ reflᵉ sXᵉ sYᵉ =
    ( invᵉ (right-inverse-law-equivᵉ id-equivᵉ)) ∙ᵉ
    ( left-unit-law-equivᵉ (inv-equivᵉ id-equivᵉ))

module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ)
  where

  hom-symmetric-group-loop-group-Setᵉ :
    hom-Groupᵉ (loop-group-Setᵉ Xᵉ) (symmetric-Groupᵉ Xᵉ)
  pr1ᵉ hom-symmetric-group-loop-group-Setᵉ =
    map-hom-symmetric-group-loop-group-Setᵉ Xᵉ Xᵉ
  pr2ᵉ hom-symmetric-group-loop-group-Setᵉ {pᵉ} {qᵉ} =
    ( apᵉ equiv-eqᵉ (distributive-inv-concatᵉ pᵉ qᵉ)) ∙ᵉ
    ( invᵉ (compute-equiv-eq-concatᵉ (invᵉ qᵉ) (invᵉ pᵉ)))

  hom-inv-symmetric-group-loop-group-Setᵉ :
    hom-Groupᵉ (symmetric-Groupᵉ Xᵉ) (loop-group-Setᵉ Xᵉ)
  pr1ᵉ hom-inv-symmetric-group-loop-group-Setᵉ =
    map-hom-inv-symmetric-group-loop-group-Setᵉ Xᵉ Xᵉ
  pr2ᵉ hom-inv-symmetric-group-loop-group-Setᵉ {fᵉ} {gᵉ} =
    ( apᵉ invᵉ (invᵉ (compute-eq-equiv-comp-equivᵉ gᵉ fᵉ))) ∙ᵉ
    ( distributive-inv-concatᵉ (eq-equivᵉ gᵉ) (eq-equivᵉ fᵉ))

  is-section-hom-inv-symmetric-group-loop-group-Setᵉ :
    Idᵉ
      ( comp-hom-Groupᵉ
        ( symmetric-Groupᵉ Xᵉ)
        ( loop-group-Setᵉ Xᵉ)
        ( symmetric-Groupᵉ Xᵉ)
        ( hom-symmetric-group-loop-group-Setᵉ)
        ( hom-inv-symmetric-group-loop-group-Setᵉ))
      ( id-hom-Groupᵉ (symmetric-Groupᵉ Xᵉ))
  is-section-hom-inv-symmetric-group-loop-group-Setᵉ =
    eq-pair-Σᵉ
      ( eq-htpyᵉ
        ( λ fᵉ →
          ( apᵉ equiv-eqᵉ (inv-invᵉ (eq-equivᵉ fᵉ))) ∙ᵉ
            ( apᵉ
              ( λ eᵉ → map-equivᵉ eᵉ fᵉ)
              ( right-inverse-law-equivᵉ equiv-univalenceᵉ))))
      ( eq-is-propᵉ
        ( is-prop-preserves-mul-Semigroupᵉ
          ( semigroup-Groupᵉ (symmetric-Groupᵉ Xᵉ))
          ( semigroup-Groupᵉ (symmetric-Groupᵉ Xᵉ))
          ( idᵉ)))

  is-retraction-hom-inv-symmetric-group-loop-group-Setᵉ :
    Idᵉ
      ( comp-hom-Groupᵉ
        ( loop-group-Setᵉ Xᵉ)
        ( symmetric-Groupᵉ Xᵉ)
        ( loop-group-Setᵉ Xᵉ)
        ( hom-inv-symmetric-group-loop-group-Setᵉ)
        ( hom-symmetric-group-loop-group-Setᵉ))
      ( id-hom-Groupᵉ (loop-group-Setᵉ Xᵉ))
  is-retraction-hom-inv-symmetric-group-loop-group-Setᵉ =
    eq-pair-Σᵉ
      ( eq-htpyᵉ
        ( λ pᵉ →
          ( apᵉ
            ( invᵉ)
            ( apᵉ
              ( λ eᵉ → map-equivᵉ eᵉ (invᵉ pᵉ))
              ( left-inverse-law-equivᵉ equiv-univalenceᵉ))) ∙ᵉ
            ( inv-invᵉ pᵉ)))
      ( eq-is-propᵉ
        ( is-prop-preserves-mul-Semigroupᵉ
          ( semigroup-Groupᵉ (loop-group-Setᵉ Xᵉ))
          ( semigroup-Groupᵉ (loop-group-Setᵉ Xᵉ))
          ( idᵉ)))

  iso-symmetric-group-loop-group-Setᵉ :
    iso-Groupᵉ (loop-group-Setᵉ Xᵉ) (symmetric-Groupᵉ Xᵉ)
  pr1ᵉ iso-symmetric-group-loop-group-Setᵉ = hom-symmetric-group-loop-group-Setᵉ
  pr1ᵉ (pr2ᵉ iso-symmetric-group-loop-group-Setᵉ) =
    hom-inv-symmetric-group-loop-group-Setᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ iso-symmetric-group-loop-group-Setᵉ)) =
    is-section-hom-inv-symmetric-group-loop-group-Setᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ iso-symmetric-group-loop-group-Setᵉ)) =
    is-retraction-hom-inv-symmetric-group-loop-group-Setᵉ
```

### The abstacted automorphism group and the loop group of a set are isomorphic

```agda
module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ)
  where

  hom-abstract-automorphism-group-loop-group-Setᵉ :
    hom-Groupᵉ
      ( loop-group-Setᵉ Xᵉ)
      ( group-Concrete-Groupᵉ
        ( Automorphism-Groupᵉ (Set-1-Typeᵉ lᵉ) Xᵉ))
  pr1ᵉ hom-abstract-automorphism-group-loop-group-Setᵉ pᵉ =
    eq-pair-Σᵉ
      ( eq-pair-Σᵉ
        ( pᵉ)
        ( eq-is-propᵉ (is-prop-is-setᵉ (type-Setᵉ Xᵉ))))
      ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)
  pr2ᵉ hom-abstract-automorphism-group-loop-group-Setᵉ {pᵉ} {qᵉ} =
    ( apᵉ
      ( λ rᵉ → eq-pair-Σᵉ rᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ))
      ( ( apᵉ
          ( λ wᵉ → eq-pair-Σᵉ (pᵉ ∙ᵉ qᵉ) wᵉ)
          ( eq-is-propᵉ (is-trunc-Idᵉ (is-prop-is-setᵉ (type-Setᵉ Xᵉ) _ _)))) ∙ᵉ
        ( interchange-concat-eq-pair-Σᵉ
          ( pᵉ)
          ( qᵉ)
          ( eq-is-propᵉ (is-prop-is-setᵉ (type-Setᵉ Xᵉ)))
          ( eq-is-propᵉ (is-prop-is-setᵉ (type-Setᵉ Xᵉ)))))) ∙ᵉ
    ( apᵉ
      ( λ wᵉ →
        eq-pair-Σᵉ
          ( ( eq-pair-Σᵉ pᵉ (eq-is-propᵉ (is-prop-is-setᵉ (pr1ᵉ Xᵉ)))) ∙ᵉ
            ( eq-pair-Σᵉ qᵉ (eq-is-propᵉ (is-prop-is-setᵉ (pr1ᵉ Xᵉ)))))
          ( wᵉ))
      ( eq-is-propᵉ (is-trunc-Idᵉ (is-prop-type-trunc-Propᵉ _ _)))) ∙ᵉ
    ( interchange-concat-eq-pair-Σᵉ
      ( eq-pair-Σᵉ pᵉ (eq-is-propᵉ (is-prop-is-setᵉ (type-Setᵉ Xᵉ))))
      ( eq-pair-Σᵉ qᵉ (eq-is-propᵉ (is-prop-is-setᵉ (type-Setᵉ Xᵉ))))
      ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)
      ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))

  hom-inv-abstract-automorphism-group-loop-group-Setᵉ :
    hom-Groupᵉ
      ( group-Concrete-Groupᵉ
        ( Automorphism-Groupᵉ (Set-1-Typeᵉ lᵉ) Xᵉ))
      ( loop-group-Setᵉ Xᵉ)
  pr1ᵉ hom-inv-abstract-automorphism-group-loop-group-Setᵉ pᵉ =
    pr1ᵉ (pair-eq-Σᵉ (pr1ᵉ (pair-eq-Σᵉ pᵉ)))
  pr2ᵉ hom-inv-abstract-automorphism-group-loop-group-Setᵉ {pᵉ} {qᵉ} =
    ( apᵉ
      ( λ rᵉ → pr1ᵉ (pair-eq-Σᵉ rᵉ))
      ( pr1-interchange-concat-pair-eq-Σᵉ pᵉ qᵉ)) ∙ᵉ
    ( pr1-interchange-concat-pair-eq-Σᵉ (pr1ᵉ (pair-eq-Σᵉ pᵉ)) (pr1ᵉ (pair-eq-Σᵉ qᵉ)))

  is-section-hom-inv-abstract-automorphism-group-loop-group-Setᵉ :
    Idᵉ
      ( comp-hom-Groupᵉ
        ( group-Concrete-Groupᵉ
          ( Automorphism-Groupᵉ (Set-1-Typeᵉ lᵉ) Xᵉ))
        ( loop-group-Setᵉ Xᵉ)
        ( group-Concrete-Groupᵉ
          ( Automorphism-Groupᵉ (Set-1-Typeᵉ lᵉ) Xᵉ))
        ( hom-abstract-automorphism-group-loop-group-Setᵉ)
        ( hom-inv-abstract-automorphism-group-loop-group-Setᵉ))
      ( id-hom-Groupᵉ
        ( group-Concrete-Groupᵉ
          ( Automorphism-Groupᵉ (Set-1-Typeᵉ lᵉ) Xᵉ)))
  is-section-hom-inv-abstract-automorphism-group-loop-group-Setᵉ =
    eq-pair-Σᵉ
      ( eq-htpyᵉ
        ( λ pᵉ →
          ( apᵉ
            ( λ rᵉ → eq-pair-Σᵉ rᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ))
            ( ( apᵉ
                ( eq-pair-Σᵉ (pr1ᵉ (pair-eq-Σᵉ (pr1ᵉ (pair-eq-Σᵉ pᵉ)))))
                ( eq-is-propᵉ (is-trunc-Idᵉ (is-prop-is-setᵉ (type-Setᵉ Xᵉ) _ _)))) ∙ᵉ
              ( is-section-pair-eq-Σᵉ Xᵉ Xᵉ (pr1ᵉ (pair-eq-Σᵉ pᵉ))))) ∙ᵉ
          ( apᵉ
            ( eq-pair-Σᵉ (pr1ᵉ (pair-eq-Σᵉ pᵉ)))
            ( eq-is-propᵉ (is-trunc-Idᵉ (is-prop-type-trunc-Propᵉ _ _)))) ∙ᵉ
          ( is-section-pair-eq-Σᵉ
            ( Xᵉ ,ᵉ unit-trunc-Propᵉ reflᵉ)
            ( Xᵉ ,ᵉ unit-trunc-Propᵉ reflᵉ)
            ( pᵉ))))
      ( eq-is-propᵉ
        ( is-prop-preserves-mul-Semigroupᵉ
          ( semigroup-Groupᵉ
            ( group-Concrete-Groupᵉ
              ( Automorphism-Groupᵉ (Set-1-Typeᵉ lᵉ) Xᵉ)))
          ( semigroup-Groupᵉ
            ( group-Concrete-Groupᵉ
              ( Automorphism-Groupᵉ (Set-1-Typeᵉ lᵉ) Xᵉ)))
          ( idᵉ)))

  is-retraction-hom-inv-abstract-automorphism-group-loop-group-Setᵉ :
    comp-hom-Groupᵉ
      ( loop-group-Setᵉ Xᵉ)
      ( group-Concrete-Groupᵉ
        ( Automorphism-Groupᵉ (Set-1-Typeᵉ lᵉ) Xᵉ))
      ( loop-group-Setᵉ Xᵉ)
      ( hom-inv-abstract-automorphism-group-loop-group-Setᵉ)
      ( hom-abstract-automorphism-group-loop-group-Setᵉ) ＝ᵉ
    id-hom-Groupᵉ (loop-group-Setᵉ Xᵉ)
  is-retraction-hom-inv-abstract-automorphism-group-loop-group-Setᵉ =
    eq-pair-Σᵉ
      ( eq-htpyᵉ
        ( λ pᵉ →
          ( apᵉ
            ( λ wᵉ → pr1ᵉ (pair-eq-Σᵉ (pr1ᵉ wᵉ)))
            ( is-retraction-pair-eq-Σᵉ
              ( Xᵉ ,ᵉ unit-trunc-Propᵉ reflᵉ)
              ( Xᵉ ,ᵉ unit-trunc-Propᵉ reflᵉ)
              ( pairᵉ
                ( eq-pair-Σᵉ
                  ( pᵉ)
                  ( eq-is-propᵉ (is-prop-is-setᵉ (type-Setᵉ Xᵉ))))
                ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)))) ∙ᵉ
            ( apᵉ pr1ᵉ
              ( is-retraction-pair-eq-Σᵉ Xᵉ Xᵉ
                ( pᵉ ,ᵉ eq-is-propᵉ (is-prop-is-setᵉ (type-Setᵉ Xᵉ)))))))
      ( eq-is-propᵉ
        ( is-prop-preserves-mul-Semigroupᵉ
          ( semigroup-Groupᵉ (loop-group-Setᵉ Xᵉ))
          ( semigroup-Groupᵉ (loop-group-Setᵉ Xᵉ))
          ( idᵉ)))

  iso-abstract-automorphism-group-loop-group-Setᵉ :
    iso-Groupᵉ
      ( loop-group-Setᵉ Xᵉ)
      ( group-Concrete-Groupᵉ
        ( Automorphism-Groupᵉ (Set-1-Typeᵉ lᵉ) Xᵉ))
  pr1ᵉ iso-abstract-automorphism-group-loop-group-Setᵉ =
    hom-abstract-automorphism-group-loop-group-Setᵉ
  pr1ᵉ (pr2ᵉ iso-abstract-automorphism-group-loop-group-Setᵉ) =
    hom-inv-abstract-automorphism-group-loop-group-Setᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ iso-abstract-automorphism-group-loop-group-Setᵉ)) =
    is-section-hom-inv-abstract-automorphism-group-loop-group-Setᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ iso-abstract-automorphism-group-loop-group-Setᵉ)) =
    is-retraction-hom-inv-abstract-automorphism-group-loop-group-Setᵉ
```

### The loop groups of two equivalent sets are isomorphic

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Setᵉ l1ᵉ) (Yᵉ : Setᵉ l2ᵉ) (eᵉ : type-Setᵉ Xᵉ ≃ᵉ type-Setᵉ Yᵉ)
  where

  iso-loop-group-equiv-Setᵉ :
    iso-Groupᵉ
      ( loop-group-Setᵉ Xᵉ)
      ( loop-group-Setᵉ Yᵉ)
  iso-loop-group-equiv-Setᵉ =
    comp-iso-Groupᵉ
      ( loop-group-Setᵉ Xᵉ)
      ( symmetric-Groupᵉ Xᵉ)
      ( loop-group-Setᵉ Yᵉ)
      ( comp-iso-Groupᵉ
        ( symmetric-Groupᵉ Xᵉ)
        ( symmetric-Groupᵉ Yᵉ)
        ( loop-group-Setᵉ Yᵉ)
        ( inv-iso-Groupᵉ
          ( loop-group-Setᵉ Yᵉ)
          ( symmetric-Groupᵉ Yᵉ)
          ( iso-symmetric-group-loop-group-Setᵉ Yᵉ))
        ( iso-symmetric-group-equiv-Setᵉ Xᵉ Yᵉ eᵉ))
      ( iso-symmetric-group-loop-group-Setᵉ Xᵉ)
```