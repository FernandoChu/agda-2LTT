# The group of n-element types

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module finite-group-theory.finite-type-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.truncated-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.homomorphisms-semigroupsᵉ
open import group-theory.isomorphisms-groupsᵉ
open import group-theory.loop-groups-setsᵉ

open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

### Definition

```agda
UU-Fin-Groupᵉ : (lᵉ : Level) (nᵉ : ℕᵉ) → Concrete-Groupᵉ (lsuc lᵉ)
pr1ᵉ (pr1ᵉ (pr1ᵉ (UU-Fin-Groupᵉ lᵉ nᵉ))) = UU-Finᵉ lᵉ nᵉ
pr2ᵉ (pr1ᵉ (pr1ᵉ (UU-Fin-Groupᵉ lᵉ nᵉ))) = Fin-UU-Finᵉ lᵉ nᵉ
pr2ᵉ (pr1ᵉ (UU-Fin-Groupᵉ lᵉ nᵉ)) = is-0-connected-UU-Finᵉ nᵉ
pr2ᵉ (UU-Fin-Groupᵉ lᵉ nᵉ) =
  is-1-type-UU-Finᵉ nᵉ (Fin-UU-Finᵉ lᵉ nᵉ) (Fin-UU-Finᵉ lᵉ nᵉ)
```

### Properties

```agda
module _
  (lᵉ : Level) (nᵉ : ℕᵉ)
  where

  hom-loop-group-fin-UU-Fin-Groupᵉ :
    hom-Groupᵉ
      ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ lᵉ nᵉ))
      ( loop-group-Setᵉ (raise-Setᵉ lᵉ (Fin-Setᵉ nᵉ)))
  pr1ᵉ hom-loop-group-fin-UU-Fin-Groupᵉ pᵉ = pr1ᵉ (pair-eq-Σᵉ pᵉ)
  pr2ᵉ hom-loop-group-fin-UU-Fin-Groupᵉ {pᵉ} {qᵉ} =
    pr1-interchange-concat-pair-eq-Σᵉ pᵉ qᵉ

  hom-inv-loop-group-fin-UU-Fin-Groupᵉ :
    hom-Groupᵉ
      ( loop-group-Setᵉ (raise-Setᵉ lᵉ (Fin-Setᵉ nᵉ)))
      ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ lᵉ nᵉ))
  pr1ᵉ hom-inv-loop-group-fin-UU-Fin-Groupᵉ pᵉ =
    eq-pair-Σᵉ pᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ)
  pr2ᵉ hom-inv-loop-group-fin-UU-Fin-Groupᵉ {pᵉ} {qᵉ} =
    ( apᵉ
      ( λ rᵉ → eq-pair-Σᵉ (pᵉ ∙ᵉ qᵉ) rᵉ)
      ( eq-is-propᵉ (is-trunc-Idᵉ (is-prop-type-trunc-Propᵉ _ _)))) ∙ᵉ
      ( interchange-concat-eq-pair-Σᵉ
        ( pᵉ)
        ( qᵉ)
        ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)
        ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))

  is-section-hom-inv-loop-group-fin-UU-Fin-Groupᵉ :
    Idᵉ
      ( comp-hom-Groupᵉ
        ( loop-group-Setᵉ (raise-Setᵉ lᵉ (Fin-Setᵉ nᵉ)))
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ lᵉ nᵉ))
        ( loop-group-Setᵉ (raise-Setᵉ lᵉ (Fin-Setᵉ nᵉ)))
        ( hom-loop-group-fin-UU-Fin-Groupᵉ)
        ( hom-inv-loop-group-fin-UU-Fin-Groupᵉ))
      ( id-hom-Groupᵉ (loop-group-Setᵉ (raise-Setᵉ lᵉ (Fin-Setᵉ nᵉ))))
  is-section-hom-inv-loop-group-fin-UU-Fin-Groupᵉ =
    eq-pair-Σᵉ
      ( eq-htpyᵉ
        ( λ pᵉ →
          apᵉ pr1ᵉ
            ( is-retraction-pair-eq-Σᵉ
              ( Fin-UU-Finᵉ lᵉ nᵉ)
              ( Fin-UU-Finᵉ lᵉ nᵉ)
              ( pairᵉ pᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ)))))
      ( eq-is-propᵉ
        ( is-prop-preserves-mul-Semigroupᵉ
          ( semigroup-Groupᵉ (loop-group-Setᵉ (raise-Setᵉ lᵉ (Fin-Setᵉ nᵉ))))
          ( semigroup-Groupᵉ (loop-group-Setᵉ (raise-Setᵉ lᵉ (Fin-Setᵉ nᵉ))))
          ( idᵉ)))

  is-retraction-hom-inv-loop-group-fin-UU-Fin-Groupᵉ :
    Idᵉ
      ( comp-hom-Groupᵉ
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ lᵉ nᵉ))
        ( loop-group-Setᵉ (raise-Setᵉ lᵉ (Fin-Setᵉ nᵉ)))
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ lᵉ nᵉ))
        ( hom-inv-loop-group-fin-UU-Fin-Groupᵉ)
        ( hom-loop-group-fin-UU-Fin-Groupᵉ))
      ( id-hom-Groupᵉ (group-Concrete-Groupᵉ (UU-Fin-Groupᵉ lᵉ nᵉ)))
  is-retraction-hom-inv-loop-group-fin-UU-Fin-Groupᵉ =
    eq-pair-Σᵉ
      ( eq-htpyᵉ
        ( λ pᵉ →
          ( apᵉ
            ( λ rᵉ → eq-pair-Σᵉ (pr1ᵉ (pair-eq-Σᵉ pᵉ)) rᵉ)
            ( eq-is-propᵉ (is-trunc-Idᵉ (is-prop-type-trunc-Propᵉ _ _)))) ∙ᵉ
            ( is-section-pair-eq-Σᵉ (Fin-UU-Finᵉ lᵉ nᵉ) (Fin-UU-Finᵉ lᵉ nᵉ) pᵉ)))
      ( eq-is-propᵉ
        ( is-prop-preserves-mul-Semigroupᵉ
          ( semigroup-Groupᵉ (group-Concrete-Groupᵉ (UU-Fin-Groupᵉ lᵉ nᵉ)))
          ( semigroup-Groupᵉ (group-Concrete-Groupᵉ (UU-Fin-Groupᵉ lᵉ nᵉ)))
          ( idᵉ)))

  iso-loop-group-fin-UU-Fin-Groupᵉ :
    iso-Groupᵉ
      ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ lᵉ nᵉ))
      ( loop-group-Setᵉ (raise-Setᵉ lᵉ (Fin-Setᵉ nᵉ)))
  pr1ᵉ iso-loop-group-fin-UU-Fin-Groupᵉ =
    hom-loop-group-fin-UU-Fin-Groupᵉ
  pr1ᵉ (pr2ᵉ iso-loop-group-fin-UU-Fin-Groupᵉ) =
    hom-inv-loop-group-fin-UU-Fin-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ iso-loop-group-fin-UU-Fin-Groupᵉ)) =
    is-section-hom-inv-loop-group-fin-UU-Fin-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ iso-loop-group-fin-UU-Fin-Groupᵉ)) =
    is-retraction-hom-inv-loop-group-fin-UU-Fin-Groupᵉ
```