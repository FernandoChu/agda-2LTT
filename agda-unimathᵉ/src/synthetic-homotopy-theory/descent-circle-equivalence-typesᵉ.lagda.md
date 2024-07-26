# Descent data for families of equivalence types over the circle

```agda
module synthetic-homotopy-theory.descent-circle-equivalence-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.dependent-descent-circleᵉ
open import synthetic-homotopy-theory.descent-circleᵉ
open import synthetic-homotopy-theory.descent-circle-dependent-pair-typesᵉ
open import synthetic-homotopy-theory.descent-circle-function-typesᵉ
open import synthetic-homotopy-theory.descent-circle-subtypesᵉ
open import synthetic-homotopy-theory.free-loopsᵉ
open import synthetic-homotopy-theory.morphisms-descent-data-circleᵉ
open import synthetic-homotopy-theory.sections-descent-circleᵉ
open import synthetic-homotopy-theory.universal-property-circleᵉ
```

</details>

## Idea

Givenᵉ twoᵉ familiesᵉ `A,ᵉ Bᵉ : 𝕊¹ᵉ → U`ᵉ overᵉ theᵉ
[circle](synthetic-homotopy-theory.circle.md),ᵉ to showᵉ thatᵉ theyᵉ areᵉ
[equivalent](foundation.equivalences.mdᵉ) isᵉ theᵉ sameᵉ asᵉ showingᵉ thatᵉ theirᵉ
[descentᵉ data](synthetic-homotopy-theory.descent-circle.mdᵉ) isᵉ equivalent.ᵉ

## Definitions

### Dependent descent data for being an equivalence of families over the circle

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  ( Bᵉ : family-with-descent-data-circleᵉ lᵉ l3ᵉ)
  where

  family-dependent-descent-data-circle-is-equivᵉ :
    ( tᵉ : Sᵉ) → family-descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ tᵉ →
    UUᵉ (l2ᵉ ⊔ l3ᵉ)
  family-dependent-descent-data-circle-is-equivᵉ tᵉ = is-equivᵉ

  dependent-descent-data-circle-is-equivᵉ :
    dependent-descent-data-circleᵉ
      ( l2ᵉ ⊔ l3ᵉ)
      ( descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ)
  pr1ᵉ dependent-descent-data-circle-is-equivᵉ = is-equivᵉ
  pr2ᵉ dependent-descent-data-circle-is-equivᵉ fᵉ =
    equiv-is-equiv-left-factorᵉ
      ( aut-family-with-descent-data-circleᵉ Bᵉ) ∘eᵉ
    ( equiv-is-equiv-right-factorᵉ
      ( inv-equivᵉ (aut-family-with-descent-data-circleᵉ Aᵉ)))
```

## Properties

### Characterization of dependent descent data for being an equivalence of families over the circle

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  ( Bᵉ : family-with-descent-data-circleᵉ lᵉ l3ᵉ)
  where

  eq-dependent-descent-data-circle-is-equivᵉ :
    equiv-dependent-descent-data-circleᵉ
      ( descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ)
      ( dependent-descent-data-circle-is-equivᵉ lᵉ Aᵉ Bᵉ)
      ( dependent-descent-data-double-family-circleᵉ lᵉ
        ( family-with-descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ)
        ( family-dependent-descent-data-circle-is-equivᵉ lᵉ Aᵉ Bᵉ))
  pr1ᵉ eq-dependent-descent-data-circle-is-equivᵉ fᵉ =
    equiv-is-equiv-left-factorᵉ
      ( equiv-family-with-descent-data-circleᵉ Bᵉ) ∘eᵉ
    ( equiv-is-equiv-right-factorᵉ
      ( inv-equivᵉ (equiv-family-with-descent-data-circleᵉ Aᵉ)))
  pr2ᵉ eq-dependent-descent-data-circle-is-equivᵉ fᵉ pᵉ =
    centerᵉ (is-property-is-equivᵉ _ _ _)

  family-with-dependent-descent-data-circle-is-equivᵉ :
    double-family-with-dependent-descent-data-circleᵉ lᵉ
      ( family-with-descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ)
      ( l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ family-with-dependent-descent-data-circle-is-equivᵉ =
    family-dependent-descent-data-circle-is-equivᵉ lᵉ Aᵉ Bᵉ
  pr1ᵉ (pr2ᵉ family-with-dependent-descent-data-circle-is-equivᵉ) =
    dependent-descent-data-circle-is-equivᵉ lᵉ Aᵉ Bᵉ
  pr2ᵉ (pr2ᵉ family-with-dependent-descent-data-circle-is-equivᵉ) =
    eq-dependent-descent-data-circle-is-equivᵉ
```

### Characterization of descent data for families of equivalence types over the circle

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  ( Bᵉ : family-with-descent-data-circleᵉ lᵉ l3ᵉ)
  where

  family-with-descent-data-circle-equivalence-typeᵉ :
    family-with-descent-data-circleᵉ lᵉ (l2ᵉ ⊔ l3ᵉ)
  family-with-descent-data-circle-equivalence-typeᵉ =
    family-with-descent-data-circle-dependent-pair-typeᵉ lᵉ
      ( family-with-descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ)
      ( family-with-dependent-descent-data-circle-is-equivᵉ lᵉ Aᵉ Bᵉ)
```

### A family of equivalences between families over the circle is given by an equivalence of the corresponding descent data

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  ( Bᵉ : family-with-descent-data-circleᵉ lᵉ l3ᵉ)
  where

  equiv-section-descent-data-circle-equiv-equiv-descent-data-circleᵉ :
    dependent-universal-property-circleᵉ lᵉ →
    ( ( tᵉ : Sᵉ) →
      ( family-family-with-descent-data-circleᵉ Aᵉ tᵉ) ≃ᵉ
      ( family-family-with-descent-data-circleᵉ Bᵉ tᵉ)) ≃ᵉ
    ( equiv-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
      ( descent-data-family-with-descent-data-circleᵉ Bᵉ))
  equiv-section-descent-data-circle-equiv-equiv-descent-data-circleᵉ dup-circleᵉ =
    equivalence-reasoningᵉ
    ( ( tᵉ : Sᵉ) →
        family-family-with-descent-data-circleᵉ Aᵉ tᵉ ≃ᵉ
        family-family-with-descent-data-circleᵉ Bᵉ tᵉ)
    ≃ᵉ Σᵉ ( fixpoint-descent-data-circleᵉ
          ( descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ))
        ( λ xᵉ → is-equivᵉ (pr1ᵉ xᵉ))
      byᵉ
      equiv-section-descent-data-circle-subtype-fixpoint-in-subtypeᵉ lᵉ
        ( family-with-descent-data-circle-function-typeᵉ lᵉ Aᵉ Bᵉ)
        ( family-with-dependent-descent-data-circle-is-equivᵉ lᵉ Aᵉ Bᵉ)
        ( λ tᵉ fᵉ → is-property-is-equivᵉ fᵉ)
        ( dup-circleᵉ)
    ≃ᵉ Σᵉ ( hom-descent-data-circleᵉ
          ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
          ( descent-data-family-with-descent-data-circleᵉ Bᵉ))
        ( λ hᵉ →
          is-equivᵉ
            ( map-hom-descent-data-circleᵉ
              ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
              ( descent-data-family-with-descent-data-circleᵉ Bᵉ)
              ( hᵉ)))
      byᵉ
      equiv-Σ-equiv-baseᵉ
        ( λ hᵉ →
          is-equivᵉ
            ( map-hom-descent-data-circleᵉ
              ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
              ( descent-data-family-with-descent-data-circleᵉ Bᵉ)
              ( hᵉ)))
        ( equiv-fixpoint-descent-data-circle-function-type-homᵉ lᵉ Aᵉ Bᵉ)
    ≃ᵉ equiv-descent-data-circleᵉ
        ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
        ( descent-data-family-with-descent-data-circleᵉ Bᵉ)
      byᵉ
      compute-equiv-descent-data-circleᵉ
        ( descent-data-family-with-descent-data-circleᵉ Aᵉ)
        ( descent-data-family-with-descent-data-circleᵉ Bᵉ)
```