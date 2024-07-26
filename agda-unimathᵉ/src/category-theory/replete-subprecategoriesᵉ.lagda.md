# Replete subprecategories

```agda
module category-theory.replete-subprecategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.isomorphism-induction-categoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.isomorphisms-in-subprecategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.subprecategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.subsingleton-inductionᵉ
open import foundation.subtypesᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **repleteᵉ subprecategory**ᵉ ofᵉ aᵉ [precategory](category-theory.categories.mdᵉ)
`C`ᵉ isᵉ aᵉ [subprecategory](category-theory.subprecategories.mdᵉ) `P`ᵉ thatᵉ isᵉ
closedᵉ underᵉ [isomorphisms](category-theory.isomorphisms-in-precategories.mdᵉ):

Givenᵉ anᵉ objectᵉ `x`ᵉ in `P`,ᵉ thenᵉ everyᵉ isomorphismᵉ `fᵉ : xᵉ ≅ᵉ y`ᵉ in `C`,ᵉ isᵉ
containedᵉ in `P`.ᵉ

## Definitions

### The predicate on a subprecategory of being closed under isomorphic objects

Weᵉ canᵉ defineᵉ whatᵉ itᵉ meansᵉ forᵉ subprecategoriesᵉ to haveᵉ objectsᵉ thatᵉ areᵉ closedᵉ
underᵉ isomorphisms.ᵉ Observeᵉ thatᵉ thisᵉ isᵉ notᵉ yetᵉ theᵉ correctᵉ definitionᵉ ofᵉ aᵉ
repleteᵉ subprecategory.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  contains-iso-obj-Subprecategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  contains-iso-obj-Subprecategoryᵉ =
    (xᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ) (yᵉ : obj-Precategoryᵉ Cᵉ) →
    iso-Precategoryᵉ Cᵉ (inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ) yᵉ →
    is-in-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ

  is-prop-contains-iso-obj-Subprecategoryᵉ :
    is-propᵉ contains-iso-obj-Subprecategoryᵉ
  is-prop-contains-iso-obj-Subprecategoryᵉ =
    is-prop-iterated-Πᵉ 3 (λ xᵉ yᵉ fᵉ → is-prop-is-in-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)

  contains-iso-obj-prop-Subprecategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ contains-iso-obj-prop-Subprecategoryᵉ = contains-iso-obj-Subprecategoryᵉ
  pr2ᵉ contains-iso-obj-prop-Subprecategoryᵉ =
    is-prop-contains-iso-obj-Subprecategoryᵉ
```

### The predicate of being a replete subprecategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  is-replete-Subprecategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-replete-Subprecategoryᵉ =
    (xᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ)
    (yᵉ : obj-Precategoryᵉ Cᵉ)
    (fᵉ : iso-Precategoryᵉ Cᵉ (inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ) yᵉ) →
    Σᵉ ( is-in-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
      ( λ y₀ᵉ → is-in-iso-obj-subprecategory-Subprecategoryᵉ Cᵉ Pᵉ {xᵉ} {yᵉ ,ᵉ y₀ᵉ} fᵉ)

  is-prop-is-replete-Subprecategoryᵉ :
    is-propᵉ is-replete-Subprecategoryᵉ
  is-prop-is-replete-Subprecategoryᵉ =
    is-prop-iterated-Πᵉ 3
      ( λ xᵉ yᵉ fᵉ →
        is-prop-Σᵉ
          ( is-prop-is-in-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
          ( λ _ → is-prop-is-in-iso-obj-subprecategory-Subprecategoryᵉ Cᵉ Pᵉ fᵉ))

  is-replete-prop-Subprecategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-replete-prop-Subprecategoryᵉ = is-replete-Subprecategoryᵉ
  pr2ᵉ is-replete-prop-Subprecategoryᵉ =
    is-prop-is-replete-Subprecategoryᵉ
```

### The type of replete subprecategories

```agda
Replete-Subprecategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ l4ᵉ : Level) (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ)
Replete-Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ =
  Σᵉ (Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ) (is-replete-Subprecategoryᵉ Cᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Replete-Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  subprecategory-Replete-Subprecategoryᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ
  subprecategory-Replete-Subprecategoryᵉ = pr1ᵉ Pᵉ

  is-replete-Replete-Subprecategoryᵉ :
    is-replete-Subprecategoryᵉ Cᵉ subprecategory-Replete-Subprecategoryᵉ
  is-replete-Replete-Subprecategoryᵉ = pr2ᵉ Pᵉ
```

## Properties

### A slight reformulation of repleteness

Inᵉ ourᵉ mainᵉ definitionᵉ ofᵉ repleteness,ᵉ theᵉ containmentᵉ proofᵉ ofᵉ theᵉ isomorphismᵉ
mustᵉ beᵉ fixedᵉ atᵉ theᵉ leftᵉ end-point.ᵉ Thisᵉ isᵉ ofᵉ courseᵉ notᵉ necessary,ᵉ soᵉ weᵉ canᵉ
askᵉ forᵉ aᵉ slightyᵉ relaxedᵉ proofᵉ ofᵉ repletenessᵉ:

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  is-unfixed-replete-Subprecategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-unfixed-replete-Subprecategoryᵉ =
    (xᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ)
    (yᵉ : obj-Precategoryᵉ Cᵉ)
    (fᵉ : iso-Precategoryᵉ Cᵉ (inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ) yᵉ) →
    is-in-iso-Subprecategoryᵉ Cᵉ Pᵉ fᵉ

  is-prop-is-unfixed-replete-Subprecategoryᵉ :
    is-propᵉ (is-unfixed-replete-Subprecategoryᵉ)
  is-prop-is-unfixed-replete-Subprecategoryᵉ =
    is-prop-iterated-Πᵉ 3
      ( λ xᵉ yᵉ fᵉ → is-prop-is-in-iso-Subprecategoryᵉ Cᵉ Pᵉ fᵉ)

  is-unfixed-replete-prop-Subprecategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-unfixed-replete-prop-Subprecategoryᵉ =
    is-unfixed-replete-Subprecategoryᵉ
  pr2ᵉ is-unfixed-replete-prop-Subprecategoryᵉ =
    is-prop-is-unfixed-replete-Subprecategoryᵉ

  is-unfixed-replete-is-replete-Subprecategoryᵉ :
    is-replete-Subprecategoryᵉ Cᵉ Pᵉ → is-unfixed-replete-Subprecategoryᵉ
  pr1ᵉ (is-unfixed-replete-is-replete-Subprecategoryᵉ replete'ᵉ (xᵉ ,ᵉ x₀ᵉ) yᵉ fᵉ) = x₀ᵉ
  pr2ᵉ (is-unfixed-replete-is-replete-Subprecategoryᵉ replete'ᵉ xᵉ yᵉ fᵉ) =
    replete'ᵉ xᵉ yᵉ fᵉ

  is-replete-is-unfixed-replete-Subprecategoryᵉ :
    is-unfixed-replete-Subprecategoryᵉ → is-replete-Subprecategoryᵉ Cᵉ Pᵉ
  is-replete-is-unfixed-replete-Subprecategoryᵉ is-unfixed-replete-Pᵉ xᵉ yᵉ fᵉ =
    ind-subsingletonᵉ
      ( is-prop-is-in-obj-Subprecategoryᵉ Cᵉ Pᵉ (pr1ᵉ xᵉ))
      { λ x₀ᵉ →
        Σᵉ ( is-in-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
          ( λ y₀ᵉ →
            is-in-iso-obj-subprecategory-Subprecategoryᵉ Cᵉ Pᵉ
              { inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ ,ᵉ x₀ᵉ} {yᵉ ,ᵉ y₀ᵉ} fᵉ)}
      ( pr1ᵉ (is-unfixed-replete-Pᵉ xᵉ yᵉ fᵉ))
      ( pr2ᵉ (is-unfixed-replete-Pᵉ xᵉ yᵉ fᵉ))
      ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
```

### Isomorphism-sets in replete subprecategories are equivalent to isomorphism-sets in the base precategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  (is-replete-Pᵉ : is-replete-Subprecategoryᵉ Cᵉ Pᵉ)
  {xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ} (fᵉ : hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ)
  where

  is-iso-is-iso-base-is-replete-Subprecategoryᵉ :
    is-iso-Precategoryᵉ Cᵉ (inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ) →
    is-iso-Subprecategoryᵉ Cᵉ Pᵉ fᵉ
  pr1ᵉ (pr1ᵉ (is-iso-is-iso-base-is-replete-Subprecategoryᵉ is-iso-C-fᵉ)) =
    hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-C-fᵉ
  pr2ᵉ (pr1ᵉ (is-iso-is-iso-base-is-replete-Subprecategoryᵉ is-iso-C-fᵉ)) =
    ind-subsingletonᵉ
      ( is-prop-is-in-obj-Subprecategoryᵉ Cᵉ Pᵉ (pr1ᵉ yᵉ))
      { λ y₀ᵉ →
        is-in-hom-obj-subprecategory-Subprecategoryᵉ Cᵉ Pᵉ (pr1ᵉ yᵉ ,ᵉ y₀ᵉ) xᵉ
          ( hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-C-fᵉ)}
      ( pr1ᵉ (is-replete-Pᵉ xᵉ (pr1ᵉ yᵉ) (pr1ᵉ fᵉ ,ᵉ is-iso-C-fᵉ)))
      ( pr2ᵉ (pr2ᵉ (is-replete-Pᵉ xᵉ (pr1ᵉ yᵉ) (pr1ᵉ fᵉ ,ᵉ is-iso-C-fᵉ))))
      ( pr2ᵉ yᵉ)
  pr1ᵉ (pr2ᵉ (is-iso-is-iso-base-is-replete-Subprecategoryᵉ is-iso-C-fᵉ)) =
    eq-type-subtypeᵉ
      ( subtype-hom-obj-subprecategory-Subprecategoryᵉ Cᵉ Pᵉ yᵉ yᵉ)
      ( is-section-hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-C-fᵉ)
  pr2ᵉ (pr2ᵉ (is-iso-is-iso-base-is-replete-Subprecategoryᵉ is-iso-C-fᵉ)) =
    eq-type-subtypeᵉ
      ( subtype-hom-obj-subprecategory-Subprecategoryᵉ Cᵉ Pᵉ xᵉ xᵉ)
      ( is-retraction-hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-C-fᵉ)

  is-equiv-is-iso-is-iso-base-is-replete-Subprecategoryᵉ :
    is-equivᵉ is-iso-is-iso-base-is-replete-Subprecategoryᵉ
  is-equiv-is-iso-is-iso-base-is-replete-Subprecategoryᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-is-iso-Precategoryᵉ Cᵉ (inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ))
      ( is-prop-is-iso-Subprecategoryᵉ Cᵉ Pᵉ fᵉ)
      ( is-iso-base-is-iso-Subprecategoryᵉ Cᵉ Pᵉ)

  equiv-is-iso-is-iso-base-is-replete-Subprecategoryᵉ :
    is-iso-Precategoryᵉ Cᵉ (inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ) ≃ᵉ
    is-iso-Subprecategoryᵉ Cᵉ Pᵉ fᵉ
  pr1ᵉ equiv-is-iso-is-iso-base-is-replete-Subprecategoryᵉ =
    is-iso-is-iso-base-is-replete-Subprecategoryᵉ
  pr2ᵉ equiv-is-iso-is-iso-base-is-replete-Subprecategoryᵉ =
    is-equiv-is-iso-is-iso-base-is-replete-Subprecategoryᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  (is-replete-Pᵉ : is-replete-Subprecategoryᵉ Cᵉ Pᵉ)
  (xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ)
  where

  compute-iso-is-replete-Subprecategoryᵉ :
    iso-Precategoryᵉ Cᵉ
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ) ≃ᵉ
    iso-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ
  compute-iso-is-replete-Subprecategoryᵉ =
    ( equiv-totᵉ
      ( equiv-is-iso-is-iso-base-is-replete-Subprecategoryᵉ
          Cᵉ Pᵉ is-replete-Pᵉ {xᵉ} {yᵉ})) ∘eᵉ
    ( inv-associative-Σᵉ _ _ _) ∘eᵉ
    ( equiv-totᵉ
      ( λ fᵉ →
        ( commutative-productᵉ) ∘eᵉ
        ( inv-right-unit-law-Σ-is-contrᵉ
          ( λ is-iso-C-fᵉ → is-proof-irrelevant-is-propᵉ
            ( is-prop-is-in-hom-obj-subprecategory-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ)
            ( ind-subsingletonᵉ
              ( is-prop-is-in-obj-Subprecategoryᵉ Cᵉ Pᵉ (pr1ᵉ yᵉ))
              { λ y₀ᵉ →
                is-in-hom-obj-subprecategory-Subprecategoryᵉ
                  Cᵉ Pᵉ xᵉ (pr1ᵉ yᵉ ,ᵉ y₀ᵉ) fᵉ}
              ( is-replete-Pᵉ xᵉ (pr1ᵉ yᵉ) (fᵉ ,ᵉ is-iso-C-fᵉ) .pr1ᵉ)
              ( is-replete-Pᵉ xᵉ (pr1ᵉ yᵉ) (fᵉ ,ᵉ is-iso-C-fᵉ) .pr2ᵉ .pr1ᵉ)
              ( pr2ᵉ yᵉ))))))

  inv-compute-iso-is-replete-Subprecategoryᵉ :
    iso-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ ≃ᵉ
    iso-Precategoryᵉ Cᵉ
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
  inv-compute-iso-is-replete-Subprecategoryᵉ =
    inv-equivᵉ compute-iso-is-replete-Subprecategoryᵉ
```

### Subprecategories of categories are replete

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  (is-category-Cᵉ : is-category-Precategoryᵉ Cᵉ)
  where

  is-unfixed-replete-subprecategory-is-category-Subprecategoryᵉ :
    {xᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ}
    {yᵉ : obj-Precategoryᵉ Cᵉ}
    (fᵉ : iso-Precategoryᵉ Cᵉ (inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ) yᵉ) →
    is-in-iso-Subprecategoryᵉ Cᵉ Pᵉ fᵉ
  is-unfixed-replete-subprecategory-is-category-Subprecategoryᵉ {xᵉ} =
    ind-iso-Categoryᵉ
      ( Cᵉ ,ᵉ is-category-Cᵉ)
      ( λ Bᵉ → is-in-iso-Subprecategoryᵉ Cᵉ Pᵉ)
      ( is-in-iso-id-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)

  is-replete-subprecategory-is-category-Subprecategoryᵉ :
    is-replete-Subprecategoryᵉ Cᵉ Pᵉ
  is-replete-subprecategory-is-category-Subprecategoryᵉ xᵉ yᵉ =
    ind-iso-Categoryᵉ
      ( Cᵉ ,ᵉ is-category-Cᵉ)
      ( λ zᵉ eᵉ →
        Σᵉ ( is-in-obj-Subprecategoryᵉ Cᵉ Pᵉ zᵉ)
          ( λ z₀ᵉ →
            is-in-iso-obj-subprecategory-Subprecategoryᵉ Cᵉ Pᵉ {xᵉ} {zᵉ ,ᵉ z₀ᵉ} eᵉ))
      ( pr2ᵉ (is-in-iso-id-Subprecategoryᵉ Cᵉ Pᵉ xᵉ))
```

### If a full subprecategory is closed under isomorphic objects then it is replete

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

### The inclusion functor of a replete subprecategory is pseudomonic

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

## See also

-ᵉ Everyᵉ [subcategory](category-theory.subcategories.mdᵉ) isᵉ replete.ᵉ
-ᵉ Becauseᵉ ofᵉ universeᵉ polymorphism,ᵉ
  [largeᵉ subcategories](category-theory.large-subcategories.mdᵉ) areᵉ notᵉ largeᵉ
  repleteᵉ byᵉ construction,ᵉ althoughᵉ theyᵉ areᵉ levelwiseᵉ replete.ᵉ

## External links

-ᵉ [repleteᵉ subcategory](https://ncatlab.org/nlab/show/replete+replete-subprecategoryᵉ)
  atᵉ $n$Labᵉ
-ᵉ [Isomorphism-closedᵉ subcategory](https://en.wikipedia.org/wiki/Isomorphism-closed_subcategoryᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [isomorphism-closedᵉ subcategory](https://www.wikidata.org/wiki/Q6086096ᵉ) atᵉ
  Wikidataᵉ