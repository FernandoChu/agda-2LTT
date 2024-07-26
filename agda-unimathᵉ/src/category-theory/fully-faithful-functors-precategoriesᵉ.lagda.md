# Fully faithful functors between precategories

```agda
module category-theory.fully-faithful-functors-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.conservative-functors-precategoriesᵉ
open import category-theory.essentially-injective-functors-precategoriesᵉ
open import category-theory.faithful-functors-precategoriesᵉ
open import category-theory.full-functors-precategoriesᵉ
open import category-theory.fully-faithful-maps-precategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.pseudomonic-functors-precategoriesᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [functor](category-theory.functors-precategories.mdᵉ) betweenᵉ
[precategories](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ `D`ᵉ isᵉ **fullyᵉ
faithful**ᵉ ifᵉ it'sᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) onᵉ
hom-[sets](foundation-core.sets.md),ᵉ orᵉ equivalently,ᵉ aᵉ
[full](category-theory.full-functors-precategories.mdᵉ) andᵉ
[faithful](category-theory.faithful-functors-precategories.mdᵉ) functorᵉ onᵉ
precategories.ᵉ

## Definitions

### The predicate on functors between precategories of being fully faithful

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-fully-faithful-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-fully-faithful-functor-Precategoryᵉ =
    is-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ (map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  is-prop-is-fully-faithful-functor-Precategoryᵉ :
    is-propᵉ is-fully-faithful-functor-Precategoryᵉ
  is-prop-is-fully-faithful-functor-Precategoryᵉ =
    is-prop-is-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  is-fully-faithful-prop-functor-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-fully-faithful-prop-functor-Precategoryᵉ =
    is-fully-faithful-prop-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  equiv-hom-is-fully-faithful-functor-Precategoryᵉ :
    is-fully-faithful-functor-Precategoryᵉ → {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ ≃ᵉ
    hom-Precategoryᵉ Dᵉ
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ)
  equiv-hom-is-fully-faithful-functor-Precategoryᵉ =
    equiv-hom-is-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  inv-equiv-hom-is-fully-faithful-functor-Precategoryᵉ :
    is-fully-faithful-functor-Precategoryᵉ →
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Dᵉ
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ) ≃ᵉ
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ
  inv-equiv-hom-is-fully-faithful-functor-Precategoryᵉ is-ff-Fᵉ =
    inv-equivᵉ (equiv-hom-is-fully-faithful-functor-Precategoryᵉ is-ff-Fᵉ)

  map-inv-hom-is-fully-faithful-functor-Precategoryᵉ :
    is-fully-faithful-functor-Precategoryᵉ →
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Dᵉ
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ) →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ
  map-inv-hom-is-fully-faithful-functor-Precategoryᵉ is-ff-Fᵉ =
    map-equivᵉ (inv-equiv-hom-is-fully-faithful-functor-Precategoryᵉ is-ff-Fᵉ)
```

### The type of fully faithful functors between two precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  fully-faithful-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  fully-faithful-functor-Precategoryᵉ =
    Σᵉ (functor-Precategoryᵉ Cᵉ Dᵉ) (is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ)

  functor-fully-faithful-functor-Precategoryᵉ :
    fully-faithful-functor-Precategoryᵉ → functor-Precategoryᵉ Cᵉ Dᵉ
  functor-fully-faithful-functor-Precategoryᵉ = pr1ᵉ

  is-fully-faithful-fully-faithful-functor-Precategoryᵉ :
    (Fᵉ : fully-faithful-functor-Precategoryᵉ) →
    is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-fully-faithful-functor-Precategoryᵉ Fᵉ)
  is-fully-faithful-fully-faithful-functor-Precategoryᵉ = pr2ᵉ

  obj-fully-faithful-functor-Precategoryᵉ :
    fully-faithful-functor-Precategoryᵉ → obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ
  obj-fully-faithful-functor-Precategoryᵉ =
    obj-functor-Precategoryᵉ Cᵉ Dᵉ ∘ᵉ functor-fully-faithful-functor-Precategoryᵉ

  hom-fully-faithful-functor-Precategoryᵉ :
    (Fᵉ : fully-faithful-functor-Precategoryᵉ)
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Dᵉ
      ( obj-fully-faithful-functor-Precategoryᵉ Fᵉ xᵉ)
      ( obj-fully-faithful-functor-Precategoryᵉ Fᵉ yᵉ)
  hom-fully-faithful-functor-Precategoryᵉ =
    hom-functor-Precategoryᵉ Cᵉ Dᵉ ∘ᵉ functor-fully-faithful-functor-Precategoryᵉ

  equiv-hom-fully-faithful-functor-Precategoryᵉ :
    (Fᵉ : fully-faithful-functor-Precategoryᵉ)
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ ≃ᵉ
    hom-Precategoryᵉ Dᵉ
      ( obj-fully-faithful-functor-Precategoryᵉ Fᵉ xᵉ)
      ( obj-fully-faithful-functor-Precategoryᵉ Fᵉ yᵉ)
  equiv-hom-fully-faithful-functor-Precategoryᵉ Fᵉ =
    equiv-hom-is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-fully-faithful-functor-Precategoryᵉ Fᵉ)
      ( is-fully-faithful-fully-faithful-functor-Precategoryᵉ Fᵉ)

  inv-equiv-hom-fully-faithful-functor-Precategoryᵉ :
    (Fᵉ : fully-faithful-functor-Precategoryᵉ)
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Dᵉ
      ( obj-fully-faithful-functor-Precategoryᵉ Fᵉ xᵉ)
      ( obj-fully-faithful-functor-Precategoryᵉ Fᵉ yᵉ) ≃ᵉ
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ
  inv-equiv-hom-fully-faithful-functor-Precategoryᵉ Fᵉ =
    inv-equivᵉ (equiv-hom-fully-faithful-functor-Precategoryᵉ Fᵉ)

  map-inv-hom-fully-faithful-functor-Precategoryᵉ :
    (Fᵉ : fully-faithful-functor-Precategoryᵉ)
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Dᵉ
      ( obj-fully-faithful-functor-Precategoryᵉ Fᵉ xᵉ)
      ( obj-fully-faithful-functor-Precategoryᵉ Fᵉ yᵉ) →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ
  map-inv-hom-fully-faithful-functor-Precategoryᵉ Fᵉ =
    map-equivᵉ (inv-equiv-hom-fully-faithful-functor-Precategoryᵉ Fᵉ)
```

## Properties

### Fully faithful functors are the same as full and faithful functors

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-full-is-fully-faithful-functor-Precategoryᵉ :
    is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    is-full-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-full-is-fully-faithful-functor-Precategoryᵉ is-ff-Fᵉ xᵉ yᵉ =
    is-surjective-is-equivᵉ (is-ff-Fᵉ xᵉ yᵉ)

  full-functor-is-fully-faithful-functor-Precategoryᵉ :
    is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ → full-functor-Precategoryᵉ Cᵉ Dᵉ
  pr1ᵉ (full-functor-is-fully-faithful-functor-Precategoryᵉ is-ff-Fᵉ) = Fᵉ
  pr2ᵉ (full-functor-is-fully-faithful-functor-Precategoryᵉ is-ff-Fᵉ) =
    is-full-is-fully-faithful-functor-Precategoryᵉ is-ff-Fᵉ

  is-faithful-is-fully-faithful-functor-Precategoryᵉ :
    is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    is-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-faithful-is-fully-faithful-functor-Precategoryᵉ is-ff-Fᵉ xᵉ yᵉ =
    is-emb-is-equivᵉ (is-ff-Fᵉ xᵉ yᵉ)

  faithful-functor-is-fully-faithful-functor-Precategoryᵉ :
    is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    faithful-functor-Precategoryᵉ Cᵉ Dᵉ
  pr1ᵉ (faithful-functor-is-fully-faithful-functor-Precategoryᵉ is-ff-Fᵉ) = Fᵉ
  pr2ᵉ (faithful-functor-is-fully-faithful-functor-Precategoryᵉ is-ff-Fᵉ) =
    is-faithful-is-fully-faithful-functor-Precategoryᵉ is-ff-Fᵉ

  is-fully-faithful-is-full-is-faithful-functor-Precategoryᵉ :
    is-full-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    is-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-fully-faithful-is-full-is-faithful-functor-Precategoryᵉ
    is-full-Fᵉ is-faithful-Fᵉ xᵉ yᵉ =
    is-equiv-is-emb-is-surjectiveᵉ (is-full-Fᵉ xᵉ yᵉ) (is-faithful-Fᵉ xᵉ yᵉ)

  fully-faithful-functor-is-full-is-faithful-functor-Precategoryᵉ :
    is-full-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    is-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ
  pr1ᵉ
    ( fully-faithful-functor-is-full-is-faithful-functor-Precategoryᵉ
      is-full-Fᵉ is-faithful-Fᵉ) =
    Fᵉ
  pr2ᵉ
    ( fully-faithful-functor-is-full-is-faithful-functor-Precategoryᵉ
      is-full-Fᵉ is-faithful-Fᵉ) =
    is-fully-faithful-is-full-is-faithful-functor-Precategoryᵉ
      ( is-full-Fᵉ) (is-faithful-Fᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  full-functor-fully-faithful-functor-Precategoryᵉ : full-functor-Precategoryᵉ Cᵉ Dᵉ
  full-functor-fully-faithful-functor-Precategoryᵉ =
    full-functor-is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( is-fully-faithful-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  faithful-functor-fully-faithful-functor-Precategoryᵉ :
    faithful-functor-Precategoryᵉ Cᵉ Dᵉ
  faithful-functor-fully-faithful-functor-Precategoryᵉ =
    faithful-functor-is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( is-fully-faithful-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
```

### Fully faithful functors are essentially injective

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (is-ff-Fᵉ : is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  ((eᵉ ,ᵉ e'ᵉ ,ᵉ lᵉ ,ᵉ rᵉ) :
      iso-Precategoryᵉ Dᵉ
        ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
        ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ))
  where

  hom-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ
  hom-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ =
    map-inv-hom-is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ is-ff-Fᵉ eᵉ

  hom-inv-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ yᵉ xᵉ
  hom-inv-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ =
    map-inv-hom-is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ is-ff-Fᵉ e'ᵉ

  is-right-inverse-hom-inv-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ :
    ( comp-hom-Precategoryᵉ Cᵉ
      ( hom-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ)
      ( hom-inv-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ)) ＝ᵉ
    ( id-hom-Precategoryᵉ Cᵉ)
  is-right-inverse-hom-inv-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ =
    ( invᵉ
      ( is-retraction-map-inv-is-equivᵉ
        ( is-ff-Fᵉ yᵉ yᵉ)
        ( comp-hom-Precategoryᵉ Cᵉ
          ( map-inv-is-equivᵉ (is-ff-Fᵉ xᵉ yᵉ) eᵉ)
          ( map-inv-is-equivᵉ (is-ff-Fᵉ yᵉ xᵉ) e'ᵉ)))) ∙ᵉ
    ( apᵉ
      ( map-inv-hom-is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ is-ff-Fᵉ)
      ( ( preserves-comp-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
          ( map-inv-is-equivᵉ (is-ff-Fᵉ xᵉ yᵉ) eᵉ)
          ( map-inv-is-equivᵉ (is-ff-Fᵉ yᵉ xᵉ) e'ᵉ)) ∙ᵉ
        ( ap-binaryᵉ
          ( comp-hom-Precategoryᵉ Dᵉ)
          ( is-section-map-inv-is-equivᵉ (is-ff-Fᵉ xᵉ yᵉ) eᵉ)
          ( is-section-map-inv-is-equivᵉ (is-ff-Fᵉ yᵉ xᵉ) e'ᵉ)) ∙ᵉ
        ( lᵉ) ∙ᵉ
        ( invᵉ (preserves-id-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ)))) ∙ᵉ
    ( is-retraction-map-inv-is-equivᵉ (is-ff-Fᵉ yᵉ yᵉ) (id-hom-Precategoryᵉ Cᵉ))

  is-left-inverse-hom-inv-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ :
    ( comp-hom-Precategoryᵉ Cᵉ
      ( hom-inv-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ)
      ( hom-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ)) ＝ᵉ
    ( id-hom-Precategoryᵉ Cᵉ)
  is-left-inverse-hom-inv-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ =
    ( invᵉ
      ( is-retraction-map-inv-is-equivᵉ
        ( is-ff-Fᵉ xᵉ xᵉ)
        ( comp-hom-Precategoryᵉ Cᵉ
          ( map-inv-is-equivᵉ (is-ff-Fᵉ yᵉ xᵉ) e'ᵉ)
          ( map-inv-is-equivᵉ (is-ff-Fᵉ xᵉ yᵉ) eᵉ)))) ∙ᵉ
    ( apᵉ
      ( map-inv-hom-is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ is-ff-Fᵉ)
      ( ( preserves-comp-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
          ( map-inv-is-equivᵉ (is-ff-Fᵉ yᵉ xᵉ) e'ᵉ)
          ( map-inv-is-equivᵉ (is-ff-Fᵉ xᵉ yᵉ) eᵉ)) ∙ᵉ
        ( ap-binaryᵉ
          (comp-hom-Precategoryᵉ Dᵉ)
          ( is-section-map-inv-is-equivᵉ (is-ff-Fᵉ yᵉ xᵉ) e'ᵉ)
          ( is-section-map-inv-is-equivᵉ (is-ff-Fᵉ xᵉ yᵉ) eᵉ)) ∙ᵉ
        ( rᵉ) ∙ᵉ
        ( invᵉ (preserves-id-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)))) ∙ᵉ
    ( is-retraction-map-inv-is-equivᵉ (is-ff-Fᵉ xᵉ xᵉ) (id-hom-Precategoryᵉ Cᵉ))

  is-iso-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ :
    is-iso-Precategoryᵉ Cᵉ
      ( hom-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ)
  pr1ᵉ
    is-iso-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ =
    hom-inv-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ
  pr1ᵉ
    ( pr2ᵉ
        is-iso-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ) =
    is-right-inverse-hom-inv-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ
  pr2ᵉ
    ( pr2ᵉ
        is-iso-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ) =
    is-left-inverse-hom-inv-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (is-ff-Fᵉ : is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  where

  is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ :
    is-essentially-injective-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  pr1ᵉ (is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ xᵉ yᵉ eᵉ) =
    hom-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ is-ff-Fᵉ eᵉ
  pr2ᵉ (is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ xᵉ yᵉ eᵉ) =
    is-iso-iso-is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ is-ff-Fᵉ eᵉ
```

### Fully faithful functors are pseudomonic

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (is-ff-Fᵉ : is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  where

  is-full-on-isos-is-fully-faithful-functor-Precategoryᵉ :
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) →
    is-surjectiveᵉ (preserves-iso-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ {xᵉ} {yᵉ})
  is-full-on-isos-is-fully-faithful-functor-Precategoryᵉ xᵉ yᵉ eᵉ =
    unit-trunc-Propᵉ
      ( ( is-essentially-injective-is-fully-faithful-functor-Precategoryᵉ
            Cᵉ Dᵉ Fᵉ is-ff-Fᵉ xᵉ yᵉ eᵉ) ,ᵉ
        eq-type-subtypeᵉ
          ( is-iso-prop-Precategoryᵉ Dᵉ)
          ( is-section-map-inv-is-equivᵉ (is-ff-Fᵉ xᵉ yᵉ) (pr1ᵉ eᵉ)))

  is-pseudomonic-is-fully-faithful-functor-Precategoryᵉ :
    is-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  pr1ᵉ is-pseudomonic-is-fully-faithful-functor-Precategoryᵉ =
    is-faithful-is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ is-ff-Fᵉ
  pr2ᵉ is-pseudomonic-is-fully-faithful-functor-Precategoryᵉ =
    is-full-on-isos-is-fully-faithful-functor-Precategoryᵉ
```

### Fully faithful functors are conservative

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (is-ff-Fᵉ : is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  where

  is-conservative-is-fully-faithful-functor-Precategoryᵉ :
    is-conservative-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-conservative-is-fully-faithful-functor-Precategoryᵉ {xᵉ} {yᵉ} =
    is-conservative-is-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
      ( is-pseudomonic-is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ is-ff-Fᵉ)
      { xᵉ} {yᵉ}
```

## External links

-ᵉ [Fullyᵉ Faithfulᵉ Functors](https://1lab.dev/Cat.Functor.Properties.html#fully-faithful-functorsᵉ)
  atᵉ 1labᵉ
-ᵉ [fullᵉ andᵉ faithfulᵉ functor](https://ncatlab.org/nlab/show/full+and+faithful+functorᵉ)
  atᵉ $n$Labᵉ
-ᵉ [Fullᵉ andᵉ faithfulᵉ functors](https://en.wikipedia.org/wiki/Full_and_faithful_functorsᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [fullyᵉ faithfulᵉ functor](https://wikidata.org/wiki/Q120721906ᵉ) atᵉ Wikidataᵉ