# Pseudomonic functors between precategories

```agda
module category-theory.pseudomonic-functors-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.conservative-functors-precategoriesᵉ
open import category-theory.faithful-functors-precategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [functor](category-theory.functors-precategories.mdᵉ) betweenᵉ
[precategories](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ `D`ᵉ isᵉ
{{#conceptᵉ "pseudomonic"ᵉ Disambiguation="functorᵉ betweenᵉ precategories"ᵉ Agda=is-pseudomonic-functor-Precategoryᵉ}}
ifᵉ itᵉ isᵉ [faithful](category-theory.faithful-functors-precategories.mdᵉ) onᵉ allᵉ
morphism-[sets](foundation-core.sets.mdᵉ) andᵉ fullᵉ onᵉ
[isomorphisms](category-theory.isomorphisms-in-precategories.md).ᵉ Inᵉ particular,ᵉ
thisᵉ meansᵉ itᵉ inducesᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) onᵉ
isomorphism-sets.ᵉ

Pseudomonicᵉ functorsᵉ presentᵉ
[repleteᵉ subprecategories](category-theory.replete-subprecategories.md),ᵉ whichᵉ
isᵉ theᵉ "rightᵉ notion"ᵉ ofᵉ subcategoryᵉ with respectᵉ to theᵉ _principleᵉ ofᵉ
invarianceᵉ underᵉ equivalences_.ᵉ

## Definition

### The predicate on isomorphisms of being full

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-full-on-isos-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-full-on-isos-functor-Precategoryᵉ =
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) →
    is-surjectiveᵉ (preserves-iso-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ {xᵉ} {yᵉ})

  is-prop-is-full-on-isos-functor-Precategoryᵉ :
    is-propᵉ is-full-on-isos-functor-Precategoryᵉ
  is-prop-is-full-on-isos-functor-Precategoryᵉ =
    is-prop-iterated-Πᵉ 2
      ( λ xᵉ yᵉ → is-prop-is-surjectiveᵉ (preserves-iso-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ))

  is-full-on-isos-prop-functor-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-full-on-isos-prop-functor-Precategoryᵉ =
    is-full-on-isos-functor-Precategoryᵉ
  pr2ᵉ is-full-on-isos-prop-functor-Precategoryᵉ =
    is-prop-is-full-on-isos-functor-Precategoryᵉ
```

### The predicate of being pseudomonic

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-pseudomonic-prop-functor-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-pseudomonic-prop-functor-Precategoryᵉ =
    product-Propᵉ
      ( is-faithful-prop-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( is-full-on-isos-prop-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  is-pseudomonic-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-pseudomonic-functor-Precategoryᵉ =
    type-Propᵉ is-pseudomonic-prop-functor-Precategoryᵉ

  is-prop-is-pseudomonic-functor-Precategoryᵉ :
    is-propᵉ is-pseudomonic-functor-Precategoryᵉ
  is-prop-is-pseudomonic-functor-Precategoryᵉ =
    is-prop-type-Propᵉ is-pseudomonic-prop-functor-Precategoryᵉ

  is-faithful-is-pseudomonic-functor-Precategoryᵉ :
    is-pseudomonic-functor-Precategoryᵉ →
    is-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-faithful-is-pseudomonic-functor-Precategoryᵉ = pr1ᵉ

  is-full-on-isos-is-pseudomonic-functor-Precategoryᵉ :
    is-pseudomonic-functor-Precategoryᵉ →
    is-full-on-isos-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-full-on-isos-is-pseudomonic-functor-Precategoryᵉ = pr2ᵉ
```

### The type of pseudomonic functors between two precategories

```agda
pseudomonic-functor-Precategoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ =
  Σᵉ (functor-Precategoryᵉ Cᵉ Dᵉ) (is-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  functor-pseudomonic-functor-Precategoryᵉ : functor-Precategoryᵉ Cᵉ Dᵉ
  functor-pseudomonic-functor-Precategoryᵉ = pr1ᵉ Fᵉ

  is-pseudomonic-pseudomonic-functor-Precategoryᵉ :
    is-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ
      functor-pseudomonic-functor-Precategoryᵉ
  is-pseudomonic-pseudomonic-functor-Precategoryᵉ = pr2ᵉ Fᵉ

  obj-pseudomonic-functor-Precategoryᵉ : obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ
  obj-pseudomonic-functor-Precategoryᵉ =
    obj-functor-Precategoryᵉ Cᵉ Dᵉ functor-pseudomonic-functor-Precategoryᵉ

  hom-pseudomonic-functor-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Dᵉ
      ( obj-pseudomonic-functor-Precategoryᵉ xᵉ)
      ( obj-pseudomonic-functor-Precategoryᵉ yᵉ)
  hom-pseudomonic-functor-Precategoryᵉ =
    hom-functor-Precategoryᵉ Cᵉ Dᵉ functor-pseudomonic-functor-Precategoryᵉ

  is-faithful-pseudomonic-functor-Precategoryᵉ :
    is-faithful-functor-Precategoryᵉ Cᵉ Dᵉ functor-pseudomonic-functor-Precategoryᵉ
  is-faithful-pseudomonic-functor-Precategoryᵉ =
    is-faithful-is-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ
      functor-pseudomonic-functor-Precategoryᵉ
      is-pseudomonic-pseudomonic-functor-Precategoryᵉ

  is-full-on-isos-pseudomonic-functor-Precategoryᵉ :
    is-full-on-isos-functor-Precategoryᵉ Cᵉ Dᵉ
      functor-pseudomonic-functor-Precategoryᵉ
  is-full-on-isos-pseudomonic-functor-Precategoryᵉ =
    is-full-on-isos-is-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ
      functor-pseudomonic-functor-Precategoryᵉ
      is-pseudomonic-pseudomonic-functor-Precategoryᵉ
```

## Properties

### Pseudomonic functors are equivalences on isomorphism-sets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (is-pseudomonic-Fᵉ : is-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  where

  is-equiv-preserves-iso-is-pseudomonic-functor-Precategoryᵉ :
    is-equivᵉ (preserves-iso-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ {xᵉ} {yᵉ})
  is-equiv-preserves-iso-is-pseudomonic-functor-Precategoryᵉ =
    is-equiv-is-emb-is-surjectiveᵉ
      ( pr2ᵉ is-pseudomonic-Fᵉ xᵉ yᵉ)
      ( is-faithful-on-isos-is-faithful-functor-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ (pr1ᵉ is-pseudomonic-Fᵉ) xᵉ yᵉ)

  equiv-iso-is-pseudomonic-functor-Precategoryᵉ :
    iso-Precategoryᵉ Cᵉ xᵉ yᵉ ≃ᵉ
    iso-Precategoryᵉ Dᵉ
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ)
  pr1ᵉ equiv-iso-is-pseudomonic-functor-Precategoryᵉ =
    preserves-iso-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  pr2ᵉ equiv-iso-is-pseudomonic-functor-Precategoryᵉ =
    is-equiv-preserves-iso-is-pseudomonic-functor-Precategoryᵉ

  inv-equiv-iso-is-pseudomonic-functor-Precategoryᵉ :
    iso-Precategoryᵉ Dᵉ
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ) ≃ᵉ
    iso-Precategoryᵉ Cᵉ xᵉ yᵉ
  inv-equiv-iso-is-pseudomonic-functor-Precategoryᵉ =
    inv-equivᵉ equiv-iso-is-pseudomonic-functor-Precategoryᵉ

  map-inv-iso-is-pseudomonic-functor-Precategoryᵉ :
    iso-Precategoryᵉ Dᵉ
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ) →
    iso-Precategoryᵉ Cᵉ xᵉ yᵉ
  map-inv-iso-is-pseudomonic-functor-Precategoryᵉ =
    map-equivᵉ inv-equiv-iso-is-pseudomonic-functor-Precategoryᵉ
```

Theᵉ previousᵉ entryᵉ recordsᵉ whatᵉ isᵉ alsoᵉ knownᵉ asᵉ "essentialᵉ injectivity".ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  where

  equiv-iso-pseudomonic-functor-Precategoryᵉ :
    iso-Precategoryᵉ Cᵉ xᵉ yᵉ ≃ᵉ
    iso-Precategoryᵉ Dᵉ
      ( obj-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ)
  equiv-iso-pseudomonic-functor-Precategoryᵉ =
    equiv-iso-is-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ
      ( functor-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( is-pseudomonic-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  inv-equiv-iso-pseudomonic-functor-Precategoryᵉ :
    iso-Precategoryᵉ Dᵉ
      ( obj-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ) ≃ᵉ
    iso-Precategoryᵉ Cᵉ xᵉ yᵉ
  inv-equiv-iso-pseudomonic-functor-Precategoryᵉ =
    inv-equivᵉ equiv-iso-pseudomonic-functor-Precategoryᵉ

  map-inv-hom-pseudomonic-functor-Precategoryᵉ :
    iso-Precategoryᵉ Dᵉ
      ( obj-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ) →
    iso-Precategoryᵉ Cᵉ xᵉ yᵉ
  map-inv-hom-pseudomonic-functor-Precategoryᵉ =
    map-equivᵉ inv-equiv-iso-pseudomonic-functor-Precategoryᵉ
```

Theᵉ previousᵉ entryᵉ recordsᵉ whatᵉ isᵉ alsoᵉ knownᵉ asᵉ "essentialᵉ injectivity".ᵉ

### Pseudomonic functors are conservative

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (is-pseudomonic-Fᵉ : is-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  where

  is-conservative-is-pseudomonic-functor-Precategoryᵉ :
    is-conservative-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-conservative-is-pseudomonic-functor-Precategoryᵉ fᵉ is-iso-Ffᵉ =
    ind-trunc-Propᵉ
      ( λ _ → is-iso-prop-Precategoryᵉ Cᵉ fᵉ)
      ( λ ((eᵉ ,ᵉ e'ᵉ ,ᵉ lᵉ ,ᵉ rᵉ) ,ᵉ pᵉ) →
        ( e'ᵉ ,ᵉ
          ( invᵉ
            ( apᵉ
              ( λ gᵉ → comp-hom-Precategoryᵉ Cᵉ gᵉ e'ᵉ)
              ( is-injective-is-embᵉ
                ( is-faithful-is-pseudomonic-functor-Precategoryᵉ
                    ( Cᵉ) Dᵉ Fᵉ is-pseudomonic-Fᵉ _ _)
                ( apᵉ pr1ᵉ pᵉ)))) ∙ᵉ
          ( lᵉ) ,ᵉ
          ( invᵉ
            ( apᵉ
              ( comp-hom-Precategoryᵉ Cᵉ e'ᵉ)
              ( is-injective-is-embᵉ
                ( is-faithful-is-pseudomonic-functor-Precategoryᵉ
                    ( Cᵉ) Dᵉ Fᵉ is-pseudomonic-Fᵉ _ _)
                ( apᵉ pr1ᵉ pᵉ)))) ∙ᵉ
          ( rᵉ)))
      ( pr2ᵉ is-pseudomonic-Fᵉ _ _ (hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ ,ᵉ is-iso-Ffᵉ))
```

## See also

-ᵉ Pseudomonicᵉ functorsᵉ presentᵉ
  [repleteᵉ subprecategories](category-theory.replete-subprecategories.md).ᵉ
-ᵉ [Fullyᵉ faithfulᵉ functorsᵉ betweenᵉ precategories](category-theory.fully-faithful-functors-precategories.mdᵉ)

## External links

-ᵉ [Pseudomonicᵉ Functors](https://1lab.dev/Cat.Functor.Properties.html#pseudomonic-functorsᵉ)
  atᵉ 1labᵉ
-ᵉ [pseudomonicᵉ functor](https://ncatlab.org/nlab/show/pseudomonic+functorᵉ) atᵉ
  $n$Labᵉ

Aᵉ wikidataᵉ identifierᵉ wasᵉ notᵉ availableᵉ forᵉ thisᵉ concept.ᵉ