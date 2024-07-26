# Maps between precategories

```agda
module category-theory.maps-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-precategoriesᵉ
open import category-theory.maps-set-magmoidsᵉ
open import category-theory.precategoriesᵉ

open import foundation.binary-transportᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **map**ᵉ fromᵉ aᵉ [precategory](category-theory.precategories.mdᵉ) `C`ᵉ to aᵉ
precategoryᵉ `D`ᵉ consistsᵉ ofᵉ:

-ᵉ aᵉ mapᵉ `F₀ᵉ : Cᵉ → D`ᵉ onᵉ objects,ᵉ
-ᵉ aᵉ mapᵉ `F₁ᵉ : homᵉ xᵉ yᵉ → homᵉ (F₀ᵉ xᵉ) (F₀ᵉ y)`ᵉ onᵉ morphismsᵉ

## Definitions

### Maps between precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  map-Precategoryᵉ =
    map-Set-Magmoidᵉ
      ( set-magmoid-Precategoryᵉ Cᵉ)
      ( set-magmoid-Precategoryᵉ Dᵉ)

  obj-map-Precategoryᵉ :
    (Fᵉ : map-Precategoryᵉ) → obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ
  obj-map-Precategoryᵉ =
    obj-map-Set-Magmoidᵉ
      ( set-magmoid-Precategoryᵉ Cᵉ)
      ( set-magmoid-Precategoryᵉ Dᵉ)

  hom-map-Precategoryᵉ :
    (Fᵉ : map-Precategoryᵉ)
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Dᵉ
      ( obj-map-Precategoryᵉ Fᵉ xᵉ)
      ( obj-map-Precategoryᵉ Fᵉ yᵉ)
  hom-map-Precategoryᵉ =
    hom-map-Set-Magmoidᵉ
      ( set-magmoid-Precategoryᵉ Cᵉ)
      ( set-magmoid-Precategoryᵉ Dᵉ)
```

## Properties

### Computing transport in the hom-family

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ x'ᵉ yᵉ y'ᵉ : obj-Precategoryᵉ Cᵉ}
  where

  compute-binary-tr-hom-Precategoryᵉ :
    (pᵉ : xᵉ ＝ᵉ x'ᵉ) (qᵉ : yᵉ ＝ᵉ y'ᵉ) (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    ( comp-hom-Precategoryᵉ Cᵉ
      ( hom-eq-Precategoryᵉ Cᵉ yᵉ y'ᵉ qᵉ)
      ( comp-hom-Precategoryᵉ Cᵉ fᵉ (hom-inv-eq-Precategoryᵉ Cᵉ xᵉ x'ᵉ pᵉ))) ＝ᵉ
    ( binary-trᵉ (hom-Precategoryᵉ Cᵉ) pᵉ qᵉ fᵉ)
  compute-binary-tr-hom-Precategoryᵉ reflᵉ reflᵉ fᵉ =
    ( left-unit-law-comp-hom-Precategoryᵉ Cᵉ
      ( comp-hom-Precategoryᵉ Cᵉ fᵉ (id-hom-Precategoryᵉ Cᵉ))) ∙ᵉ
    ( right-unit-law-comp-hom-Precategoryᵉ Cᵉ fᵉ)

  naturality-binary-tr-hom-Precategoryᵉ :
    (pᵉ : xᵉ ＝ᵉ x'ᵉ) (qᵉ : yᵉ ＝ᵉ y'ᵉ)
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    ( coherence-square-hom-Precategoryᵉ Cᵉ
      ( fᵉ)
      ( hom-eq-Precategoryᵉ Cᵉ xᵉ x'ᵉ pᵉ)
      ( hom-eq-Precategoryᵉ Cᵉ yᵉ y'ᵉ qᵉ)
      ( binary-trᵉ (hom-Precategoryᵉ Cᵉ) pᵉ qᵉ fᵉ))
  naturality-binary-tr-hom-Precategoryᵉ reflᵉ reflᵉ fᵉ =
    ( right-unit-law-comp-hom-Precategoryᵉ Cᵉ fᵉ) ∙ᵉ
    ( invᵉ (left-unit-law-comp-hom-Precategoryᵉ Cᵉ fᵉ))

  naturality-binary-tr-hom-Precategory'ᵉ :
    (pᵉ : xᵉ ＝ᵉ x'ᵉ) (qᵉ : yᵉ ＝ᵉ y'ᵉ)
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    ( coherence-square-hom-Precategoryᵉ Cᵉ
      ( hom-eq-Precategoryᵉ Cᵉ xᵉ x'ᵉ pᵉ)
      ( fᵉ)
      ( binary-trᵉ (hom-Precategoryᵉ Cᵉ) pᵉ qᵉ fᵉ)
      ( hom-eq-Precategoryᵉ Cᵉ yᵉ y'ᵉ qᵉ))
  naturality-binary-tr-hom-Precategory'ᵉ reflᵉ reflᵉ fᵉ =
    ( left-unit-law-comp-hom-Precategoryᵉ Cᵉ fᵉ) ∙ᵉ
    ( invᵉ (right-unit-law-comp-hom-Precategoryᵉ Cᵉ fᵉ))
```

### Characterization of equality of maps between precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  coherence-htpy-map-Precategoryᵉ :
    (fᵉ gᵉ : map-Precategoryᵉ Cᵉ Dᵉ) →
    obj-map-Precategoryᵉ Cᵉ Dᵉ fᵉ ~ᵉ obj-map-Precategoryᵉ Cᵉ Dᵉ gᵉ →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  coherence-htpy-map-Precategoryᵉ fᵉ gᵉ Hᵉ =
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
    (aᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    coherence-square-hom-Precategoryᵉ Dᵉ
      ( hom-map-Precategoryᵉ Cᵉ Dᵉ fᵉ aᵉ)
      ( hom-eq-Precategoryᵉ Dᵉ
        ( obj-map-Precategoryᵉ Cᵉ Dᵉ fᵉ xᵉ)
        ( obj-map-Precategoryᵉ Cᵉ Dᵉ gᵉ xᵉ)
        ( Hᵉ xᵉ))
      ( hom-eq-Precategoryᵉ Dᵉ
        ( obj-map-Precategoryᵉ Cᵉ Dᵉ fᵉ yᵉ)
        ( obj-map-Precategoryᵉ Cᵉ Dᵉ gᵉ yᵉ)
        ( Hᵉ yᵉ))
      ( hom-map-Precategoryᵉ Cᵉ Dᵉ gᵉ aᵉ)

  htpy-map-Precategoryᵉ :
    (fᵉ gᵉ : map-Precategoryᵉ Cᵉ Dᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-map-Precategoryᵉ fᵉ gᵉ =
    Σᵉ ( obj-map-Precategoryᵉ Cᵉ Dᵉ fᵉ ~ᵉ obj-map-Precategoryᵉ Cᵉ Dᵉ gᵉ)
      ( coherence-htpy-map-Precategoryᵉ fᵉ gᵉ)

  refl-htpy-map-Precategoryᵉ :
    (fᵉ : map-Precategoryᵉ Cᵉ Dᵉ) → htpy-map-Precategoryᵉ fᵉ fᵉ
  pr1ᵉ (refl-htpy-map-Precategoryᵉ fᵉ) = refl-htpyᵉ
  pr2ᵉ (refl-htpy-map-Precategoryᵉ fᵉ) aᵉ =
    naturality-binary-tr-hom-Precategoryᵉ Dᵉ
      ( reflᵉ)
      ( reflᵉ)
      ( hom-map-Precategoryᵉ Cᵉ Dᵉ fᵉ aᵉ)

  htpy-eq-map-Precategoryᵉ :
    (fᵉ gᵉ : map-Precategoryᵉ Cᵉ Dᵉ) → fᵉ ＝ᵉ gᵉ → htpy-map-Precategoryᵉ fᵉ gᵉ
  htpy-eq-map-Precategoryᵉ fᵉ .fᵉ reflᵉ = refl-htpy-map-Precategoryᵉ fᵉ

  is-torsorial-htpy-map-Precategoryᵉ :
    (fᵉ : map-Precategoryᵉ Cᵉ Dᵉ) → is-torsorialᵉ (htpy-map-Precategoryᵉ fᵉ)
  is-torsorial-htpy-map-Precategoryᵉ fᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (obj-map-Precategoryᵉ Cᵉ Dᵉ fᵉ))
      ( obj-map-Precategoryᵉ Cᵉ Dᵉ fᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-Eq-implicit-Πᵉ
        ( λ xᵉ →
          is-torsorial-Eq-implicit-Πᵉ
            ( λ yᵉ →
              is-contr-equivᵉ
                ( Σᵉ
                  ( (aᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
                    hom-Precategoryᵉ Dᵉ
                      ( obj-map-Precategoryᵉ Cᵉ Dᵉ fᵉ xᵉ)
                      ( obj-map-Precategoryᵉ Cᵉ Dᵉ fᵉ yᵉ))
                  ( _~ᵉ hom-map-Precategoryᵉ Cᵉ Dᵉ fᵉ))
                ( equiv-totᵉ
                  ( λ g₁ᵉ →
                    equiv-binary-concat-htpyᵉ
                      ( inv-htpyᵉ (right-unit-law-comp-hom-Precategoryᵉ Dᵉ ∘ᵉ g₁ᵉ))
                      ( left-unit-law-comp-hom-Precategoryᵉ Dᵉ ∘ᵉ
                        hom-map-Precategoryᵉ Cᵉ Dᵉ fᵉ)))
                ( is-torsorial-htpy'ᵉ (hom-map-Precategoryᵉ Cᵉ Dᵉ fᵉ)))))

  is-equiv-htpy-eq-map-Precategoryᵉ :
    (fᵉ gᵉ : map-Precategoryᵉ Cᵉ Dᵉ) → is-equivᵉ (htpy-eq-map-Precategoryᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-map-Precategoryᵉ fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-map-Precategoryᵉ fᵉ)
      ( htpy-eq-map-Precategoryᵉ fᵉ)

  equiv-htpy-eq-map-Precategoryᵉ :
    (fᵉ gᵉ : map-Precategoryᵉ Cᵉ Dᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-map-Precategoryᵉ fᵉ gᵉ
  pr1ᵉ (equiv-htpy-eq-map-Precategoryᵉ fᵉ gᵉ) = htpy-eq-map-Precategoryᵉ fᵉ gᵉ
  pr2ᵉ (equiv-htpy-eq-map-Precategoryᵉ fᵉ gᵉ) = is-equiv-htpy-eq-map-Precategoryᵉ fᵉ gᵉ

  eq-htpy-map-Precategoryᵉ :
    (fᵉ gᵉ : map-Precategoryᵉ Cᵉ Dᵉ) → htpy-map-Precategoryᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-map-Precategoryᵉ fᵉ gᵉ =
    map-inv-equivᵉ (equiv-htpy-eq-map-Precategoryᵉ fᵉ gᵉ)
```

## See also

-ᵉ [Functorsᵉ betweenᵉ precategories](category-theory.functors-precategories.mdᵉ)
-ᵉ [Theᵉ precategoryᵉ ofᵉ mapsᵉ andᵉ naturalᵉ transformationsᵉ betweenᵉ precategories](category-theory.precategory-of-maps-precategories.mdᵉ)