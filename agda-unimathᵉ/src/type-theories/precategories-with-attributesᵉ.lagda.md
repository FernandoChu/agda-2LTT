# Precategories with attributes

```agda
module type-theories.precategories-with-attributesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-precategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ
open import category-theory.opposite-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.precategory-of-elements-of-a-presheafᵉ
open import category-theory.presheaf-categoriesᵉ
open import category-theory.pullbacks-in-precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.category-of-setsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.sectionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **precategoryᵉ with attributes**ᵉ consistsᵉ ofᵉ:

-ᵉ aᵉ [precategory](category-theory.precategories.mdᵉ) `C`,ᵉ whichᵉ weᵉ thinkᵉ ofᵉ asᵉ aᵉ
  categoryᵉ ofᵉ contextsᵉ andᵉ contextᵉ morphismsᵉ
-ᵉ aᵉ [presheaf](category-theory.presheaf-categories.mdᵉ) `Ty`ᵉ onᵉ `C`,ᵉ whichᵉ weᵉ
  thinkᵉ ofᵉ asᵉ givingᵉ theᵉ typesᵉ in eachᵉ contextᵉ
-ᵉ aᵉ [functor](category-theory.functors-precategories.mdᵉ) `ext`ᵉ fromᵉ `∫ᵉ Ty`ᵉ to
  `C`,ᵉ whichᵉ weᵉ thinkᵉ ofᵉ asᵉ contextᵉ extensionᵉ
-ᵉ aᵉ
  [naturalᵉ transformation](category-theory.natural-transformations-functors-precategories.mdᵉ)
  `p`ᵉ fromᵉ `ext`ᵉ to theᵉ projectionᵉ fromᵉ `∫ᵉ Ty`ᵉ to `C`ᵉ suchᵉ thatᵉ
-ᵉ theᵉ naturalityᵉ squaresᵉ ofᵉ `p`ᵉ areᵉ
  [pullback](category-theory.pullbacks-in-precategories.mdᵉ) squaresᵉ

Thisᵉ isᵉ aᵉ reformulationᵉ ofᵉ Definitionᵉ 1,ᵉ slideᵉ 24 ofᵉ
<https://staff.math.su.se/palmgren/ErikP_Variants_CWF.pdf>

```agda
record
  Precategory-With-Attributesᵉ
    (l1ᵉ l2ᵉ l3ᵉ : Level) :
    UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
  where

  field
    ctx-categoryᵉ : Precategoryᵉ l1ᵉ l2ᵉ

  Ctxᵉ : UUᵉ l1ᵉ
  Ctxᵉ = obj-Precategoryᵉ ctx-categoryᵉ

  Subᵉ : Ctxᵉ → Ctxᵉ → UUᵉ l2ᵉ
  Subᵉ = hom-Precategoryᵉ ctx-categoryᵉ

  field
    ty-presheafᵉ : presheaf-Precategoryᵉ ctx-categoryᵉ l3ᵉ

  Tyᵉ : Ctxᵉ → UUᵉ l3ᵉ
  Tyᵉ Γᵉ = element-presheaf-Precategoryᵉ ctx-categoryᵉ ty-presheafᵉ Γᵉ

  ∫Tyᵉ : Precategoryᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l3ᵉ)
  ∫Tyᵉ = precategory-of-elements-presheaf-Precategoryᵉ ctx-categoryᵉ ty-presheafᵉ

  obj-∫Tyᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  obj-∫Tyᵉ = obj-Precategoryᵉ ∫Tyᵉ

  hom-∫Tyᵉ : obj-∫Tyᵉ → obj-∫Tyᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  hom-∫Tyᵉ = hom-Precategoryᵉ ∫Tyᵉ

  proj-∫Tyᵉ : functor-Precategoryᵉ ∫Tyᵉ ctx-categoryᵉ
  proj-∫Tyᵉ =
    proj-functor-precategory-of-elements-presheaf-Precategoryᵉ
      ( ctx-categoryᵉ)
      ( ty-presheafᵉ)

  _·ᵉ_ : {Δᵉ Γᵉ : Ctxᵉ} (Aᵉ : Tyᵉ Γᵉ) (γᵉ : Subᵉ Δᵉ Γᵉ) → Tyᵉ Δᵉ
  Aᵉ ·ᵉ γᵉ = action-presheaf-Precategoryᵉ ctx-categoryᵉ ty-presheafᵉ γᵉ Aᵉ

  preserves-comp-Tyᵉ :
    {Δᵉ Δ'ᵉ Γᵉ : Ctxᵉ} (Aᵉ : Tyᵉ Γᵉ) (γᵉ : Subᵉ Δ'ᵉ Γᵉ) (δᵉ : Subᵉ Δᵉ Δ'ᵉ) →
    Aᵉ ·ᵉ comp-hom-Precategoryᵉ ctx-categoryᵉ γᵉ δᵉ ＝ᵉ (Aᵉ ·ᵉ γᵉ) ·ᵉ δᵉ
  preserves-comp-Tyᵉ Aᵉ γᵉ δᵉ =
    preserves-comp-action-presheaf-Precategoryᵉ ctx-categoryᵉ ty-presheafᵉ γᵉ δᵉ Aᵉ

  preserves-id-Tyᵉ :
    {Γᵉ : Ctxᵉ} (Aᵉ : Tyᵉ Γᵉ) → Aᵉ ·ᵉ id-hom-Precategoryᵉ ctx-categoryᵉ ＝ᵉ Aᵉ
  preserves-id-Tyᵉ {Γᵉ} =
    preserves-id-action-presheaf-Precategoryᵉ ctx-categoryᵉ ty-presheafᵉ

  field
    ext-functorᵉ : functor-Precategoryᵉ ∫Tyᵉ ctx-categoryᵉ

  extᵉ : (Γᵉ : Ctxᵉ) (Aᵉ : Tyᵉ Γᵉ) → Ctxᵉ
  extᵉ Γᵉ Aᵉ = obj-functor-Precategoryᵉ ∫Tyᵉ ctx-categoryᵉ ext-functorᵉ (Γᵉ ,ᵉ Aᵉ)

  ⟨_,_⟩ᵉ : {Γᵉ Δᵉ : Ctxᵉ} (σᵉ : Subᵉ Γᵉ Δᵉ) (Aᵉ : Tyᵉ Δᵉ) → Subᵉ (extᵉ Γᵉ (Aᵉ ·ᵉ σᵉ)) (extᵉ Δᵉ Aᵉ)
  ⟨ᵉ σᵉ ,ᵉ Aᵉ ⟩ᵉ = hom-functor-Precategoryᵉ ∫Tyᵉ ctx-categoryᵉ ext-functorᵉ (σᵉ ,ᵉ reflᵉ)

  field
    p-natural-transformationᵉ :
      natural-transformation-Precategoryᵉ ∫Tyᵉ ctx-categoryᵉ ext-functorᵉ proj-∫Tyᵉ

  pᵉ : (Γᵉ : Ctxᵉ) (Aᵉ : Tyᵉ Γᵉ) → Subᵉ (extᵉ Γᵉ Aᵉ) Γᵉ
  pᵉ Γᵉ Aᵉ = pr1ᵉ p-natural-transformationᵉ (Γᵉ ,ᵉ Aᵉ)

  naturality-pᵉ :
    {xᵉ yᵉ : obj-∫Tyᵉ} (fᵉ : hom-∫Tyᵉ xᵉ yᵉ) →
    coherence-square-hom-Precategoryᵉ
      ( ctx-categoryᵉ)
      ( hom-functor-Precategoryᵉ ∫Tyᵉ ctx-categoryᵉ ext-functorᵉ fᵉ)
      ( pᵉ (pr1ᵉ xᵉ) (pr2ᵉ xᵉ))
      ( pᵉ (pr1ᵉ yᵉ) (pr2ᵉ yᵉ))
      ( hom-functor-Precategoryᵉ ∫Tyᵉ ctx-categoryᵉ proj-∫Tyᵉ fᵉ)
  naturality-pᵉ =
    naturality-natural-transformation-Precategoryᵉ
      ( precategory-of-elements-presheaf-Precategoryᵉ
        ( ctx-categoryᵉ)
        ( ty-presheafᵉ))
      ( ctx-categoryᵉ)
      ( ext-functorᵉ)
      ( proj-functor-precategory-of-elements-presheaf-Precategoryᵉ
        ( ctx-categoryᵉ)
          ( ty-presheafᵉ))
      ( p-natural-transformationᵉ)

  field
    is-pullback-pᵉ :
      (xᵉ yᵉ : obj-∫Tyᵉ) (fᵉ : hom-∫Tyᵉ xᵉ yᵉ) →
      is-pullback-obj-Precategoryᵉ ctx-categoryᵉ _ _ _ _ _ _ _ _ (naturality-pᵉ fᵉ)
```

Theᵉ termsᵉ areᵉ definedᵉ asᵉ sectionsᵉ to `ext`.ᵉ

```agda
  module _
    (Γᵉ : Ctxᵉ) (Aᵉ : Tyᵉ Γᵉ)
    where

    Tmᵉ : UUᵉ l2ᵉ
    Tmᵉ =
      Σᵉ ( Subᵉ Γᵉ (extᵉ Γᵉ Aᵉ))
        ( λ tᵉ →
          comp-hom-Precategoryᵉ ctx-categoryᵉ (pᵉ Γᵉ Aᵉ) tᵉ ＝ᵉ
          id-hom-Precategoryᵉ ctx-categoryᵉ)

    is-set-Tmᵉ : is-setᵉ Tmᵉ
    is-set-Tmᵉ =
      is-set-type-subtypeᵉ
        ( λ tᵉ →
          Id-Propᵉ
            ( hom-set-Precategoryᵉ ctx-categoryᵉ Γᵉ Γᵉ)
            ( comp-hom-Precategoryᵉ ctx-categoryᵉ (pᵉ Γᵉ Aᵉ) tᵉ)
            ( id-hom-Precategoryᵉ ctx-categoryᵉ))
        ( is-set-hom-Precategoryᵉ ctx-categoryᵉ Γᵉ (extᵉ Γᵉ Aᵉ))

    Tm-Setᵉ : Setᵉ l2ᵉ
    pr1ᵉ Tm-Setᵉ = Tmᵉ
    pr2ᵉ Tm-Setᵉ = is-set-Tmᵉ

  _[ᵉ_] :
    {Γᵉ Δᵉ : Ctxᵉ} {Aᵉ : Tyᵉ Δᵉ} (tᵉ : Tmᵉ Δᵉ Aᵉ) (σᵉ : Subᵉ Γᵉ Δᵉ) → Tmᵉ Γᵉ (Aᵉ ·ᵉ σᵉ)
  _[ᵉ_] {Γᵉ} {Δᵉ} {Aᵉ} (sᵉ ,ᵉ eqᵉ) σᵉ =
    ( pr1ᵉ gap-mapᵉ ,ᵉ pr1ᵉ (pr2ᵉ gap-mapᵉ))
    where
    sqᵉ :
      comp-hom-Precategoryᵉ ctx-categoryᵉ σᵉ (id-hom-Precategoryᵉ ctx-categoryᵉ) ＝ᵉ
      comp-hom-Precategoryᵉ ctx-categoryᵉ
        ( pᵉ Δᵉ Aᵉ)
        ( comp-hom-Precategoryᵉ ctx-categoryᵉ sᵉ σᵉ)
    sqᵉ =
      equational-reasoningᵉ
        comp-hom-Precategoryᵉ ctx-categoryᵉ σᵉ (id-hom-Precategoryᵉ ctx-categoryᵉ)
          ＝ᵉ σᵉ byᵉ right-unit-law-comp-hom-Precategoryᵉ ctx-categoryᵉ σᵉ
          ＝ᵉ comp-hom-Precategoryᵉ
              ctx-categoryᵉ
              (id-hom-Precategoryᵉ ctx-categoryᵉ)
              σᵉ byᵉ invᵉ (left-unit-law-comp-hom-Precategoryᵉ ctx-categoryᵉ σᵉ)
          ＝ᵉ comp-hom-Precategoryᵉ ctx-categoryᵉ
              (comp-hom-Precategoryᵉ ctx-categoryᵉ (pᵉ Δᵉ Aᵉ) sᵉ)
              σᵉ byᵉ apᵉ (λ kᵉ → comp-hom-Precategoryᵉ ctx-categoryᵉ kᵉ σᵉ) (invᵉ eqᵉ)
          ＝ᵉ comp-hom-Precategoryᵉ ctx-categoryᵉ
              (pᵉ Δᵉ Aᵉ)
              (comp-hom-Precategoryᵉ ctx-categoryᵉ sᵉ σᵉ)
              byᵉ associative-comp-hom-Precategoryᵉ ctx-categoryᵉ _ _ _

    gap-mapᵉ :
      Σᵉ ( Subᵉ Γᵉ (extᵉ Γᵉ (Aᵉ ·ᵉ σᵉ)))
        ( λ gᵉ →
          ( comp-hom-Precategoryᵉ ctx-categoryᵉ (pᵉ Γᵉ (Aᵉ ·ᵉ σᵉ)) gᵉ ＝ᵉ
            id-hom-Precategoryᵉ ctx-categoryᵉ) ×ᵉ
          ( ( comp-hom-Precategoryᵉ ctx-categoryᵉ
              ( pr1ᵉ (pr2ᵉ ext-functorᵉ) (σᵉ ,ᵉ reflᵉ))
              ( gᵉ)) ＝ᵉ
            ( comp-hom-Precategoryᵉ ctx-categoryᵉ sᵉ σᵉ)))
    gap-mapᵉ =
      pr1ᵉ
        ( is-pullback-pᵉ
          ( Γᵉ ,ᵉ (Aᵉ ·ᵉ σᵉ))
          ( Δᵉ ,ᵉ Aᵉ)
          ( σᵉ ,ᵉ reflᵉ)
          ( Γᵉ)
          ( id-hom-Precategoryᵉ ctx-categoryᵉ)
          ( comp-hom-Precategoryᵉ ctx-categoryᵉ sᵉ σᵉ)
          ( sqᵉ))
```