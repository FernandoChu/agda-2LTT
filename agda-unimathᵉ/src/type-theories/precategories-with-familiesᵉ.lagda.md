# Precategories with families

```agda
module type-theories.precategories-with-familiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ
open import category-theory.opposite-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.precategory-of-elements-of-a-presheafᵉ
open import category-theory.presheaf-categoriesᵉ
open import category-theory.pullbacks-in-precategoriesᵉ

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

Aᵉ **precategoryᵉ with families**ᵉ consistsᵉ ofᵉ:

-ᵉ aᵉ [precategory](category-theory.precategories.mdᵉ) `C`,ᵉ whichᵉ weᵉ thinkᵉ ofᵉ asᵉ aᵉ
  categoryᵉ ofᵉ contextsᵉ andᵉ contextᵉ morphismsᵉ
-ᵉ aᵉ [presheaf](category-theory.presheaf-categories.mdᵉ) `Ty`ᵉ onᵉ `C`,ᵉ whichᵉ weᵉ
  thinkᵉ ofᵉ asᵉ givingᵉ theᵉ typesᵉ in eachᵉ contextᵉ
-ᵉ aᵉ [presheaf](category-theory.presheaf-categories.mdᵉ) `Tm`ᵉ onᵉ `∫ᵉ Ty`,ᵉ whichᵉ weᵉ
  thinkᵉ ofᵉ asᵉ givingᵉ theᵉ termsᵉ ofᵉ eachᵉ typeᵉ in eachᵉ contextᵉ
-ᵉ aᵉ [functor](category-theory.functors-precategories.mdᵉ) `ext`ᵉ fromᵉ `∫ᵉ Ty`ᵉ to
  `C`,ᵉ whichᵉ weᵉ thinkᵉ ofᵉ asᵉ contextᵉ extensionᵉ suchᵉ thatᵉ
-ᵉ forᵉ everyᵉ pairᵉ ofᵉ contextsᵉ `Γ`ᵉ andᵉ `Δ`,ᵉ andᵉ typesᵉ `A`ᵉ in contextᵉ `Γ`,ᵉ thereᵉ isᵉ
  anᵉ equivalenceᵉ betweenᵉ theᵉ typeᵉ ofᵉ contextᵉ morphismsᵉ fromᵉ `Δ`ᵉ to `Γ`ᵉ extendedᵉ
  byᵉ `A`,ᵉ andᵉ theᵉ typeᵉ ofᵉ contextᵉ morphismsᵉ fromᵉ `Δ`ᵉ to `Γ`ᵉ togetherᵉ with termsᵉ
  ofᵉ `A`.ᵉ

## Definitions

### Precategories with families

```agda
record
  Precategory-With-Familiesᵉ
    (l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level) :
    UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ)
  where

  field
    ctx-categoryᵉ : Precategoryᵉ l1ᵉ l2ᵉ

  Ctxᵉ : UUᵉ l1ᵉ
  Ctxᵉ = obj-Precategoryᵉ ctx-categoryᵉ

  Subᵉ : Ctxᵉ → Ctxᵉ → UUᵉ l2ᵉ
  Subᵉ = hom-Precategoryᵉ ctx-categoryᵉ

  field
    ty-presheafᵉ : presheaf-Precategoryᵉ ctx-categoryᵉ l3ᵉ

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

  Tyᵉ : Ctxᵉ → UUᵉ l3ᵉ
  Tyᵉ = element-presheaf-Precategoryᵉ ctx-categoryᵉ ty-presheafᵉ

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
    tm-presheafᵉ : presheaf-Precategoryᵉ ∫Tyᵉ l4ᵉ

  Tmᵉ : (Γᵉ : Ctxᵉ) (Aᵉ : Tyᵉ Γᵉ) → UUᵉ l4ᵉ
  Tmᵉ Γᵉ Aᵉ = element-presheaf-Precategoryᵉ ∫Tyᵉ tm-presheafᵉ (Γᵉ ,ᵉ Aᵉ)

  _[ᵉ_] :
    {Δᵉ Γᵉ : Ctxᵉ} {Aᵉ : Tyᵉ Γᵉ} (Mᵉ : Tmᵉ Γᵉ Aᵉ) (γᵉ : Subᵉ Δᵉ Γᵉ) → Tmᵉ Δᵉ (Aᵉ ·ᵉ γᵉ)
  _[ᵉ_] {Δᵉ} {Γᵉ} {Aᵉ} Mᵉ γᵉ =
    action-presheaf-Precategoryᵉ ∫Tyᵉ tm-presheafᵉ (γᵉ ,ᵉ reflᵉ) Mᵉ

  field
    ext-functorᵉ : functor-Precategoryᵉ ∫Tyᵉ ctx-categoryᵉ

  extᵉ : (Γᵉ : Ctxᵉ) (Aᵉ : Tyᵉ Γᵉ) → Ctxᵉ
  extᵉ Γᵉ Aᵉ = obj-functor-Precategoryᵉ ∫Tyᵉ ctx-categoryᵉ ext-functorᵉ (Γᵉ ,ᵉ Aᵉ)

  field
    ext-isoᵉ :
      (Δᵉ Γᵉ : Ctxᵉ) (Aᵉ : Tyᵉ Γᵉ) →
      Subᵉ Δᵉ (extᵉ Γᵉ Aᵉ) ≃ᵉ Σᵉ (Subᵉ Δᵉ Γᵉ) (λ γᵉ → Tmᵉ Δᵉ (Aᵉ ·ᵉ γᵉ))

  ext-subᵉ :
    {Δᵉ Γᵉ : Ctxᵉ} (Aᵉ : Tyᵉ Γᵉ) (γᵉ : Subᵉ Δᵉ Γᵉ) → Tmᵉ Δᵉ (Aᵉ ·ᵉ γᵉ) → Subᵉ Δᵉ (extᵉ Γᵉ Aᵉ)
  ext-subᵉ {Δᵉ} {Γᵉ} Aᵉ γᵉ Mᵉ = map-inv-equivᵉ (ext-isoᵉ Δᵉ Γᵉ Aᵉ) (γᵉ ,ᵉ Mᵉ)

  wkᵉ : {Γᵉ : Ctxᵉ} (Aᵉ : Tyᵉ Γᵉ) → Subᵉ (extᵉ Γᵉ Aᵉ) Γᵉ
  wkᵉ {Γᵉ} Aᵉ =
    pr1ᵉ (map-equivᵉ (ext-isoᵉ (extᵉ Γᵉ Aᵉ) Γᵉ Aᵉ) (id-hom-Precategoryᵉ ctx-categoryᵉ))

  qᵉ : {Γᵉ : Ctxᵉ} (Aᵉ : Tyᵉ Γᵉ) → Tmᵉ (extᵉ Γᵉ Aᵉ) (Aᵉ ·ᵉ wkᵉ Aᵉ)
  qᵉ {Γᵉ} Aᵉ =
    pr2ᵉ (map-equivᵉ (ext-isoᵉ (extᵉ Γᵉ Aᵉ) Γᵉ Aᵉ) (id-hom-Precategoryᵉ ctx-categoryᵉ))

  ⟨_,_⟩ᵉ :
    {Δᵉ Γᵉ : Ctxᵉ} (γᵉ : Subᵉ Δᵉ Γᵉ) (Aᵉ : Tyᵉ Γᵉ) → Subᵉ (extᵉ Δᵉ (Aᵉ ·ᵉ γᵉ)) (extᵉ Γᵉ Aᵉ)
  ⟨_,_⟩ᵉ {Δᵉ} {Γᵉ} γᵉ Aᵉ =
    ext-subᵉ
      ( Aᵉ)
      ( comp-hom-Precategoryᵉ ctx-categoryᵉ γᵉ (wkᵉ (Aᵉ ·ᵉ γᵉ)))
      ( trᵉ
        ( Tmᵉ (extᵉ Δᵉ (Aᵉ ·ᵉ γᵉ)))
        ( invᵉ (preserves-comp-Tyᵉ Aᵉ γᵉ (wkᵉ (Aᵉ ·ᵉ γᵉ))))
        ( qᵉ (Aᵉ ·ᵉ γᵉ)))
```