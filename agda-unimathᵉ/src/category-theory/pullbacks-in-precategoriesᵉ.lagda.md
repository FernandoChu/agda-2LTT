# Pullbacks in precategories

```agda
module category-theory.pullbacks-in-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.uniqueness-quantificationᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "pullback"ᵉ Disambiguation="ofᵉ objectsᵉ in precategories"ᵉ Agda=pullback-obj-Precategoryᵉ}}
ofᵉ twoᵉ morphismsᵉ `fᵉ : homᵉ yᵉ x`ᵉ andᵉ `gᵉ : homᵉ zᵉ x`ᵉ in aᵉ categoryᵉ `C`ᵉ consistsᵉ ofᵉ:

-ᵉ anᵉ objectᵉ `w`ᵉ
-ᵉ morphismsᵉ `p₁ᵉ : homᵉ wᵉ y`ᵉ andᵉ `p₂ᵉ : homᵉ wᵉ z`ᵉ suchᵉ thatᵉ
-ᵉ `fᵉ ∘ᵉ p₁ᵉ = gᵉ ∘ᵉ p₂`ᵉ togetherᵉ with theᵉ universalᵉ propertyᵉ thatᵉ forᵉ everyᵉ objectᵉ
  `w'`ᵉ andᵉ pairᵉ ofᵉ morphismsᵉ `p₁'ᵉ : homᵉ w'ᵉ y`ᵉ andᵉ `p₂'ᵉ : homᵉ w'ᵉ z`ᵉ suchᵉ thatᵉ
  `fᵉ ∘ᵉ p₁'ᵉ = gᵉ ∘ᵉ p₂'`ᵉ thereᵉ existsᵉ aᵉ uniqueᵉ morphismᵉ `hᵉ : homᵉ w'ᵉ w`ᵉ suchᵉ thatᵉ
-ᵉ `p₁ᵉ ∘ᵉ hᵉ = p₁'`ᵉ
-ᵉ `p₂ᵉ ∘ᵉ hᵉ = p₂'`.ᵉ

Weᵉ sayᵉ thatᵉ `C`ᵉ
{{#conceptᵉ "hasᵉ allᵉ pullbacks"ᵉ Disambiguation="precategory"ᵉ Agda=has-all-pullback-obj-Precategoryᵉ}}
ifᵉ thereᵉ isᵉ aᵉ choiceᵉ ofᵉ aᵉ pullbackᵉ forᵉ eachᵉ objectᵉ `x`ᵉ andᵉ pairᵉ ofᵉ morphismsᵉ
intoᵉ `x`ᵉ in `C`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-pullback-obj-Precategoryᵉ :
    (xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ) →
    (fᵉ : hom-Precategoryᵉ Cᵉ yᵉ xᵉ) →
    (gᵉ : hom-Precategoryᵉ Cᵉ zᵉ xᵉ) →
    (wᵉ : obj-Precategoryᵉ Cᵉ) →
    (p₁ᵉ : hom-Precategoryᵉ Cᵉ wᵉ yᵉ) →
    (p₂ᵉ : hom-Precategoryᵉ Cᵉ wᵉ zᵉ) →
    comp-hom-Precategoryᵉ Cᵉ fᵉ p₁ᵉ ＝ᵉ comp-hom-Precategoryᵉ Cᵉ gᵉ p₂ᵉ →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-pullback-obj-Precategoryᵉ xᵉ yᵉ zᵉ fᵉ gᵉ wᵉ p₁ᵉ p₂ᵉ _ =
    (w'ᵉ : obj-Precategoryᵉ Cᵉ) →
    (p₁'ᵉ : hom-Precategoryᵉ Cᵉ w'ᵉ yᵉ) →
    (p₂'ᵉ : hom-Precategoryᵉ Cᵉ w'ᵉ zᵉ) →
    comp-hom-Precategoryᵉ Cᵉ fᵉ p₁'ᵉ ＝ᵉ comp-hom-Precategoryᵉ Cᵉ gᵉ p₂'ᵉ →
    uniquely-exists-structureᵉ
      ( hom-Precategoryᵉ Cᵉ w'ᵉ wᵉ)
      ( λ hᵉ →
        ( comp-hom-Precategoryᵉ Cᵉ p₁ᵉ hᵉ ＝ᵉ p₁'ᵉ) ×ᵉ
        ( comp-hom-Precategoryᵉ Cᵉ p₂ᵉ hᵉ ＝ᵉ p₂'ᵉ))

  pullback-obj-Precategoryᵉ :
    (xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ) →
    hom-Precategoryᵉ Cᵉ yᵉ xᵉ →
    hom-Precategoryᵉ Cᵉ zᵉ xᵉ →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  pullback-obj-Precategoryᵉ xᵉ yᵉ zᵉ fᵉ gᵉ =
    Σᵉ (obj-Precategoryᵉ Cᵉ) λ wᵉ →
    Σᵉ (hom-Precategoryᵉ Cᵉ wᵉ yᵉ) λ p₁ᵉ →
    Σᵉ (hom-Precategoryᵉ Cᵉ wᵉ zᵉ) λ p₂ᵉ →
    Σᵉ (comp-hom-Precategoryᵉ Cᵉ fᵉ p₁ᵉ ＝ᵉ comp-hom-Precategoryᵉ Cᵉ gᵉ p₂ᵉ) λ αᵉ →
      is-pullback-obj-Precategoryᵉ xᵉ yᵉ zᵉ fᵉ gᵉ wᵉ p₁ᵉ p₂ᵉ αᵉ

  has-all-pullback-obj-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-all-pullback-obj-Precategoryᵉ =
    (xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ) →
    (fᵉ : hom-Precategoryᵉ Cᵉ yᵉ xᵉ) →
    (gᵉ : hom-Precategoryᵉ Cᵉ zᵉ xᵉ) →
    pullback-obj-Precategoryᵉ xᵉ yᵉ zᵉ fᵉ gᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (tᵉ : has-all-pullback-obj-Precategoryᵉ Cᵉ)
  (xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ)
  (fᵉ : hom-Precategoryᵉ Cᵉ yᵉ xᵉ)
  (gᵉ : hom-Precategoryᵉ Cᵉ zᵉ xᵉ)
  where

  object-pullback-obj-Precategoryᵉ : obj-Precategoryᵉ Cᵉ
  object-pullback-obj-Precategoryᵉ = pr1ᵉ (tᵉ xᵉ yᵉ zᵉ fᵉ gᵉ)

  pr1-pullback-obj-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ object-pullback-obj-Precategoryᵉ yᵉ
  pr1-pullback-obj-Precategoryᵉ = pr1ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ zᵉ fᵉ gᵉ))

  pr2-pullback-obj-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ object-pullback-obj-Precategoryᵉ zᵉ
  pr2-pullback-obj-Precategoryᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ zᵉ fᵉ gᵉ)))

  pullback-square-Precategory-commᵉ :
    comp-hom-Precategoryᵉ Cᵉ fᵉ pr1-pullback-obj-Precategoryᵉ ＝ᵉ
    comp-hom-Precategoryᵉ Cᵉ gᵉ pr2-pullback-obj-Precategoryᵉ
  pullback-square-Precategory-commᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ zᵉ fᵉ gᵉ))))

  module _
    (w'ᵉ : obj-Precategoryᵉ Cᵉ)
    (p₁'ᵉ : hom-Precategoryᵉ Cᵉ w'ᵉ yᵉ)
    (p₂'ᵉ : hom-Precategoryᵉ Cᵉ w'ᵉ zᵉ)
    (αᵉ : comp-hom-Precategoryᵉ Cᵉ fᵉ p₁'ᵉ ＝ᵉ comp-hom-Precategoryᵉ Cᵉ gᵉ p₂'ᵉ)
    where

    morphism-into-pullback-obj-Precategoryᵉ :
      hom-Precategoryᵉ Cᵉ w'ᵉ object-pullback-obj-Precategoryᵉ
    morphism-into-pullback-obj-Precategoryᵉ =
      pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ zᵉ fᵉ gᵉ)))) w'ᵉ p₁'ᵉ p₂'ᵉ αᵉ))

    morphism-into-pullback-comm-pr1ᵉ :
      comp-hom-Precategoryᵉ Cᵉ
        pr1-pullback-obj-Precategoryᵉ
        morphism-into-pullback-obj-Precategoryᵉ ＝ᵉ
      p₁'ᵉ
    morphism-into-pullback-comm-pr1ᵉ =
      pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ zᵉ fᵉ gᵉ)))) w'ᵉ p₁'ᵉ p₂'ᵉ αᵉ)))

    morphism-into-pullback-comm-pr2ᵉ :
      comp-hom-Precategoryᵉ Cᵉ
        pr2-pullback-obj-Precategoryᵉ
        morphism-into-pullback-obj-Precategoryᵉ ＝ᵉ
      p₂'ᵉ
    morphism-into-pullback-comm-pr2ᵉ =
      pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ zᵉ fᵉ gᵉ)))) w'ᵉ p₁'ᵉ p₂'ᵉ αᵉ)))

    is-unique-morphism-into-pullback-obj-Precategoryᵉ :
      (h'ᵉ : hom-Precategoryᵉ Cᵉ w'ᵉ object-pullback-obj-Precategoryᵉ) →
      comp-hom-Precategoryᵉ Cᵉ pr1-pullback-obj-Precategoryᵉ h'ᵉ ＝ᵉ p₁'ᵉ →
      comp-hom-Precategoryᵉ Cᵉ pr2-pullback-obj-Precategoryᵉ h'ᵉ ＝ᵉ p₂'ᵉ →
      morphism-into-pullback-obj-Precategoryᵉ ＝ᵉ h'ᵉ
    is-unique-morphism-into-pullback-obj-Precategoryᵉ h'ᵉ α₁ᵉ α₂ᵉ =
      apᵉ
        ( pr1ᵉ)
        ( pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (tᵉ xᵉ yᵉ zᵉ fᵉ gᵉ)))) w'ᵉ p₁'ᵉ p₂'ᵉ αᵉ) (h'ᵉ ,ᵉ α₁ᵉ ,ᵉ α₂ᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ)
  (fᵉ : hom-Precategoryᵉ Cᵉ yᵉ xᵉ)
  (gᵉ : hom-Precategoryᵉ Cᵉ zᵉ xᵉ)
  (wᵉ : obj-Precategoryᵉ Cᵉ)
  (p₁ᵉ : hom-Precategoryᵉ Cᵉ wᵉ yᵉ)
  (p₂ᵉ : hom-Precategoryᵉ Cᵉ wᵉ zᵉ)
  (αᵉ : comp-hom-Precategoryᵉ Cᵉ fᵉ p₁ᵉ ＝ᵉ comp-hom-Precategoryᵉ Cᵉ gᵉ p₂ᵉ)
  where

  is-prop-is-pullback-obj-Precategoryᵉ :
    is-propᵉ (is-pullback-obj-Precategoryᵉ Cᵉ xᵉ yᵉ zᵉ fᵉ gᵉ wᵉ p₁ᵉ p₂ᵉ αᵉ)
  is-prop-is-pullback-obj-Precategoryᵉ =
    is-prop-iterated-Πᵉ 3
      ( λ w'ᵉ p₁'ᵉ p₂'ᵉ → is-prop-function-typeᵉ is-property-is-contrᵉ)

  is-pullback-prop-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ is-pullback-prop-Precategoryᵉ =
    is-pullback-obj-Precategoryᵉ Cᵉ xᵉ yᵉ zᵉ fᵉ gᵉ wᵉ p₁ᵉ p₂ᵉ αᵉ
  pr2ᵉ is-pullback-prop-Precategoryᵉ =
    is-prop-is-pullback-obj-Precategoryᵉ
```