# Natural numbers object in a precategory

```agda
module category-theory.natural-numbers-object-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ
open import category-theory.terminal-objects-precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.uniqueness-quantificationᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Letᵉ `C`ᵉ beᵉ aᵉ precategoryᵉ with aᵉ terminalᵉ objectᵉ `t`.ᵉ Aᵉ naturalᵉ numbersᵉ objectᵉ in
`C`ᵉ isᵉ anᵉ objectᵉ `n`ᵉ with morphismsᵉ `zᵉ : homᵉ tᵉ n`ᵉ andᵉ `sᵉ : homᵉ nᵉ n`ᵉ suchᵉ thatᵉ
forᵉ anyᵉ objectᵉ `x`ᵉ andᵉ morphismsᵉ `qᵉ : homᵉ tᵉ x`ᵉ andᵉ `fᵉ : homᵉ xᵉ x`ᵉ thereᵉ existsᵉ aᵉ
uniqueᵉ `uᵉ : homᵉ nᵉ x`ᵉ suchᵉ thatᵉ:

-ᵉ uᵉ ∘ᵉ zᵉ = qᵉ
-ᵉ uᵉ ∘ᵉ sᵉ = fᵉ ∘ᵉ u.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  ((tᵉ ,ᵉ _) : terminal-obj-Precategoryᵉ Cᵉ)
  where

  is-natural-numbers-object-Precategoryᵉ :
    (nᵉ : obj-Precategoryᵉ Cᵉ) →
    hom-Precategoryᵉ Cᵉ tᵉ nᵉ → hom-Precategoryᵉ Cᵉ nᵉ nᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-natural-numbers-object-Precategoryᵉ nᵉ zᵉ sᵉ =
    (xᵉ : obj-Precategoryᵉ Cᵉ)
    (qᵉ : hom-Precategoryᵉ Cᵉ tᵉ xᵉ)
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ xᵉ) →
    uniquely-exists-structureᵉ
      ( hom-Precategoryᵉ Cᵉ nᵉ xᵉ)
      ( λ uᵉ →
        ( comp-hom-Precategoryᵉ Cᵉ uᵉ zᵉ ＝ᵉ qᵉ) ×ᵉ
        ( comp-hom-Precategoryᵉ Cᵉ uᵉ sᵉ ＝ᵉ comp-hom-Precategoryᵉ Cᵉ fᵉ uᵉ))

  natural-numbers-object-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  natural-numbers-object-Precategoryᵉ =
    Σᵉ (obj-Precategoryᵉ Cᵉ) λ nᵉ →
    Σᵉ (hom-Precategoryᵉ Cᵉ tᵉ nᵉ) λ zᵉ →
    Σᵉ (hom-Precategoryᵉ Cᵉ nᵉ nᵉ) λ sᵉ →
      is-natural-numbers-object-Precategoryᵉ nᵉ zᵉ sᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  ((tᵉ ,ᵉ pᵉ) : terminal-obj-Precategoryᵉ Cᵉ)
  (nnoᵉ : natural-numbers-object-Precategoryᵉ Cᵉ (tᵉ ,ᵉ pᵉ))
  where

  object-natural-numbers-object-Precategoryᵉ : obj-Precategoryᵉ Cᵉ
  object-natural-numbers-object-Precategoryᵉ = pr1ᵉ nnoᵉ

  zero-natural-numbers-object-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ tᵉ object-natural-numbers-object-Precategoryᵉ
  zero-natural-numbers-object-Precategoryᵉ = pr1ᵉ (pr2ᵉ nnoᵉ)

  succ-natural-numbers-object-Precategoryᵉ :
    hom-Precategoryᵉ Cᵉ
      ( object-natural-numbers-object-Precategoryᵉ)
      ( object-natural-numbers-object-Precategoryᵉ)
  succ-natural-numbers-object-Precategoryᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ nnoᵉ))

  module _
    (xᵉ : obj-Precategoryᵉ Cᵉ)
    (qᵉ : hom-Precategoryᵉ Cᵉ tᵉ xᵉ)
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ xᵉ)
    where

    morphism-natural-numbers-object-Precategoryᵉ :
      hom-Precategoryᵉ Cᵉ object-natural-numbers-object-Precategoryᵉ xᵉ
    morphism-natural-numbers-object-Precategoryᵉ =
      pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ nnoᵉ)) xᵉ qᵉ fᵉ))

    morphism-natural-numbers-object-Precategory-zero-commᵉ :
      comp-hom-Precategoryᵉ Cᵉ morphism-natural-numbers-object-Precategoryᵉ
        ( zero-natural-numbers-object-Precategoryᵉ) ＝ᵉ qᵉ
    morphism-natural-numbers-object-Precategory-zero-commᵉ =
      pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ nnoᵉ)) xᵉ qᵉ fᵉ)))

    morphism-natural-numbers-object-Precategory-succ-commᵉ :
      comp-hom-Precategoryᵉ
        ( Cᵉ)
        ( morphism-natural-numbers-object-Precategoryᵉ)
        ( succ-natural-numbers-object-Precategoryᵉ) ＝ᵉ
      comp-hom-Precategoryᵉ (Cᵉ) (fᵉ) (morphism-natural-numbers-object-Precategoryᵉ)
    morphism-natural-numbers-object-Precategory-succ-commᵉ =
      pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ nnoᵉ)) xᵉ qᵉ fᵉ)))

    is-unique-morphism-natural-numbers-object-Precategoryᵉ :
      ( u'ᵉ :
        hom-Precategoryᵉ Cᵉ object-natural-numbers-object-Precategoryᵉ xᵉ) →
      comp-hom-Precategoryᵉ Cᵉ u'ᵉ zero-natural-numbers-object-Precategoryᵉ ＝ᵉ qᵉ →
      comp-hom-Precategoryᵉ Cᵉ u'ᵉ succ-natural-numbers-object-Precategoryᵉ ＝ᵉ
      comp-hom-Precategoryᵉ Cᵉ fᵉ u'ᵉ →
      morphism-natural-numbers-object-Precategoryᵉ ＝ᵉ u'ᵉ
    is-unique-morphism-natural-numbers-object-Precategoryᵉ u'ᵉ αᵉ βᵉ =
      apᵉ pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ nnoᵉ)) xᵉ qᵉ fᵉ) (u'ᵉ ,ᵉ αᵉ ,ᵉ βᵉ))
```