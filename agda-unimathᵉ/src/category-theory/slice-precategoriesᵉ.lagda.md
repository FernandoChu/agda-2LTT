# Slice precategories

```agda
module category-theory.slice-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ
open import category-theory.products-in-precategoriesᵉ
open import category-theory.pullbacks-in-precategoriesᵉ
open import category-theory.terminal-objects-precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ sliceᵉ precategoryᵉ ofᵉ aᵉ precategoryᵉ `C`ᵉ overᵉ anᵉ objectᵉ `X`ᵉ ofᵉ `C`ᵉ isᵉ theᵉ
categoryᵉ ofᵉ objectsᵉ ofᵉ `C`ᵉ equippedᵉ with aᵉ morphismᵉ intoᵉ `X`.ᵉ

## Definitions

### Objects and morphisms in the slice category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Xᵉ : obj-Precategoryᵉ Cᵉ)
  where

  obj-Slice-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  obj-Slice-Precategoryᵉ =
    Σᵉ (obj-Precategoryᵉ Cᵉ) (λ Aᵉ → hom-Precategoryᵉ Cᵉ Aᵉ Xᵉ)

  hom-set-Slice-Precategoryᵉ :
    obj-Slice-Precategoryᵉ → obj-Slice-Precategoryᵉ → Setᵉ l2ᵉ
  hom-set-Slice-Precategoryᵉ (Aᵉ ,ᵉ fᵉ) (Bᵉ ,ᵉ gᵉ) =
    Σ-Setᵉ
      ( hom-set-Precategoryᵉ Cᵉ Aᵉ Bᵉ)
      ( λ hᵉ →
        set-Propᵉ
          ( Id-Propᵉ (hom-set-Precategoryᵉ Cᵉ Aᵉ Xᵉ) fᵉ (comp-hom-Precategoryᵉ Cᵉ gᵉ hᵉ)))

  hom-Slice-Precategoryᵉ :
    obj-Slice-Precategoryᵉ → obj-Slice-Precategoryᵉ → UUᵉ l2ᵉ
  hom-Slice-Precategoryᵉ Aᵉ Bᵉ = type-Setᵉ (hom-set-Slice-Precategoryᵉ Aᵉ Bᵉ)

  is-set-hom-Slice-Precategoryᵉ :
    (Aᵉ Bᵉ : obj-Slice-Precategoryᵉ) → is-setᵉ (hom-Slice-Precategoryᵉ Aᵉ Bᵉ)
  is-set-hom-Slice-Precategoryᵉ Aᵉ Bᵉ =
    is-set-type-Setᵉ (hom-set-Slice-Precategoryᵉ Aᵉ Bᵉ)

  Eq-hom-Slice-Precategoryᵉ :
    {Aᵉ Bᵉ : obj-Slice-Precategoryᵉ}
    (fᵉ gᵉ : hom-Slice-Precategoryᵉ Aᵉ Bᵉ) → UUᵉ l2ᵉ
  Eq-hom-Slice-Precategoryᵉ fᵉ gᵉ = (pr1ᵉ fᵉ ＝ᵉ pr1ᵉ gᵉ)

  refl-Eq-hom-Slice-Precategoryᵉ :
    {Aᵉ Bᵉ : obj-Slice-Precategoryᵉ} (fᵉ : hom-Slice-Precategoryᵉ Aᵉ Bᵉ) →
    Eq-hom-Slice-Precategoryᵉ fᵉ fᵉ
  refl-Eq-hom-Slice-Precategoryᵉ fᵉ = reflᵉ

  extensionality-hom-Slice-Precategoryᵉ :
    {Aᵉ Bᵉ : obj-Slice-Precategoryᵉ} (fᵉ gᵉ : hom-Slice-Precategoryᵉ Aᵉ Bᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ Eq-hom-Slice-Precategoryᵉ fᵉ gᵉ
  extensionality-hom-Slice-Precategoryᵉ {Aᵉ} {Bᵉ} =
    extensionality-type-subtype'ᵉ
      ( λ hᵉ →
        Id-Propᵉ
          ( hom-set-Precategoryᵉ Cᵉ (pr1ᵉ Aᵉ) Xᵉ)
          ( pr2ᵉ Aᵉ)
          ( comp-hom-Precategoryᵉ Cᵉ (pr2ᵉ Bᵉ) hᵉ))

  eq-hom-Slice-Precategoryᵉ :
    {Aᵉ Bᵉ : obj-Slice-Precategoryᵉ} (fᵉ gᵉ : hom-Slice-Precategoryᵉ Aᵉ Bᵉ) →
    Eq-hom-Slice-Precategoryᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-hom-Slice-Precategoryᵉ fᵉ gᵉ =
    map-inv-equivᵉ (extensionality-hom-Slice-Precategoryᵉ fᵉ gᵉ)
```

### Identity morphisms in the slice category

```agda
  id-hom-Slice-Precategoryᵉ :
    (Aᵉ : obj-Slice-Precategoryᵉ) → hom-Slice-Precategoryᵉ Aᵉ Aᵉ
  pr1ᵉ (id-hom-Slice-Precategoryᵉ Aᵉ) = id-hom-Precategoryᵉ Cᵉ
  pr2ᵉ (id-hom-Slice-Precategoryᵉ Aᵉ) =
    invᵉ (right-unit-law-comp-hom-Precategoryᵉ Cᵉ (pr2ᵉ Aᵉ))
```

### Composition of morphisms in the slice category

```agda
  comp-hom-Slice-Precategoryᵉ :
    {A1ᵉ A2ᵉ A3ᵉ : obj-Slice-Precategoryᵉ} →
    hom-Slice-Precategoryᵉ A2ᵉ A3ᵉ → hom-Slice-Precategoryᵉ A1ᵉ A2ᵉ →
    hom-Slice-Precategoryᵉ A1ᵉ A3ᵉ
  pr1ᵉ (comp-hom-Slice-Precategoryᵉ gᵉ fᵉ) = comp-hom-Precategoryᵉ Cᵉ (pr1ᵉ gᵉ) (pr1ᵉ fᵉ)
  pr2ᵉ (comp-hom-Slice-Precategoryᵉ gᵉ fᵉ) =
    ( pr2ᵉ fᵉ) ∙ᵉ
    ( ( apᵉ (λ uᵉ → comp-hom-Precategoryᵉ Cᵉ uᵉ (pr1ᵉ fᵉ)) (pr2ᵉ gᵉ)) ∙ᵉ
      ( associative-comp-hom-Precategoryᵉ Cᵉ _ (pr1ᵉ gᵉ) (pr1ᵉ fᵉ)))
```

### Associativity of composition of morphisms in the slice category

```agda
  associative-comp-hom-Slice-Precategoryᵉ :
    {A1ᵉ A2ᵉ A3ᵉ A4ᵉ : obj-Slice-Precategoryᵉ} →
    (hᵉ : hom-Slice-Precategoryᵉ A3ᵉ A4ᵉ)
    (gᵉ : hom-Slice-Precategoryᵉ A2ᵉ A3ᵉ)
    (fᵉ : hom-Slice-Precategoryᵉ A1ᵉ A2ᵉ) →
    comp-hom-Slice-Precategoryᵉ (comp-hom-Slice-Precategoryᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Slice-Precategoryᵉ hᵉ (comp-hom-Slice-Precategoryᵉ gᵉ fᵉ)
  associative-comp-hom-Slice-Precategoryᵉ hᵉ gᵉ fᵉ =
    eq-hom-Slice-Precategoryᵉ
      ( comp-hom-Slice-Precategoryᵉ (comp-hom-Slice-Precategoryᵉ hᵉ gᵉ) fᵉ)
      ( comp-hom-Slice-Precategoryᵉ hᵉ (comp-hom-Slice-Precategoryᵉ gᵉ fᵉ))
      ( associative-comp-hom-Precategoryᵉ Cᵉ (pr1ᵉ hᵉ) (pr1ᵉ gᵉ) (pr1ᵉ fᵉ))

  involutive-eq-associative-comp-hom-Slice-Precategoryᵉ :
    {A1ᵉ A2ᵉ A3ᵉ A4ᵉ : obj-Slice-Precategoryᵉ} →
    (hᵉ : hom-Slice-Precategoryᵉ A3ᵉ A4ᵉ)
    (gᵉ : hom-Slice-Precategoryᵉ A2ᵉ A3ᵉ)
    (fᵉ : hom-Slice-Precategoryᵉ A1ᵉ A2ᵉ) →
    comp-hom-Slice-Precategoryᵉ (comp-hom-Slice-Precategoryᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-Slice-Precategoryᵉ hᵉ (comp-hom-Slice-Precategoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Slice-Precategoryᵉ hᵉ gᵉ fᵉ =
    involutive-eq-eqᵉ (associative-comp-hom-Slice-Precategoryᵉ hᵉ gᵉ fᵉ)
```

### The left unit law for composition of morphisms in the slice category

```agda
  left-unit-law-comp-hom-Slice-Precategoryᵉ :
    {Aᵉ Bᵉ : obj-Slice-Precategoryᵉ} (fᵉ : hom-Slice-Precategoryᵉ Aᵉ Bᵉ) →
    comp-hom-Slice-Precategoryᵉ (id-hom-Slice-Precategoryᵉ Bᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Slice-Precategoryᵉ fᵉ =
    eq-hom-Slice-Precategoryᵉ
      ( comp-hom-Slice-Precategoryᵉ (id-hom-Slice-Precategoryᵉ _) fᵉ)
      ( fᵉ)
      ( left-unit-law-comp-hom-Precategoryᵉ Cᵉ (pr1ᵉ fᵉ))
```

### The right unit law for composition of morphisms in the slice category

```agda
  right-unit-law-comp-hom-Slice-Precategoryᵉ :
    {Aᵉ Bᵉ : obj-Slice-Precategoryᵉ} (fᵉ : hom-Slice-Precategoryᵉ Aᵉ Bᵉ) →
    comp-hom-Slice-Precategoryᵉ fᵉ (id-hom-Slice-Precategoryᵉ Aᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Slice-Precategoryᵉ fᵉ =
    eq-hom-Slice-Precategoryᵉ
      ( comp-hom-Slice-Precategoryᵉ fᵉ (id-hom-Slice-Precategoryᵉ _))
      ( fᵉ)
      ( right-unit-law-comp-hom-Precategoryᵉ Cᵉ (pr1ᵉ fᵉ))
```

### The slice precategory

```agda
  Slice-Precategoryᵉ : Precategoryᵉ (l1ᵉ ⊔ l2ᵉ) l2ᵉ
  pr1ᵉ Slice-Precategoryᵉ = obj-Slice-Precategoryᵉ
  pr1ᵉ (pr2ᵉ Slice-Precategoryᵉ) = hom-set-Slice-Precategoryᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ Slice-Precategoryᵉ))) = comp-hom-Slice-Precategoryᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ Slice-Precategoryᵉ))) =
    involutive-eq-associative-comp-hom-Slice-Precategoryᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Slice-Precategoryᵉ))) = id-hom-Slice-Precategoryᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Slice-Precategoryᵉ)))) =
    left-unit-law-comp-hom-Slice-Precategoryᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Slice-Precategoryᵉ)))) =
    right-unit-law-comp-hom-Slice-Precategoryᵉ
```

## Properties

### The slice precategory always has a terminal object

Theᵉ terminalᵉ objectᵉ in theᵉ sliceᵉ (pre-)categoryᵉ `C/X`ᵉ isᵉ theᵉ identityᵉ morphismᵉ
`idᵉ : homᵉ Xᵉ X`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Xᵉ : obj-Precategoryᵉ Cᵉ)
  where

  terminal-obj-Precategory-Slice-Precategoryᵉ :
    terminal-obj-Precategoryᵉ (Slice-Precategoryᵉ Cᵉ Xᵉ)
  pr1ᵉ terminal-obj-Precategory-Slice-Precategoryᵉ = (Xᵉ ,ᵉ id-hom-Precategoryᵉ Cᵉ)
  pr2ᵉ terminal-obj-Precategory-Slice-Precategoryᵉ (Aᵉ ,ᵉ fᵉ) =
    is-contr-equivᵉ
      ( Σᵉ (hom-Precategoryᵉ Cᵉ Aᵉ Xᵉ) (λ gᵉ → fᵉ ＝ᵉ gᵉ))
      ( equiv-totᵉ
        ( λ gᵉ → equiv-concat'ᵉ fᵉ (left-unit-law-comp-hom-Precategoryᵉ Cᵉ gᵉ)))
      ( is-torsorial-Idᵉ fᵉ)
```

### Products in slice precategories are pullbacks in the original category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) {Aᵉ Xᵉ Yᵉ : obj-Precategoryᵉ Cᵉ}
  (fᵉ : hom-Precategoryᵉ Cᵉ Xᵉ Aᵉ) (gᵉ : hom-Precategoryᵉ Cᵉ Yᵉ Aᵉ)
  where

  module _
    {Wᵉ : obj-Precategoryᵉ Cᵉ}
    (p₁ᵉ : hom-Precategoryᵉ Cᵉ Wᵉ Xᵉ) (p₂ᵉ : hom-Precategoryᵉ Cᵉ Wᵉ Yᵉ)
    (pᵉ : hom-Precategoryᵉ Cᵉ Wᵉ Aᵉ)
    (α₁ᵉ : pᵉ ＝ᵉ comp-hom-Precategoryᵉ Cᵉ fᵉ p₁ᵉ)
    (α₂ᵉ : pᵉ ＝ᵉ comp-hom-Precategoryᵉ Cᵉ gᵉ p₂ᵉ)
    (αᵉ : comp-hom-Precategoryᵉ Cᵉ fᵉ p₁ᵉ ＝ᵉ comp-hom-Precategoryᵉ Cᵉ gᵉ p₂ᵉ)
    where

    map-is-pullback-is-product-Slice-Precategoryᵉ :
      is-pullback-obj-Precategoryᵉ Cᵉ Aᵉ Xᵉ Yᵉ fᵉ gᵉ Wᵉ p₁ᵉ p₂ᵉ αᵉ →
      is-product-obj-Precategoryᵉ
        (Slice-Precategoryᵉ Cᵉ Aᵉ) (Xᵉ ,ᵉ fᵉ) (Yᵉ ,ᵉ gᵉ) (Wᵉ ,ᵉ pᵉ) (p₁ᵉ ,ᵉ α₁ᵉ) (p₂ᵉ ,ᵉ α₂ᵉ)
    map-is-pullback-is-product-Slice-Precategoryᵉ
      ϕᵉ (Zᵉ ,ᵉ .(comp-hom-Precategoryᵉ Cᵉ fᵉ h₁ᵉ)) (h₁ᵉ ,ᵉ reflᵉ) (h₂ᵉ ,ᵉ β₂ᵉ) =
      is-contr-Σ-is-propᵉ cᵉ dᵉ qᵉ σᵉ
      where
      cᵉ :
        hom-Precategoryᵉ
          ( Slice-Precategoryᵉ Cᵉ Aᵉ)
          ( Zᵉ ,ᵉ comp-hom-Precategoryᵉ Cᵉ fᵉ h₁ᵉ)
          ( Wᵉ ,ᵉ pᵉ)
      pr1ᵉ cᵉ = pr1ᵉ (pr1ᵉ (ϕᵉ Zᵉ h₁ᵉ h₂ᵉ β₂ᵉ))
      pr2ᵉ cᵉ =
        ( apᵉ
          ( comp-hom-Precategoryᵉ Cᵉ fᵉ)
          ( invᵉ (pr1ᵉ (pr2ᵉ (pr1ᵉ (ϕᵉ Zᵉ h₁ᵉ h₂ᵉ β₂ᵉ)))))) ∙ᵉ
        ( invᵉ (associative-comp-hom-Precategoryᵉ Cᵉ fᵉ p₁ᵉ _) ∙ᵉ
        apᵉ
          ( λ kᵉ → comp-hom-Precategoryᵉ Cᵉ kᵉ (pr1ᵉ (pr1ᵉ (ϕᵉ Zᵉ h₁ᵉ h₂ᵉ β₂ᵉ))))
          ( invᵉ α₁ᵉ))

      dᵉ :
        ( ( comp-hom-Precategoryᵉ (Slice-Precategoryᵉ Cᵉ Aᵉ) (p₁ᵉ ,ᵉ α₁ᵉ) cᵉ) ＝ᵉ
          ( h₁ᵉ ,ᵉ reflᵉ)) ×ᵉ
        ( ( comp-hom-Precategoryᵉ (Slice-Precategoryᵉ Cᵉ Aᵉ) (p₂ᵉ ,ᵉ α₂ᵉ) cᵉ) ＝ᵉ
          ( h₂ᵉ ,ᵉ β₂ᵉ))
      pr1ᵉ dᵉ =
        eq-hom-Slice-Precategoryᵉ Cᵉ Aᵉ _ _ (pr1ᵉ (pr2ᵉ (pr1ᵉ (ϕᵉ Zᵉ h₁ᵉ h₂ᵉ β₂ᵉ))))
      pr2ᵉ dᵉ =
        eq-hom-Slice-Precategoryᵉ Cᵉ Aᵉ _ _ (pr2ᵉ (pr2ᵉ (pr1ᵉ (ϕᵉ Zᵉ h₁ᵉ h₂ᵉ β₂ᵉ))))

      qᵉ :
        (kᵉ :
          hom-Precategoryᵉ
            ( Slice-Precategoryᵉ Cᵉ Aᵉ)
            ( Zᵉ ,ᵉ comp-hom-Precategoryᵉ Cᵉ fᵉ h₁ᵉ)
            ( Wᵉ ,ᵉ pᵉ)) →
        is-propᵉ
          ( ( comp-hom-Precategoryᵉ
              (Slice-Precategoryᵉ Cᵉ Aᵉ) (p₁ᵉ ,ᵉ α₁ᵉ) kᵉ ＝ᵉ (h₁ᵉ ,ᵉ reflᵉ)) ×ᵉ
            ( comp-hom-Precategoryᵉ
              (Slice-Precategoryᵉ Cᵉ Aᵉ) (p₂ᵉ ,ᵉ α₂ᵉ) kᵉ ＝ᵉ (h₂ᵉ ,ᵉ β₂ᵉ)))
      qᵉ kᵉ =
        is-prop-productᵉ
          ( is-set-hom-Slice-Precategoryᵉ Cᵉ Aᵉ _ _ _ _)
          ( is-set-hom-Slice-Precategoryᵉ Cᵉ Aᵉ _ _ _ _)

      σᵉ :
        (kᵉ :
          hom-Precategoryᵉ
            ( Slice-Precategoryᵉ Cᵉ Aᵉ)
            ( Zᵉ ,ᵉ comp-hom-Precategoryᵉ Cᵉ fᵉ h₁ᵉ)
            ( Wᵉ ,ᵉ pᵉ)) →
        ( ( comp-hom-Precategoryᵉ
            ( Slice-Precategoryᵉ Cᵉ Aᵉ)
            ( p₁ᵉ ,ᵉ α₁ᵉ)
            ( kᵉ)) ＝ᵉ
          ( h₁ᵉ ,ᵉ reflᵉ)) ×ᵉ
        ( ( comp-hom-Precategoryᵉ
            ( Slice-Precategoryᵉ Cᵉ Aᵉ)
            ( p₂ᵉ ,ᵉ α₂ᵉ)
            ( kᵉ)) ＝ᵉ
          ( h₂ᵉ ,ᵉ β₂ᵉ)) →
        cᵉ ＝ᵉ kᵉ
      σᵉ (kᵉ ,ᵉ γᵉ) (γ₁ᵉ ,ᵉ γ₂ᵉ) =
        eq-hom-Slice-Precategoryᵉ Cᵉ Aᵉ _ _
          ( apᵉ pr1ᵉ (pr2ᵉ (ϕᵉ Zᵉ h₁ᵉ h₂ᵉ β₂ᵉ) (kᵉ ,ᵉ (apᵉ pr1ᵉ γ₁ᵉ ,ᵉ apᵉ pr1ᵉ γ₂ᵉ))))

    map-inv-is-pullback-is-product-Slice-Precategoryᵉ :
      is-product-obj-Precategoryᵉ
        (Slice-Precategoryᵉ Cᵉ Aᵉ) (Xᵉ ,ᵉ fᵉ) (Yᵉ ,ᵉ gᵉ) (Wᵉ ,ᵉ pᵉ) (p₁ᵉ ,ᵉ α₁ᵉ) (p₂ᵉ ,ᵉ α₂ᵉ) →
      is-pullback-obj-Precategoryᵉ Cᵉ Aᵉ Xᵉ Yᵉ fᵉ gᵉ Wᵉ p₁ᵉ p₂ᵉ αᵉ
    map-inv-is-pullback-is-product-Slice-Precategoryᵉ ψᵉ W'ᵉ p₁'ᵉ p₂'ᵉ α'ᵉ =
      is-contr-Σ-is-propᵉ kᵉ γᵉ qᵉ σᵉ
      where
      kᵉ : hom-Precategoryᵉ Cᵉ W'ᵉ Wᵉ
      kᵉ =
        pr1ᵉ
          ( pr1ᵉ
            ( pr1ᵉ
              ( ψᵉ
                ( W'ᵉ ,ᵉ comp-hom-Precategoryᵉ Cᵉ fᵉ p₁'ᵉ)
                ( p₁'ᵉ ,ᵉ reflᵉ)
                ( p₂'ᵉ ,ᵉ α'ᵉ))))

      γᵉ :
        (comp-hom-Precategoryᵉ Cᵉ p₁ᵉ kᵉ ＝ᵉ p₁'ᵉ) ×ᵉ
        (comp-hom-Precategoryᵉ Cᵉ p₂ᵉ kᵉ ＝ᵉ p₂'ᵉ)
      pr1ᵉ γᵉ =
        apᵉ pr1ᵉ
          ( pr1ᵉ
            ( pr2ᵉ
              ( pr1ᵉ
                ( ψᵉ
                  ( W'ᵉ ,ᵉ comp-hom-Precategoryᵉ Cᵉ fᵉ p₁'ᵉ)
                  ( p₁'ᵉ ,ᵉ reflᵉ)
                  ( p₂'ᵉ ,ᵉ α'ᵉ)))))
      pr2ᵉ γᵉ =
        apᵉ pr1ᵉ
          ( pr2ᵉ
            ( pr2ᵉ
              ( pr1ᵉ
                ( ψᵉ
                  ( W'ᵉ ,ᵉ comp-hom-Precategoryᵉ Cᵉ fᵉ p₁'ᵉ)
                  ( p₁'ᵉ ,ᵉ reflᵉ)
                  ( p₂'ᵉ ,ᵉ α'ᵉ)))))

      qᵉ :
        (k'ᵉ : hom-Precategoryᵉ Cᵉ W'ᵉ Wᵉ) →
        is-propᵉ
          (( comp-hom-Precategoryᵉ Cᵉ p₁ᵉ k'ᵉ ＝ᵉ p₁'ᵉ) ×ᵉ
          ( comp-hom-Precategoryᵉ Cᵉ p₂ᵉ k'ᵉ ＝ᵉ p₂'ᵉ))
      qᵉ k'ᵉ =
        is-prop-productᵉ
          ( is-set-hom-Precategoryᵉ Cᵉ _ _ _ _)
          ( is-set-hom-Precategoryᵉ Cᵉ _ _ _ _)

      σᵉ :
        ( k'ᵉ : hom-Precategoryᵉ Cᵉ W'ᵉ Wᵉ) →
        ( γ'ᵉ :
          ( comp-hom-Precategoryᵉ Cᵉ p₁ᵉ k'ᵉ ＝ᵉ p₁'ᵉ) ×ᵉ
          ( comp-hom-Precategoryᵉ Cᵉ p₂ᵉ k'ᵉ ＝ᵉ p₂'ᵉ)) →
          kᵉ ＝ᵉ k'ᵉ
      σᵉ k'ᵉ (γ₁ᵉ ,ᵉ γ₂ᵉ) =
        apᵉ
          ( pr1ᵉ ∘ᵉ pr1ᵉ)
          ( pr2ᵉ
            ( ψᵉ (W'ᵉ ,ᵉ comp-hom-Precategoryᵉ Cᵉ fᵉ p₁'ᵉ) (p₁'ᵉ ,ᵉ reflᵉ) (p₂'ᵉ ,ᵉ α'ᵉ))
            ( ( ( k'ᵉ) ,ᵉ
                ( ( apᵉ (comp-hom-Precategoryᵉ Cᵉ fᵉ) (invᵉ γ₁ᵉ)) ∙ᵉ
                  ( ( invᵉ (associative-comp-hom-Precategoryᵉ Cᵉ fᵉ p₁ᵉ k'ᵉ)) ∙ᵉ
                    ( apᵉ (λ lᵉ → comp-hom-Precategoryᵉ Cᵉ lᵉ k'ᵉ) (invᵉ α₁ᵉ))))) ,ᵉ
              ( eq-hom-Slice-Precategoryᵉ Cᵉ Aᵉ _ _ γ₁ᵉ) ,ᵉ
              ( eq-hom-Slice-Precategoryᵉ Cᵉ Aᵉ _ _ γ₂ᵉ)))

    equiv-is-pullback-is-product-Slice-Precategoryᵉ :
      is-pullback-obj-Precategoryᵉ Cᵉ Aᵉ Xᵉ Yᵉ fᵉ gᵉ Wᵉ p₁ᵉ p₂ᵉ αᵉ ≃ᵉ
      is-product-obj-Precategoryᵉ
        (Slice-Precategoryᵉ Cᵉ Aᵉ) (Xᵉ ,ᵉ fᵉ) (Yᵉ ,ᵉ gᵉ) (Wᵉ ,ᵉ pᵉ) (p₁ᵉ ,ᵉ α₁ᵉ) (p₂ᵉ ,ᵉ α₂ᵉ)
    equiv-is-pullback-is-product-Slice-Precategoryᵉ =
      equiv-iff-is-propᵉ
        ( is-prop-is-pullback-obj-Precategoryᵉ Cᵉ Aᵉ Xᵉ Yᵉ fᵉ gᵉ Wᵉ p₁ᵉ p₂ᵉ αᵉ)
        ( is-prop-is-product-obj-Precategoryᵉ
          (Slice-Precategoryᵉ Cᵉ Aᵉ) (Xᵉ ,ᵉ fᵉ) (Yᵉ ,ᵉ gᵉ) (Wᵉ ,ᵉ pᵉ) (p₁ᵉ ,ᵉ α₁ᵉ) (p₂ᵉ ,ᵉ α₂ᵉ))
        ( map-is-pullback-is-product-Slice-Precategoryᵉ)
        ( map-inv-is-pullback-is-product-Slice-Precategoryᵉ)

  map-pullback-product-Slice-Precategoryᵉ :
    pullback-obj-Precategoryᵉ Cᵉ Aᵉ Xᵉ Yᵉ fᵉ gᵉ →
    product-obj-Precategoryᵉ (Slice-Precategoryᵉ Cᵉ Aᵉ) (Xᵉ ,ᵉ fᵉ) (Yᵉ ,ᵉ gᵉ)
  pr1ᵉ (map-pullback-product-Slice-Precategoryᵉ (Wᵉ ,ᵉ p₁ᵉ ,ᵉ p₂ᵉ ,ᵉ αᵉ ,ᵉ qᵉ)) =
    (Wᵉ ,ᵉ comp-hom-Precategoryᵉ Cᵉ fᵉ p₁ᵉ)
  pr1ᵉ (pr2ᵉ (map-pullback-product-Slice-Precategoryᵉ (Wᵉ ,ᵉ p₁ᵉ ,ᵉ p₂ᵉ ,ᵉ αᵉ ,ᵉ qᵉ))) =
    (p₁ᵉ ,ᵉ reflᵉ)
  pr1ᵉ
    ( pr2ᵉ
      ( pr2ᵉ (map-pullback-product-Slice-Precategoryᵉ (Wᵉ ,ᵉ p₁ᵉ ,ᵉ p₂ᵉ ,ᵉ αᵉ ,ᵉ qᵉ)))) =
    (p₂ᵉ ,ᵉ αᵉ)
  pr2ᵉ
    ( pr2ᵉ
      ( pr2ᵉ (map-pullback-product-Slice-Precategoryᵉ (Wᵉ ,ᵉ p₁ᵉ ,ᵉ p₂ᵉ ,ᵉ αᵉ ,ᵉ qᵉ)))) =
    map-is-pullback-is-product-Slice-Precategoryᵉ
      p₁ᵉ p₂ᵉ (comp-hom-Precategoryᵉ Cᵉ fᵉ p₁ᵉ) reflᵉ αᵉ αᵉ qᵉ

  map-inv-pullback-product-Slice-Precategoryᵉ :
    product-obj-Precategoryᵉ (Slice-Precategoryᵉ Cᵉ Aᵉ) (Xᵉ ,ᵉ fᵉ) (Yᵉ ,ᵉ gᵉ) →
    pullback-obj-Precategoryᵉ Cᵉ Aᵉ Xᵉ Yᵉ fᵉ gᵉ
  pr1ᵉ (map-inv-pullback-product-Slice-Precategoryᵉ
    ((Zᵉ ,ᵉ hᵉ) ,ᵉ (h₁ᵉ ,ᵉ β₁ᵉ) ,ᵉ (h₂ᵉ ,ᵉ β₂ᵉ) ,ᵉ qᵉ)) = Zᵉ
  pr1ᵉ (pr2ᵉ (map-inv-pullback-product-Slice-Precategoryᵉ
    ((Zᵉ ,ᵉ hᵉ) ,ᵉ (h₁ᵉ ,ᵉ β₁ᵉ) ,ᵉ (h₂ᵉ ,ᵉ β₂ᵉ) ,ᵉ qᵉ))) = h₁ᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (map-inv-pullback-product-Slice-Precategoryᵉ
    ((Zᵉ ,ᵉ hᵉ) ,ᵉ (h₁ᵉ ,ᵉ β₁ᵉ) ,ᵉ (h₂ᵉ ,ᵉ β₂ᵉ) ,ᵉ qᵉ)))) = h₂ᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (map-inv-pullback-product-Slice-Precategoryᵉ
    ((Zᵉ ,ᵉ hᵉ) ,ᵉ (h₁ᵉ ,ᵉ β₁ᵉ) ,ᵉ (h₂ᵉ ,ᵉ β₂ᵉ) ,ᵉ qᵉ))))) = invᵉ β₁ᵉ ∙ᵉ β₂ᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (map-inv-pullback-product-Slice-Precategoryᵉ
    ((Zᵉ ,ᵉ hᵉ) ,ᵉ (h₁ᵉ ,ᵉ β₁ᵉ) ,ᵉ (h₂ᵉ ,ᵉ β₂ᵉ) ,ᵉ qᵉ))))) =
    map-inv-is-pullback-is-product-Slice-Precategoryᵉ h₁ᵉ h₂ᵉ hᵉ β₁ᵉ β₂ᵉ
      ( invᵉ β₁ᵉ ∙ᵉ β₂ᵉ)
      ( qᵉ)

  is-section-map-inv-pullback-product-Slice-Precategoryᵉ :
    ( map-pullback-product-Slice-Precategoryᵉ ∘ᵉ
      map-inv-pullback-product-Slice-Precategoryᵉ) ~ᵉ idᵉ
  is-section-map-inv-pullback-product-Slice-Precategoryᵉ
    ((Zᵉ ,ᵉ .(comp-hom-Precategoryᵉ Cᵉ fᵉ h₁ᵉ)) ,ᵉ (h₁ᵉ ,ᵉ reflᵉ) ,ᵉ (h₂ᵉ ,ᵉ β₂ᵉ) ,ᵉ qᵉ) =
    eq-pair-eq-fiberᵉ
      ( eq-pair-eq-fiberᵉ
        ( eq-type-subtypeᵉ
          ( is-product-prop-Precategoryᵉ
              ( Slice-Precategoryᵉ Cᵉ Aᵉ)
              ( Xᵉ ,ᵉ fᵉ)
              ( Yᵉ ,ᵉ gᵉ)
              ( Zᵉ ,ᵉ comp-hom-Precategoryᵉ Cᵉ fᵉ h₁ᵉ)
              ( h₁ᵉ ,ᵉ reflᵉ))
          ( reflᵉ)))

  is-retraction-map-inv-pullback-product-Slice-Precategoryᵉ :
    ( map-inv-pullback-product-Slice-Precategoryᵉ ∘ᵉ
      map-pullback-product-Slice-Precategoryᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-pullback-product-Slice-Precategoryᵉ
    ( Wᵉ ,ᵉ p₁ᵉ ,ᵉ p₂ᵉ ,ᵉ αᵉ ,ᵉ qᵉ) =
    eq-pair-eq-fiberᵉ
      ( eq-pair-eq-fiberᵉ
          ( eq-pair-eq-fiberᵉ
              ( eq-type-subtypeᵉ
                  ( λ _ → is-pullback-prop-Precategoryᵉ Cᵉ Aᵉ Xᵉ Yᵉ fᵉ gᵉ _ _ _ αᵉ)
                  ( reflᵉ))))

  equiv-pullback-product-Slice-Precategoryᵉ :
    pullback-obj-Precategoryᵉ Cᵉ Aᵉ Xᵉ Yᵉ fᵉ gᵉ ≃ᵉ
    product-obj-Precategoryᵉ (Slice-Precategoryᵉ Cᵉ Aᵉ) (Xᵉ ,ᵉ fᵉ) (Yᵉ ,ᵉ gᵉ)
  pr1ᵉ equiv-pullback-product-Slice-Precategoryᵉ =
    map-pullback-product-Slice-Precategoryᵉ
  pr2ᵉ equiv-pullback-product-Slice-Precategoryᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-pullback-product-Slice-Precategoryᵉ
      is-section-map-inv-pullback-product-Slice-Precategoryᵉ
      is-retraction-map-inv-pullback-product-Slice-Precategoryᵉ
```