# Representable functors between large precategories

```agda
module category-theory.representable-functors-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.natural-transformations-functors-large-precategoriesᵉ

open import foundation.category-of-setsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [largeᵉ precategory](category-theory.large-precategories.mdᵉ) `C`ᵉ andᵉ anᵉ
objectᵉ `c`,ᵉ thereᵉ isᵉ aᵉ
[functor](category-theory.functors-large-precategories.mdᵉ) fromᵉ `C`ᵉ to theᵉ
[precategoryᵉ ofᵉ sets](foundation.category-of-sets.mdᵉ) **represented**ᵉ byᵉ `c`ᵉ
thatᵉ:

-ᵉ sendsᵉ anᵉ objectᵉ `x`ᵉ ofᵉ `C`ᵉ to theᵉ [set](foundation-core.sets.mdᵉ) `homᵉ cᵉ x`ᵉ andᵉ
-ᵉ sendsᵉ aᵉ morphismᵉ `gᵉ : homᵉ xᵉ y`ᵉ ofᵉ `C`ᵉ to theᵉ functionᵉ `homᵉ cᵉ xᵉ → homᵉ cᵉ y`ᵉ
  definedᵉ byᵉ postcompositionᵉ with `g`.ᵉ

Theᵉ functorialityᵉ axiomsᵉ follow,ᵉ byᵉ
[functionᵉ extensionality](foundation.function-extensionality.md),ᵉ fromᵉ
associativityᵉ andᵉ theᵉ leftᵉ unitᵉ lawᵉ forᵉ theᵉ precategoryᵉ `C`.ᵉ

## Definition

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ : Level} (cᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ)
  where

  obj-representable-functor-Large-Precategoryᵉ :
    {l2ᵉ : Level} (xᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ) → Setᵉ (βᵉ l1ᵉ l2ᵉ)
  obj-representable-functor-Large-Precategoryᵉ =
    hom-set-Large-Precategoryᵉ Cᵉ cᵉ

  hom-representable-functor-Large-Precategoryᵉ :
    {l2ᵉ l3ᵉ : Level}
    {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ} →
    hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ →
    hom-Setᵉ
      ( obj-representable-functor-Large-Precategoryᵉ Xᵉ)
      ( obj-representable-functor-Large-Precategoryᵉ Yᵉ)
  hom-representable-functor-Large-Precategoryᵉ =
    postcomp-hom-Large-Precategoryᵉ Cᵉ cᵉ

  preserves-comp-representable-functor-Large-Precategoryᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level}
    {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
    {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ}
    {Zᵉ : obj-Large-Precategoryᵉ Cᵉ l4ᵉ}
    (gᵉ : hom-Large-Precategoryᵉ Cᵉ Yᵉ Zᵉ)
    (fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
    hom-representable-functor-Large-Precategoryᵉ
      ( comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ) ＝ᵉ
    hom-representable-functor-Large-Precategoryᵉ gᵉ ∘ᵉ
    hom-representable-functor-Large-Precategoryᵉ fᵉ
  preserves-comp-representable-functor-Large-Precategoryᵉ gᵉ fᵉ =
    eq-htpyᵉ (associative-comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ)

  preserves-id-representable-functor-Large-Precategoryᵉ :
    {l2ᵉ : Level} {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ} →
    hom-representable-functor-Large-Precategoryᵉ
      ( id-hom-Large-Precategoryᵉ Cᵉ {Xᵉ = Xᵉ}) ＝ᵉ
    idᵉ
  preserves-id-representable-functor-Large-Precategoryᵉ =
    eq-htpyᵉ (left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ)

  representable-functor-Large-Precategoryᵉ :
    functor-Large-Precategoryᵉ (βᵉ l1ᵉ) Cᵉ (Set-Large-Precategoryᵉ)
  obj-functor-Large-Precategoryᵉ representable-functor-Large-Precategoryᵉ =
    obj-representable-functor-Large-Precategoryᵉ
  hom-functor-Large-Precategoryᵉ representable-functor-Large-Precategoryᵉ =
    hom-representable-functor-Large-Precategoryᵉ
  preserves-comp-functor-Large-Precategoryᵉ
    representable-functor-Large-Precategoryᵉ =
    preserves-comp-representable-functor-Large-Precategoryᵉ
  preserves-id-functor-Large-Precategoryᵉ
    representable-functor-Large-Precategoryᵉ =
    preserves-id-representable-functor-Large-Precategoryᵉ
```

## Natural transformations between representable functors

Aᵉ morphismᵉ `fᵉ : homᵉ bᵉ c`ᵉ in aᵉ largeᵉ precategoryᵉ `C`ᵉ definesᵉ aᵉ
[naturalᵉ transformation](category-theory.natural-transformations-functors-large-precategories.mdᵉ)
fromᵉ theᵉ functorᵉ representedᵉ byᵉ `c`ᵉ to theᵉ functorᵉ representedᵉ byᵉ `b`.ᵉ Itsᵉ
componentsᵉ `homᵉ cᵉ xᵉ → homᵉ bᵉ x`ᵉ areᵉ definedᵉ byᵉ precompositionᵉ with `f`.ᵉ

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  {l1ᵉ l2ᵉ : Level}
  (bᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) (cᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ)
  (fᵉ : hom-Large-Precategoryᵉ Cᵉ bᵉ cᵉ)
  where

  hom-representable-natural-transformation-Large-Precategoryᵉ :
    family-of-morphisms-functor-Large-Precategoryᵉ Cᵉ Set-Large-Precategoryᵉ
      ( representable-functor-Large-Precategoryᵉ Cᵉ cᵉ)
      ( representable-functor-Large-Precategoryᵉ Cᵉ bᵉ)
  hom-representable-natural-transformation-Large-Precategoryᵉ =
    precomp-hom-Large-Precategoryᵉ Cᵉ fᵉ

  naturality-representable-natural-transformation-Large-Precategoryᵉ :
    naturality-family-of-morphisms-functor-Large-Precategoryᵉ Cᵉ
      ( Set-Large-Precategoryᵉ)
      ( representable-functor-Large-Precategoryᵉ Cᵉ cᵉ)
      ( representable-functor-Large-Precategoryᵉ Cᵉ bᵉ)
      ( hom-representable-natural-transformation-Large-Precategoryᵉ)
  naturality-representable-natural-transformation-Large-Precategoryᵉ hᵉ =
    invᵉ (eq-htpyᵉ (λ gᵉ → associative-comp-hom-Large-Precategoryᵉ Cᵉ hᵉ gᵉ fᵉ))

  representable-natural-transformation-Large-Precategoryᵉ :
    natural-transformation-Large-Precategoryᵉ Cᵉ Set-Large-Precategoryᵉ
      ( representable-functor-Large-Precategoryᵉ Cᵉ cᵉ)
      ( representable-functor-Large-Precategoryᵉ Cᵉ bᵉ)
  hom-natural-transformation-Large-Precategoryᵉ
    representable-natural-transformation-Large-Precategoryᵉ =
    hom-representable-natural-transformation-Large-Precategoryᵉ
  naturality-natural-transformation-Large-Precategoryᵉ
    representable-natural-transformation-Large-Precategoryᵉ =
    naturality-representable-natural-transformation-Large-Precategoryᵉ
```