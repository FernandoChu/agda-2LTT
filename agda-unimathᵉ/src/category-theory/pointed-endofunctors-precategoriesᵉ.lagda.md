# Pointed endofunctors

```agda
module category-theory.pointed-endofunctors-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ [endofunctor](category-theory.functors-precategories.mdᵉ) `Fᵉ : Cᵉ → C`ᵉ onᵉ aᵉ
[precategory](category-theory.precategories.mdᵉ) `C`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "pointed"ᵉ Disambiguation="endofunctorᵉ onᵉ aᵉ category"ᵉ Agda=pointed-endofunctor-Precategoryᵉ}}
ifᵉ itᵉ comesᵉ equippedᵉ with aᵉ
[naturalᵉ transformation](category-theory.natural-transformations-functors-precategories.mdᵉ)
`idᵉ ⇒ᵉ F`ᵉ fromᵉ theᵉ identityᵉ [functor](category-theory.functors-precategories.mdᵉ)
to `F`.ᵉ

Moreᵉ explicitly,ᵉ aᵉ
{{#conceptᵉ "pointing"ᵉ Disambiguation="endofunctorᵉ onᵉ aᵉ precategory"ᵉ Agda=pointing-endofunctor-Precategoryᵉ}}
ofᵉ anᵉ endofunctorᵉ `Fᵉ : Cᵉ → C`ᵉ consistsᵉ ofᵉ aᵉ familyᵉ ofᵉ morphismsᵉ `ηᵉ Xᵉ : Xᵉ → Fᵉ X`ᵉ
suchᵉ thatᵉ forᵉ eachᵉ morphismᵉ `fᵉ : Xᵉ → Y`ᵉ in `C`ᵉ theᵉ diagramᵉ

```text
       ηᵉ Xᵉ
    Xᵉ ----->ᵉ Fᵉ Xᵉ
    |         |
  fᵉ |         | Fᵉ fᵉ
    ∨ᵉ         ∨ᵉ
    Yᵉ ----->ᵉ Fᵉ Yᵉ
       ηᵉ Yᵉ
```

[commutes](category-theory.commuting-squares-of-morphisms-in-precategories.md).ᵉ

## Definitions

### The structure of a pointing on an endofunctor on a precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Tᵉ : functor-Precategoryᵉ Cᵉ Cᵉ)
  where

  pointing-endofunctor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  pointing-endofunctor-Precategoryᵉ =
    natural-transformation-Precategoryᵉ Cᵉ Cᵉ (id-functor-Precategoryᵉ Cᵉ) Tᵉ
```

### Pointed endofunctors on a precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  pointed-endofunctor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  pointed-endofunctor-Precategoryᵉ =
    Σᵉ (functor-Precategoryᵉ Cᵉ Cᵉ) (pointing-endofunctor-Precategoryᵉ Cᵉ)

  module _
    (Fᵉ : pointed-endofunctor-Precategoryᵉ)
    where

    functor-pointed-endofunctor-Precategoryᵉ :
      functor-Precategoryᵉ Cᵉ Cᵉ
    functor-pointed-endofunctor-Precategoryᵉ =
      pr1ᵉ Fᵉ

    obj-pointed-endofunctor-Precategoryᵉ : obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Cᵉ
    obj-pointed-endofunctor-Precategoryᵉ =
      obj-functor-Precategoryᵉ Cᵉ Cᵉ functor-pointed-endofunctor-Precategoryᵉ

    hom-pointed-endofunctor-Precategoryᵉ :
      {Xᵉ Yᵉ : obj-Precategoryᵉ Cᵉ} →
      hom-Precategoryᵉ Cᵉ Xᵉ Yᵉ →
      hom-Precategoryᵉ Cᵉ
        ( obj-pointed-endofunctor-Precategoryᵉ Xᵉ)
        ( obj-pointed-endofunctor-Precategoryᵉ Yᵉ)
    hom-pointed-endofunctor-Precategoryᵉ =
      hom-functor-Precategoryᵉ Cᵉ Cᵉ functor-pointed-endofunctor-Precategoryᵉ

    preserves-id-pointed-endofunctor-Precategoryᵉ :
      (Xᵉ : obj-Precategoryᵉ Cᵉ) →
      hom-pointed-endofunctor-Precategoryᵉ (id-hom-Precategoryᵉ Cᵉ {Xᵉ}) ＝ᵉ
      id-hom-Precategoryᵉ Cᵉ
    preserves-id-pointed-endofunctor-Precategoryᵉ =
      preserves-id-functor-Precategoryᵉ Cᵉ Cᵉ
        ( functor-pointed-endofunctor-Precategoryᵉ)

    preserves-comp-pointed-endofunctor-Precategoryᵉ :
      {Xᵉ Yᵉ Zᵉ : obj-Precategoryᵉ Cᵉ}
      (gᵉ : hom-Precategoryᵉ Cᵉ Yᵉ Zᵉ) (fᵉ : hom-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
      hom-pointed-endofunctor-Precategoryᵉ
        ( comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ) ＝ᵉ
      comp-hom-Precategoryᵉ Cᵉ
        ( hom-pointed-endofunctor-Precategoryᵉ gᵉ)
        ( hom-pointed-endofunctor-Precategoryᵉ fᵉ)
    preserves-comp-pointed-endofunctor-Precategoryᵉ =
      preserves-comp-functor-Precategoryᵉ Cᵉ Cᵉ
        ( functor-pointed-endofunctor-Precategoryᵉ)

    pointing-pointed-endofunctor-Precategoryᵉ :
      natural-transformation-Precategoryᵉ Cᵉ Cᵉ
        ( id-functor-Precategoryᵉ Cᵉ)
        ( functor-pointed-endofunctor-Precategoryᵉ)
    pointing-pointed-endofunctor-Precategoryᵉ = pr2ᵉ Fᵉ

    hom-family-pointing-pointed-endofunctor-Precategoryᵉ :
      hom-family-functor-Precategoryᵉ Cᵉ Cᵉ
        ( id-functor-Precategoryᵉ Cᵉ)
        ( functor-pointed-endofunctor-Precategoryᵉ)
    hom-family-pointing-pointed-endofunctor-Precategoryᵉ =
      hom-family-natural-transformation-Precategoryᵉ Cᵉ Cᵉ
        ( id-functor-Precategoryᵉ Cᵉ)
        ( functor-pointed-endofunctor-Precategoryᵉ)
        ( pointing-pointed-endofunctor-Precategoryᵉ)

    naturality-pointing-pointed-endofunctor-Precategoryᵉ :
      is-natural-transformation-Precategoryᵉ Cᵉ Cᵉ
        ( id-functor-Precategoryᵉ Cᵉ)
        ( functor-pointed-endofunctor-Precategoryᵉ)
        ( hom-family-pointing-pointed-endofunctor-Precategoryᵉ)
    naturality-pointing-pointed-endofunctor-Precategoryᵉ =
      naturality-natural-transformation-Precategoryᵉ Cᵉ Cᵉ
        ( id-functor-Precategoryᵉ Cᵉ)
        ( functor-pointed-endofunctor-Precategoryᵉ)
        ( pointing-pointed-endofunctor-Precategoryᵉ)
```