# Equivalences between large precategories

```agda
module category-theory.equivalences-of-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.natural-isomorphisms-functors-large-precategoriesᵉ

open import foundation.universe-levelsᵉ
```

</details>

## Idea

Twoᵉ [largeᵉ precategories](category-theory.large-precategories.mdᵉ) `C`ᵉ andᵉ `D`ᵉ
areᵉ saidᵉ to beᵉ **equivalent**ᵉ ifᵉ thereᵉ areᵉ
[functors](category-theory.functors-large-precategories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ andᵉ
`Gᵉ : Dᵉ → C`ᵉ suchᵉ thatᵉ

-ᵉ `Gᵉ ∘ᵉ F`ᵉ isᵉ
  [naturallyᵉ isomorphic](category-theory.natural-isomorphisms-functors-large-precategories.mdᵉ)
  to theᵉ identityᵉ functorᵉ onᵉ `C`,ᵉ
-ᵉ `Fᵉ ∘ᵉ G`ᵉ isᵉ naturallyᵉ isomorphicᵉ to theᵉ identityᵉ functorᵉ onᵉ `D`.ᵉ

## Definition

```agda
module _
  {αCᵉ αDᵉ : Level → Level} {βCᵉ βDᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ) (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  where

  record
    equivalence-Large-Precategoryᵉ (γᵉ γ'ᵉ : Level → Level) : UUωᵉ where
    constructor
      make-equivalence-Large-Precategoryᵉ
    field
      functor-equivalence-Large-Precategoryᵉ :
        functor-Large-Precategoryᵉ γᵉ Cᵉ Dᵉ
      functor-inv-equivalence-Large-Precategoryᵉ :
        functor-Large-Precategoryᵉ γ'ᵉ Dᵉ Cᵉ
      is-section-functor-inv-equivalence-Large-Precategoryᵉ :
        natural-isomorphism-Large-Precategoryᵉ
          ( comp-functor-Large-Precategoryᵉ Dᵉ Cᵉ Dᵉ
            functor-equivalence-Large-Precategoryᵉ
            functor-inv-equivalence-Large-Precategoryᵉ)
          ( id-functor-Large-Precategoryᵉ Dᵉ)
      is-retraction-functor-inv-equivalence-Large-Precategoryᵉ :
        natural-isomorphism-Large-Precategoryᵉ
          ( comp-functor-Large-Precategoryᵉ Cᵉ Dᵉ Cᵉ
            functor-inv-equivalence-Large-Precategoryᵉ
            functor-equivalence-Large-Precategoryᵉ)
          ( id-functor-Large-Precategoryᵉ Cᵉ)
```