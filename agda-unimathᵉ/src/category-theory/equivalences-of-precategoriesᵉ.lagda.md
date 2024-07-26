# Equivalences between precategories

```agda
module category-theory.equivalences-of-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.natural-isomorphisms-functors-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [functor](category-theory.functors-precategories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ isᵉ anᵉ
**equivalence**ᵉ ofᵉ [precategories](category-theory.precategories.mdᵉ) ifᵉ thereᵉ isᵉ

1.ᵉ aᵉ functorᵉ `Gᵉ : Dᵉ → C`ᵉ suchᵉ thatᵉ `Gᵉ ∘ᵉ F`ᵉ isᵉ
   [naturallyᵉ isomorphic](category-theory.natural-isomorphisms-functors-precategories.mdᵉ)
   to theᵉ identityᵉ functorᵉ onᵉ `C`,ᵉ
2.ᵉ aᵉ functorᵉ `Hᵉ : Dᵉ → C`ᵉ suchᵉ thatᵉ `Fᵉ ∘ᵉ H`ᵉ isᵉ naturallyᵉ isomorphicᵉ to theᵉ
   identityᵉ functorᵉ onᵉ `D`.ᵉ

## Definition

### The predicate on functors of being an equivalence of precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  is-equiv-functor-Precategoryᵉ :
    functor-Precategoryᵉ Cᵉ Dᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-equiv-functor-Precategoryᵉ Fᵉ =
    Σᵉ ( functor-Precategoryᵉ Dᵉ Cᵉ)
      ( λ Gᵉ →
        ( natural-isomorphism-Precategoryᵉ Cᵉ Cᵉ
          ( comp-functor-Precategoryᵉ Cᵉ Dᵉ Cᵉ Gᵉ Fᵉ)
          ( id-functor-Precategoryᵉ Cᵉ))) ×ᵉ
    Σᵉ ( functor-Precategoryᵉ Dᵉ Cᵉ)
      ( λ Hᵉ →
        ( natural-isomorphism-Precategoryᵉ Dᵉ Dᵉ
          ( comp-functor-Precategoryᵉ Dᵉ Cᵉ Dᵉ Fᵉ Hᵉ)
          ( id-functor-Precategoryᵉ Dᵉ)))
```

### The type of equivalences of precategories

```agda
  equiv-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  equiv-Precategoryᵉ = Σᵉ (functor-Precategoryᵉ Cᵉ Dᵉ) (is-equiv-functor-Precategoryᵉ)
```