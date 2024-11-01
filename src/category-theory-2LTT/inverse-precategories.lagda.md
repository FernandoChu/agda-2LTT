# Inverse categories

```agda
module category-theory-2LTT.inverse-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.opposite-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.binary-transportᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

An inverse category is the categorification of the notion of an inverted well
order.

## Definitions

### Reflecting identities

```agda
is-id-Precategoryᵉ :
  {l1 l2 : Level}
  (C : Precategoryᵉ l1 l2)
  (x : obj-Precategoryᵉ C)
  (f : hom-Precategoryᵉ C x x) →
  UUᵉ l2
is-id-Precategoryᵉ C x f =
  f ＝ᵉ id-hom-Precategoryᵉ C

module _
  {l1 l2 l3 l4 : Level} (C : Precategoryᵉ l1 l2) (D : Precategoryᵉ l3 l4)
  (F : functor-Precategoryᵉ C D)
  where

  reflects-id-functor-Precategoryᵉ : UUᵉ (l1 ⊔ l2 ⊔ l4)
  reflects-id-functor-Precategoryᵉ =
    {x : obj-Precategoryᵉ C} (f : hom-Precategoryᵉ C x x) →
    is-id-Precategoryᵉ D
      ( obj-functor-Precategoryᵉ C D F x)
      ( hom-functor-Precategoryᵉ C D F f) →
    is-id-Precategoryᵉ C x f
```

### Inverse categories

```agda
module _
  {l1 l2 : Level} (C : Precategoryᵉ l1 l2)
  where

  is-inverse-Precategoryᵉ : UUᵉ (l1 ⊔ l2)
  is-inverse-Precategoryᵉ =
    Σᵉ ( functor-Precategoryᵉ (opposite-Precategoryᵉ C) ℕ-Precategoryᵉ)
      ( λ F →
        reflects-id-functor-Precategoryᵉ
          ( opposite-Precategoryᵉ C)
          ( ℕ-Precategoryᵉ)
          ( F))

Inverse-Precategoryᵉ :
  (l1 l2 : Level) → UUᵉ (lsuc (l1 ⊔ l2))
Inverse-Precategoryᵉ l1 l2 =
  Σᵉ ( Precategoryᵉ l1 l2)
    ( λ C → is-inverse-Precategoryᵉ C)

module _
  {l1 l2 : Level} (C : Inverse-Precategoryᵉ l1 l2)
  where

  precategory-Inverse-Precategoryᵉ : Precategoryᵉ l1 l2
  precategory-Inverse-Precategoryᵉ = pr1ᵉ C

  hom-Inverse-Precategoryᵉ :
    obj-Precategoryᵉ precategory-Inverse-Precategoryᵉ →
    obj-Precategoryᵉ precategory-Inverse-Precategoryᵉ →
    UUᵉ l2
  hom-Inverse-Precategoryᵉ = hom-Precategoryᵉ precategory-Inverse-Precategoryᵉ

  is-inverse-Inverse-Precategoryᵉ :
    is-inverse-Precategoryᵉ precategory-Inverse-Precategoryᵉ
  is-inverse-Inverse-Precategoryᵉ = pr2ᵉ C

  rank-functor-Inverse-Precategoryᵉ :
    functor-Precategoryᵉ
      (opposite-Precategoryᵉ precategory-Inverse-Precategoryᵉ)
      ℕ-Precategoryᵉ
  rank-functor-Inverse-Precategoryᵉ = pr1ᵉ is-inverse-Inverse-Precategoryᵉ

  obj-rank-functor-Inverse-Precategoryᵉ :
    obj-Precategoryᵉ (opposite-Precategoryᵉ precategory-Inverse-Precategoryᵉ) →
    obj-Precategoryᵉ ℕ-Precategoryᵉ
  obj-rank-functor-Inverse-Precategoryᵉ =
    obj-functor-Precategoryᵉ
      (opposite-Precategoryᵉ precategory-Inverse-Precategoryᵉ)
      ℕ-Precategoryᵉ
      rank-functor-Inverse-Precategoryᵉ

  hom-rank-functor-Inverse-Precategoryᵉ :
    { x y :
      obj-Precategoryᵉ
        ( opposite-Precategoryᵉ precategory-Inverse-Precategoryᵉ)} →
      hom-Inverse-Precategoryᵉ y x →
      hom-Precategoryᵉ
        ℕ-Precategoryᵉ
        ( obj-rank-functor-Inverse-Precategoryᵉ x)
        ( obj-rank-functor-Inverse-Precategoryᵉ y)
  hom-rank-functor-Inverse-Precategoryᵉ =
    hom-functor-Precategoryᵉ
      (opposite-Precategoryᵉ precategory-Inverse-Precategoryᵉ)
      ℕ-Precategoryᵉ
      rank-functor-Inverse-Precategoryᵉ

  reflects-id-rank-functor-Inverse-Precategoryᵉ :
    reflects-id-functor-Precategoryᵉ
      (opposite-Precategoryᵉ precategory-Inverse-Precategoryᵉ)
      ℕ-Precategoryᵉ
      rank-functor-Inverse-Precategoryᵉ
  reflects-id-rank-functor-Inverse-Precategoryᵉ =
    pr2ᵉ is-inverse-Inverse-Precategoryᵉ

  has-height : ℕᵉ → UUᵉ l1
  has-height n =
    (a : obj-Precategoryᵉ precategory-Inverse-Precategoryᵉ) →
    succ-ℕᵉ (obj-rank-functor-Inverse-Precategoryᵉ a) ≤-ℕᵉ n
```

### Ranked sorts

```agda
record ranked-sort
  {l1 l2 : Level} (C : Inverse-Precategoryᵉ l1 l2) (n : ℕᵉ) : UUᵉ l1 where
  field
    sort-ranked-sort : obj-Precategoryᵉ (precategory-Inverse-Precategoryᵉ C)
    is-ranked-sort-ranked-sort :
      obj-rank-functor-Inverse-Precategoryᵉ C sort-ranked-sort ＝ᵉ n

open ranked-sort public

preserves-order-hom-ranked-sort :
  {l1 l2 : Level} {C : Inverse-Precategoryᵉ l1 l2} {n m : ℕᵉ}
  (K : ranked-sort C n) (K' : ranked-sort C m) →
  hom-Inverse-Precategoryᵉ C (sort-ranked-sort K) (sort-ranked-sort K') →
  leq-ℕᵉ m n
preserves-order-hom-ranked-sort {C = C} K K' f =
  binary-trᵉ
    ( hom-Precategoryᵉ ℕ-Precategoryᵉ)
    ( is-ranked-sort-ranked-sort K')
    ( is-ranked-sort-ranked-sort K)
    ( hom-rank-functor-Inverse-Precategoryᵉ C f)
```

### Fanouts

```agda
record Fanout
  {l1 l2 : Level} {C : Inverse-Precategoryᵉ l1 l2} {n : ℕᵉ}
  (K : ranked-sort C n) (m : ℕᵉ) (m<n : succ-ℕᵉ m ≤-ℕᵉ n) : UUᵉ (l1 ⊔ l2)
  where

  field
    ranked-sort-Fanout : ranked-sort C m

  sort-Fanout :
    obj-Precategoryᵉ (precategory-Inverse-Precategoryᵉ C)
  sort-Fanout = sort-ranked-sort ranked-sort-Fanout

  field
    arrow-Fanout :
      hom-Precategoryᵉ
        ( precategory-Inverse-Precategoryᵉ C)
        ( sort-ranked-sort K)
        ( sort-Fanout)

open Fanout public

mk-Fanout :
  {l1 l2 : Level} {C : Inverse-Precategoryᵉ l1 l2} {n : ℕᵉ}
  (K : ranked-sort C n) (m : ℕᵉ) (m<n : succ-ℕᵉ m ≤-ℕᵉ n)
  (ranked-sort-Fanout : ranked-sort C m) →
  hom-Precategoryᵉ
    ( precategory-Inverse-Precategoryᵉ C)
    ( sort-ranked-sort K)
    ( sort-ranked-sort ranked-sort-Fanout) →
  Fanout K m m<n
ranked-sort-Fanout (mk-Fanout K m m<n ranked-sort-Fanout F) =
  ranked-sort-Fanout
arrow-Fanout (mk-Fanout K m m<n ranked-sort-Fanout F) = F

-- precomposition-Fanout :
--   {l1 l2 : Level} {C : Inverse-Precategoryᵉ l1 l2} {n : ℕᵉ}
--   {K : ranked-sort C n} {m : ℕᵉ} {m<n : succ-ℕᵉ m ≤-ℕᵉ n} →
--   Fanout K m m<n →
--   {o : ℕᵉ}
--   (K' : ranked-sort C o) →
--   hom-Inverse-Precategoryᵉ C (sort-ranked-sort K') (sort-ranked-sort K) →
--   Fanout K' m {!!}
-- ranked-sort-Fanout (precomposition-Fanout F K' f) = {!!}
-- arrow-Fanout (precomposition-Fanout F K' f) = {!!}
```
