# Diagram signatures

```agda
module univalence-principle.diagram-signatures where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.inverse-precategoriesᵉ
open import category-theory.opposite-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ

open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.propositionsᵉ
open import foundation.binary-transportᵉ
open import foundation.cofibrant-typesᵉ
open import foundation.setsᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.fibrant-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.sharp-typesᵉ
open import foundation.exotypesᵉ
```

</details>

## Idea


## Definitions

```agda
record is-DSig
  {l1 l2 : Level} (𝓛 : Inverse-Precategoryᵉ l1 l2)
  (p : ℕᵉ) (l3 l4 : Level) : UUᵉ (lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4))
  where

  field
   has-height-is-DSig : has-height 𝓛 p
   is-sharp-ranked-sort-is-DSig :
     (n : ℕᵉ) → is-sharp (ranked-sort 𝓛 n) l3
   is-cofibrant-fanout-is-DSig :
     (n : ℕᵉ) (K : ranked-sort 𝓛 n) (m : ℕᵉ) (m<n : succ-ℕᵉ m ≤-ℕᵉ n) →
     is-cofibrant (Fanout K m m<n) l4

open is-DSig

DSig :
  (l1 l2 l3 l4 : Level) (p : ℕᵉ) → UUᵉ (lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4))
DSig l1 l2 l3 l4 p =
  Σᵉ (Inverse-Precategoryᵉ l1 l2)
    (λ 𝓛 → is-DSig 𝓛 p l3 l4)

obj-derivative-is-DSig-Precategoryᵉ :
  {l1 l2 : Level} (𝓛 : Inverse-Precategoryᵉ l1 l2)
  (p : ℕᵉ) {l3 l4 : Level} → (is-DSig 𝓛 (succ-ℕᵉ p) l3 l4) → (l5 : Level) →
  (ranked-sort 𝓛 0ᵉ → Fibrant-Type l5) →
  UUᵉ (l1 ⊔ l2 ⊔ l5)
obj-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M =
  Σᵉ ℕᵉ
    ( λ n →
      Σᵉ (ranked-sort 𝓛 (succ-ℕᵉ n))
        ( λ K → (F : Fanout K 0ᵉ _) →
          type-Fibrant-Type (M (ranked-sort-Fanout F))))

hom-derivative-is-DSig-Precategoryᵉ :
  {l1 l2 : Level} (𝓛 : Inverse-Precategoryᵉ l1 l2)
  (p : ℕᵉ) {l3 l4 : Level} (is-DSig-𝓛 : is-DSig 𝓛 (succ-ℕᵉ p) l3 l4) → (l5 : Level) →
  (M : ranked-sort 𝓛 0ᵉ → Fibrant-Type l5) →
  (obj-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M) →
  (obj-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M) →
  UUᵉ (l1 ⊔ l2 ⊔ l5)
hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M (n ,ᵉ K ,ᵉ α) (m ,ᵉ K' ,ᵉ α') =
  Σᵉ
    ( hom-Precategoryᵉ
      ( precategory-Inverse-Precategoryᵉ 𝓛)
      ( sort-ranked-sort K)
      ( sort-ranked-sort K'))
    ( λ f →
      ( F : Fanout K' 0ᵉ _) →
        ( α
          ( mk-Fanout K 0ᵉ _
            ( ranked-sort-Fanout F)
            ( comp-hom-Precategoryᵉ
              ( precategory-Inverse-Precategoryᵉ 𝓛)
              ( arrow-Fanout F)
              ( f)))) ＝ᵉ
        ( α' F))

hom-set-derivative-is-DSig-Precategoryᵉ :
  {l1 l2 : Level} (𝓛 : Inverse-Precategoryᵉ l1 l2)
  (p : ℕᵉ) {l3 l4 : Level} (is-DSig-𝓛 : is-DSig 𝓛 (succ-ℕᵉ p) l3 l4) → (l5 : Level) →
  (M : ranked-sort 𝓛 0ᵉ → Fibrant-Type l5) →
  (obj-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M) →
  (obj-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M) →
  Setᵉ (l1 ⊔ l2 ⊔ l5)
pr1ᵉ (hom-set-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M (n ,ᵉ K ,ᵉ α) (m ,ᵉ K' ,ᵉ α')) =
  hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M (n ,ᵉ K ,ᵉ α) (m ,ᵉ K' ,ᵉ α')
pr2ᵉ (hom-set-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M (n ,ᵉ K ,ᵉ α) (m ,ᵉ K' ,ᵉ α')) =
   is-set-exotypeᵉ _

comp-hom-derivative-is-DSig-Precategoryᵉ :
  {l1 l2 : Level} (𝓛 : Inverse-Precategoryᵉ l1 l2)
  (p : ℕᵉ) {l3 l4 : Level} (is-DSig-𝓛 : is-DSig 𝓛 (succ-ℕᵉ p) l3 l4) → (l5 : Level) →
  (M : ranked-sort 𝓛 0ᵉ → Fibrant-Type l5) →
  {x y z : obj-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M} →
  ( hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M y z) →
  ( hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M x y) →
  ( hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M x z)
pr1ᵉ (comp-hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M g f) =
  comp-hom-Precategoryᵉ ( precategory-Inverse-Precategoryᵉ 𝓛) (pr1ᵉ g) (pr1ᵉ f)
pr2ᵉ (comp-hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M {(n ,ᵉ K ,ᵉ α)} {(m ,ᵉ K' ,ᵉ β)} {(o ,ᵉ K'' ,ᵉ θ)} g f) F =
  trᵉ
    (λ - → α (mk-Fanout K 0ᵉ starᵉ (ranked-sort-Fanout F) -) ＝ᵉ θ F)
    ( associative-comp-hom-Precategoryᵉ
      ( precategory-Inverse-Precategoryᵉ 𝓛)
      ( arrow-Fanout F)
      ( pr1ᵉ g)
      ( pr1ᵉ f))
    ( pr2ᵉ f
      ( mk-Fanout K' 0ᵉ starᵉ
        ( ranked-sort-Fanout F)
        ( comp-hom-Precategoryᵉ
          ( pr1ᵉ 𝓛)
          ( arrow-Fanout F)
          ( pr1ᵉ g))) ∙ᵉ
    ( pr2ᵉ g
      ( mk-Fanout K'' 0ᵉ starᵉ
        ( ranked-sort-Fanout F)
        ( arrow-Fanout F))))

id-hom-derivative-is-DSig-Precategoryᵉ :
  {l1 l2 : Level} (𝓛 : Inverse-Precategoryᵉ l1 l2)
  (p : ℕᵉ) {l3 l4 : Level} (is-DSig-𝓛 : is-DSig 𝓛 (succ-ℕᵉ p) l3 l4)
  (l5 : Level) (M : ranked-sort 𝓛 0ᵉ → Fibrant-Type l5)
  (K : obj-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M) →
  hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M K K
pr1ᵉ (id-hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M K) =
  id-hom-Precategoryᵉ (precategory-Inverse-Precategoryᵉ 𝓛)
pr2ᵉ (id-hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M (n ,ᵉ K ,ᵉ α)) F =
  trᵉ
    ( λ - → α (mk-Fanout K 0ᵉ starᵉ (ranked-sort-Fanout F) -) ＝ᵉ α F)
    ( invᵉ
      ( right-unit-law-comp-hom-Precategoryᵉ
        ( precategory-Inverse-Precategoryᵉ 𝓛)
        ( arrow-Fanout F)))
    reflᵉ

associative-comp-hom-derivative-is-DSig-Precategoryᵉ :
  {l1 l2 : Level} (𝓛 : Inverse-Precategoryᵉ l1 l2)
  (p : ℕᵉ) {l3 l4 : Level} (is-DSig-𝓛 : is-DSig 𝓛 (succ-ℕᵉ p) l3 l4)
  (l5 : Level) (M : ranked-sort 𝓛 0ᵉ → Fibrant-Type l5)
  {x y z w : obj-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M}
  (h : hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M z w)
  (g : hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M y z)
  (f : hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M x y) →
  comp-hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M {x} {y} {w}
    ( comp-hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M {y} {z} {w} h g)
    ( f) ＝ᵉ
  comp-hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M {x} {z} {w} h
    ( comp-hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M {x} {y} {z} g f)
associative-comp-hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M {x} {y} {z} {w} h g f =
  eq-pair-Σᵉ
    ( associative-comp-hom-Precategoryᵉ
      ( precategory-Inverse-Precategoryᵉ 𝓛)
      ( pr1ᵉ h)
      ( pr1ᵉ g)
      ( pr1ᵉ f))
    ( eq-is-propᵉ (is-prop-Πᵉ (λ _ → is-set-exotypeᵉ _ _ _)))

derivative-is-DSig-Precategoryᵉ :
  {l1 l2 : Level} (𝓛 : Inverse-Precategoryᵉ l1 l2)
  (p : ℕᵉ) {l3 l4 : Level} → (is-DSig 𝓛 (succ-ℕᵉ p) l3 l4) → (l5 : Level) →
  (ranked-sort 𝓛 0ᵉ → Fibrant-Type l5) →
  Precategoryᵉ (l1 ⊔ l2 ⊔ l5) (l1 ⊔ l2 ⊔ l5)
derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M =
  make-Precategoryᵉ
    ( obj-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M)
    ( hom-set-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M)
    ( λ {x} {y} {z} g f → comp-hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M {x} {y} {z} g f)
    ( id-hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M)
    ( λ {x} {y} {z} {w} h g f →
      associative-comp-hom-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M {x} {y} {z} {w} h g f)
    ( λ f →
      eq-pair-Σᵉ
        ( left-unit-law-comp-hom-Precategoryᵉ
          ( precategory-Inverse-Precategoryᵉ 𝓛)
          ( pr1ᵉ f))
        ( eq-is-propᵉ (is-prop-Πᵉ (λ _ → is-set-exotypeᵉ _ _ _))))
    ( λ f →
      eq-pair-Σᵉ
        ( right-unit-law-comp-hom-Precategoryᵉ
          ( precategory-Inverse-Precategoryᵉ 𝓛)
          ( pr1ᵉ f))
        ( eq-is-propᵉ (is-prop-Πᵉ (λ _ → is-set-exotypeᵉ _ _ _))))

rank-functor-is-inverse-derivative-is-DSig-Precategoryᵉ :
  {l1 l2 : Level} (𝓛 : Inverse-Precategoryᵉ l1 l2)
  (p : ℕᵉ) {l3 l4 : Level} (is-DSig-𝓛 : is-DSig 𝓛 (succ-ℕᵉ p) l3 l4)
  (l5 : Level) (M : ranked-sort 𝓛 0ᵉ → Fibrant-Type l5) →
  functor-Precategoryᵉ
    ( opposite-Precategoryᵉ
      ( derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M))
    ℕ-Precategoryᵉ
pr1ᵉ (rank-functor-is-inverse-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M) (n ,ᵉ K ,ᵉ α) = n 
pr1ᵉ (pr2ᵉ (rank-functor-is-inverse-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M)) {n ,ᵉ K ,ᵉ α} {m ,ᵉ K' ,ᵉ β} f =
  preserves-order-hom-ranked-sort K' K (pr1ᵉ f)
pr1ᵉ (pr2ᵉ (pr2ᵉ (rank-functor-is-inverse-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M))) {n ,ᵉ K ,ᵉ α} {_} {m ,ᵉ K' ,ᵉ β} g f =
  eq-is-propᵉ (is-prop-leq-ℕᵉ n m)
pr2ᵉ (pr2ᵉ (pr2ᵉ (rank-functor-is-inverse-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M))) (n ,ᵉ K ,ᵉ α) =
  eq-is-propᵉ (is-prop-leq-ℕᵉ n n)

reflects-id-rank-functor-is-inverse-derivative-is-DSig-Precategoryᵉ :
  {l1 l2 : Level} (𝓛 : Inverse-Precategoryᵉ l1 l2)
  (p : ℕᵉ) {l3 l4 : Level} (is-DSig-𝓛 : is-DSig 𝓛 (succ-ℕᵉ p) l3 l4)
  (l5 : Level) (M : ranked-sort 𝓛 0ᵉ → Fibrant-Type l5) →
  reflects-id-functor-Precategoryᵉ
    ( opposite-Precategoryᵉ
      ( derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M))
    ℕ-Precategoryᵉ
    (rank-functor-is-inverse-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M)
reflects-id-rank-functor-is-inverse-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M {n ,ᵉ K ,ᵉ α} (f1 ,ᵉ f2) H =
  eq-pair-Σᵉ
    ( reflects-id-rank-functor-Inverse-Precategoryᵉ 𝓛 f1
      ( trᵉ
        ( λ (x ,ᵉ r) → is-id-Precategoryᵉ ℕ-Precategoryᵉ x r)
        ( eq-pair-Σᵉ
          ( invᵉ (is-ranked-sort-ranked-sort K ))
          ( eq-is-propᵉ
            ( is-prop-leq-ℕᵉ
              ( obj-rank-functor-Inverse-Precategoryᵉ 𝓛 (sort-ranked-sort K))
              ( obj-rank-functor-Inverse-Precategoryᵉ 𝓛 (sort-ranked-sort K)))))
        ( H)))
    ( eq-is-propᵉ (is-prop-Πᵉ (λ _ → is-set-exotypeᵉ _ _ _)))

is-inverse-derivative-is-DSig-Precategoryᵉ :
  {l1 l2 : Level} (𝓛 : Inverse-Precategoryᵉ l1 l2)
  (p : ℕᵉ) {l3 l4 : Level} (is-DSig-𝓛 : is-DSig 𝓛 (succ-ℕᵉ p) l3 l4)
  (l5 : Level) (M : ranked-sort 𝓛 0ᵉ → Fibrant-Type l5) →
  is-inverse-Precategoryᵉ (derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M)
pr1ᵉ (is-inverse-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M) =
  rank-functor-is-inverse-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M
pr2ᵉ (is-inverse-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M) =
  reflects-id-rank-functor-is-inverse-derivative-is-DSig-Precategoryᵉ 𝓛 p is-DSig-𝓛 l5 M

derivative-DSig :
  (l1 l2 l3 l4 : Level) (p : ℕᵉ) →
  DSig l1 l2 l3 l4 (succ-ℕᵉ p) → DSig l1 l2 l3 l4 p
pr1ᵉ (derivative-DSig l1 l2 l3 l4 p 𝓛) = {!!}
pr2ᵉ (derivative-DSig l1 l2 l3 l4 p 𝓛) = {!!}
```
