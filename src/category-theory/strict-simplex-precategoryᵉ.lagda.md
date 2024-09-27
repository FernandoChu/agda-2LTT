# Strict simplex precategory

```agda
module category-theory.strict-simplex-precategoryᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-subprecategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.yoneda-lemma-precategoriesᵉ
open import category-theory.opposite-precategoriesᵉ
open import category-theory.inverse-precategoriesᵉ
open import category-theory.copresheaf-categoriesᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ
open import category-theory.representable-functors-precategoriesᵉ

open import elementary-number-theory.inequality-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coercing-inner-typesᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.category-of-setsᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.coproduct-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.negationᵉ
open import foundation.universe-levelsᵉ
open import foundation.function-typesᵉ
open import foundation.setsᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.exotypesᵉ


open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

## Definitions

### The strict simplex category

```agda
lt-Finᵉ : (k : ℕᵉ) → Finᵉ k → Finᵉ k → UUᵉ lzero
lt-Finᵉ (succ-ℕᵉ k) (inlᵉ x) (inlᵉ y) = lt-Finᵉ k x y
lt-Finᵉ (succ-ℕᵉ k) (inlᵉ x) (inrᵉ starᵉ) = unitᵉ
lt-Finᵉ (succ-ℕᵉ k) (inrᵉ starᵉ) y = emptyᵉ

is-prop-lt-Finᵉ :
  (k : ℕᵉ) (x y : Finᵉ k) → is-propᵉ (lt-Finᵉ k x y)
is-prop-lt-Finᵉ (succ-ℕᵉ k) (inlᵉ x) (inlᵉ y) = is-prop-lt-Finᵉ k x y
is-prop-lt-Finᵉ (succ-ℕᵉ k) (inlᵉ x) (inrᵉ star) = is-prop-unitᵉ
is-prop-lt-Finᵉ (succ-ℕᵉ k) (inrᵉ star) (inlᵉ y) = is-prop-emptyᵉ
is-prop-lt-Finᵉ (succ-ℕᵉ k) (inrᵉ star) (inrᵉ star) = is-prop-emptyᵉ

preserves-lt-Finᵉ : (n m : ℕᵉ) → (Finᵉ n → Finᵉ m) → UUᵉ lzero
preserves-lt-Finᵉ n m f =
  (a b : Finᵉ n) →
  lt-Finᵉ n a b →
  lt-Finᵉ m (f a) (f b)

is-prop-preserves-lt-Finᵉ :
  (n m : ℕᵉ) (f : Finᵉ n → Finᵉ m) →
  is-propᵉ (preserves-lt-Finᵉ n m f)
is-prop-preserves-lt-Finᵉ n m f =
  is-prop-Πᵉ λ a →
  is-prop-Πᵉ λ b →
  is-prop-Πᵉ λ p →
  is-prop-lt-Finᵉ m (f a) (f b)

restriction-preserves-lt-Fin'ᵉ :
  (m n : ℕᵉ) (f : Finᵉ (succ-ℕᵉ m) → Finᵉ (succ-ℕᵉ n)) →
  (preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ n) f) →
  (x : Finᵉ m) → (y : Finᵉ (succ-ℕᵉ n)) →
  (f (inlᵉ x) ＝ᵉ y) → Finᵉ n
restriction-preserves-lt-Fin'ᵉ (succ-ℕᵉ m) n f pf x (inlᵉ y) p = y
restriction-preserves-lt-Fin'ᵉ (succ-ℕᵉ m) n f pf x (inrᵉ y) p =
  ex-falsoᵉ
    (trᵉ (λ - → lt-Finᵉ (succ-ℕᵉ n) - (f (inrᵉ starᵉ))) p
      (pf (inlᵉ x) (inrᵉ starᵉ) starᵉ))

restriction-preserves-lt-Finᵉ :
  (m n : ℕᵉ) (f : Finᵉ (succ-ℕᵉ m) → Finᵉ (succ-ℕᵉ n)) →
  (preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ n) f) →
  Finᵉ m → Finᵉ n
restriction-preserves-lt-Finᵉ m n f pf x =
  restriction-preserves-lt-Fin'ᵉ m n f pf x (f (inlᵉ x)) reflᵉ

inl-restriction-preserves-lt-Fin'ᵉ :
  (m n : ℕᵉ) (f : Finᵉ (succ-ℕᵉ m) → Finᵉ (succ-ℕᵉ n)) →
  (pf : preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ n) f) →
  (x : Finᵉ m) →
  (rx : Finᵉ (succ-ℕᵉ n)) →
  (px : f (inlᵉ x) ＝ᵉ rx) →
  inlᵉ (restriction-preserves-lt-Fin'ᵉ m n f pf x rx px) ＝ᵉ f (inlᵉ x)
inl-restriction-preserves-lt-Fin'ᵉ (succ-ℕᵉ m) n f pf x (inlᵉ a) px = invᵉ px
inl-restriction-preserves-lt-Fin'ᵉ (succ-ℕᵉ m) n f pf x (inrᵉ a) px =
  ex-falsoᵉ
    (trᵉ (λ - → lt-Finᵉ (succ-ℕᵉ n) - (f (inrᵉ starᵉ))) px
      (pf (inlᵉ x) (inrᵉ starᵉ) starᵉ))

inl-restriction-preserves-lt-Finᵉ :
  (m n : ℕᵉ) (f : Finᵉ (succ-ℕᵉ m) → Finᵉ (succ-ℕᵉ n)) →
  (pf : preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ n) f) →
  (x : Finᵉ m) →
  inlᵉ (restriction-preserves-lt-Finᵉ m n f pf x) ＝ᵉ f (inlᵉ x)
inl-restriction-preserves-lt-Finᵉ m n f pf x =
  inl-restriction-preserves-lt-Fin'ᵉ m n f pf x (f (inlᵉ x)) reflᵉ

preserves-lt-restriction-preserves-lt-Fin'ᵉ :
  (m n : ℕᵉ) (f : Finᵉ (succ-ℕᵉ m) → Finᵉ (succ-ℕᵉ n)) →
  (pf : preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ n) f) →
  ( a : Finᵉ m)
  ( b : Finᵉ m) →
  ( ra : Finᵉ (succ-ℕᵉ n)) →
  ( pa : f (inlᵉ a) ＝ᵉ ra) →
  ( rb : Finᵉ (succ-ℕᵉ n)) →
  ( pb : f (inlᵉ b) ＝ᵉ rb) →
  lt-Finᵉ m a b →
  lt-Finᵉ n
    (restriction-preserves-lt-Fin'ᵉ m n f pf a ra pa)
    (restriction-preserves-lt-Fin'ᵉ m n f pf b rb pb)
preserves-lt-restriction-preserves-lt-Fin'ᵉ (succ-ℕᵉ m) n f pf a b (inlᵉ x) pa (inlᵉ y) pb H =
  trᵉ (lt-Finᵉ (succ-ℕᵉ n) (inlᵉ x)) pb
   (trᵉ (λ - → lt-Finᵉ (succ-ℕᵉ n) - (f (inlᵉ b))) pa
     (pf (inlᵉ a) (inlᵉ b) H))
preserves-lt-restriction-preserves-lt-Fin'ᵉ (succ-ℕᵉ m) n f pf a b (inlᵉ x) pa (inrᵉ y) pb H =
  ex-falsoᵉ
    (trᵉ (λ - → lt-Finᵉ (succ-ℕᵉ n) - (f (inrᵉ starᵉ))) pb
      (pf (inlᵉ b) (inrᵉ starᵉ) starᵉ))
preserves-lt-restriction-preserves-lt-Fin'ᵉ (succ-ℕᵉ m) n f pf a b (inrᵉ x) pa y pb H =
  ex-falsoᵉ
    (trᵉ (λ - → lt-Finᵉ (succ-ℕᵉ n) - (f (inrᵉ starᵉ))) pa
      (pf (inlᵉ a) (inrᵉ starᵉ) starᵉ))

preserves-lt-restriction-preserves-lt-Finᵉ :
  (m n : ℕᵉ) (f : Finᵉ (succ-ℕᵉ m) → Finᵉ (succ-ℕᵉ n)) →
  (pf : preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ n) f) →
  preserves-lt-Finᵉ m n (restriction-preserves-lt-Finᵉ m n f pf)
preserves-lt-restriction-preserves-lt-Finᵉ m n f pf a b H =
  preserves-lt-restriction-preserves-lt-Fin'ᵉ m n f pf a b
     (f (inlᵉ a)) reflᵉ (f (inlᵉ b)) reflᵉ H

leq-preserves-lt-Finᵉ :
  (m n : ℕᵉ) → (f : Finᵉ m → Finᵉ n) →
  preserves-lt-Finᵉ m n f → leq-ℕᵉ m n
leq-preserves-lt-Finᵉ 0ᵉ 0ᵉ f pf = starᵉ
leq-preserves-lt-Finᵉ 0ᵉ (succ-ℕᵉ n) f pf = starᵉ
leq-preserves-lt-Finᵉ (succ-ℕᵉ m) 0ᵉ f pf = f (inrᵉ starᵉ)
leq-preserves-lt-Finᵉ (succ-ℕᵉ 0ᵉ) (succ-ℕᵉ n) f pf = starᵉ
leq-preserves-lt-Finᵉ (succ-ℕᵉ (succ-ℕᵉ m)) (succ-ℕᵉ n) f pf =
  leq-preserves-lt-Finᵉ (succ-ℕᵉ m) n
    (restriction-preserves-lt-Finᵉ (succ-ℕᵉ m) n f pf)
    (preserves-lt-restriction-preserves-lt-Finᵉ (succ-ℕᵉ m) n f pf)

comp-preserves-lt-Finᵉ :
  (m n o : ℕᵉ)
  (g : Finᵉ n → Finᵉ o)
  (f : Finᵉ m → Finᵉ n) →
  preserves-lt-Finᵉ m n f →
  preserves-lt-Finᵉ n o g →
  preserves-lt-Finᵉ m o (g ∘ᵉ f)
comp-preserves-lt-Finᵉ m n o g f pf pg a b H =
  pg (f a) (f b) (pf a b H)

obj-strict-simplex-Precategoryᵉ : UUᵉ lzero
obj-strict-simplex-Precategoryᵉ = ℕᵉ

hom-strict-simplex-Precategoryᵉ :
  obj-strict-simplex-Precategoryᵉ → obj-strict-simplex-Precategoryᵉ → UUᵉ lzero
hom-strict-simplex-Precategoryᵉ n m =
  Σᵉ (Finᵉ (succ-ℕᵉ n) → Finᵉ (succ-ℕᵉ m))
    (λ f → preserves-lt-Finᵉ (succ-ℕᵉ n) (succ-ℕᵉ m) f)

hom-set-strict-simplex-Precategoryᵉ :
  obj-strict-simplex-Precategoryᵉ → obj-strict-simplex-Precategoryᵉ → Setᵉ lzero
pr1ᵉ (hom-set-strict-simplex-Precategoryᵉ n m) = hom-strict-simplex-Precategoryᵉ n m
pr2ᵉ (hom-set-strict-simplex-Precategoryᵉ n m) = is-setᵉ-exotype _

id-strict-simplex-Precategoryᵉ :
  (n : obj-strict-simplex-Precategoryᵉ) →
  hom-strict-simplex-Precategoryᵉ n n
pr1ᵉ (id-strict-simplex-Precategoryᵉ n) = idᵉ
pr2ᵉ (id-strict-simplex-Precategoryᵉ n) a b m = m

comp-hom-strict-simplex-Precategoryᵉ :
  {m n o : obj-strict-simplex-Precategoryᵉ} →
  hom-strict-simplex-Precategoryᵉ n o →
  hom-strict-simplex-Precategoryᵉ m n →
  hom-strict-simplex-Precategoryᵉ m o
pr1ᵉ (comp-hom-strict-simplex-Precategoryᵉ (g ,ᵉ pg) (f ,ᵉ pf)) = g ∘ᵉ f
pr2ᵉ (comp-hom-strict-simplex-Precategoryᵉ {m} {n} {o} (g ,ᵉ pg) (f ,ᵉ pf)) =
  comp-preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ n) (succ-ℕᵉ o) g f pf pg

strict-simplex-Precategoryᵉ : Precategoryᵉ lzero lzero
strict-simplex-Precategoryᵉ =
  make-Precategoryᵉ
    obj-strict-simplex-Precategoryᵉ 
    hom-set-strict-simplex-Precategoryᵉ 
    comp-hom-strict-simplex-Precategoryᵉ  
    id-strict-simplex-Precategoryᵉ 
    ( λ h g f → reflᵉ)
    ( λ f → reflᵉ)
    ( λ f → reflᵉ)

⟨0⟩₁-strict-simplex-Precategoryᵉ :
  hom-strict-simplex-Precategoryᵉ 0ᵉ 1ᵉ
pr1ᵉ ⟨0⟩₁-strict-simplex-Precategoryᵉ x = zero-Finᵉ 1ᵉ
pr2ᵉ ⟨0⟩₁-strict-simplex-Precategoryᵉ (inrᵉ starᵉ) (inrᵉ starᵉ) p = p

⟨1⟩₁-strict-simplex-Precategoryᵉ :
  hom-strict-simplex-Precategoryᵉ 0ᵉ 1ᵉ
pr1ᵉ ⟨1⟩₁-strict-simplex-Precategoryᵉ x = succ-Finᵉ 2ᵉ (zero-Finᵉ 1ᵉ)
pr2ᵉ ⟨1⟩₁-strict-simplex-Precategoryᵉ (inrᵉ starᵉ) (inrᵉ starᵉ) p = p

⟨02⟩₂-strict-simplex-Precategoryᵉ :
  hom-strict-simplex-Precategoryᵉ 1ᵉ 2ᵉ
pr1ᵉ ⟨02⟩₂-strict-simplex-Precategoryᵉ (inlᵉ (inrᵉ starᵉ)) = zero-Finᵉ 2ᵉ 
pr1ᵉ ⟨02⟩₂-strict-simplex-Precategoryᵉ (inrᵉ starᵉ) = succ-Finᵉ 3ᵉ (succ-Finᵉ 3ᵉ (zero-Finᵉ 2ᵉ))  
pr2ᵉ ⟨02⟩₂-strict-simplex-Precategoryᵉ (inlᵉ (inrᵉ x)) (inlᵉ (inrᵉ y)) p = p
pr2ᵉ ⟨02⟩₂-strict-simplex-Precategoryᵉ (inlᵉ (inrᵉ x)) (inrᵉ starᵉ) p = x

op-strict-simplex-Precategoryᵉ : Precategoryᵉ lzero lzero
op-strict-simplex-Precategoryᵉ =
  opposite-Precategoryᵉ strict-simplex-Precategoryᵉ
```

### Strict simplicial set

```agda
strict-simplicial-set : UUᵉ (lsuc lzero)
strict-simplicial-set =
  copresheaf-Precategoryᵉ op-strict-simplex-Precategoryᵉ lzero

obj-strict-simplicial-set :
  strict-simplicial-set →
  ℕᵉ → Setᵉ lzero
obj-strict-simplicial-set =
  obj-functor-Precategoryᵉ
    op-strict-simplex-Precategoryᵉ
    (Set-Precategoryᵉ lzero)

type-obj-strict-simplicial-set :
  strict-simplicial-set →
  ℕᵉ → UUᵉ lzero
type-obj-strict-simplicial-set X n =
  type-Setᵉ (obj-strict-simplicial-set X n)
```

### The standard strict simplex

```agda
lt-ℕᵉ : ℕᵉ → ℕᵉ → UUᵉ lzero
lt-ℕᵉ 0ᵉ 0ᵉ = emptyᵉ
lt-ℕᵉ 0ᵉ (succ-ℕᵉ b) = unitᵉ
lt-ℕᵉ (succ-ℕᵉ a) 0ᵉ = emptyᵉ
lt-ℕᵉ (succ-ℕᵉ a) (succ-ℕᵉ b) = lt-ℕᵉ a b

is-prop-lt-ℕᵉ :
  (m n : ℕᵉ) → is-propᵉ (lt-ℕᵉ m n)
is-prop-lt-ℕᵉ 0ᵉ 0ᵉ = is-prop-emptyᵉ
is-prop-lt-ℕᵉ 0ᵉ (succ-ℕᵉ n) = is-prop-unitᵉ
is-prop-lt-ℕᵉ (succ-ℕᵉ m) 0ᵉ = is-prop-emptyᵉ
is-prop-lt-ℕᵉ (succ-ℕᵉ m) (succ-ℕᵉ n) = is-prop-lt-ℕᵉ m n

bounded-strict-simplex-Full-Subcategoryᵉ :
    ℕᵉ → Full-Subprecategoryᵉ (lzero ⊔ lzero) (strict-simplex-Precategoryᵉ)
pr1ᵉ (bounded-strict-simplex-Full-Subcategoryᵉ n x) = lt-ℕᵉ x n
pr2ᵉ (bounded-strict-simplex-Full-Subcategoryᵉ n x) = is-prop-lt-ℕᵉ x n

bounded-strict-simplex-Precategoryᵉ : ℕᵉ → Precategoryᵉ lzero lzero
bounded-strict-simplex-Precategoryᵉ n =
  precategory-Full-Subprecategoryᵉ
    ( strict-simplex-Precategoryᵉ)
    ( bounded-strict-simplex-Full-Subcategoryᵉ n)

standard-strict-simplex :
  ℕᵉ → strict-simplicial-set
standard-strict-simplex n =
  representable-functor-Precategoryᵉ op-strict-simplex-Precategoryᵉ n
```

### The horns

```agda
bounded-succ-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ
bounded-succ-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = skip-zero-Finᵉ kᵉ xᵉ
bounded-succ-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) = inrᵉ starᵉ

-- Maps n to to it's corresponding element in Fin (k + 1), bounding above.
Fin-natᵉ : (kᵉ : ℕᵉ) → ℕᵉ → Finᵉ (succ-ℕᵉ kᵉ)
Fin-natᵉ 0ᵉ 0ᵉ = zero-Finᵉ 0ᵉ
Fin-natᵉ 0ᵉ (succ-ℕᵉ n) = zero-Finᵉ 0ᵉ
Fin-natᵉ (succ-ℕᵉ k) 0ᵉ = zero-Finᵉ (succ-ℕᵉ k) 
Fin-natᵉ (succ-ℕᵉ k) (succ-ℕᵉ n) =
  bounded-succ-Finᵉ (succ-ℕᵉ (succ-ℕᵉ k)) (inl-Finᵉ (succ-ℕᵉ k) (Fin-natᵉ k n))

type-obj-horn-strict-simplex :
  ℕᵉ → ℕᵉ → ℕᵉ → UUᵉ lzero
type-obj-horn-strict-simplex j n k =
  Σᵉ (hom-strict-simplex-Precategoryᵉ k n)
    ( λ (f ,ᵉ p) →
      Σᵉ ( Finᵉ (succ-ℕᵉ n))
        ( λ r →
          ( ¬ᵉ (r ＝ᵉ Fin-natᵉ n j) ×ᵉ ¬ᵉ (fiberᵉ f r))))

hom-horn-strict-simplex :
  (j n k l : ℕᵉ) →
  hom-Precategoryᵉ op-strict-simplex-Precategoryᵉ k l →
  type-obj-horn-strict-simplex j n k →
  type-obj-horn-strict-simplex j n l
pr1ᵉ (pr1ᵉ (hom-horn-strict-simplex j n k l (f ,ᵉ pf) ((g ,ᵉ pg) ,ᵉ r ,ᵉ pr ,ᵉ pgr))) =
  g ∘ᵉ f 
pr2ᵉ (pr1ᵉ (hom-horn-strict-simplex j n k l (f ,ᵉ pf) ((g ,ᵉ pg) ,ᵉ r ,ᵉ pr ,ᵉ pgr))) =
  comp-preserves-lt-Finᵉ (succ-ℕᵉ l) (succ-ℕᵉ k) (succ-ℕᵉ n) g f pf pg
pr1ᵉ (pr2ᵉ (hom-horn-strict-simplex j n k l (f ,ᵉ pf) ((g ,ᵉ pg) ,ᵉ r ,ᵉ pr ,ᵉ pgr))) = r
pr1ᵉ (pr2ᵉ (pr2ᵉ (hom-horn-strict-simplex j n k l (f ,ᵉ pf) ((g ,ᵉ pg) ,ᵉ r ,ᵉ pr ,ᵉ pgr)))) = pr
pr2ᵉ (pr2ᵉ (pr2ᵉ (hom-horn-strict-simplex j n k l (f ,ᵉ pf) ((g ,ᵉ pg) ,ᵉ r ,ᵉ pr ,ᵉ pgr)))) (s ,ᵉ ps) =
  pgr (f s ,ᵉ ps)

-- The jth horn
horn-strict-simplex :
  ℕᵉ → ℕᵉ →
  strict-simplicial-set
pr1ᵉ (pr1ᵉ (horn-strict-simplex j n) k) = type-obj-horn-strict-simplex j n k
pr2ᵉ (pr1ᵉ (horn-strict-simplex j n) k) = is-setᵉ-exotype _
pr1ᵉ (pr2ᵉ (horn-strict-simplex j n)) {x} {y} f = hom-horn-strict-simplex j n x y f
pr1ᵉ (pr2ᵉ (pr2ᵉ (horn-strict-simplex j n))) g f = reflᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (horn-strict-simplex j n))) x = reflᵉ
```

### Strict simplicial maps

```agda
strict-simplicial-map :
  strict-simplicial-set →
  strict-simplicial-set →
  UUᵉ lzero
strict-simplicial-map =
  natural-transformation-Precategoryᵉ
    op-strict-simplex-Precategoryᵉ
    (Set-Precategoryᵉ lzero)

comp-strict-simplicial-map :
  (X Y Z : strict-simplicial-set) →
  strict-simplicial-map Y Z →
  strict-simplicial-map X Y →
  strict-simplicial-map X Z
comp-strict-simplicial-map X Y Z g f =
  comp-natural-transformation-Precategoryᵉ
    op-strict-simplex-Precategoryᵉ
    (Set-Precategoryᵉ lzero)
    X Y Z g f

horn-inclusion-strict-simplex :
  (j n : ℕᵉ) →
  strict-simplicial-map
    (horn-strict-simplex j n)
    (standard-strict-simplex n)
pr1ᵉ (horn-inclusion-strict-simplex j n) x ((f ,ᵉ pf) ,ᵉ r) = (f ,ᵉ pf)
pr2ᵉ (horn-inclusion-strict-simplex j n) fᵉ = reflᵉ

strict-simplicial-map-hom-strict-simplex-Precategoryᵉ :
  (m n : ℕᵉ) →
  hom-strict-simplex-Precategoryᵉ m n →
  strict-simplicial-map
    (standard-strict-simplex m)
    (standard-strict-simplex n)
strict-simplicial-map-hom-strict-simplex-Precategoryᵉ m n =
  map-inv-equivᵉ
    ( equiv-lemma-yoneda-representable-Precategoryᵉ
      op-strict-simplex-Precategoryᵉ m n)
```

### Vertices, edges and triangles

```agda
vertex-strict-simplicial-set :
  strict-simplicial-set → UUᵉ lzero
vertex-strict-simplicial-set X =
  strict-simplicial-map
    (standard-strict-simplex 0ᵉ)
    X

edge-strict-simplicial-set :
  strict-simplicial-set → UUᵉ lzero
edge-strict-simplicial-set X =
  strict-simplicial-map
    (standard-strict-simplex 1ᵉ)
    X

triangle-strict-simplicial-set :
  strict-simplicial-set → UUᵉ lzero
triangle-strict-simplicial-set X =
  strict-simplicial-map
    (standard-strict-simplex 2ᵉ)
    X

domain-edge-strict-simplicial-set :
  (X : strict-simplicial-set) →
  edge-strict-simplicial-set X →
  vertex-strict-simplicial-set X
domain-edge-strict-simplicial-set X f =
  comp-strict-simplicial-map
    ( standard-strict-simplex 0ᵉ)
    ( standard-strict-simplex 1ᵉ)
    ( X)
    ( f)
    ( strict-simplicial-map-hom-strict-simplex-Precategoryᵉ 0ᵉ 1ᵉ
      ⟨0⟩₁-strict-simplex-Precategoryᵉ)

codomain-edge-strict-simplicial-set :
  (X : strict-simplicial-set) →
  edge-strict-simplicial-set X →
  vertex-strict-simplicial-set X
codomain-edge-strict-simplicial-set X f =
  comp-strict-simplicial-map
    ( standard-strict-simplex 0ᵉ)
    ( standard-strict-simplex 1ᵉ)
    ( X)
    ( f)
    ( strict-simplicial-map-hom-strict-simplex-Precategoryᵉ 0ᵉ 1ᵉ
      ⟨1⟩₁-strict-simplex-Precategoryᵉ)

hom-strict-simplicial-set :
  (X : strict-simplicial-set) →
  vertex-strict-simplicial-set X →
  vertex-strict-simplicial-set X →
  UUᵉ lzero
hom-strict-simplicial-set X x y =
  Σᵉ (edge-strict-simplicial-set X)
    ( λ f →
      ( domain-edge-strict-simplicial-set X f ＝ᵉ x) ×ᵉ
      ( codomain-edge-strict-simplicial-set X f ＝ᵉ y))

composition-triangle-strict-simplicial-set :
  (X : strict-simplicial-set) →
  triangle-strict-simplicial-set X →
  edge-strict-simplicial-set X
composition-triangle-strict-simplicial-set X f =
  comp-strict-simplicial-map
    ( standard-strict-simplex 1ᵉ)
    ( standard-strict-simplex 2ᵉ)
    ( X)
    ( f)
    ( strict-simplicial-map-hom-strict-simplex-Precategoryᵉ 1ᵉ 2ᵉ
      ⟨02⟩₂-strict-simplex-Precategoryᵉ)

-- test :
--   (X : strict-simplicial-set) →
--   (x y z : vertex-strict-simplicial-set X) →
--   hom-strict-simplicial-set X y z →
--   hom-strict-simplicial-set X x y →
--   strict-simplicial-map (horn-strict-simplex 1ᵉ 2ᵉ) X
-- pr1ᵉ (test X x y z f g) 0ᵉ (α ,ᵉ pα) = {!case α star =ᵉ 0 !}
-- pr1ᵉ (test X x y z f g) (succ-ℕᵉ 0ᵉ) (α ,ᵉ pα) = {!!}
-- pr1ᵉ (test X x y z f g) (succ-ℕᵉ (succ-ℕᵉ m)) (α ,ᵉ pα) = {!!}
-- pr2ᵉ (test X x y z f g) = {!!}
```

## Properties

### The strict simplex precategory if inverse

```agda
hom-rank-functor-op-strict-simplex-Precategoryᵉ :
  {m n : obj-Precategoryᵉ strict-simplex-Precategoryᵉ}
  (f : hom-strict-simplex-Precategoryᵉ m n) →
  leq-ℕᵉ m n
hom-rank-functor-op-strict-simplex-Precategoryᵉ {m} {n} (f ,ᵉ pf) =
  leq-preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ n) f pf 

rank-functor-op-strict-simplex-Precategoryᵉ :
  functor-Precategoryᵉ strict-simplex-Precategoryᵉ ℕ-Precategoryᵉ
pr1ᵉ rank-functor-op-strict-simplex-Precategoryᵉ n = n
pr1ᵉ (pr2ᵉ rank-functor-op-strict-simplex-Precategoryᵉ) =
  hom-rank-functor-op-strict-simplex-Precategoryᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ rank-functor-op-strict-simplex-Precategoryᵉ)) {m} {n} {o} g f =
  eq-is-propᵉ (is-prop-leq-ℕᵉ m o)
pr2ᵉ (pr2ᵉ (pr2ᵉ rank-functor-op-strict-simplex-Precategoryᵉ)) n =
  eq-is-propᵉ (is-prop-leq-ℕᵉ n n)

reflects-isos-rank-functor-op-strict-simplex-Precategoryᵉ' :
    (m n : obj-Precategoryᵉ strict-simplex-Precategoryᵉ) →
    (m ＝ᵉ n) →
    (f : hom-strict-simplex-Precategoryᵉ m n) →
    is-iso-Precategoryᵉ ℕ-Precategoryᵉ {m} {n} (hom-rank-functor-op-strict-simplex-Precategoryᵉ f) →
    is-iso-Precategoryᵉ strict-simplex-Precategoryᵉ f
reflects-isos-rank-functor-op-strict-simplex-Precategoryᵉ' m .m reflᵉ (f ,ᵉ pf) (p1 ,ᵉ p2) =
  trᵉ
    ( is-iso-Precategoryᵉ strict-simplex-Precategoryᵉ)
    ( invᵉ f＝ᵉid)
    ( is-iso-id-hom-Precategoryᵉ strict-simplex-Precategoryᵉ {m})
  where
    lemma :
      (m : obj-strict-simplex-Precategoryᵉ) →
      ((f ,ᵉ pf) : hom-strict-simplex-Precategoryᵉ m m) →
      (x : Finᵉ (succ-ℕᵉ m)) →
      (y : Finᵉ (succ-ℕᵉ m)) →
      (f (inrᵉ starᵉ) ＝ᵉ y) →
      (f x ＝ᵉ x)
    lemma 0ᵉ (f ,ᵉ pf) (inrᵉ starᵉ) y p with f (inrᵉ starᵉ)
    ... | inrᵉ starᵉ = reflᵉ
    lemma (succ-ℕᵉ m) (f ,ᵉ pf) (inlᵉ x) y p =
      invᵉ (inl-restriction-preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ m) f pf x) ∙ᵉ
        apᵉ inlᵉ
          (lemma m
            ((restriction-preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ m) f pf) ,ᵉ
              preserves-lt-restriction-preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ m) f pf ) x ( restriction-preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ m) f pf
                   (inrᵉ starᵉ)) reflᵉ)
    lemma (succ-ℕᵉ m) (f ,ᵉ pf) (inrᵉ starᵉ) (inlᵉ y) p =
      ex-falsoᵉ
        (trᵉ (λ - → lt-Finᵉ (succ-ℕᵉ (succ-ℕᵉ m)) -
            (inlᵉ y)) fiis
          (trᵉ (lt-Finᵉ (succ-ℕᵉ (succ-ℕᵉ m)) (f (inlᵉ (inrᵉ starᵉ)))) p
          (pf (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) starᵉ)))
      where
        fiis : f (inlᵉ (inrᵉ starᵉ)) ＝ᵉ inlᵉ (inrᵉ starᵉ)
        fiis =  invᵉ (inl-restriction-preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ m) f pf (inrᵉ starᵉ)) ∙ᵉ
          apᵉ inlᵉ (lemma m
            ((restriction-preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ m) f pf) ,ᵉ
              preserves-lt-restriction-preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ m) f pf ) (inrᵉ starᵉ) ( restriction-preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ m) f pf
                   (inrᵉ starᵉ)) reflᵉ )
    lemma (succ-ℕᵉ m) (f ,ᵉ pf) (inrᵉ starᵉ) (inrᵉ starᵉ) p = p

    f＝ᵉid :
      (f ,ᵉ pf) ＝ᵉ id-strict-simplex-Precategoryᵉ m
    f＝ᵉid =
      eq-pair-Σᵉ
        ( eq-htpyᵉ (λ x → lemma m (f ,ᵉ pf) x (f (inrᵉ starᵉ)) reflᵉ))
        ( eq-is-propᵉ (is-prop-preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ m) idᵉ))

reflects-isos-rank-functor-op-strict-simplex-Precategoryᵉ :
  reflects-isos-functor-Precategoryᵉ
    strict-simplex-Precategoryᵉ
    ℕ-Precategoryᵉ
    rank-functor-op-strict-simplex-Precategoryᵉ
reflects-isos-rank-functor-op-strict-simplex-Precategoryᵉ {m} {n} (f ,ᵉ pf) (p1 ,ᵉ p2) =
  reflects-isos-rank-functor-op-strict-simplex-Precategoryᵉ' m n m＝ᵉn (f ,ᵉ pf) (p1 ,ᵉ p2) 
  where
    m＝ᵉn : m ＝ᵉ n
    m＝ᵉn =
      antisymmetric-leq-ℕᵉ m n
        ( leq-preserves-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ n) f pf)
        ( p1)

is-inverse-op-strict-simplex-Precategoryᵉ :
  is-inverse-Precategoryᵉ op-strict-simplex-Precategoryᵉ
pr1ᵉ is-inverse-op-strict-simplex-Precategoryᵉ =
  rank-functor-op-strict-simplex-Precategoryᵉ
pr2ᵉ is-inverse-op-strict-simplex-Precategoryᵉ =
  reflects-isos-rank-functor-op-strict-simplex-Precategoryᵉ
```
