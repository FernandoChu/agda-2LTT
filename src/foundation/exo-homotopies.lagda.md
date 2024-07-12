# Homotopies

```agda
module foundation.exo-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.exo-function-types
open import foundation.exo-identity-types
open import foundation.exo-universes
```

</details>

## Idea

A homotopy of identifications is a pointwise equality between dependent
functions.

## Definitions

```agda
module _
  {l1 l2 : Level} {X : UUᵉ l1} {P : X → UUᵉ l2} (f g : (x : X) → P x)
  where

  eq-valueᵉ : X → UUᵉ l2
  eq-valueᵉ x = (f x ＝ᵉ g x)

  map-compute-path-over-eq-valueᵉ :
    {x y : X} (p : x ＝ᵉ y) (q : eq-valueᵉ x) (r : eq-valueᵉ y) →
    ((apdᵉ f p) ∙ᵉ r) ＝ᵉ ((apᵉ (trᵉ P p) q) ∙ᵉ (apdᵉ g p)) → trᵉ eq-valueᵉ p q ＝ᵉ r
  map-compute-path-over-eq-valueᵉ reflᵉ q r =
    invᵉ ∘ᵉ (concat'ᵉ r (right-unitᵉ ∙ᵉ ap-idᵉ q))

map-compute-path-over-eq-value'ᵉ :
  {l1 l2 : Level} {X : UUᵉ l1} {Y : UUᵉ l2} (f g : X → Y) →
  {x y : X} (p : x ＝ᵉ y) (q : eq-valueᵉ f g x) (r : eq-valueᵉ f g y) →
  (apᵉ f p ∙ᵉ r) ＝ᵉ (q ∙ᵉ apᵉ g p) → trᵉ (eq-valueᵉ f g) p q ＝ᵉ r
map-compute-path-over-eq-value'ᵉ f g reflᵉ q r = invᵉ ∘ᵉ concat'ᵉ r right-unitᵉ

map-compute-path-over-eq-value-id-idᵉ :
  {l1 : Level} {A : UUᵉ l1} →
  {a b : A} (p : a ＝ᵉ b) (q : a ＝ᵉ a) (r : b ＝ᵉ b) →
  (p ∙ᵉ r) ＝ᵉ (q ∙ᵉ p) → (trᵉ (eq-valueᵉ idᵉ idᵉ) p q) ＝ᵉ r
map-compute-path-over-eq-value-id-idᵉ reflᵉ q r s = invᵉ (s ∙ᵉ right-unitᵉ)
```

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2}
  where

  infix 6 _~ᵉ_
  _~ᵉ_ : (f g : (x : A) → B x) → UUᵉ (l1 ⊔ l2)
  f ~ᵉ g = (x : A) → eq-valueᵉ f g x
```

## Properties

### Reflexivity

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2}
  where

  refl-htpyᵉ : {f : (x : A) → B x} → f ~ᵉ f
  refl-htpyᵉ x = reflᵉ

  refl-htpy'ᵉ : (f : (x : A) → B x) → f ~ᵉ f
  refl-htpy'ᵉ f = refl-htpyᵉ
```

### Inverting homotopies

```agda
  inv-htpyᵉ : {f g : (x : A) → B x} → f ~ᵉ g → g ~ᵉ f
  inv-htpyᵉ H x = invᵉ (H x)
```

### Concatenating homotopies

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2}
  where

  _∙ᵉh_ : {f g h : (x : A) → B x} → f ~ᵉ g → g ~ᵉ h → f ~ᵉ h
  (H ∙ᵉh K) x = (H x) ∙ᵉ (K x)

  concat-htpyᵉ :
    {f g : (x : A) → B x} →
    f ~ᵉ g → (h : (x : A) → B x) → g ~ᵉ h → f ~ᵉ h
  concat-htpyᵉ H h K x = concatᵉ (H x) (h x) (K x)

  concat-htpy'ᵉ :
    (f : (x : A) → B x) {g h : (x : A) → B x} →
    g ~ᵉ h → f ~ᵉ g → f ~ᵉ h
  concat-htpy'ᵉ f K H = H ∙ᵉh K

  concat-inv-htpyᵉ :
    {f g : (x : A) → B x} →
    f ~ᵉ g → (h : (x : A) → B x) → f ~ᵉ h → g ~ᵉ h
  concat-inv-htpyᵉ = concat-htpyᵉ ∘ᵉ inv-htpyᵉ

  concat-inv-htpy'ᵉ :
    (f : (x : A) → B x) {g h : (x : A) → B x} →
    (g ~ᵉ h) → (f ~ᵉ h) → (f ~ᵉ g)
  concat-inv-htpy'ᵉ f K = concat-htpy'ᵉ f (inv-htpyᵉ K)
```

### Whiskering of homotopies

```agda
htpy-left-whiskᵉ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {C : UUᵉ l3}
  (h : B → C) {f g : A → B} → f ~ᵉ g → (h ∘ᵉ f) ~ᵉ (h ∘ᵉ g)
htpy-left-whiskᵉ h H x = apᵉ h (H x)

_·ᵉl_ = htpy-left-whiskᵉ

htpy-right-whiskᵉ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {C : B → UUᵉ l3}
  {g h : (y : B) → C y} (H : g ~ᵉ h) (f : A → B) → (g ∘ᵉ f) ~ᵉ (h ∘ᵉ f)
htpy-right-whiskᵉ H f x = H (f x)

_·ᵉr_ = htpy-right-whiskᵉ
```

**Note**: The infix whiskering operators `_·ᵉ l_` and `_·ᵉ r_` use the
[middle dot](https://codepoints.net/U+00B7) `·ᵉ ` (agda-input: `\cdot`
`\centerdot`), as opposed to the infix homotopy concatenation operator `_∙ᵉh_`
which uses the [bullet operator](https://codepoints.net/U+2219) `∙ᵉ` (agda-input:
`\.`). If these look the same in your editor, we suggest that you change your
font. For a reference, see [How to install](HOWTO-INSTALL.md).

### Horizontal composition of homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {C : UUᵉ l3}
  {f f' : A → B} {g g' : B → C}
  where

  htpy-comp-horizontalᵉ : (f ~ᵉ f') → (g ~ᵉ g') → (g ∘ᵉ f) ~ᵉ (g' ∘ᵉ f')
  htpy-comp-horizontalᵉ F G = (g ·ᵉl F) ∙ᵉh (G ·ᵉr f')

  htpy-comp-horizontal'ᵉ : (f ~ᵉ f') → (g ~ᵉ g') → (g ∘ᵉ f) ~ᵉ (g' ∘ᵉ f')
  htpy-comp-horizontal'ᵉ F G = (G ·ᵉr f) ∙ᵉh (g' ·ᵉl F)
```

### Transposition of homotopies

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {f g h : (x : A) → B x}
  (H : f ~ᵉ g) (K : g ~ᵉ h) (L : f ~ᵉ h) (M : (H ∙ᵉh K) ~ᵉ L)
  where

  inv-con-htpyᵉ : K ~ᵉ ((inv-htpyᵉ H) ∙ᵉh L)
  inv-con-htpyᵉ x = inv-conᵉ (H x) (K x) (L x) (M x)

  inv-htpy-inv-con-htpyᵉ : ((inv-htpyᵉ H) ∙ᵉh L) ~ᵉ K
  inv-htpy-inv-con-htpyᵉ = inv-htpyᵉ inv-con-htpyᵉ

  con-inv-htpyᵉ : H ~ᵉ (L ∙ᵉh (inv-htpyᵉ K))
  con-inv-htpyᵉ x = con-invᵉ (H x) (K x) (L x) (M x)

  inv-htpy-con-inv-htpyᵉ : (L ∙ᵉh (inv-htpyᵉ K)) ~ᵉ H
  inv-htpy-con-inv-htpyᵉ = inv-htpyᵉ con-inv-htpyᵉ
```

### Associativity of concatenation of homotopies

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {f g h k : (x : A) → B x}
  (H : f ~ᵉ g) (K : g ~ᵉ h) (L : h ~ᵉ k)
  where

  assoc-htpyᵉ : ((H ∙ᵉh K) ∙ᵉh L) ~ᵉ (H ∙ᵉh (K ∙ᵉh L))
  assoc-htpyᵉ x = assocᵉ (H x) (K x) (L x)

  inv-htpy-assoc-htpyᵉ : (H ∙ᵉh (K ∙ᵉh L)) ~ᵉ ((H ∙ᵉh K) ∙ᵉh L)
  inv-htpy-assoc-htpyᵉ = inv-htpyᵉ assoc-htpyᵉ
```

### Unit laws for homotopies

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2}
  {f g : (x : A) → B x} {H : f ~ᵉ g}
  where

  left-unit-htpyᵉ : (refl-htpyᵉ ∙ᵉh H) ~ᵉ H
  left-unit-htpyᵉ x = left-unitᵉ

  inv-htpy-left-unit-htpyᵉ : H ~ᵉ (refl-htpyᵉ ∙ᵉh H)
  inv-htpy-left-unit-htpyᵉ = inv-htpyᵉ left-unit-htpyᵉ

  right-unit-htpyᵉ : (H ∙ᵉh refl-htpyᵉ) ~ᵉ H
  right-unit-htpyᵉ x = right-unitᵉ

  inv-htpy-right-unit-htpyᵉ : H ~ᵉ (H ∙ᵉh refl-htpyᵉ)
  inv-htpy-right-unit-htpyᵉ = inv-htpyᵉ right-unit-htpyᵉ
```

### Inverse laws for homotopies

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2}
  {f g : (x : A) → B x} (H : f ~ᵉ g)
  where

  left-inv-htpyᵉ : ((inv-htpyᵉ H) ∙ᵉh H) ~ᵉ refl-htpyᵉ
  left-inv-htpyᵉ = left-invᵉ ∘ᵉ H

  inv-htpy-left-inv-htpyᵉ : refl-htpyᵉ ~ᵉ ((inv-htpyᵉ H) ∙ᵉh H)
  inv-htpy-left-inv-htpyᵉ = inv-htpyᵉ left-inv-htpyᵉ

  right-inv-htpyᵉ : (H ∙ᵉh (inv-htpyᵉ H)) ~ᵉ refl-htpyᵉ
  right-inv-htpyᵉ = right-invᵉ ∘ᵉ H

  inv-htpy-right-inv-htpyᵉ : refl-htpyᵉ ~ᵉ (H ∙ᵉh (inv-htpyᵉ H))
  inv-htpy-right-inv-htpyᵉ = inv-htpyᵉ right-inv-htpyᵉ
```

### Distributivity of `inv` over `concat` for homotopies

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {f g h : (x : A) → B x}
  (H : f ~ᵉ g) (K : g ~ᵉ h)
  where

  distributive-inv-concat-htpyᵉ :
    (inv-htpyᵉ (H ∙ᵉh K)) ~ᵉ ((inv-htpyᵉ K) ∙ᵉh (inv-htpyᵉ H))
  distributive-inv-concat-htpyᵉ x = distributive-inv-concatᵉ (H x) (K x)

  inv-htpy-distributive-inv-concat-htpyᵉ :
    ((inv-htpyᵉ K) ∙ᵉh (inv-htpyᵉ H)) ~ᵉ (inv-htpyᵉ (H ∙ᵉh K))
  inv-htpy-distributive-inv-concat-htpyᵉ =
    inv-htpyᵉ distributive-inv-concat-htpyᵉ
```

### Naturality of homotopies with respect to identifications

```agda
nat-htpyᵉ :
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {f g : A → B} (H : f ~ᵉ g)
  {x y : A} (p : x ＝ᵉ y) →
  ((H x) ∙ᵉ (apᵉ g p)) ＝ᵉ ((apᵉ f p) ∙ᵉ (H y))
nat-htpyᵉ H reflᵉ = right-unitᵉ

inv-nat-htpyᵉ :
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {f g : A → B} (H : f ~ᵉ g)
  {x y : A} (p : x ＝ᵉ y) →
  ((apᵉ f p) ∙ᵉ (H y)) ＝ᵉ ((H x) ∙ᵉ (apᵉ g p))
inv-nat-htpyᵉ H p = invᵉ (nat-htpyᵉ H p)

nat-htpy-idᵉ :
  {l : Level} {A : UUᵉ l} {f : A → A} (H : f ~ᵉ idᵉ)
  {x y : A} (p : x ＝ᵉ y) → ((H x) ∙ᵉ p) ＝ᵉ ((apᵉ f p) ∙ᵉ (H y))
nat-htpy-idᵉ H reflᵉ = right-unitᵉ

inv-nat-htpy-idᵉ :
  {l : Level} {A : UUᵉ l} {f : A → A} (H : f ~ᵉ idᵉ)
  {x y : A} (p : x ＝ᵉ y) → ((apᵉ f p) ∙ᵉ (H y)) ＝ᵉ ((H x) ∙ᵉ p)
inv-nat-htpy-idᵉ H p = invᵉ (nat-htpy-idᵉ H p)
```

### A coherence for homotopies to the identity function

````agda
module _
  {l : Level} {A : UUᵉ l} {f : A → A} (H : f ~ᵉ idᵉ)
  where

  coh-htpy-idᵉ : (H ·ᵉr f) ~ᵉ (f ·ᵉl H)
  coh-htpy-idᵉ x = is-injective-concat'ᵉ (H x) (nat-htpy-idᵉ H (H x))

  inv-htpy-coh-htpy-idᵉ : (f ·ᵉl H) ~ᵉ (H ·ᵉr f)
  inv-htpy-coh-htpy-idᵉ = inv-htpyᵉ coh-htpy-idᵉ
```

### Homotopies preserve the laws of the action on identity types

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {f g h : (x : A) → B x}
  where

  ap-concat-htpyᵉ :
    (H : f ~ᵉ g) (K K' : g ~ᵉ h) → K ~ᵉ K' → (H ∙ᵉh K) ~ᵉ (H ∙ᵉh K')
  ap-concat-htpyᵉ H K K' L x = apᵉ (concatᵉ (H x) (h x)) (L x)

  ap-concat-htpy'ᵉ :
    (H H' : f ~ᵉ g) (K : g ~ᵉ h) → H ~ᵉ H' → (H ∙ᵉh K) ~ᵉ (H' ∙ᵉh K)
  ap-concat-htpy'ᵉ H H' K L x =
    apᵉ (concat'ᵉ _ (K x)) (L x)

module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {f g : (x : A) → B x}
  {H H' : f ~ᵉ g}
  where

  ap-inv-htpyᵉ :
    H ~ᵉ H' → (inv-htpyᵉ H) ~ᵉ (inv-htpyᵉ H')
  ap-inv-htpyᵉ K x = apᵉ invᵉ (K x)
```

### Laws for whiskering an inverted homotopy

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {C : UUᵉ l3}
  where

  left-whisk-inv-htpyᵉ :
    {f f' : A → B} (g : B → C) (H : f ~ᵉ f') →
    (g ·ᵉl (inv-htpyᵉ H)) ~ᵉ inv-htpyᵉ (g ·ᵉl H)
  left-whisk-inv-htpyᵉ g H x = ap-invᵉ g (H x)

  inv-htpy-left-whisk-inv-htpyᵉ :
    {f f' : A → B} (g : B → C) (H : f ~ᵉ f') →
    inv-htpyᵉ (g ·ᵉl H) ~ᵉ (g ·ᵉl (inv-htpyᵉ H))
  inv-htpy-left-whisk-inv-htpyᵉ g H =
    inv-htpyᵉ (left-whisk-inv-htpyᵉ g H)

  right-whisk-inv-htpyᵉ :
    {g g' : B → C} (H : g ~ᵉ g') (f : A → B) →
    ((inv-htpyᵉ H) ·ᵉr f) ~ᵉ (inv-htpyᵉ (H ·ᵉr f))
  right-whisk-inv-htpyᵉ H f = refl-htpyᵉ

  inv-htpy-right-whisk-inv-htpyᵉ :
    {g g' : B → C} (H : g ~ᵉ g') (f : A → B) →
    ((inv-htpyᵉ H) ·ᵉr f) ~ᵉ (inv-htpyᵉ (H ·ᵉr f))
  inv-htpy-right-whisk-inv-htpyᵉ H f =
    inv-htpyᵉ (right-whisk-inv-htpyᵉ H f)
```

## Reasoning with homotopies

Homotopies can be constructed by equational reasoning in the following way:

```text
homotopy-reasoning
  f ~ᵉ g by htpy-1
    ~ᵉ h by htpy-2
    ~ᵉ i by htpy-3
```

The homotopy obtained in this way is `htpy-1 ∙ᵉh (htpy-2 ∙ᵉh htpy-3)`, i.e., it is
associated fully to the right.

```agda
infixl 1 homotopy-reasoningᵉ_
infixl 0 step-homotopy-reasoningᵉ

homotopy-reasoningᵉ_ :
  {l1 l2 : Level} {X : UUᵉ l1} {Y : X → UUᵉ l2}
  (f : (x : X) → Y x) → f ~ᵉ f
homotopy-reasoningᵉ f = refl-htpyᵉ

step-homotopy-reasoningᵉ :
  {l1 l2 : Level} {X : UUᵉ l1} {Y : X → UUᵉ l2}
  {f g : (x : X) → Y x} → (f ~ᵉ g) →
  (h : (x : X) → Y x) → (g ~ᵉ h) → (f ~ᵉ h)
step-homotopy-reasoningᵉ p h q = p ∙ᵉh q

syntax step-homotopy-reasoningᵉ p h q = p ~ᵉ h by q
```

## See also

- We postulate that homotopies characterize identifications in (dependent)
  function types in the file
  [`foundation-core.function-extensionality`](foundation-core.function-extensionality.md).
````
