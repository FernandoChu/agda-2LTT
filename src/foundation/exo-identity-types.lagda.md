# Identity types

```agda
module foundation.exo-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.exo-constant-maps
open import foundation.exo-function-types
open import foundation.exo-universes
```

</details>

## Idea

The equality relation on a type is a reflexive relation, with the universal
property that it maps uniquely into any other reflexive relation. In type
theory, we introduce the identity type as an inductive family of types, where
the induction principle can be understood as expressing that the identity type
is the least reflexive relation.

### Notation of the identity type

We include two notations for the identity type. First, we introduce the identity
type using Martin-Löf's original notation `Id`. Then we introduce as a secondary
option the infix notation `_＝_`.

**Note**: The equals sign in the infix notation is not the standard equals sign
on your keyboard, but it is the
[full width equals sign](https://codepoints.net/U+ff1d). Note that the full
width equals sign is slightly wider, and it is highlighted like all the other
defined constructions in Agda. In order to type the full width equals sign in
Agda's Emacs Mode, you need to add it to your agda input method as follows:

- Type `M-x customize-variable` and press enter.
- Type `agda-input-user-translations` and press enter.
- Click the `INS` button
- Type the regular equals sign `=` in the Key sequence field.
- Click the `INS` button
- Type the full width equals sign `＝` in the translations field.
- Click the `Apply and save` button.

After completing these steps, you can type `\=` in order to obtain the full
width equals sign `＝`.

## Definition

```agda
module _
  {l : Level} {A : UUᵉ l}
  where

  data Idᵉ (x : A) : A → UUᵉ l where
    reflᵉ : Idᵉ x x

  infix 6 _＝ᵉ_
  _＝ᵉ_ : A → A → UUᵉ l
  (a ＝ᵉ b) = Idᵉ a b
```

### UIP

```agda
module _
  {l : Level} {A : UUᵉ l}
  where
  UIPᵉ : {x y : A} (p q : x ＝ᵉ y) → p ＝ᵉ q
  UIPᵉ reflᵉ reflᵉ = reflᵉ
```

### The induction principle

The induction principle of identity types states that given a base point `x : A`
and a family of types over the identity types based at `x`,
`B : (y : A) (p : x ＝ᵉ y) → UUᵉ l2`, then to construct a dependent function
`f : (y : A) (p : x ＝ᵉ y) → B y p` it suffices to define it at `f x reflᵉ`.

Note that Agda's pattern matching machinery allows us to define many operations
on the identity type directly. However, sometimes it is useful to explicitly
have the induction principle of the identity type.

```agda
ind-Idᵉ :
  {l1 l2 : Level} {A : UUᵉ l1}
  (x : A) (B : (y : A) (p : x ＝ᵉ y) → UUᵉ l2) →
  (B x reflᵉ) → (y : A) (p : x ＝ᵉ y) → B y p
ind-Idᵉ x B b y reflᵉ = b
```

## Structure

The identity types form a weak groupoidal structure on types.

### Concatenation of identifications

```agda
module _
  {l : Level} {A : UUᵉ l}
  where

  infixl 15 _∙ᵉ_
  _∙ᵉ_ : {x y z : A} → x ＝ᵉ y → y ＝ᵉ z → x ＝ᵉ z
  reflᵉ ∙ᵉ q = q

  concatᵉ : {x y : A} → x ＝ᵉ y → (z : A) → y ＝ᵉ z → x ＝ᵉ z
  concatᵉ p z q = p ∙ᵉ q

  concat'ᵉ : (x : A) {y z : A} → y ＝ᵉ z → x ＝ᵉ y → x ＝ᵉ z
  concat'ᵉ x q p = p ∙ᵉ q
```

### Inverting identifications

```agda
module _
  {l : Level} {A : UUᵉ l}
  where

  invᵉ : {x y : A} → x ＝ᵉ y → y ＝ᵉ x
  invᵉ reflᵉ = reflᵉ
```

### The groupoidal laws for types

```agda
module _
  {l : Level} {A : UUᵉ l}
  where

  assocᵉ :
    {x y z w : A} (p : x ＝ᵉ y) (q : y ＝ᵉ z) (r : z ＝ᵉ w) →
    ((p ∙ᵉ q) ∙ᵉ r) ＝ᵉ (p ∙ᵉ (q ∙ᵉ r))
  assocᵉ reflᵉ q r = reflᵉ

  left-unitᵉ : {x y : A} {p : x ＝ᵉ y} → (reflᵉ ∙ᵉ p) ＝ᵉ p
  left-unitᵉ = reflᵉ

  right-unitᵉ : {x y : A} {p : x ＝ᵉ y} → (p ∙ᵉ reflᵉ) ＝ᵉ p
  right-unitᵉ {p = reflᵉ} = reflᵉ

  left-invᵉ : {x y : A} (p : x ＝ᵉ y) → ((invᵉ p) ∙ᵉ p) ＝ᵉ reflᵉ
  left-invᵉ reflᵉ = reflᵉ

  right-invᵉ : {x y : A} (p : x ＝ᵉ y) → (p ∙ᵉ (invᵉ p)) ＝ᵉ reflᵉ
  right-invᵉ reflᵉ = reflᵉ

  inv-invᵉ : {x y : A} (p : x ＝ᵉ y) → (invᵉ (invᵉ p)) ＝ᵉ p
  inv-invᵉ reflᵉ = reflᵉ

  distributive-inv-concatᵉ :
    {x y : A} (p : x ＝ᵉ y) {z : A} (q : y ＝ᵉ z) →
    (invᵉ (p ∙ᵉ q)) ＝ᵉ ((invᵉ q) ∙ᵉ (invᵉ p))
  distributive-inv-concatᵉ reflᵉ reflᵉ = reflᵉ
```

### Transposing inverses

The fact that `inv-con` and `con-inv` are equivalences is recorded in
[`foundation.identity-types`](foundation.identity-types.md).

```agda
inv-conᵉ :
  {l : Level} {A : UUᵉ l} {x y : A} (p : x ＝ᵉ y) {z : A} (q : y ＝ᵉ z)
  (r : x ＝ᵉ z) → ((p ∙ᵉ q) ＝ᵉ r) → q ＝ᵉ ((invᵉ p) ∙ᵉ r)
inv-conᵉ reflᵉ q r s = s

con-invᵉ :
  {l : Level} {A : UUᵉ l} {x y : A} (p : x ＝ᵉ y) {z : A} (q : y ＝ᵉ z)
  (r : x ＝ᵉ z) → ((p ∙ᵉ q) ＝ᵉ r) → p ＝ᵉ (r ∙ᵉ (invᵉ q))
con-invᵉ p reflᵉ r s = ((invᵉ right-unitᵉ) ∙ᵉ s) ∙ᵉ (invᵉ right-unitᵉ)
```

### The functorial action of functions on identity types

```agda
apᵉ :
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) {x y : A} →
  x ＝ᵉ y → (f x) ＝ᵉ (f y)
apᵉ f reflᵉ = reflᵉ
```

### Laws for the functorial action on paths

```agda
ap-idᵉ :
  {l : Level} {A : UUᵉ l} {x y : A} (p : x ＝ᵉ y) → (apᵉ idᵉ p) ＝ᵉ p
ap-idᵉ reflᵉ = reflᵉ

ap-compᵉ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {C : UUᵉ l3} (g : B → C)
  (f : A → B) {x y : A} (p : x ＝ᵉ y) → (apᵉ (g ∘ᵉ f) p) ＝ᵉ ((apᵉ g ∘ᵉ apᵉ f) p)
ap-compᵉ g f reflᵉ = reflᵉ

ap-reflᵉ :
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) (x : A) →
  (apᵉ f (reflᵉ {x = x})) ＝ᵉ reflᵉ
ap-reflᵉ f x = reflᵉ

inv-ap-reflᵉ-concatᵉ :
  {l : Level} {A : UUᵉ l} {x y : A} {p q : x ＝ᵉ y} (r : p ＝ᵉ q) →
  (right-unitᵉ ∙ᵉ (r ∙ᵉ invᵉ right-unitᵉ)) ＝ᵉ (apᵉ (_∙ᵉ reflᵉ) r)
inv-ap-reflᵉ-concatᵉ reflᵉ = right-invᵉ right-unitᵉ

ap-reflᵉ-concatᵉ :
  {l : Level} {A : UUᵉ l} {x y : A} {p q : x ＝ᵉ y} (r : p ＝ᵉ q) →
  (apᵉ (_∙ᵉ reflᵉ) r) ＝ᵉ (right-unitᵉ ∙ᵉ (r ∙ᵉ invᵉ right-unitᵉ))
ap-reflᵉ-concatᵉ = invᵉ ∘ᵉ inv-ap-reflᵉ-concatᵉ

ap-concatᵉ :
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) {x y z : A}
  (p : x ＝ᵉ y) (q : y ＝ᵉ z) → (apᵉ f (p ∙ᵉ q)) ＝ᵉ ((apᵉ f p) ∙ᵉ (apᵉ f q))
ap-concatᵉ f reflᵉ q = reflᵉ

ap-concatᵉ-eq :
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) {x y z : A}
  (p : x ＝ᵉ y) (q : y ＝ᵉ z) (r : x ＝ᵉ z)
  (H : r ＝ᵉ (p ∙ᵉ q)) → (apᵉ f r) ＝ᵉ ((apᵉ f p) ∙ᵉ (apᵉ f q))
ap-concatᵉ-eq f p q .(p ∙ᵉ q) reflᵉ = ap-concatᵉ f p q

ap-invᵉ :
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) {x y : A}
  (p : x ＝ᵉ y) → (apᵉ f (invᵉ p)) ＝ᵉ (invᵉ (apᵉ f p))
ap-invᵉ f reflᵉ = reflᵉ

ap-constᵉ :
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (b : B) {x y : A}
  (p : x ＝ᵉ y) → (apᵉ (const A B b) p) ＝ᵉ reflᵉ
ap-constᵉ b reflᵉ = reflᵉ
```

### Transport

We introduce the operation of transport between fibers over an identification.

The fact that `trᵉ B p` is an equivalence is recorded in
[`foundation.identity-types`](foundation.identity-types.md).

```agda
trᵉ :
  {l1 l2 : Level} {A : UUᵉ l1} (B : A → UUᵉ l2) {x y : A} (p : x ＝ᵉ y) → B x → B y
trᵉ B reflᵉ b = b

path-overᵉ :
  {l1 l2 : Level} {A : UUᵉ l1} (B : A → UUᵉ l2) {x x' : A} (p : x ＝ᵉ x') →
  B x → B x' → UUᵉ l2
path-overᵉ B p y y' = (trᵉ B p y) ＝ᵉ y'

reflᵉ-path-overᵉ :
  {l1 l2 : Level} {A : UUᵉ l1} (B : A → UUᵉ l2) (x : A) (y : B x) →
  path-overᵉ B reflᵉ y y
reflᵉ-path-overᵉ B x y = reflᵉ
```

### Laws for transport

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2}
  where

  tr-concatᵉ :
    {x y z : A} (p : x ＝ᵉ y) (q : y ＝ᵉ z) (b : B x) →
    trᵉ B (p ∙ᵉ q) b ＝ᵉ trᵉ B q (trᵉ B p b)
  tr-concatᵉ reflᵉ q b = reflᵉ

  eq-transpose-trᵉ :
    {x y : A} (p : x ＝ᵉ y) {u : B x} {v : B y} →
    v ＝ᵉ (trᵉ B p u) → (trᵉ B (invᵉ p) v) ＝ᵉ u
  eq-transpose-trᵉ reflᵉ q = q

  eq-transpose-tr'ᵉ :
    {x y : A} (p : x ＝ᵉ y) {u : B x} {v : B y} →
    (trᵉ B p u) ＝ᵉ v → u ＝ᵉ (trᵉ B (invᵉ p) v)
  eq-transpose-tr'ᵉ reflᵉ q = q

tr-apᵉ :
  {l1 l2 l3 l4 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {C : UUᵉ l3} {D : C → UUᵉ l4}
  (f : A → C) (g : (x : A) → B x → D (f x)) {x y : A} (p : x ＝ᵉ y) (z : B x) →
  (trᵉ D (apᵉ f p) (g x z)) ＝ᵉ (g y (trᵉ B p z))
tr-apᵉ f g reflᵉ z = reflᵉ

preserves-trᵉ :
  {l1 l2 l3 : Level} {I : UUᵉ l1} {A : I → UUᵉ l2} {B : I → UUᵉ l3}
  (f : (i : I) → A i → B i) {i j : I} (p : i ＝ᵉ j) (x : A i) →
  f j (trᵉ A p x) ＝ᵉ trᵉ B p (f i x)
preserves-trᵉ f reflᵉ x = reflᵉ

tr-Id-leftᵉ :
  {l : Level} {A : UUᵉ l} {a b c : A} (q : b ＝ᵉ c) (p : b ＝ᵉ a) →
  (trᵉ (_＝ᵉ a) q p) ＝ᵉ ((invᵉ q) ∙ᵉ p)
tr-Id-leftᵉ reflᵉ p = reflᵉ

tr-Id-rightᵉ :
  {l : Level} {A : UUᵉ l} {a b c : A} (q : b ＝ᵉ c) (p : a ＝ᵉ b) →
  trᵉ (a ＝ᵉ_) q p ＝ᵉ (p ∙ᵉ q)
tr-Id-rightᵉ reflᵉ reflᵉ = reflᵉ

tr-constᵉ :
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {x y : A} (p : x ＝ᵉ y) (b : B) →
  trᵉ (λ (a : A) → B) p b ＝ᵉ b
tr-constᵉ reflᵉ b = reflᵉ
```

### Functorial action of dependent functions on identity types

```agda
apdᵉ :
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} (f : (x : A) → B x) {x y : A}
  (p : x ＝ᵉ y) → trᵉ B p (f x) ＝ᵉ f y
apdᵉ f reflᵉ = reflᵉ

apd-constᵉ :
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) {x y : A}
  (p : x ＝ᵉ y) → apdᵉ f p ＝ᵉ ((tr-constᵉ p (f x)) ∙ᵉ (apᵉ f p))
apd-constᵉ f reflᵉ = reflᵉ
```

### Concatᵉenation is injective

```agda
module _
  {l1 : Level} {A : UUᵉ l1}
  where

  is-injective-concatᵉ :
    {x y z : A} (p : x ＝ᵉ y) {q r : y ＝ᵉ z} → (p ∙ᵉ q) ＝ᵉ (p ∙ᵉ r) → q ＝ᵉ r
  is-injective-concatᵉ reflᵉ s = s

  issec-is-injective-concatᵉ :
    {x y z : A} (p : x ＝ᵉ y) {q r : y ＝ᵉ z} (s : (p ∙ᵉ q) ＝ᵉ (p ∙ᵉ r)) →
    apᵉ (concatᵉ p z) (is-injective-concatᵉ p s) ＝ᵉ s
  issec-is-injective-concatᵉ reflᵉ reflᵉ = reflᵉ

  is-injective-concat'ᵉ :
    {x y z : A} (r : y ＝ᵉ z) {p q : x ＝ᵉ y} → (p ∙ᵉ r) ＝ᵉ (q ∙ᵉ r) → p ＝ᵉ q
  is-injective-concat'ᵉ reflᵉ s = (invᵉ right-unitᵉ) ∙ᵉ (s ∙ᵉ right-unitᵉ)

  cases-issec-is-injective-concat'ᵉ :
    {x y : A} {p q : x ＝ᵉ y} (s : p ＝ᵉ q) →
    ( apᵉ
      ( concat'ᵉ x reflᵉ)
      ( is-injective-concat'ᵉ reflᵉ (right-unitᵉ ∙ᵉ (s ∙ᵉ invᵉ right-unitᵉ)))) ＝ᵉ
    ( right-unitᵉ ∙ᵉ (s ∙ᵉ invᵉ right-unitᵉ))
  cases-issec-is-injective-concat'ᵉ {p = reflᵉ} reflᵉ = reflᵉ

  issec-is-injective-concat'ᵉ :
    {x y z : A} (r : y ＝ᵉ z) {p q : x ＝ᵉ y} (s : (p ∙ᵉ r) ＝ᵉ (q ∙ᵉ r)) →
    apᵉ (concat'ᵉ x r) (is-injective-concat'ᵉ r s) ＝ᵉ s
  issec-is-injective-concat'ᵉ reflᵉ s =
    apᵉ (λ u → apᵉ (concat'ᵉ _ reflᵉ) (is-injective-concat'ᵉ reflᵉ u)) (invᵉ α) ∙ᵉ
    ( ( cases-issec-is-injective-concat'ᵉ (invᵉ right-unitᵉ ∙ᵉ (s ∙ᵉ right-unitᵉ))) ∙ᵉ
      α)
    where
    α :
      ( ( right-unitᵉ) ∙ᵉ
        ( ( invᵉ right-unitᵉ ∙ᵉ (s ∙ᵉ right-unitᵉ)) ∙ᵉ
          ( invᵉ right-unitᵉ))) ＝ᵉ
      ( s)
    α =
      ( apᵉ
        ( concatᵉ right-unitᵉ _)
        ( ( assocᵉ (invᵉ right-unitᵉ) (s ∙ᵉ right-unitᵉ) (invᵉ right-unitᵉ)) ∙ᵉ
          ( ( apᵉ
              ( concatᵉ (invᵉ right-unitᵉ) _)
              ( ( assocᵉ s right-unitᵉ (invᵉ right-unitᵉ)) ∙ᵉ
                ( ( apᵉ (concatᵉ s _) (right-invᵉ right-unitᵉ)) ∙ᵉ
                  ( right-unitᵉ))))))) ∙ᵉ
      ( ( invᵉ (assocᵉ right-unitᵉ (invᵉ right-unitᵉ) s)) ∙ᵉ
        ( ( apᵉ (concat'ᵉ _ s) (right-invᵉ right-unitᵉ))))
```

### The Mac Lane pentagon for identity types

```agda
Mac-Lane-pentagonᵉ :
  {l : Level} {A : UUᵉ l} {a b c d e : A}
  (p : a ＝ᵉ b) (q : b ＝ᵉ c) (r : c ＝ᵉ d) (s : d ＝ᵉ e) →
  let α₁ = (apᵉ (λ t → t ∙ᵉ s) (assocᵉ p q r))
      α₂ = (assocᵉ p (q ∙ᵉ r) s)
      α₃ = (apᵉ (λ t → p ∙ᵉ t) (assocᵉ q r s))
      α₄ = (assocᵉ (p ∙ᵉ q) r s)
      α₅ = (assocᵉ p q (r ∙ᵉ s))
  in
  ((α₁ ∙ᵉ α₂) ∙ᵉ α₃) ＝ᵉ (α₄ ∙ᵉ α₅)
Mac-Lane-pentagonᵉ reflᵉ reflᵉ reflᵉ reflᵉ = reflᵉ
```

### The binary action on identifications

```agda
ap-binaryᵉ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2}
  {C : UUᵉ l3} (f : A → B → C) →
  {x x' : A} (p : x ＝ᵉ x') {y y' : B}
  (q : y ＝ᵉ y') → (f x y) ＝ᵉ (f x' y')
ap-binaryᵉ f reflᵉ reflᵉ = reflᵉ

ap-binary-diagonalᵉ :
  {l1 l2 : Level} {A : UUᵉ l1}
  {B : UUᵉ l2} (f : A → A → B) →
  {x x' : A} (p : x ＝ᵉ x') →
  (ap-binaryᵉ f p p) ＝ᵉ (apᵉ (λ a → f a a) p)
ap-binary-diagonalᵉ f reflᵉ = reflᵉ

triangle-ap-binaryᵉ :
  {l1 l2 l3 : Level} {A : UUᵉ l1}
  {B : UUᵉ l2} {C : UUᵉ l3} (f : A → B → C) →
  {x x' : A} (p : x ＝ᵉ x') {y y' : B} (q : y ＝ᵉ y') →
  (ap-binaryᵉ f p q) ＝ᵉ (apᵉ (λ z → f z y) p ∙ᵉ apᵉ (f x') q)
triangle-ap-binaryᵉ f reflᵉ reflᵉ = reflᵉ

triangle-ap-binary'ᵉ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2}
  {C : UUᵉ l3} (f : A → B → C) →
  {x x' : A} (p : x ＝ᵉ x') {y y' : B} (q : y ＝ᵉ y') →
  (ap-binaryᵉ f p q) ＝ᵉ (apᵉ (f x) q ∙ᵉ apᵉ (λ z → f z y') p)
triangle-ap-binary'ᵉ f reflᵉ reflᵉ = reflᵉ

left-unit-ap-binaryᵉ :
  {l1 l2 l3 : Level} {A : UUᵉ l1}
  {B : UUᵉ l2} {C : UUᵉ l3} (f : A → B → C) →
  {x : A} {y y' : B} (q : y ＝ᵉ y') →
  (ap-binaryᵉ f reflᵉ q) ＝ᵉ (apᵉ (f x) q)
left-unit-ap-binaryᵉ f reflᵉ = reflᵉ

right-unit-ap-binaryᵉ :
  {l1 l2 l3 : Level} {A : UUᵉ l1}
  {B : UUᵉ l2} {C : UUᵉ l3} (f : A → B → C) →
  {x x' : A} (p : x ＝ᵉ x') {y : B} →
  (ap-binaryᵉ f p reflᵉ) ＝ᵉ (apᵉ (λ z → f z y) p)
right-unit-ap-binaryᵉ f reflᵉ = reflᵉ

ap-binary-compᵉ :
  {l1 l2 l3 l4 l5 : Level} {X : UUᵉ l4} {Y : UUᵉ l5}
  {A : UUᵉ l1} {B : UUᵉ l2} {C : UUᵉ l3} (H : A → B → C)
  (f : X → A) (g : Y → B) {x0 x1 : X} (p : x0 ＝ᵉ x1)
  {y0 y1 : Y} (q : y0 ＝ᵉ y1) → (ap-binaryᵉ (λ x y → H (f x) (g y)) p q) ＝ᵉ
    ap-binaryᵉ H (apᵉ f p) (apᵉ g q)
ap-binary-compᵉ H f g reflᵉ reflᵉ = reflᵉ

ap-binary-comp-diagonalᵉ :
  {l1 l2 l3 l4 : Level} {A' : UUᵉ l4} {A : UUᵉ l1}
  {B : UUᵉ l2} {C : UUᵉ l3} (H : A → B → C)
  (f : A' → A) (g : A' → B) {a'0 a'1 : A'} (p : a'0 ＝ᵉ a'1) →
  (apᵉ (λ z → H (f z) (g z)) p) ＝ᵉ ap-binaryᵉ H (apᵉ f p) (apᵉ g p)
ap-binary-comp-diagonalᵉ H f g p =
  ( invᵉ (ap-binary-diagonalᵉ (λ x y → H (f x) (g y)) p)) ∙ᵉ
  ( ap-binary-compᵉ H f g p p)

ap-binary-comp'ᵉ :
  {l1 l2 l3 l4 : Level} {A : UUᵉ l1} {B : UUᵉ l2}
  {C : UUᵉ l3} {D : UUᵉ l4} (f : C → D) (H : A → B → C)
  {a0 a1 : A} (p : a0 ＝ᵉ a1) {b0 b1 : B} (q : b0 ＝ᵉ b1) →
  (ap-binaryᵉ (λ a b → f (H a b)) p q) ＝ᵉ (apᵉ f (ap-binaryᵉ H p q))
ap-binary-comp'ᵉ f H reflᵉ reflᵉ = reflᵉ

ap-binary-permuteᵉ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {a0 a1 : A}
  {B : UUᵉ l2} {b0 b1 : B} {C : UUᵉ l3} (f : A → B → C) →
  (p : a0 ＝ᵉ a1) (q : b0 ＝ᵉ b1) →
  (ap-binaryᵉ (λ y x → f x y) q p) ＝ᵉ (ap-binaryᵉ f p q)
ap-binary-permuteᵉ f reflᵉ reflᵉ = reflᵉ

ap-binary-concatᵉ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {a0 a1 a2 : A}
  {B : UUᵉ l2} {b0 b1 b2 : B} {C : UUᵉ l3}
  (f : A → B → C) (p : a0 ＝ᵉ a1) (p' : a1 ＝ᵉ a2)
  (q : b0 ＝ᵉ b1) (q' : b1 ＝ᵉ b2) →
  (ap-binaryᵉ f (p ∙ᵉ p') (q ∙ᵉ q')) ＝ᵉ
    ((ap-binaryᵉ f p q) ∙ᵉ (ap-binaryᵉ f p' q'))
ap-binary-concatᵉ f reflᵉ reflᵉ reflᵉ reflᵉ = reflᵉ
```

## Equational reasoning

Identifications can be constructed by equational reasoning in the following way:

```text
equational-reasoning
  x ＝ᵉ y by eq-1
    ＝ᵉ z by eq-2
    ＝ᵉ v by eq-3
```

The resulting identification of this computaion is `eq-1 ∙ᵉ (eq-2 ∙ᵉ eq-3)`, i.e.,
the identification is associated fully to the right. For examples of the use of
equational reasoning, see
[addition-integers](elementary-number-theory.addition-integers.md).

```agda
infixl 1 equational-reasoningᵉ_
infixl 0 step-equational-reasoningᵉ

equational-reasoningᵉ_ :
  {l : Level} {X : UUᵉ l} (x : X) → x ＝ᵉ x
equational-reasoningᵉ x = reflᵉ

step-equational-reasoningᵉ :
  {l : Level} {X : UUᵉ l} {x y : X} →
  (x ＝ᵉ y) → (u : X) → (y ＝ᵉ u) → (x ＝ᵉ u)
step-equational-reasoningᵉ p z q = p ∙ᵉ q

syntax step-equational-reasoningᵉ p z q = p ＝ᵉ z byᵉ q
```

## References

Our setup of equational reasoning is derived from the following sources:

1. Martín Escardó.
   <https://github.com/martinescardo/TypeTopology/blob/master/source/Id.lagda>

2. Martín Escardó.
   <https://github.com/martinescardo/TypeTopology/blob/master/source/UF-Equiv.lagda>

3. The Agda standard library.
   <https://github.com/agda/agda-stdlib/blob/master/src/Relation/Binary/PropositionalEquality/Core.agda>
