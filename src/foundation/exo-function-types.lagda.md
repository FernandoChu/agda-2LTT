# Functions

```agda
module foundation.exo-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.exo-universes
```

</details>

## Idea

Functions are primitive in Agda. Here we construct some basic functions

## Examples

### The identity function

```agda
idᵉ : {l : Level} {A : UUᵉ l} → A → A
idᵉ a = a

idω : {A : UUᵉω} → A → A
idω a = a
```

### Dependent composition of functions

```agda
infixr 15 _∘ᵉ_

_∘ᵉ_ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {C : (a : A) → B a → UUᵉ l3} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ᵉ f) a = g (f a)
```

### Evaluation at a point

```agda
ev-point :
  {l1 l2 : Level} {A : UUᵉ l1} (a : A) {P : A → UUᵉ l2} → ((x : A) → P x) → P a
ev-point a f = f a

ev-point' :
  {l1 l2 : Level} {A : UUᵉ l1} (a : A) {X : UUᵉ l2} → (A → X) → X
ev-point' a f = f a
```

### Precomposition functions

```agda
precomp-Π :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) (C : B → UUᵉ l3) →
  ((b : B) → C b) → ((a : A) → C (f a))
precomp-Π f C h a = h (f a)

precomp :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) (C : UUᵉ l3) →
  (B → C) → (A → C)
precomp f C = precomp-Π f (λ b → C)
```

### Postcomposition functions

```agda
postcomp :
  {l1 l2 l3 : Level} {X : UUᵉ l1} {Y : UUᵉ l2} (A : UUᵉ l3) →
  (X → Y) → (A → X) → (A → Y)
postcomp A f h = f ∘ᵉ h

map-Π :
  {l1 l2 l3 : Level} {I : UUᵉ l1} {A : I → UUᵉ l2} {B : I → UUᵉ l3}
  (f : (i : I) → A i → B i) →
  ((i : I) → A i) → ((i : I) → B i)
map-Π f h i = f i (h i)

map-Π' :
  {l1 l2 l3 l4 : Level} {I : UUᵉ l1} {A : I → UUᵉ l2} {B : I → UUᵉ l3}
  {J : UUᵉ l4} (α : J → I) →
  ((i : I) → A i → B i) → ((j : J) → A (α j)) → ((j : J) → B (α j))
map-Π' α f = map-Π (λ j → f (α j))
```
