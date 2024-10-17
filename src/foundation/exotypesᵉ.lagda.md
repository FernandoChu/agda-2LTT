```agda
module foundation.exotypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.identity-types
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
open import foundation.universe-levels
```

</details>

### The mixed function composition

```agda
_∘ᵉᵉᶠ_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UUᵉ l2} {C : (a : A) → B a → UUᵉ l3} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ᵉᵉᶠ f) a = g (f a)

_∘ᵉᶠᵉ_ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : A → UU l2} {C : (a : A) → B a → UUᵉ l3} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ᵉᶠᵉ f) a = g (f a)

_∘ᶠᵉᵉ_ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {C : (a : A) → B a → UU l3} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ᶠᵉᵉ f) a = g (f a)

_∘ᵉᶠᶠ_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (a : A) → B a → UUᵉ l3} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ᵉᶠᶠ f) a = g (f a)

_∘ᶠᶠᵉ_ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : A → UU l2} {C : (a : A) → B a → UU l3} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ᶠᶠᵉ f) a = g (f a)

_∘ᶠᵉᶠ_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UUᵉ l2} {C : (a : A) → B a → UU l3} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ᶠᵉᶠ f) a = g (f a)

infixr 15 _∘ᵉᵉᶠ_
infixr 15 _∘ᵉᶠᵉ_
infixr 15 _∘ᶠᵉᵉ_
infixr 15 _∘ᵉᶠᶠ_
infixr 15 _∘ᶠᶠᵉ_
infixr 15 _∘ᶠᵉᶠ_
```

# Mixed ap

```agda
apᵐ :
  {l1 l2 : Level} {A : UUᵉ l1} {B : UU l2} (f : A → B) {x y : A} →
  x ＝ᵉ y → (f x) ＝ (f y)
apᵐ fᵉ reflᵉ = refl
```

# Mixed transport

```agda
trᵐ :
  {l1 l2 : Level} {A : UUᵉ l1} (B : A → UU l2) {x y : A} (p : x ＝ᵉ y) → B x → B y
trᵐ B reflᵉ b = b

is-set-exotypeᵉ : {l : Level} (X : UUᵉ l) → is-setᵉ X
pr1ᵉ (is-set-exotypeᵉ X x .x reflᵉ reflᵉ) = reflᵉ
pr2ᵉ (is-set-exotypeᵉ X x .x reflᵉ reflᵉ) reflᵉ = reflᵉ

exotype-Setᵉ : {l : Level} (X : UUᵉ l) → Setᵉ l
pr1ᵉ (exotype-Setᵉ X) = X
pr2ᵉ (exotype-Setᵉ X) = is-set-exotypeᵉ X

has-uip-exotypeᵉ : {l : Level} → (X : UUᵉ l) → has-uipᵉ X
has-uip-exotypeᵉ X = is-set-has-uipᵉ (is-set-exotypeᵉ X)
```
