# Coercing

```agda
module foundation.coercing-inner-typesᵉ where

open import foundation.pi-decompositionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.equivalencesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.coproduct-types
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.pi-decompositions
```

## Idea

Every inner type can be coerced into an outer type.

## Definition

```agda
record coerce {i : Level} (A : UU i) : UUᵉ i where
  constructor map-coerce
  field
    map-inv-coerce : A

open coerce public
```

## Properties

### The functorial action of `map-inv-coerce` on identity types

```agda
ap-map-inv-coerce :
  {l : Level} {A : UU l} {x y : coerce A} →
  x ＝ᵉ y → map-inv-coerce x ＝ map-inv-coerce y
ap-map-inv-coerce reflᵉ = refl
```

### Coercion respects dependent pair types up isomorphism

```agda
Σᵉ-coerce :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  UUᵉ (l1 ⊔ l2)
Σᵉ-coerce A B = Σᵉ (coerce A) (λ a → coerce (B (map-inv-coerce a)))

map-coerce-Σᵉ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  Σᵉ-coerce A B → coerce (Σ A B)
map-coerce-Σᵉ A B (map-coerce a ,ᵉ map-coerce b) = map-coerce (a , b)

map-inv-coerce-Σᵉ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  coerce (Σ A B) → Σᵉ-coerce A B
map-inv-coerce-Σᵉ A B (map-coerce (a , b)) =
  pairᵉ (map-coerce a) (map-coerce b)

is-equiv-map-coerce-Σᵉ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  is-equivᵉ (map-coerce-Σᵉ A B)
is-equiv-map-coerce-Σᵉ A B =
  is-equiv-is-invertibleᵉ
    ( map-inv-coerce-Σᵉ A B)
    ( λ { (map-coerce (a , b)) → reflᵉ})
    ( λ { (map-coerce a ,ᵉ map-coerce b) → reflᵉ})

equiv-coerce-Σᵉ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  Σᵉ-coerce A B ≃ᵉ coerce (Σ A B)
pr1ᵉ (equiv-coerce-Σᵉ A B) = map-coerce-Σᵉ A B
pr2ᵉ (equiv-coerce-Σᵉ A B) = is-equiv-map-coerce-Σᵉ A B
```

### Coercion respects dependent function types up to isomorphism

```agda
Πᵉ-coerce :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  UUᵉ (l1 ⊔ l2)
Πᵉ-coerce A B = Πᵉ (coerce A) (λ a → coerce (B (map-inv-coerce a)))

map-coerce-Πᵉ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  Πᵉ-coerce A B → coerce (Π A B)
map-coerce-Πᵉ A B f = map-coerce λ a → map-inv-coerce (f (map-coerce a))

map-inv-coerce-Πᵉ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  coerce (Π A B) → Πᵉ-coerce A B
map-inv-coerce-Πᵉ A B (map-coerce f) (map-coerce a) = map-coerce (f a)

is-equiv-map-coerce-Πᵉ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  is-equivᵉ (map-coerce-Πᵉ A B)
is-equiv-map-coerce-Πᵉ A B =
  is-equiv-is-invertibleᵉ
    ( map-inv-coerce-Πᵉ A B)
    ( λ { (map-coerce f) → reflᵉ} )
    ( λ { f → reflᵉ} )

equiv-coerce-Πᵉ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  Πᵉ-coerce A B ≃ᵉ coerce (Π A B)
pr1ᵉ (equiv-coerce-Πᵉ A B) = map-coerce-Πᵉ A B
pr2ᵉ (equiv-coerce-Πᵉ A B) = is-equiv-map-coerce-Πᵉ A B
```

### Coercion respects function types up to isomorphism

```agda
hom-coerce :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  UUᵉ (l1 ⊔ l2)
hom-coerce A B = coerce A → coerce B

map-coerce-hom :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  hom-coerce A B → coerce (A → B)
map-coerce-hom A B f = map-coerce λ a → map-inv-coerce (f (map-coerce a))

map-inv-coerce-hom :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  coerce (A → B) → hom-coerce A B
map-inv-coerce-hom A B (map-coerce f) (map-coerce a) = map-coerce (f a)

is-equiv-map-coerce-hom :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-equivᵉ (map-coerce-hom A B)
is-equiv-map-coerce-hom A B =
  is-equiv-is-invertibleᵉ
    ( map-inv-coerce-hom A B)
    ( λ f → reflᵉ )
    ( λ f → reflᵉ )

equiv-coerce-hom :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  hom-coerce A B ≃ᵉ coerce (A → B)
pr1ᵉ (equiv-coerce-hom A B) = map-coerce-hom A B
pr2ᵉ (equiv-coerce-hom A B) = is-equiv-map-coerce-hom A B
```
