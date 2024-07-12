# Coercing

```agda
module foundation.coercing-inner-types where

open import foundation.exo-isomorphisms public
open import foundation.exo-identity-types public
open import foundation.exo-universes public
open import foundation.exo-dependent-pair-types public
open import foundation.dependent-pair-types public
open import foundation.exo-equality-exo-dependent-pair-types public
```

## Idea

Every inner type can be coerced into an outer type.

```agda
data coerce {i : Level} (A : UU i) : UUᵉ i where
  map-coerce : A → coerce A
```

### Coercion respects dependent pair types up to isomorphism

```agda
Σᵉ-coerce :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  UUᵉ (l1 ⊔ l2)
Σᵉ-coerce A B = Σᵉ (coerce A) (λ {(map-coerce a) → coerce (B a)})

map-coerce-Σᵉ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  Σᵉ-coerce A B → coerce (Σ A B)
map-coerce-Σᵉ A B (map-coerce a ,ᵉ map-coerce b) = map-coerce (a , b)

map-inv-coerce-Σᵉ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  coerce (Σ A B) → Σᵉ-coerce A B
map-inv-coerce-Σᵉ A B (map-coerce (a , b)) =
  pairᵉ (map-coerce a) (map-coerce b)

is-exo-iso-map-coerce-Σᵉ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  is-exo-iso (map-coerce-Σᵉ A B)
pr1ᵉ (is-exo-iso-map-coerce-Σᵉ A B) = map-inv-coerce-Σᵉ A B
pr1ᵉ (pr2ᵉ (is-exo-iso-map-coerce-Σᵉ A B)) (map-coerce (a , b)) = reflᵉ
pr2ᵉ (pr2ᵉ (is-exo-iso-map-coerce-Σᵉ A B)) (map-coerce a ,ᵉ map-coerce b) = reflᵉ

exo-iso-coerce-Σᵉ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  Σᵉ-coerce A B ≅ᵉ coerce (Σ A B)
pr1ᵉ (exo-iso-coerce-Σᵉ A B) = map-coerce-Σᵉ A B
pr2ᵉ (exo-iso-coerce-Σᵉ A B) = is-exo-iso-map-coerce-Σᵉ A B
```
