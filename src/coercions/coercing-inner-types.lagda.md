# Coercing

```agda
module coercions.coercing-inner-types where

open import foundation.universe-levelsᵉ public
open import foundation.equivalencesᵉ public
open import foundation.dependent-pair-typesᵉ public
open import foundation.identity-typesᵉ public

open import foundation.universe-levels public
open import foundation.dependent-pair-types public
```

## Idea

Every inner type can be coerced into an outer type.

```agda
data coerce {i : Level} (A : UU i) : UUᵉ i where
  map-coerce : A → coerce A
```

### Coercion respects dependent pair types up to equivᵉmorphism

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

is-equivᵉ-map-coerce-Σᵉ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  is-equivᵉ (map-coerce-Σᵉ A B)
is-equivᵉ-map-coerce-Σᵉ A B =
  is-equiv-is-invertibleᵉ
    ( map-inv-coerce-Σᵉ A B)
    ( λ { (map-coerce (a , b)) → reflᵉ})
    ( λ { (map-coerce a ,ᵉ map-coerce b) → reflᵉ})

equivᵉ-coerce-Σᵉ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  Σᵉ-coerce A B ≃ᵉ coerce (Σ A B)
pr1ᵉ (equivᵉ-coerce-Σᵉ A B) = map-coerce-Σᵉ A B
pr2ᵉ (equivᵉ-coerce-Σᵉ A B) = is-equivᵉ-map-coerce-Σᵉ A B
```
