# Contractible exo types

```agda
module foundation.exo-contractible-exo-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.exo-dependent-pair-types
open import foundation.exo-retracts-of-exo-types
-- open import foundation.exo-equality-cartesian-product-types
open import foundation.exo-function-extensionality
open import foundation.exo-universes

open import foundation.exo-cartesian-product-types
open import foundation.exo-equality-exo-dependent-pair-types
open import foundation.exo-isomorphisms
open import foundation.exo-homotopies
open import foundation.exo-identity-types
-- open import foundation.exo-retracts-of-types
```

</details>

## Idea

Contractible types are types that have, up to identification, exactly one
element.

## Definition

```agda
is-contrᵉ :
  {l : Level} → UUᵉ l → UUᵉ l
is-contrᵉ A = Σᵉ A (λ a → (x : A) → a ＝ᵉ x)

abstract
  center :
    {l : Level} {A : UUᵉ l} → is-contrᵉ A → A
  center (pairᵉ c is-contrᵉ-A) = c

eq-is-contrᵉ' :
  {l : Level} {A : UUᵉ l} → is-contrᵉ A → (x y : A) → x ＝ᵉ y
eq-is-contrᵉ' (pairᵉ c C) x y = (invᵉ (C x)) ∙ᵉ (C y)

eq-is-contrᵉ :
  {l : Level} {A : UUᵉ l} → is-contrᵉ A → {x y : A} → x ＝ᵉ y
eq-is-contrᵉ C {x} {y} = eq-is-contrᵉ' C x y

abstract
  contraction :
    {l : Level} {A : UUᵉ l} (is-contrᵉ-A : is-contrᵉ A) →
    (x : A) → (center is-contrᵉ-A) ＝ᵉ x
  contraction C x = eq-is-contrᵉ C

  coh-contraction :
    {l : Level} {A : UUᵉ l} (is-contrᵉ-A : is-contrᵉ A) →
    (contraction is-contrᵉ-A (center is-contrᵉ-A)) ＝ᵉ reflᵉ
  coh-contraction (pairᵉ c C) = left-invᵉ (C c)
```

## Properties

### Retracts of contractible types are contractible

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} (B : UUᵉ l2)
  where

  abstract
    is-contrᵉ-retractᵉ-of : A retractᵉ-of B → is-contrᵉ B → is-contrᵉ A
    pr1ᵉ (is-contrᵉ-retractᵉ-of (pairᵉ i (pairᵉ r is-retractionᵉ-r)) H) = r (center H)
    pr2ᵉ (is-contrᵉ-retractᵉ-of (pairᵉ i (pairᵉ r is-retractionᵉ-r)) H) x =
      apᵉ r (contraction H (i x)) ∙ᵉ (is-retractionᵉ-r x)
```

### Contractible types are closed under equivalences

````agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} (B : UUᵉ l2)
  where

  abstract
    is-contrᵉ-is-exo-iso :
      (f : A → B) → is-exo-iso f → is-contrᵉ B → is-contrᵉ A
    is-contrᵉ-is-exo-iso f is-exo-iso-f =
      is-contrᵉ-retractᵉ-of B
        (f ,ᵉ  map-inv-is-exo-iso is-exo-iso-f ,ᵉ is-sectionᵉ-is-exo-iso is-exo-iso-f)

  abstract
    is-contrᵉ-exo-iso : (e : A ≅ᵉ B) → is-contrᵉ B → is-contrᵉ A
    is-contrᵉ-exo-iso (pairᵉ e is-exo-iso-e) is-contrᵉ-B =
      is-contrᵉ-is-exo-iso e is-exo-iso-e is-contrᵉ-B

module _
  {l1 l2 : Level} (A : UUᵉ l1) {B : UUᵉ l2}
  where

  abstract
    is-contrᵉ-is-exo-iso' :
      (f : A → B) → is-exo-iso f → is-contrᵉ A → is-contrᵉ B
    is-contrᵉ-is-exo-iso' f is-exo-iso-f is-contrᵉ-A =
      is-contrᵉ-is-exo-iso A
        ( map-inv-is-exo-iso is-exo-iso-f)
        ( f ,ᵉ  is-sectionᵉ-is-exo-iso is-exo-iso-f ,ᵉ is-retractionᵉ-is-exo-iso is-exo-iso-f)
        ( is-contrᵉ-A)

  abstract
    is-contrᵉ-exo-iso' : (e : A ≅ᵉ B) → is-contrᵉ A → is-contrᵉ B
    is-contrᵉ-exo-iso' (pairᵉ e is-exo-iso-e) is-contrᵉ-A =
      is-contrᵉ-is-exo-iso' e is-exo-iso-e is-contrᵉ-A

module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2}
  where

  abstract
    is-exo-iso-is-contrᵉ :
      (f : A → B) → is-contrᵉ A → is-contrᵉ B → is-exo-iso f
    pr1ᵉ (is-exo-iso-is-contrᵉ f is-contrᵉ-A is-contrᵉ-B) =
      λ y → center is-contrᵉ-A
    pr1ᵉ (pr2ᵉ (is-exo-iso-is-contrᵉ f is-contrᵉ-A is-contrᵉ-B)) =
      λ y → eq-is-contrᵉ is-contrᵉ-B
    pr2ᵉ (pr2ᵉ (is-exo-iso-is-contrᵉ f is-contrᵉ-A is-contrᵉ-B)) =
      contraction is-contrᵉ-A

  iso-is-contrᵉ : is-contrᵉ A → is-contrᵉ B → A ≅ᵉ B
  pr1ᵉ (iso-is-contrᵉ is-contrᵉ-A is-contrᵉ-B) a = center is-contrᵉ-B
  pr2ᵉ (iso-is-contrᵉ is-contrᵉ-A is-contrᵉ-B) =
    is-exo-iso-is-contrᵉ _ is-contrᵉ-A is-contrᵉ-B
```

-- ### Contractibility of cartesian product types

-- Given two types `A` and `B`, the following are equivalent:

-- 1. The type `A × B` is contractible.
-- 2. Both `A` and `B` are contractible.

-- ```agda
-- module _
--   {l1 l2 : Level} (A : UUᵉ l1) (B : UUᵉ l2)
--   where

--   abstract
--     is-contrᵉ-left-factor-product : is-contrᵉ (A × B) → is-contrᵉ A
--     is-contrᵉ-left-factor-product is-contrᵉ-AB =
--       is-contrᵉ-retract-of
--         ( A × B)
--         ( pair
--           ( λ x → pairᵉ x (pr2ᵉ (center is-contrᵉ-AB)))
--           ( pairᵉ pr1ᵉ refl-htpy))
--         ( is-contrᵉ-AB)

-- module _
--   {l1 l2 : Level} (A : UUᵉ l1) (B : UUᵉ l2)
--   where

--   abstract
--     is-contrᵉ-right-factor-product : is-contrᵉ (A × B) → is-contrᵉ B
--     is-contrᵉ-right-factor-product is-contrᵉ-AB =
--       is-contrᵉ-retract-of
--         ( A × B)
--         ( pair
--           ( pairᵉ (pr1ᵉ (center is-contrᵉ-AB)))
--           ( pairᵉ pr2ᵉ refl-htpy))
--         ( is-contrᵉ-AB)

-- module _
--   {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2}
--   where

--   abstract
--     is-contrᵉ-product : is-contrᵉ A → is-contrᵉ B → is-contrᵉ (A × B)
--     pr1ᵉ (pr1ᵉ (is-contrᵉ-product (pairᵉ a C) (pairᵉ b D))) = a
--     pr2ᵉ (pr1ᵉ (is-contrᵉ-product (pairᵉ a C) (pairᵉ b D))) = b
--     pr2ᵉ (is-contrᵉ-product (pairᵉ a C) (pairᵉ b D)) (pairᵉ x y) =
--       eq-pairᵉ (C x) (D y)
-- ```

-- ### Contractibility of Σᵉ-types

-- ```agda
-- module _
--   {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2}
--   where

--   abstract
--     is-contrᵉ-Σᵉ' :
--       is-contrᵉ A → ((x : A) → is-contrᵉ (B x)) → is-contrᵉ (Σᵉ A B)
--     pr1ᵉ (pr1ᵉ (is-contrᵉ-Σᵉ' (pairᵉ a H) is-contrᵉ-B)) = a
--     pr2ᵉ (pr1ᵉ (is-contrᵉ-Σᵉ' (pairᵉ a H) is-contrᵉ-B)) = center (is-contrᵉ-B a)
--     pr2ᵉ (is-contrᵉ-Σᵉ' (pairᵉ a H) is-contrᵉ-B) (pairᵉ x y) =
--       eq-pair-Σᵉ
--         ( invᵉ (invᵉ (H x)))
--         ( eq-transpose-tr (invᵉ (H x)) (eq-is-contrᵉ (is-contrᵉ-B a)))

--   abstract
--     is-contrᵉ-Σᵉ :
--       is-contrᵉ A → (a : A) → is-contrᵉ (B a) → is-contrᵉ (Σᵉ A B)
--     pr1ᵉ (pr1ᵉ (is-contrᵉ-Σᵉ H a K)) = a
--     pr2ᵉ (pr1ᵉ (is-contrᵉ-Σᵉ H a K)) = center K
--     pr2ᵉ (is-contrᵉ-Σᵉ H a K) (pairᵉ x y) =
--       eq-pair-Σᵉ
--         ( invᵉ (eq-is-contrᵉ H))
--         ( eq-transpose-tr (eq-is-contrᵉ H) (eq-is-contrᵉ K))
-- ```

-- **Note**: In the previous construction, we showed that `Σᵉ A B` is contractible
-- whenever `A` is contractible and whenever `B a` is contractible for a specified
-- term `a : A`. We _could_ have chosen this term `a` to be the center of
-- contraction of `A`. However, it turns out to be better not to do so in the
-- construction of `is-contrᵉ-Σᵉ`. The reason is that proofs of contractibility could
-- be quite complicated and difficult to normalize. If we would require in the
-- definition of `is-contrᵉ-Σᵉ` that `B (center c)` is contractible, given the proof
-- `c` of contractibility of `A`, then the type inference algorithm of Agda will be
-- forced to normalize the proof `c` including the contraction. By instead
-- providing a center of contraction by hand, we avoid this unnecessary load on the
-- type inference algorithm, and hence any instance of `is-contrᵉ-Σᵉ` will type check
-- more efficiently.

-- The general theme is that it may be computationally expensive to extract
-- information from proofs of propositions, such as the center of contraction of a
-- proof of contractibility. The reason for that is that when Agda normalizes an
-- element (as it inevitably will do sometimes) then in such cases it will not just
-- normalize the extracted information (in this case the first projection of the
-- proof of contractibility), but it will normalize the entire proof of
-- contractibility first, and then apply the projection.

-- ### Contractible types are propositions

-- ```agda
-- is-prop-is-contrᵉ :
--   {l : Level} {A : UUᵉ l} → is-contrᵉ A → (x y : A) → is-contrᵉ (x ＝ᵉ y)
-- pr1ᵉ (is-prop-is-contrᵉ H x y) = eq-is-contrᵉ H
-- pr2ᵉ (is-prop-is-contrᵉ H x .x) reflᵉ = left-invᵉ (pr2ᵉ H x)
-- ```

-- ### Products of families of contractible types are contractible

-- ```agda
-- abstract
--   is-contrᵉ-Π :
--     {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} →
--     ((x : A) → is-contrᵉ (B x)) → is-contrᵉ ((x : A) → B x)
--   pr1ᵉ (is-contrᵉ-Π {A = A} {B = B} H) x = center (H x)
--   pr2ᵉ (is-contrᵉ-Π {A = A} {B = B} H) f =
--     eq-htpy (λ x → contraction (H x) (f x))

-- abstract
--   is-contrᵉ-implicit-Π :
--     {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} →
--     ((x : A) → is-contrᵉ (B x)) → is-contrᵉ ({x : A} → B x)
--   is-contrᵉ-implicit-Π H =
--     is-contrᵉ-equiv _ equiv-explicit-implicit-Π (is-contrᵉ-Π H)
-- ```

-- ### The type of functions into a contractible type is contractible

-- ```agda
-- is-contrᵉ-function-type :
--   {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} →
--   is-contrᵉ B → is-contrᵉ (A → B)
-- is-contrᵉ-function-type is-contrᵉ-B = is-contrᵉ-Π (λ _ → is-contrᵉ-B)
-- ```

-- ### The type of equivalences between contractible types is contractible

-- ```agda
-- module _
--   {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2}
--   where

--   is-contrᵉ-equiv-is-contrᵉ :
--     is-contrᵉ A → is-contrᵉ B → is-contrᵉ (A ≃ B)
--   is-contrᵉ-equiv-is-contrᵉ (pairᵉ a α) (pairᵉ b β) =
--     is-contrᵉ-Σᵉ
--       ( is-contrᵉ-function-type (pairᵉ b β))
--       ( λ x → b)
--       ( is-contrᵉ-product
--         ( is-contrᵉ-Σᵉ
--           ( is-contrᵉ-function-type (pairᵉ a α))
--           ( λ y → a)
--           ( is-contrᵉ-Π (is-prop-is-contrᵉ (pairᵉ b β) b)))
--         ( is-contrᵉ-Σᵉ
--           ( is-contrᵉ-function-type (pairᵉ a α))
--           ( λ y → a)
--           ( is-contrᵉ-Π (is-prop-is-contrᵉ (pairᵉ a α) a))))
-- ```

-- ### Being contractible is a proposition

-- ```agda
-- module _
--   {l : Level} {A : UUᵉ l}
--   where

--   abstract
--     is-contrᵉ-is-contrᵉ : is-contrᵉ A → is-contrᵉ (is-contrᵉ A)
--     is-contrᵉ-is-contrᵉ (pairᵉ a α) =
--       is-contrᵉ-Σᵉ
--         ( pairᵉ a α)
--         ( a)
--         ( is-contrᵉ-Π (is-prop-is-contrᵉ (pairᵉ a α) a))

--   abstract
--     is-property-is-contrᵉ : (H K : is-contrᵉ A) → is-contrᵉ (H ＝ᵉ K)
--     is-property-is-contrᵉ H = is-prop-is-contrᵉ (is-contrᵉ-is-contrᵉ H) H
-- ```
