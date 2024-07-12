# Equality of dependent pair types

```agda
module foundation.exo-equality-exo-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.exo-isomorphisms
open import foundation.exo-function-types
open import foundation.exo-homotopies
open import foundation.exo-dependent-pair-types
open import foundation.exo-cartesian-product-types
open import foundation.exo-identity-types
open import foundation.exo-universes
```

</details>

## Idea

An identification `(pairᵉ x y) ＝ᵉ (pairᵉ x' y')` in a dependent pair type `Σᵉ A B`
is equivalently described as a pairᵉ `pairᵉ α β` consisting of an identification
`α : x ＝ᵉ x'` and an identification `β : (trᵉ B α y) ＝ᵉ y'`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2}
  where

  Eq-Σᵉ : (s t : Σᵉ A B) → UUᵉ (l1 ⊔ l2)
  Eq-Σᵉ s t =
    Σᵉ (pr1ᵉ s ＝ᵉ pr1ᵉ t) (λ α → trᵉ B α (pr2ᵉ s) ＝ᵉ (pr2ᵉ t))
```

## Properties

### The type `Id s t` is equivalent to `Eq-Σᵉ s t` for any `s t : Σᵉ A B`

```agda
  reflᵉ-Eq-Σᵉ : (s : Σᵉ A B) → Eq-Σᵉ s s
  pr1ᵉ (reflᵉ-Eq-Σᵉ (pairᵉ a b)) = reflᵉ
  pr2ᵉ (reflᵉ-Eq-Σᵉ (pairᵉ a b)) = reflᵉ

  pairᵉ-eq-Σᵉ : {s t : Σᵉ A B} → s ＝ᵉ t → Eq-Σᵉ s t
  pairᵉ-eq-Σᵉ {s} reflᵉ = reflᵉ-Eq-Σᵉ s

  eq-pairᵉ-eq-base :
    {x y : A} {s : B x} (p : x ＝ᵉ y) → (x ,ᵉ s) ＝ᵉ (y ,ᵉ trᵉ B p s)
  eq-pairᵉ-eq-base reflᵉ = reflᵉ

  eq-pairᵉ-eq-base' :
    {x y : A} {t : B y} (p : x ＝ᵉ y) → (x ,ᵉ trᵉ B (invᵉ p) t) ＝ᵉ (y ,ᵉ t)
  eq-pairᵉ-eq-base' reflᵉ = reflᵉ

  eq-pairᵉ-eq-fiber :
    {x : A} {s t : B x} → s ＝ᵉ t → (x ,ᵉ s) ＝ᵉ (x ,ᵉ t)
  eq-pairᵉ-eq-fiber {x} = apᵉ {B = Σᵉ A B} (pairᵉ x)

  eq-pairᵉ-Σᵉ :
    {s t : Σᵉ A B}
    (α : pr1ᵉ s ＝ᵉ pr1ᵉ t) →
    trᵉ B α (pr2ᵉ s) ＝ᵉ (pr2ᵉ t) → s ＝ᵉ t
  eq-pairᵉ-Σᵉ reflᵉ = eq-pairᵉ-eq-fiber

  eq-pairᵉ-Σᵉ' : {s t : Σᵉ A B} → Eq-Σᵉ s t → s ＝ᵉ t
  eq-pairᵉ-Σᵉ' p = eq-pairᵉ-Σᵉ (pr1ᵉ p) (pr2ᵉ p)

  apᵉ-pr1ᵉ-eq-pairᵉ-eq-fiber :
    {x : A} {s t : B x} (p : s ＝ᵉ t) → apᵉ pr1ᵉ (eq-pairᵉ-eq-fiber p) ＝ᵉ reflᵉ
  apᵉ-pr1ᵉ-eq-pairᵉ-eq-fiber reflᵉ = reflᵉ

  is-retractionᵉ-pairᵉ-eq-Σᵉ :
    (s t : Σᵉ A B) → (pairᵉ-eq-Σᵉ {s} {t} ∘ᵉ eq-pairᵉ-Σᵉ' {s} {t}) ~ᵉ idᵉ
  is-retractionᵉ-pairᵉ-eq-Σᵉ (pairᵉ x y) (pairᵉ .x .y) (pairᵉ reflᵉ reflᵉ) = reflᵉ

  is-sectionᵉ-pairᵉ-eq-Σᵉ :
    (s t : Σᵉ A B) → ((eq-pairᵉ-Σᵉ' {s} {t}) ∘ᵉ (pairᵉ-eq-Σᵉ {s} {t})) ~ᵉ idᵉ
  is-sectionᵉ-pairᵉ-eq-Σᵉ (pairᵉ x y) .(pairᵉ x y) reflᵉ = reflᵉ

  is-exo-iso-eq-pairᵉ-Σᵉ : (s t : Σᵉ A B) → is-exo-iso (eq-pairᵉ-Σᵉ' {s} {t})
  pr1ᵉ (is-exo-iso-eq-pairᵉ-Σᵉ s t) = pairᵉ-eq-Σᵉ
  pr1ᵉ (pr2ᵉ (is-exo-iso-eq-pairᵉ-Σᵉ s t)) = is-sectionᵉ-pairᵉ-eq-Σᵉ s t
  pr2ᵉ (pr2ᵉ (is-exo-iso-eq-pairᵉ-Σᵉ s t)) = is-retractionᵉ-pairᵉ-eq-Σᵉ s t

  exo-iso-eq-pairᵉ-Σᵉ : (s t : Σᵉ A B) → Eq-Σᵉ s t ≅ᵉ (s ＝ᵉ t)
  pr1ᵉ (exo-iso-eq-pairᵉ-Σᵉ s t) = eq-pairᵉ-Σᵉ'
  pr2ᵉ (exo-iso-eq-pairᵉ-Σᵉ s t) = is-exo-iso-eq-pairᵉ-Σᵉ s t

  is-exo-iso-pairᵉ-eq-Σᵉ : (s t : Σᵉ A B) → is-exo-iso (pairᵉ-eq-Σᵉ {s} {t})
  pr1ᵉ (is-exo-iso-pairᵉ-eq-Σᵉ s t) = eq-pairᵉ-Σᵉ'
  pr1ᵉ (pr2ᵉ (is-exo-iso-pairᵉ-eq-Σᵉ s t)) = is-retractionᵉ-pairᵉ-eq-Σᵉ s t
  pr2ᵉ (pr2ᵉ (is-exo-iso-pairᵉ-eq-Σᵉ s t)) = is-sectionᵉ-pairᵉ-eq-Σᵉ s t

  equiv-pairᵉ-eq-Σᵉ : (s t : Σᵉ A B) → (s ＝ᵉ t) ≅ᵉ Eq-Σᵉ s t
  pr1ᵉ (equiv-pairᵉ-eq-Σᵉ s t) = pairᵉ-eq-Σᵉ
  pr2ᵉ (equiv-pairᵉ-eq-Σᵉ s t) = is-exo-iso-pairᵉ-eq-Σᵉ s t

  η-pairᵉ : (t : Σᵉ A B) → (pairᵉ (pr1ᵉ t) (pr2ᵉ t)) ＝ᵉ t
  η-pairᵉ t = reflᵉ

  eq-base-eq-pairᵉ-Σᵉ : {s t : Σᵉ A B} → (s ＝ᵉ t) → (pr1ᵉ s ＝ᵉ pr1ᵉ t)
  eq-base-eq-pairᵉ-Σᵉ p = pr1ᵉ (pairᵉ-eq-Σᵉ p)

  dependent-eq-family-eq-pairᵉ-Σᵉ :
    {s t : Σᵉ A B} → (p : s ＝ᵉ t) →
    trᵉ B (eq-base-eq-pairᵉ-Σᵉ p) (pr2ᵉ s) ＝ᵉ (pr2ᵉ t)
  dependent-eq-family-eq-pairᵉ-Σᵉ p = pr2ᵉ (pairᵉ-eq-Σᵉ p)
```

### Lifting equality to the total space

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2}
  where

  lift-eq-Σᵉ :
    {x y : A} (p : x ＝ᵉ y) (b : B x) → (pairᵉ x b) ＝ᵉ (pairᵉ y (trᵉ B p b))
  lift-eq-Σᵉ reflᵉ b = reflᵉ
```

### transport in a family of dependent pairᵉ types

```agda
trᵉ-Σᵉ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {a0 a1 : A} {B : A → UUᵉ l2}
  (C : (x : A) → B x → UUᵉ l3) (p : a0 ＝ᵉ a1) (z : Σᵉ (B a0) (λ x → C a0 x)) →
  trᵉ (λ a → (Σᵉ (B a) (C a))) p z ＝ᵉ
  pairᵉ (trᵉ B p (pr1ᵉ z)) (trᵉ (ind-Σᵉ C) (eq-pairᵉ-Σᵉ p reflᵉ) (pr2ᵉ z))
trᵉ-Σᵉ C reflᵉ z = reflᵉ
```

### transport in a family over a dependent pairᵉ type

```agda
trᵉ-eq-pairᵉ-Σᵉ :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {a0 a1 : A}
  {B : A → UUᵉ l2} {b0 : B a0} {b1 : B a1} (C : (Σᵉ A B) → UUᵉ l3)
  (p : a0 ＝ᵉ a1) (q : trᵉ B p b0 ＝ᵉ b1) (u : C (a0 ,ᵉ b0)) →
  trᵉ C (eq-pairᵉ-Σᵉ p q) u ＝ᵉ
  trᵉ (λ x → C (a1 ,ᵉ x)) q (trᵉ C (eq-pairᵉ-Σᵉ p reflᵉ) u)
trᵉ-eq-pairᵉ-Σᵉ C reflᵉ reflᵉ u = reflᵉ
```
