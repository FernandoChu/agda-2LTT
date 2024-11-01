# Exotypes

```agda
module foundation-2LTT.exotypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.identity-types
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levels
open import foundation.universe-levelsᵉ
```

</details>

## The mixed function composition

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

## Mixed ap

```agda
apᵐ :
  {l1 l2 : Level} {A : UUᵉ l1} {B : UU l2} (f : A → B) {x y : A} →
  x ＝ᵉ y → (f x) ＝ (f y)
apᵐ fᵉ reflᵉ = refl
```

## Mixed transport

```agda
trᵐ :
  {l1 l2 : Level} {A : UUᵉ l1} (B : A → UU l2)
  {x y : A} (p : x ＝ᵉ y) → B x → B y
trᵐ B reflᵉ b = b
```

## Exotypes are set and satisfy UIP

```agda
is-set-exotypeᵉ : {l : Level} (X : UUᵉ l) → is-setᵉ X
pr1ᵉ (is-set-exotypeᵉ X x .x reflᵉ reflᵉ) = reflᵉ
pr2ᵉ (is-set-exotypeᵉ X x .x reflᵉ reflᵉ) reflᵉ = reflᵉ

exotype-Setᵉ : {l : Level} (X : UUᵉ l) → Setᵉ l
pr1ᵉ (exotype-Setᵉ X) = X
pr2ᵉ (exotype-Setᵉ X) = is-set-exotypeᵉ X

has-uip-exotypeᵉ : {l : Level} → (X : UUᵉ l) → has-uipᵉ X
has-uip-exotypeᵉ X = is-set-has-uipᵉ (is-set-exotypeᵉ X)
```

## Functioriality of Π

We reprove this since it doesn't compute in Agda-Unimath, which difficults some
things.

```agda
module _
  { l1 l2 l3 l4 : Level}
  { A' : UUᵉ l1} {B' : A' → UUᵉ l2} {A : UUᵉ l3} (B : A → UUᵉ l4)
  ( e : A' ≃ᵉ A) (f : (a' : A') → B' a' ≃ᵉ B (map-equivᵉ e a'))
  where

  map-equiv-Πᵉ : ((a' : A') → B' a') → ((a : A) → B a)
  map-equiv-Πᵉ h a =
    trᵉ B
      ( is-section-map-inv-equivᵉ e a)
      ( map-equivᵉ (f (map-inv-equivᵉ e a)) (h (map-inv-equivᵉ e a)))

  is-equiv-map-equiv-Πᵉ : is-equivᵉ map-equiv-Πᵉ
  is-equiv-map-equiv-Πᵉ =
    is-equiv-is-invertibleᵉ
      ( λ k a' → ←f a' (k (→e a')))
      ( λ k → eq-htpyᵉ λ a →
        apᵉ (trᵉ B (is-section-map-inv-equivᵉ e a))
          (is-section-map-inv-equivᵉ (f (←e a)) _) ∙ᵉ
        apdᵉ k (is-section-map-inv-equivᵉ e a))
      ( λ h → eq-htpyᵉ λ a' →
        apᵉ
          ( ←f a')
          ( apᵉ
            ( λ - → trᵉ B - ((→f (←e (→e a'))) (h (←e (→e a')))))
            ( has-uip-exotypeᵉ _ _ _ _ _) ∙ᵉ
            substitution-law-trᵉ B →e ( is-retraction-map-inv-equivᵉ e a') ∙ᵉ
            apdᵉ (λ - → →f - (h -)) (is-retraction-map-inv-equivᵉ e a')) ∙ᵉ
        is-retraction-map-inv-equivᵉ (f a') (h a'))
    where
      →e = map-equivᵉ e
      ←e = map-inv-equivᵉ e
      →f = λ a' → map-equivᵉ (f a')
      ←f = λ a' → map-inv-equivᵉ (f a')

  equiv-Πᵉ : ((a' : A') → B' a') ≃ᵉ ((a : A) → B a)
  pr1ᵉ equiv-Πᵉ = map-equiv-Πᵉ
  pr2ᵉ equiv-Πᵉ = is-equiv-map-equiv-Πᵉ
```
