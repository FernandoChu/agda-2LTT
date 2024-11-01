# Cofibrations

```agda
module foundation-2LTT.cofibrations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-types
open import foundation.dependent-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopies-morphisms-arrowsᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.pi-decompositionsᵉ
open import foundation.pullbacksᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levels
open import foundation.universe-levelsᵉ

open import foundation-2LTT.exotypes
open import foundation-2LTT.fibrant-types
open import foundation-2LTT.fibrations

open import orthogonal-factorization-systems.pullback-homᵉ
```

</details>

## Definition

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B)
  where

  is-cofibration : (l : Level) → UUᵉ (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l)
  is-cofibration l =
    ((Y : B → UU l) →
    is-fibration
      (λ (g : (b : B) → Y b) → (g ∘ᶠᵉᵉ f))) ×ᵉ
    ((Y : B → UU l) →
    ((b : B) → is-contr (Y b)) →
    is-trivial-fibration
      (λ (g : (b : B) → Y b) → (g ∘ᶠᵉᵉ f)))

  is-cofibration' : (l3 l4 : Level) → UUᵉ (lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4))
  is-cofibration' l3 l4 =
    {X : UUᵉ l3} {Y : UUᵉ l4} (p : Y → X) →
    (is-fibration p → is-fibration (pullback-homᵉ f p)) ×ᵉ
    (is-trivial-fibration p → is-trivial-fibration (pullback-homᵉ f p))
```

## Properties

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B)
  where

  lemma319 :
    {l3 : Level} (X : B → UUᵉ l2) →
    is-pullbackᵉ
      (λ (x : unitᵉ) → f)
      (λ (f : A → Σᵉ B X) → pr1ᵉ ∘ᵉ f)
      ((λ _ → starᵉ) ,ᵉ
        (λ (g : (a : A) → (X (f a))) a → (f a ,ᵉ g a)) ,ᵉ
        ( λ g → reflᵉ))
  lemma319 X =
    is-equiv-is-invertibleᵉ
      (λ (starᵉ ,ᵉ g ,ᵉ p) a → trᵉ X (invᵉ (htpy-eqᵉ p a)) (pr2ᵉ (g a)))
      (λ (starᵉ ,ᵉ g ,ᵉ p) →
        eq-pair-Σᵉ reflᵉ
          ( eq-pair-Σᵉ
            ( eq-htpyᵉ
              (λ a → eq-pair-Σᵉ (htpy-eqᵉ p a) (helper (htpy-eqᵉ p a))))
            ( has-uip-exotypeᵉ _ _ _ _ _)))
      (λ g → reflᵉ)
    where
      helper :
        {x y : B} (p : y ＝ᵉ x) {h : X x} →
        trᵉ X p (trᵉ X (invᵉ p) h) ＝ᵉ h
      helper reflᵉ = reflᵉ

  -- is-cofibration-is-cofibration' :
  --   is-cofibration' f l2 l2 → is-cofibration f l2
  -- pr1ᵉ (is-cofibration-is-cofibration' H) Y' g =
  --   is-fibrant-equivᵉ (pr1ᵉ (H p) is-fibration-p diag) lemma
  --   where
  --     Y : UUᵉ (l2)
  --     Y = Σᵉ B (λ b → type-Fibrant-Type (Y' b))
  --     p : Y → B
  --     p = pr1ᵉ
  --     g' : A → Y
  --     g' a = (f a ,ᵉ g a)
  --     is-fibration-p : is-fibration p
  --     is-fibration-p b =
  --       is-fibrant-equivᵉ
  --         (is-fibrant-Fibrant-Type (Y' b))
  --         -- type-Fibrant-Type (Y' b) ≃ᵉ fiberᵉ p b
  --         (inv-equiv-fiber-pr1ᵉ (type-Fibrant-Type ∘ᵉ Y') b)
  --     diag : hom-arrowᵉ f p
  --     diag = (g' ,ᵉ idᵉ ,ᵉ λ _ → reflᵉ)
  --     lemma' : fiberᵉ (pullback-homᵉ f p) diag →
  --       fiberᵉ (λ (g₁ : (b : B) → type-Fibrant-Type (Y' b)) → g₁ ∘ᵉ f) g
  --     pr1ᵉ (lemma' (h ,ᵉ e)) b = {!!}
  --     pr2ᵉ (lemma' (h ,ᵉ e)) = {!!}

  --     lemma : fiberᵉ (pullback-homᵉ f p) diag ≃ᵉ
  --       fiberᵉ (λ (g₁ : (b : B) → type-Fibrant-Type (Y' b)) → g₁ ∘ᵉ f) g
  --     lemma =
  --       pairᵉ
  --         (λ (h ,ᵉ e) → pairᵉ (λ b → {! pr1ᵉ (pr2ᵉ (htpy-eq-hom-arrowᵉ f p (pullback-homᵉ f pr1ᵉ h) diag e)) b!})  {!!})
  --         -- (λ (h ,ᵉ e) → pairᵉ (λ b → {!!})  {!!})
  --         {!!}
  -- pr2ᵉ (is-cofibration-is-cofibration' H) = {!!}

  -- is-cofibration'-is-cofibration :
  --   is-cofibration f l2 → is-cofibration' f l2 l2
  -- pr1ᵉ (is-cofibration'-is-cofibration H p) is-fibration-p (v ,ᵉ g ,ᵉ φ) =
  --   {!!}
  -- pr2ᵉ (is-cofibration'-is-cofibration H p) = {!!}
```
