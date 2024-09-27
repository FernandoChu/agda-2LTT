# Cofibrations

```agda
module foundation.cofibrationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.morphisms-arrowsᵉ
open import foundation.homotopies-morphisms-arrowsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.fibrationsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fibrant-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.universe-levels
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.unit-typeᵉ
open import foundation.equivalencesᵉ
open import foundation.homotopiesᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ

open import orthogonal-factorization-systems.pullback-homᵉ
```

## Idea

## Definition

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B)
  where

  is-cofibration : (l : Level) → UUᵉ (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l)
  is-cofibration l =
    ((Y : B → Fibrant-Type l) →
    is-fibration
      (λ (g : (b : B) → type-Fibrant-Type (Y b)) → (g ∘ᵉ f))) ×ᵉ
    ((Y : B → Trivially-Fibrant-Type l) →
    is-fibration
      (λ (g : (b : B) → type-Trivially-Fibrant-Type (Y b)) → (g ∘ᵉ f)))

  is-cofibration' : (l3 l4 : Level) → UUᵉ (lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4))
  is-cofibration' l3 l4 =
    {X : UUᵉ l3} {Y : UUᵉ l4} (p : Y → X) →
    (is-fibration p → is-fibration (pullback-homᵉ f p)) ×ᵉ
    (is-trivial-fibration p → is-trivial-fibration (pullback-homᵉ f p))

  -- is-trivial-cofibration : UUωᵉ
  -- is-trivial-cofibration =
  --   {l3 l4 : Level} {X : UUᵉ l2} {Y : UUᵉ l4} (p : Y → X) →
  --   is-fibration p → is-trivial-fibration (pullback-homᵉ f p)
```

## Properties

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B)
  where

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
  --     lemma : fiberᵉ (pullback-homᵉ f (λ r → pr1ᵉ r)) diag ≃ᵉ
  --       fiberᵉ (λ (g₁ : (b : B) → type-Fibrant-Type (Y' b)) → g₁ ∘ᵉ f) g
  --     lemma =
  --       pairᵉ
  --         (λ (h ,ᵉ e) → pairᵉ (λ b → {! pr1ᵉ (pr2ᵉ (htpy-eq-hom-arrowᵉ f p (pullback-homᵉ f pr1ᵉ h) diag e)) b!})  {!!})
  --         -- (λ (h ,ᵉ e) → pairᵉ (λ b → {!!})  {!!})
  --         {!!}
  -- pr2ᵉ (is-cofibration-is-cofibration' H) = {!!}

```
