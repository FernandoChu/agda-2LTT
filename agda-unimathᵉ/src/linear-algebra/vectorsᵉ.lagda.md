# Vectors

```agda
module linear-algebra.vectorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-higher-homotopies-compositionᵉ

open import univalent-combinatorics.involution-standard-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Thereᵉ areᵉ twoᵉ equivalentᵉ definitionsᵉ ofᵉ vectorsᵉ ofᵉ lengthᵉ `n`.ᵉ First,ᵉ aᵉ **listedᵉ
vector**ᵉ ofᵉ lengthᵉ `n`ᵉ isᵉ aᵉ listᵉ ofᵉ `n`ᵉ elementsᵉ ofᵉ typeᵉ `A`.ᵉ Secondly,ᵉ aᵉ
**functionalᵉ vector**ᵉ ofᵉ lengthᵉ `n`ᵉ isᵉ aᵉ mapᵉ `Finᵉ nᵉ → A`.ᵉ Weᵉ defineᵉ bothᵉ typesᵉ
ofᵉ vectorsᵉ andᵉ showᵉ thatᵉ theyᵉ areᵉ equivalent.ᵉ

## Definitions

### The type of listed vectors

```agda
infixr 10 _∷ᵉ_

data vecᵉ {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) : ℕᵉ → UUᵉ lᵉ where
  empty-vecᵉ : vecᵉ Aᵉ zero-ℕᵉ
  _∷ᵉ_ : {nᵉ : ℕᵉ} → Aᵉ → vecᵉ Aᵉ nᵉ → vecᵉ Aᵉ (succ-ℕᵉ nᵉ)

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  head-vecᵉ : {nᵉ : ℕᵉ} → vecᵉ Aᵉ (succ-ℕᵉ nᵉ) → Aᵉ
  head-vecᵉ (xᵉ ∷ᵉ vᵉ) = xᵉ

  tail-vecᵉ : {nᵉ : ℕᵉ} → vecᵉ Aᵉ (succ-ℕᵉ nᵉ) → vecᵉ Aᵉ nᵉ
  tail-vecᵉ (xᵉ ∷ᵉ vᵉ) = vᵉ

  snoc-vecᵉ : {nᵉ : ℕᵉ} → vecᵉ Aᵉ nᵉ → Aᵉ → vecᵉ Aᵉ (succ-ℕᵉ nᵉ)
  snoc-vecᵉ empty-vecᵉ aᵉ = aᵉ ∷ᵉ empty-vecᵉ
  snoc-vecᵉ (xᵉ ∷ᵉ vᵉ) aᵉ = xᵉ ∷ᵉ (snoc-vecᵉ vᵉ aᵉ)

  revert-vecᵉ : {nᵉ : ℕᵉ} → vecᵉ Aᵉ nᵉ → vecᵉ Aᵉ nᵉ
  revert-vecᵉ empty-vecᵉ = empty-vecᵉ
  revert-vecᵉ (xᵉ ∷ᵉ vᵉ) = snoc-vecᵉ (revert-vecᵉ vᵉ) xᵉ

  all-vecᵉ : {l2ᵉ : Level} {nᵉ : ℕᵉ} → (Pᵉ : Aᵉ → UUᵉ l2ᵉ) → vecᵉ Aᵉ nᵉ → UUᵉ l2ᵉ
  all-vecᵉ Pᵉ empty-vecᵉ = raise-unitᵉ _
  all-vecᵉ Pᵉ (xᵉ ∷ᵉ vᵉ) = Pᵉ xᵉ ×ᵉ all-vecᵉ Pᵉ vᵉ

  component-vecᵉ :
    (nᵉ : ℕᵉ) → vecᵉ Aᵉ nᵉ → Finᵉ nᵉ → Aᵉ
  component-vecᵉ (succ-ℕᵉ nᵉ) (aᵉ ∷ᵉ vᵉ) (inlᵉ kᵉ) = component-vecᵉ nᵉ vᵉ kᵉ
  component-vecᵉ (succ-ℕᵉ nᵉ) (aᵉ ∷ᵉ vᵉ) (inrᵉ kᵉ) = aᵉ

  infix 6 _∈-vecᵉ_
  data _∈-vecᵉ_ : {nᵉ : ℕᵉ} → Aᵉ → vecᵉ Aᵉ nᵉ → UUᵉ lᵉ where
    is-headᵉ : {nᵉ : ℕᵉ} (aᵉ : Aᵉ) (lᵉ : vecᵉ Aᵉ nᵉ) → aᵉ ∈-vecᵉ (aᵉ ∷ᵉ lᵉ)
    is-in-tailᵉ : {nᵉ : ℕᵉ} (aᵉ xᵉ : Aᵉ) (lᵉ : vecᵉ Aᵉ nᵉ) → aᵉ ∈-vecᵉ lᵉ → aᵉ ∈-vecᵉ (xᵉ ∷ᵉ lᵉ)

  index-in-vecᵉ : (nᵉ : ℕᵉ) → (aᵉ : Aᵉ) → (vᵉ : vecᵉ Aᵉ nᵉ) → aᵉ ∈-vecᵉ vᵉ → Finᵉ nᵉ
  index-in-vecᵉ (succ-ℕᵉ nᵉ) aᵉ (.aᵉ ∷ᵉ vᵉ) (is-headᵉ .aᵉ .vᵉ) =
    inrᵉ starᵉ
  index-in-vecᵉ (succ-ℕᵉ nᵉ) aᵉ (xᵉ ∷ᵉ vᵉ) (is-in-tailᵉ .aᵉ .xᵉ .vᵉ Iᵉ) =
    inlᵉ (index-in-vecᵉ nᵉ aᵉ vᵉ Iᵉ)

  eq-component-vec-index-in-vecᵉ :
    (nᵉ : ℕᵉ) (aᵉ : Aᵉ) (vᵉ : vecᵉ Aᵉ nᵉ) (Iᵉ : aᵉ ∈-vecᵉ vᵉ) →
    aᵉ ＝ᵉ component-vecᵉ nᵉ vᵉ (index-in-vecᵉ nᵉ aᵉ vᵉ Iᵉ)
  eq-component-vec-index-in-vecᵉ (succ-ℕᵉ nᵉ) aᵉ (.aᵉ ∷ᵉ vᵉ) (is-headᵉ .aᵉ .vᵉ) = reflᵉ
  eq-component-vec-index-in-vecᵉ (succ-ℕᵉ nᵉ) aᵉ (xᵉ ∷ᵉ vᵉ) (is-in-tailᵉ .aᵉ .xᵉ .vᵉ Iᵉ) =
    eq-component-vec-index-in-vecᵉ nᵉ aᵉ vᵉ Iᵉ
```

### The functional type of vectors

```agda
functional-vecᵉ : {lᵉ : Level} → UUᵉ lᵉ → ℕᵉ → UUᵉ lᵉ
functional-vecᵉ Aᵉ nᵉ = Finᵉ nᵉ → Aᵉ

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  empty-functional-vecᵉ : functional-vecᵉ Aᵉ 0
  empty-functional-vecᵉ ()

  head-functional-vecᵉ : (nᵉ : ℕᵉ) → functional-vecᵉ Aᵉ (succ-ℕᵉ nᵉ) → Aᵉ
  head-functional-vecᵉ nᵉ vᵉ = vᵉ (inrᵉ starᵉ)

  tail-functional-vecᵉ :
    (nᵉ : ℕᵉ) → functional-vecᵉ Aᵉ (succ-ℕᵉ nᵉ) → functional-vecᵉ Aᵉ nᵉ
  tail-functional-vecᵉ nᵉ vᵉ = vᵉ ∘ᵉ (inl-Finᵉ nᵉ)

  cons-functional-vecᵉ :
    (nᵉ : ℕᵉ) → Aᵉ → functional-vecᵉ Aᵉ nᵉ → functional-vecᵉ Aᵉ (succ-ℕᵉ nᵉ)
  cons-functional-vecᵉ nᵉ aᵉ vᵉ (inlᵉ xᵉ) = vᵉ xᵉ
  cons-functional-vecᵉ nᵉ aᵉ vᵉ (inrᵉ xᵉ) = aᵉ

  snoc-functional-vecᵉ :
    (nᵉ : ℕᵉ) → functional-vecᵉ Aᵉ nᵉ → Aᵉ → functional-vecᵉ Aᵉ (succ-ℕᵉ nᵉ)
  snoc-functional-vecᵉ zero-ℕᵉ vᵉ aᵉ iᵉ = aᵉ
  snoc-functional-vecᵉ (succ-ℕᵉ nᵉ) vᵉ aᵉ (inlᵉ xᵉ) =
    snoc-functional-vecᵉ nᵉ (tail-functional-vecᵉ nᵉ vᵉ) aᵉ xᵉ
  snoc-functional-vecᵉ (succ-ℕᵉ nᵉ) vᵉ aᵉ (inrᵉ xᵉ) = head-functional-vecᵉ nᵉ vᵉ

  revert-functional-vecᵉ :
    (nᵉ : ℕᵉ) → functional-vecᵉ Aᵉ nᵉ → functional-vecᵉ Aᵉ nᵉ
  revert-functional-vecᵉ nᵉ vᵉ iᵉ = vᵉ (opposite-Finᵉ nᵉ iᵉ)

  in-functional-vecᵉ : (nᵉ : ℕᵉ) → Aᵉ → functional-vecᵉ Aᵉ nᵉ → UUᵉ lᵉ
  in-functional-vecᵉ nᵉ aᵉ vᵉ = Σᵉ (Finᵉ nᵉ) (λ kᵉ → aᵉ ＝ᵉ vᵉ kᵉ)

  index-in-functional-vecᵉ :
    (nᵉ : ℕᵉ) (xᵉ : Aᵉ) (vᵉ : functional-vecᵉ Aᵉ nᵉ) →
    in-functional-vecᵉ nᵉ xᵉ vᵉ → Finᵉ nᵉ
  index-in-functional-vecᵉ nᵉ xᵉ vᵉ Iᵉ = pr1ᵉ Iᵉ

  eq-component-functional-vec-index-in-functional-vecᵉ :
    (nᵉ : ℕᵉ) (xᵉ : Aᵉ) (vᵉ : functional-vecᵉ Aᵉ nᵉ) (Iᵉ : in-functional-vecᵉ nᵉ xᵉ vᵉ) →
    xᵉ ＝ᵉ vᵉ (index-in-functional-vecᵉ nᵉ xᵉ vᵉ Iᵉ)
  eq-component-functional-vec-index-in-functional-vecᵉ nᵉ xᵉ vᵉ Iᵉ = pr2ᵉ Iᵉ
```

## Properties

### Characterizing equality of listed vectors

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  Eq-vecᵉ : (nᵉ : ℕᵉ) → vecᵉ Aᵉ nᵉ → vecᵉ Aᵉ nᵉ → UUᵉ lᵉ
  Eq-vecᵉ zero-ℕᵉ empty-vecᵉ empty-vecᵉ = raise-unitᵉ lᵉ
  Eq-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ xsᵉ) (yᵉ ∷ᵉ ysᵉ) = (Idᵉ xᵉ yᵉ) ×ᵉ (Eq-vecᵉ nᵉ xsᵉ ysᵉ)

  refl-Eq-vecᵉ : (nᵉ : ℕᵉ) → (uᵉ : vecᵉ Aᵉ nᵉ) → Eq-vecᵉ nᵉ uᵉ uᵉ
  refl-Eq-vecᵉ zero-ℕᵉ empty-vecᵉ = map-raiseᵉ starᵉ
  pr1ᵉ (refl-Eq-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ xsᵉ)) = reflᵉ
  pr2ᵉ (refl-Eq-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ xsᵉ)) = refl-Eq-vecᵉ nᵉ xsᵉ

  Eq-eq-vecᵉ : (nᵉ : ℕᵉ) → (uᵉ vᵉ : vecᵉ Aᵉ nᵉ) → Idᵉ uᵉ vᵉ → Eq-vecᵉ nᵉ uᵉ vᵉ
  Eq-eq-vecᵉ nᵉ uᵉ .uᵉ reflᵉ = refl-Eq-vecᵉ nᵉ uᵉ

  eq-Eq-vecᵉ : (nᵉ : ℕᵉ) → (uᵉ vᵉ : vecᵉ Aᵉ nᵉ) → Eq-vecᵉ nᵉ uᵉ vᵉ → Idᵉ uᵉ vᵉ
  eq-Eq-vecᵉ zero-ℕᵉ empty-vecᵉ empty-vecᵉ eq-vecᵉ = reflᵉ
  eq-Eq-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ xsᵉ) (.xᵉ ∷ᵉ ysᵉ) (reflᵉ ,ᵉ eqsᵉ) =
    apᵉ (xᵉ ∷ᵉ_) (eq-Eq-vecᵉ nᵉ xsᵉ ysᵉ eqsᵉ)

  is-retraction-eq-Eq-vecᵉ :
    (nᵉ : ℕᵉ) → (uᵉ vᵉ : vecᵉ Aᵉ nᵉ) →
    (pᵉ : uᵉ ＝ᵉ vᵉ) → eq-Eq-vecᵉ nᵉ uᵉ vᵉ (Eq-eq-vecᵉ nᵉ uᵉ vᵉ pᵉ) ＝ᵉ pᵉ
  is-retraction-eq-Eq-vecᵉ zero-ℕᵉ empty-vecᵉ empty-vecᵉ reflᵉ = reflᵉ
  is-retraction-eq-Eq-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ xsᵉ) .(xᵉ ∷ᵉ xsᵉ) reflᵉ =
    left-whisker-comp²ᵉ (xᵉ ∷ᵉ_) (is-retraction-eq-Eq-vecᵉ nᵉ xsᵉ xsᵉ) reflᵉ

  square-Eq-eq-vecᵉ :
    (nᵉ : ℕᵉ) (xᵉ : Aᵉ) (uᵉ vᵉ : vecᵉ Aᵉ nᵉ) (pᵉ : Idᵉ uᵉ vᵉ) →
    (Eq-eq-vecᵉ _ (xᵉ ∷ᵉ uᵉ) (xᵉ ∷ᵉ vᵉ) (apᵉ (xᵉ ∷ᵉ_) pᵉ)) ＝ᵉ (reflᵉ ,ᵉ (Eq-eq-vecᵉ nᵉ uᵉ vᵉ pᵉ))
  square-Eq-eq-vecᵉ zero-ℕᵉ xᵉ empty-vecᵉ empty-vecᵉ reflᵉ = reflᵉ
  square-Eq-eq-vecᵉ (succ-ℕᵉ nᵉ) aᵉ (xᵉ ∷ᵉ xsᵉ) (.xᵉ ∷ᵉ .xsᵉ) reflᵉ = reflᵉ

  is-section-eq-Eq-vecᵉ :
    (nᵉ : ℕᵉ) (uᵉ vᵉ : vecᵉ Aᵉ nᵉ) →
    (pᵉ : Eq-vecᵉ nᵉ uᵉ vᵉ) → Eq-eq-vecᵉ nᵉ uᵉ vᵉ (eq-Eq-vecᵉ nᵉ uᵉ vᵉ pᵉ) ＝ᵉ pᵉ
  is-section-eq-Eq-vecᵉ zero-ℕᵉ empty-vecᵉ empty-vecᵉ (map-raiseᵉ starᵉ) = reflᵉ
  is-section-eq-Eq-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ xsᵉ) (.xᵉ ∷ᵉ ysᵉ) (reflᵉ ,ᵉ psᵉ) =
    ( square-Eq-eq-vecᵉ nᵉ xᵉ xsᵉ ysᵉ (eq-Eq-vecᵉ nᵉ xsᵉ ysᵉ psᵉ)) ∙ᵉ
    ( eq-pair-eq-fiberᵉ (is-section-eq-Eq-vecᵉ nᵉ xsᵉ ysᵉ psᵉ))

  is-equiv-Eq-eq-vecᵉ :
    (nᵉ : ℕᵉ) → (uᵉ vᵉ : vecᵉ Aᵉ nᵉ) → is-equivᵉ (Eq-eq-vecᵉ nᵉ uᵉ vᵉ)
  is-equiv-Eq-eq-vecᵉ nᵉ uᵉ vᵉ =
    is-equiv-is-invertibleᵉ
      ( eq-Eq-vecᵉ nᵉ uᵉ vᵉ)
      ( is-section-eq-Eq-vecᵉ nᵉ uᵉ vᵉ)
      ( is-retraction-eq-Eq-vecᵉ nᵉ uᵉ vᵉ)

  extensionality-vecᵉ : (nᵉ : ℕᵉ) → (uᵉ vᵉ : vecᵉ Aᵉ nᵉ) → Idᵉ uᵉ vᵉ ≃ᵉ Eq-vecᵉ nᵉ uᵉ vᵉ
  extensionality-vecᵉ nᵉ uᵉ vᵉ = (Eq-eq-vecᵉ nᵉ uᵉ vᵉ ,ᵉ is-equiv-Eq-eq-vecᵉ nᵉ uᵉ vᵉ)
```

### The types of listed vectors and functional vectors are equivalent

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  listed-vec-functional-vecᵉ : (nᵉ : ℕᵉ) → functional-vecᵉ Aᵉ nᵉ → vecᵉ Aᵉ nᵉ
  listed-vec-functional-vecᵉ zero-ℕᵉ vᵉ = empty-vecᵉ
  listed-vec-functional-vecᵉ (succ-ℕᵉ nᵉ) vᵉ =
    head-functional-vecᵉ nᵉ vᵉ ∷ᵉ
    listed-vec-functional-vecᵉ nᵉ (tail-functional-vecᵉ nᵉ vᵉ)

  functional-vec-vecᵉ : (nᵉ : ℕᵉ) → vecᵉ Aᵉ nᵉ → functional-vecᵉ Aᵉ nᵉ
  functional-vec-vecᵉ zero-ℕᵉ vᵉ = empty-functional-vecᵉ
  functional-vec-vecᵉ (succ-ℕᵉ nᵉ) (aᵉ ∷ᵉ vᵉ) =
    cons-functional-vecᵉ nᵉ aᵉ (functional-vec-vecᵉ nᵉ vᵉ)

  is-section-functional-vec-vecᵉ :
    (nᵉ : ℕᵉ) → (listed-vec-functional-vecᵉ nᵉ ∘ᵉ functional-vec-vecᵉ nᵉ) ~ᵉ idᵉ
  is-section-functional-vec-vecᵉ .zero-ℕᵉ empty-vecᵉ = reflᵉ
  is-section-functional-vec-vecᵉ .(succ-ℕᵉ _) (aᵉ ∷ᵉ vᵉ) =
    apᵉ (λ uᵉ → aᵉ ∷ᵉ uᵉ) (is-section-functional-vec-vecᵉ _ vᵉ)

  abstract
    is-retraction-functional-vec-vecᵉ :
      (nᵉ : ℕᵉ) → (functional-vec-vecᵉ nᵉ ∘ᵉ listed-vec-functional-vecᵉ nᵉ) ~ᵉ idᵉ
    is-retraction-functional-vec-vecᵉ zero-ℕᵉ vᵉ = eq-htpyᵉ (λ ())
    is-retraction-functional-vec-vecᵉ (succ-ℕᵉ nᵉ) vᵉ =
      eq-htpyᵉ
        ( λ where
          ( inlᵉ xᵉ) →
            htpy-eqᵉ
              ( is-retraction-functional-vec-vecᵉ nᵉ (tail-functional-vecᵉ nᵉ vᵉ))
              ( xᵉ)
          ( inrᵉ starᵉ) → reflᵉ)

  is-equiv-listed-vec-functional-vecᵉ :
    (nᵉ : ℕᵉ) → is-equivᵉ (listed-vec-functional-vecᵉ nᵉ)
  is-equiv-listed-vec-functional-vecᵉ nᵉ =
    is-equiv-is-invertibleᵉ
      ( functional-vec-vecᵉ nᵉ)
      ( is-section-functional-vec-vecᵉ nᵉ)
      ( is-retraction-functional-vec-vecᵉ nᵉ)

  is-equiv-functional-vec-vecᵉ :
    (nᵉ : ℕᵉ) → is-equivᵉ (functional-vec-vecᵉ nᵉ)
  is-equiv-functional-vec-vecᵉ nᵉ =
    is-equiv-is-invertibleᵉ
      ( listed-vec-functional-vecᵉ nᵉ)
      ( is-retraction-functional-vec-vecᵉ nᵉ)
      ( is-section-functional-vec-vecᵉ nᵉ)

  compute-vecᵉ : (nᵉ : ℕᵉ) → functional-vecᵉ Aᵉ nᵉ ≃ᵉ vecᵉ Aᵉ nᵉ
  pr1ᵉ (compute-vecᵉ nᵉ) = listed-vec-functional-vecᵉ nᵉ
  pr2ᵉ (compute-vecᵉ nᵉ) = is-equiv-listed-vec-functional-vecᵉ nᵉ
```

### Characterizing the elementhood predicate

```agda
  is-in-functional-vec-is-in-vecᵉ :
    (nᵉ : ℕᵉ) (vᵉ : vecᵉ Aᵉ nᵉ) (xᵉ : Aᵉ) →
    (xᵉ ∈-vecᵉ vᵉ) → (in-functional-vecᵉ nᵉ xᵉ (functional-vec-vecᵉ nᵉ vᵉ))
  is-in-functional-vec-is-in-vecᵉ (succ-ℕᵉ nᵉ) (yᵉ ∷ᵉ lᵉ) xᵉ (is-headᵉ .xᵉ lᵉ) =
    (inrᵉ starᵉ) ,ᵉ reflᵉ
  is-in-functional-vec-is-in-vecᵉ (succ-ℕᵉ nᵉ) (yᵉ ∷ᵉ lᵉ) xᵉ (is-in-tailᵉ .xᵉ x₁ᵉ lᵉ Iᵉ) =
    inlᵉ (pr1ᵉ (is-in-functional-vec-is-in-vecᵉ nᵉ lᵉ xᵉ Iᵉ)) ,ᵉ
    pr2ᵉ (is-in-functional-vec-is-in-vecᵉ nᵉ lᵉ xᵉ Iᵉ)

  is-in-vec-is-in-functional-vecᵉ :
    (nᵉ : ℕᵉ) (vᵉ : vecᵉ Aᵉ nᵉ) (xᵉ : Aᵉ) →
    (in-functional-vecᵉ nᵉ xᵉ (functional-vec-vecᵉ nᵉ vᵉ)) → (xᵉ ∈-vecᵉ vᵉ)
  is-in-vec-is-in-functional-vecᵉ (succ-ℕᵉ nᵉ) (yᵉ ∷ᵉ vᵉ) xᵉ (inlᵉ kᵉ ,ᵉ pᵉ) =
    is-in-tailᵉ xᵉ yᵉ vᵉ (is-in-vec-is-in-functional-vecᵉ nᵉ vᵉ xᵉ (kᵉ ,ᵉ pᵉ))
  is-in-vec-is-in-functional-vecᵉ (succ-ℕᵉ nᵉ) (yᵉ ∷ᵉ vᵉ) _ (inrᵉ kᵉ ,ᵉ reflᵉ) =
    is-headᵉ (functional-vec-vecᵉ (succ-ℕᵉ nᵉ) (yᵉ ∷ᵉ vᵉ) (inrᵉ kᵉ)) vᵉ
```

### The type of vectors of elements in a truncated type is truncated

#### The type of listed vectors of elements in a truncated type is truncated

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-trunc-Eq-vecᵉ :
    (kᵉ : 𝕋ᵉ) (nᵉ : ℕᵉ) → is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ →
    (uᵉ vᵉ : vecᵉ Aᵉ nᵉ) → is-truncᵉ (kᵉ) (Eq-vecᵉ nᵉ uᵉ vᵉ)
  is-trunc-Eq-vecᵉ kᵉ zero-ℕᵉ A-truncᵉ empty-vecᵉ empty-vecᵉ =
    is-trunc-is-contrᵉ kᵉ is-contr-raise-unitᵉ
  is-trunc-Eq-vecᵉ kᵉ (succ-ℕᵉ nᵉ) A-truncᵉ (xᵉ ∷ᵉ xsᵉ) (yᵉ ∷ᵉ ysᵉ) =
    is-trunc-productᵉ kᵉ (A-truncᵉ xᵉ yᵉ) (is-trunc-Eq-vecᵉ kᵉ nᵉ A-truncᵉ xsᵉ ysᵉ)

  center-is-contr-vecᵉ :
    {nᵉ : ℕᵉ} → is-contrᵉ Aᵉ → vecᵉ Aᵉ nᵉ
  center-is-contr-vecᵉ {zero-ℕᵉ} Hᵉ = empty-vecᵉ
  center-is-contr-vecᵉ {succ-ℕᵉ nᵉ} Hᵉ = centerᵉ Hᵉ ∷ᵉ center-is-contr-vecᵉ {nᵉ} Hᵉ

  contraction-is-contr-vec'ᵉ :
    {nᵉ : ℕᵉ} (Hᵉ : is-contrᵉ Aᵉ) → (vᵉ : vecᵉ Aᵉ nᵉ) →
    Eq-vecᵉ nᵉ (center-is-contr-vecᵉ Hᵉ) vᵉ
  contraction-is-contr-vec'ᵉ {zero-ℕᵉ} Hᵉ empty-vecᵉ =
    refl-Eq-vecᵉ {lᵉ} {Aᵉ} 0 empty-vecᵉ
  pr1ᵉ (contraction-is-contr-vec'ᵉ {succ-ℕᵉ nᵉ} Hᵉ (xᵉ ∷ᵉ vᵉ)) =
    eq-is-contrᵉ Hᵉ
  pr2ᵉ (contraction-is-contr-vec'ᵉ {succ-ℕᵉ nᵉ} Hᵉ (xᵉ ∷ᵉ vᵉ)) =
    contraction-is-contr-vec'ᵉ {nᵉ} Hᵉ vᵉ

  contraction-is-contr-vecᵉ :
    {nᵉ : ℕᵉ} (Hᵉ : is-contrᵉ Aᵉ) → (vᵉ : vecᵉ Aᵉ nᵉ) → (center-is-contr-vecᵉ Hᵉ) ＝ᵉ vᵉ
  contraction-is-contr-vecᵉ {nᵉ} Hᵉ vᵉ =
    eq-Eq-vecᵉ nᵉ (center-is-contr-vecᵉ Hᵉ) vᵉ (contraction-is-contr-vec'ᵉ Hᵉ vᵉ)

  is-contr-vecᵉ :
    {nᵉ : ℕᵉ} → is-contrᵉ Aᵉ → is-contrᵉ (vecᵉ Aᵉ nᵉ)
  pr1ᵉ (is-contr-vecᵉ Hᵉ) = center-is-contr-vecᵉ Hᵉ
  pr2ᵉ (is-contr-vecᵉ Hᵉ) = contraction-is-contr-vecᵉ Hᵉ

  is-trunc-vecᵉ :
    (kᵉ : 𝕋ᵉ) → (nᵉ : ℕᵉ) → is-truncᵉ kᵉ Aᵉ → is-truncᵉ kᵉ (vecᵉ Aᵉ nᵉ)
  is-trunc-vecᵉ neg-two-𝕋ᵉ nᵉ Hᵉ = is-contr-vecᵉ Hᵉ
  is-trunc-vecᵉ (succ-𝕋ᵉ kᵉ) nᵉ Hᵉ xᵉ yᵉ =
    is-trunc-equivᵉ kᵉ
      ( Eq-vecᵉ nᵉ xᵉ yᵉ)
      ( extensionality-vecᵉ nᵉ xᵉ yᵉ)
      ( is-trunc-Eq-vecᵉ kᵉ nᵉ Hᵉ xᵉ yᵉ)
```

#### The type of functional vectors of elements in a truncated type is truncated

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-trunc-functional-vecᵉ :
    (kᵉ : 𝕋ᵉ) (nᵉ : ℕᵉ) → is-truncᵉ kᵉ Aᵉ → is-truncᵉ kᵉ (functional-vecᵉ Aᵉ nᵉ)
  is-trunc-functional-vecᵉ kᵉ nᵉ Hᵉ = is-trunc-function-typeᵉ kᵉ Hᵉ
```

### The type of vectors of elements in a set is a set

#### The type of listed vectors of elements in a set is a set

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-set-vecᵉ : (nᵉ : ℕᵉ) → is-setᵉ Aᵉ ->ᵉ is-setᵉ (vecᵉ Aᵉ nᵉ)
  is-set-vecᵉ = is-trunc-vecᵉ zero-𝕋ᵉ

vec-Setᵉ : {lᵉ : Level} → Setᵉ lᵉ → ℕᵉ → Setᵉ lᵉ
pr1ᵉ (vec-Setᵉ Aᵉ nᵉ) = vecᵉ (type-Setᵉ Aᵉ) nᵉ
pr2ᵉ (vec-Setᵉ Aᵉ nᵉ) = is-set-vecᵉ nᵉ (is-set-type-Setᵉ Aᵉ)
```

#### The type of functional vectors of elements in a set is a set

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-set-functional-vecᵉ : (nᵉ : ℕᵉ) → is-setᵉ Aᵉ → is-setᵉ (functional-vecᵉ Aᵉ nᵉ)
  is-set-functional-vecᵉ = is-trunc-functional-vecᵉ zero-𝕋ᵉ

functional-vec-Setᵉ : {lᵉ : Level} → Setᵉ lᵉ → ℕᵉ → Setᵉ lᵉ
pr1ᵉ (functional-vec-Setᵉ Aᵉ nᵉ) = functional-vecᵉ (type-Setᵉ Aᵉ) nᵉ
pr2ᵉ (functional-vec-Setᵉ Aᵉ nᵉ) = is-set-functional-vecᵉ nᵉ (is-set-type-Setᵉ Aᵉ)
```

### Adding the tail to the head gives the same vector

#### Adding the tail to the head gives the same listed vector

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  cons-head-tail-vecᵉ :
    (nᵉ : ℕᵉ) →
    (vᵉ : vecᵉ Aᵉ (succ-ℕᵉ nᵉ)) →
    ((head-vecᵉ vᵉ) ∷ᵉ (tail-vecᵉ vᵉ)) ＝ᵉ vᵉ
  cons-head-tail-vecᵉ nᵉ (xᵉ ∷ᵉ vᵉ) = reflᵉ
```

#### Adding the tail to the head gives the same functional vector

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where
  htpy-cons-head-tail-functional-vecᵉ :
    ( nᵉ : ℕᵉ) →
    ( vᵉ : functional-vecᵉ Aᵉ (succ-ℕᵉ nᵉ)) →
    ( cons-functional-vecᵉ nᵉ
      ( head-functional-vecᵉ nᵉ vᵉ)
      ( tail-functional-vecᵉ nᵉ vᵉ)) ~ᵉ
      ( vᵉ)
  htpy-cons-head-tail-functional-vecᵉ nᵉ vᵉ (inlᵉ xᵉ) = reflᵉ
  htpy-cons-head-tail-functional-vecᵉ nᵉ vᵉ (inrᵉ starᵉ) = reflᵉ

  cons-head-tail-functional-vecᵉ :
    ( nᵉ : ℕᵉ) →
    ( vᵉ : functional-vecᵉ Aᵉ (succ-ℕᵉ nᵉ)) →
    ( cons-functional-vecᵉ nᵉ
      ( head-functional-vecᵉ nᵉ vᵉ)
      ( tail-functional-vecᵉ nᵉ vᵉ)) ＝ᵉ
      ( vᵉ)
  cons-head-tail-functional-vecᵉ nᵉ vᵉ =
    eq-htpyᵉ (htpy-cons-head-tail-functional-vecᵉ nᵉ vᵉ)
```

### Computing the transport of a vector over its size

```agda
compute-tr-vecᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  {nᵉ mᵉ : ℕᵉ} (pᵉ : succ-ℕᵉ nᵉ ＝ᵉ succ-ℕᵉ mᵉ) (vᵉ : vecᵉ Aᵉ nᵉ) (xᵉ : Aᵉ) →
  trᵉ (vecᵉ Aᵉ) pᵉ (xᵉ ∷ᵉ vᵉ) ＝ᵉ
  (xᵉ ∷ᵉ trᵉ (vecᵉ Aᵉ) (is-injective-succ-ℕᵉ pᵉ) vᵉ)
compute-tr-vecᵉ reflᵉ vᵉ xᵉ = reflᵉ
```