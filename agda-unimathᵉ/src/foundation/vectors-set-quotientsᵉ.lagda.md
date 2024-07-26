# Vectors of set quotients

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module foundation.vectors-set-quotientsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-products-set-quotientsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.multivariable-operationsᵉ
open import foundation.products-equivalence-relationsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.set-quotientsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-set-quotientsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalence-relationsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ

open import linear-algebra.vectorsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Sayᵉ weᵉ haveᵉ aᵉ familyᵉ ofᵉ typesᵉ `A1`,ᵉ ...,ᵉ `An`ᵉ eachᵉ equippedᵉ with anᵉ equivalenceᵉ
relationᵉ `Ri`.ᵉ Then,ᵉ theᵉ setᵉ quotientᵉ ofᵉ aᵉ vectorᵉ with theseᵉ typesᵉ isᵉ theᵉ vectorᵉ
ofᵉ theᵉ setᵉ quotientsᵉ ofᵉ eachᵉ `Ai`.ᵉ

## Definition

### The induced relation on the vector of types

```agda
all-sim-equivalence-relationᵉ :
  { l1ᵉ l2ᵉ : Level}
  ( nᵉ : ℕᵉ)
  ( Aᵉ : functional-vecᵉ (UUᵉ l1ᵉ) nᵉ)
  ( Rᵉ : (iᵉ : Finᵉ nᵉ) → equivalence-relationᵉ l2ᵉ (Aᵉ iᵉ)) →
  ( equivalence-relationᵉ l2ᵉ (multivariable-inputᵉ nᵉ Aᵉ))
all-sim-equivalence-relationᵉ {l1ᵉ} {l2ᵉ} zero-ℕᵉ Aᵉ Rᵉ =
  raise-indiscrete-equivalence-relationᵉ l2ᵉ (raise-unitᵉ l1ᵉ)
all-sim-equivalence-relationᵉ (succ-ℕᵉ nᵉ) Aᵉ Rᵉ =
  product-equivalence-relationᵉ (Rᵉ (inrᵉ starᵉ))
    ( all-sim-equivalence-relationᵉ nᵉ
      ( tail-functional-vecᵉ nᵉ Aᵉ)
      ( λ xᵉ → Rᵉ (inlᵉ xᵉ)))
```

### The set quotient of a vector of types

```agda
set-quotient-vectorᵉ :
  { l1ᵉ l2ᵉ : Level}
  ( nᵉ : ℕᵉ)
  ( Aᵉ : functional-vecᵉ (UUᵉ l1ᵉ) nᵉ)
  ( Rᵉ : (iᵉ : Finᵉ nᵉ) → equivalence-relationᵉ l2ᵉ (Aᵉ iᵉ)) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
set-quotient-vectorᵉ nᵉ Aᵉ Rᵉ =
  multivariable-inputᵉ nᵉ (λ iᵉ → ( set-quotientᵉ (Rᵉ iᵉ)))

is-set-set-quotient-vectorᵉ :
  { l1ᵉ l2ᵉ : Level}
  ( nᵉ : ℕᵉ)
  ( Aᵉ : functional-vecᵉ (UUᵉ l1ᵉ) nᵉ)
  ( Rᵉ : (iᵉ : Finᵉ nᵉ) → equivalence-relationᵉ l2ᵉ (Aᵉ iᵉ)) →
  is-setᵉ (set-quotient-vectorᵉ nᵉ Aᵉ Rᵉ)
is-set-set-quotient-vectorᵉ zero-ℕᵉ Aᵉ Rᵉ = is-set-raise-unitᵉ
is-set-set-quotient-vectorᵉ (succ-ℕᵉ nᵉ) Aᵉ Rᵉ =
  is-set-productᵉ
  ( is-set-set-quotientᵉ (Rᵉ (inrᵉ starᵉ)))
  ( is-set-set-quotient-vectorᵉ nᵉ
    ( tail-functional-vecᵉ nᵉ Aᵉ)
    ( λ xᵉ → Rᵉ (inlᵉ xᵉ)))

set-quotient-vector-Setᵉ :
  { l1ᵉ l2ᵉ : Level}
  ( nᵉ : ℕᵉ)
  ( Aᵉ : functional-vecᵉ (UUᵉ l1ᵉ) nᵉ)
  ( Rᵉ : (iᵉ : Finᵉ nᵉ) → equivalence-relationᵉ l2ᵉ (Aᵉ iᵉ)) →
  Setᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (set-quotient-vector-Setᵉ nᵉ Aᵉ Rᵉ) =
  set-quotient-vectorᵉ nᵉ Aᵉ Rᵉ
pr2ᵉ (set-quotient-vector-Setᵉ nᵉ Aᵉ Rᵉ) =
  is-set-set-quotient-vectorᵉ nᵉ Aᵉ Rᵉ

quotient-vector-mapᵉ :
  { l1ᵉ l2ᵉ : Level}
  ( nᵉ : ℕᵉ)
  ( Aᵉ : functional-vecᵉ (UUᵉ l1ᵉ) nᵉ)
  ( Rᵉ : (iᵉ : Finᵉ nᵉ) → equivalence-relationᵉ l2ᵉ (Aᵉ iᵉ)) →
  multivariable-inputᵉ nᵉ Aᵉ →
  set-quotient-vectorᵉ nᵉ Aᵉ Rᵉ
quotient-vector-mapᵉ zero-ℕᵉ Aᵉ Rᵉ aᵉ = raise-starᵉ
pr1ᵉ (quotient-vector-mapᵉ (succ-ℕᵉ nᵉ) Aᵉ Rᵉ (a0ᵉ ,ᵉ aᵉ)) =
  quotient-mapᵉ (Rᵉ (inrᵉ starᵉ)) (a0ᵉ)
pr2ᵉ (quotient-vector-mapᵉ (succ-ℕᵉ nᵉ) Aᵉ Rᵉ aᵉ) =
  quotient-vector-mapᵉ nᵉ
    ( tail-functional-vecᵉ nᵉ Aᵉ)
    ( λ xᵉ → Rᵉ (inlᵉ xᵉ))
    ( tail-multivariable-inputᵉ nᵉ Aᵉ aᵉ)

reflects-quotient-vector-mapᵉ :
  { l1ᵉ l2ᵉ : Level}
  ( nᵉ : ℕᵉ)
  ( Aᵉ : functional-vecᵉ (UUᵉ l1ᵉ) nᵉ)
  ( Rᵉ : (iᵉ : Finᵉ nᵉ) → equivalence-relationᵉ l2ᵉ (Aᵉ iᵉ)) →
  reflects-equivalence-relationᵉ
    ( all-sim-equivalence-relationᵉ nᵉ Aᵉ Rᵉ)
    ( quotient-vector-mapᵉ nᵉ Aᵉ Rᵉ)
reflects-quotient-vector-mapᵉ zero-ℕᵉ Aᵉ Rᵉ pᵉ = reflᵉ
reflects-quotient-vector-mapᵉ (succ-ℕᵉ nᵉ) Aᵉ Rᵉ (pᵉ ,ᵉ p'ᵉ) =
  eq-pairᵉ
    ( apply-effectiveness-quotient-map'ᵉ (Rᵉ (inrᵉ starᵉ)) pᵉ)
    ( reflects-quotient-vector-mapᵉ nᵉ
      ( tail-functional-vecᵉ nᵉ Aᵉ)
      ( λ xᵉ → Rᵉ (inlᵉ xᵉ)) p'ᵉ)

reflecting-map-quotient-vector-mapᵉ :
  { l1ᵉ l2ᵉ : Level}
  ( nᵉ : ℕᵉ)
  ( Aᵉ : functional-vecᵉ (UUᵉ l1ᵉ) nᵉ)
  ( Rᵉ : (iᵉ : Finᵉ nᵉ) → equivalence-relationᵉ l2ᵉ (Aᵉ iᵉ)) →
  reflecting-map-equivalence-relationᵉ
    ( all-sim-equivalence-relationᵉ nᵉ Aᵉ Rᵉ)
    ( set-quotient-vectorᵉ nᵉ Aᵉ Rᵉ)
pr1ᵉ (reflecting-map-quotient-vector-mapᵉ nᵉ Aᵉ Rᵉ) =
  quotient-vector-mapᵉ nᵉ Aᵉ Rᵉ
pr2ᵉ (reflecting-map-quotient-vector-mapᵉ nᵉ Aᵉ Rᵉ) =
  reflects-quotient-vector-mapᵉ nᵉ Aᵉ Rᵉ

equiv-set-quotient-vectorᵉ :
  { l1ᵉ l2ᵉ : Level}
  ( nᵉ : ℕᵉ)
  ( Aᵉ : functional-vecᵉ (UUᵉ l1ᵉ) nᵉ)
  ( Rᵉ : (iᵉ : Finᵉ nᵉ) → equivalence-relationᵉ l2ᵉ (Aᵉ iᵉ)) →
  set-quotient-vectorᵉ nᵉ Aᵉ Rᵉ ≃ᵉ set-quotientᵉ (all-sim-equivalence-relationᵉ nᵉ Aᵉ Rᵉ)
pr1ᵉ (equiv-set-quotient-vectorᵉ zero-ℕᵉ Aᵉ Rᵉ) _ = quotient-mapᵉ _ raise-starᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ (equiv-set-quotient-vectorᵉ zero-ℕᵉ Aᵉ Rᵉ))) _ = raise-starᵉ
pr2ᵉ (pr1ᵉ (pr2ᵉ (equiv-set-quotient-vectorᵉ {l1ᵉ} {l2ᵉ} zero-ℕᵉ Aᵉ Rᵉ))) =
  induction-set-quotientᵉ
    ( raise-indiscrete-equivalence-relationᵉ l2ᵉ (raise-unitᵉ l1ᵉ))
    ( λ xᵉ → pairᵉ _ (is-set-set-quotientᵉ _ _ xᵉ))
    ( λ xᵉ → apply-effectiveness-quotient-map'ᵉ _ raise-starᵉ)
pr1ᵉ (pr2ᵉ (pr2ᵉ (equiv-set-quotient-vectorᵉ zero-ℕᵉ Aᵉ Rᵉ))) _ = raise-starᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (equiv-set-quotient-vectorᵉ zero-ℕᵉ Aᵉ Rᵉ))) (map-raiseᵉ starᵉ) = reflᵉ
equiv-set-quotient-vectorᵉ (succ-ℕᵉ nᵉ) Aᵉ Rᵉ =
  equivalence-reasoningᵉ
    set-quotientᵉ (Rᵉ (inrᵉ starᵉ)) ×ᵉ
        ( set-quotient-vectorᵉ nᵉ
          ( tail-functional-vecᵉ nᵉ Aᵉ)
          ( λ xᵉ → Rᵉ (inlᵉ xᵉ)))
    ≃ᵉ set-quotientᵉ (Rᵉ (inrᵉ starᵉ)) ×ᵉ
        ( set-quotientᵉ
          (all-sim-equivalence-relationᵉ nᵉ
          ( tail-functional-vecᵉ nᵉ Aᵉ)
          ( λ xᵉ → Rᵉ (inlᵉ xᵉ))))
      byᵉ lemmaᵉ
    ≃ᵉ set-quotientᵉ (all-sim-equivalence-relationᵉ (succ-ℕᵉ nᵉ) Aᵉ Rᵉ)
      byᵉ (equiv-quotient-product-product-set-quotientᵉ _ _)
  where
  lemmaᵉ :
    ( set-quotientᵉ (Rᵉ (inrᵉ starᵉ)) ×ᵉ
      ( set-quotient-vectorᵉ nᵉ
        ( tail-functional-vecᵉ nᵉ Aᵉ)
        (λ xᵉ → Rᵉ (inlᵉ xᵉ)))) ≃ᵉ
      ( set-quotientᵉ (Rᵉ (inrᵉ starᵉ)) ×ᵉ
        ( set-quotientᵉ
          ( all-sim-equivalence-relationᵉ nᵉ
            ( tail-functional-vecᵉ nᵉ Aᵉ)
            ( λ xᵉ → Rᵉ (inlᵉ xᵉ)))))
  pr1ᵉ (pr1ᵉ lemmaᵉ (qa0ᵉ ,ᵉ qaᵉ)) = qa0ᵉ
  pr2ᵉ (pr1ᵉ lemmaᵉ (qa0ᵉ ,ᵉ qaᵉ)) = map-equivᵉ (equiv-set-quotient-vectorᵉ nᵉ _ _) qaᵉ
  pr1ᵉ (pr1ᵉ (pr1ᵉ (pr2ᵉ lemmaᵉ)) (qa0ᵉ ,ᵉ qaᵉ)) = qa0ᵉ
  pr2ᵉ (pr1ᵉ (pr1ᵉ (pr2ᵉ lemmaᵉ)) (qa0ᵉ ,ᵉ qaᵉ)) =
    map-inv-equivᵉ (equiv-set-quotient-vectorᵉ nᵉ _ _) qaᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ lemmaᵉ)) (qa0ᵉ ,ᵉ qaᵉ) =
    eq-pairᵉ reflᵉ (is-section-map-inv-equivᵉ (equiv-set-quotient-vectorᵉ nᵉ _ _) qaᵉ)
  pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ lemmaᵉ)) (qa0ᵉ ,ᵉ qaᵉ)) = qa0ᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ lemmaᵉ)) (qa0ᵉ ,ᵉ qaᵉ)) =
    map-inv-equivᵉ (equiv-set-quotient-vectorᵉ nᵉ _ _) qaᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ lemmaᵉ)) (qa0ᵉ ,ᵉ qaᵉ) =
    eq-pairᵉ
      ( reflᵉ)
      ( is-retraction-map-inv-equivᵉ (equiv-set-quotient-vectorᵉ nᵉ _ _) qaᵉ)

map-equiv-equiv-set-quotient-vector-quotient-mapᵉ :
  { l1ᵉ l2ᵉ : Level}
  ( nᵉ : ℕᵉ)
  ( Aᵉ : functional-vecᵉ (UUᵉ l1ᵉ) nᵉ)
  ( Rᵉ : (iᵉ : Finᵉ nᵉ) → equivalence-relationᵉ l2ᵉ (Aᵉ iᵉ)) →
  ( map-equivᵉ (equiv-set-quotient-vectorᵉ nᵉ Aᵉ Rᵉ) ∘ᵉ
    ( quotient-vector-mapᵉ nᵉ Aᵉ Rᵉ)) ~ᵉ
  ( quotient-mapᵉ (all-sim-equivalence-relationᵉ nᵉ Aᵉ Rᵉ))
map-equiv-equiv-set-quotient-vector-quotient-mapᵉ zero-ℕᵉ Aᵉ Rᵉ (map-raiseᵉ starᵉ) =
  reflᵉ
map-equiv-equiv-set-quotient-vector-quotient-mapᵉ (succ-ℕᵉ nᵉ) Aᵉ Rᵉ (a0ᵉ ,ᵉ aᵉ) =
  apᵉ
    ( λ qaᵉ →
      map-equivᵉ
        ( equiv-quotient-product-product-set-quotientᵉ _ _)
        ( quotient-mapᵉ (Rᵉ (inrᵉ starᵉ)) a0ᵉ ,ᵉ qaᵉ))
    ( map-equiv-equiv-set-quotient-vector-quotient-mapᵉ nᵉ
        ( tail-functional-vecᵉ nᵉ Aᵉ)
        ( λ xᵉ → Rᵉ (inlᵉ xᵉ)) aᵉ) ∙ᵉ
  ( triangle-uniqueness-product-set-quotientᵉ
    ( Rᵉ (inrᵉ starᵉ))
    ( all-sim-equivalence-relationᵉ nᵉ (λ zᵉ → tail-functional-vecᵉ nᵉ Aᵉ zᵉ)
    ( λ iᵉ → Rᵉ (inlᵉ iᵉ)))
    ( a0ᵉ ,ᵉ aᵉ))

inv-precomp-vector-set-quotientᵉ :
  { lᵉ l1ᵉ l2ᵉ : Level}
  ( nᵉ : ℕᵉ)
  ( Aᵉ : functional-vecᵉ (UUᵉ l1ᵉ) nᵉ)
  ( Rᵉ : (iᵉ : Finᵉ nᵉ) → equivalence-relationᵉ l2ᵉ (Aᵉ iᵉ)) →
  (Xᵉ : Setᵉ lᵉ) →
  reflecting-map-equivalence-relationᵉ
    ( all-sim-equivalence-relationᵉ nᵉ Aᵉ Rᵉ)
    ( type-Setᵉ Xᵉ) →
  ((set-quotient-vectorᵉ nᵉ Aᵉ Rᵉ) → type-Setᵉ Xᵉ)
inv-precomp-vector-set-quotientᵉ zero-ℕᵉ Aᵉ Rᵉ Xᵉ fᵉ (map-raiseᵉ starᵉ) =
  pr1ᵉ fᵉ raise-starᵉ
inv-precomp-vector-set-quotientᵉ (succ-ℕᵉ nᵉ) Aᵉ Rᵉ Xᵉ fᵉ (qa0ᵉ ,ᵉ qaᵉ) =
  inv-precomp-set-quotient-product-set-quotientᵉ
    ( Rᵉ (inrᵉ starᵉ))
    ( all-sim-equivalence-relationᵉ nᵉ
      ( tail-functional-vecᵉ nᵉ Aᵉ)
      ( λ xᵉ → Rᵉ (inlᵉ xᵉ)))
    ( Xᵉ)
    ( fᵉ)
    ( qa0ᵉ ,ᵉ map-equivᵉ (equiv-set-quotient-vectorᵉ nᵉ _ _) qaᵉ)

abstract
  is-section-inv-precomp-vector-set-quotientᵉ :
    { lᵉ l1ᵉ l2ᵉ : Level}
    ( nᵉ : ℕᵉ)
    ( Aᵉ : functional-vecᵉ (UUᵉ l1ᵉ) nᵉ)
    ( Rᵉ : (iᵉ : Finᵉ nᵉ) → equivalence-relationᵉ l2ᵉ (Aᵉ iᵉ)) →
    ( Xᵉ : Setᵉ lᵉ) →
    ( precomp-Set-Quotientᵉ
      ( all-sim-equivalence-relationᵉ nᵉ Aᵉ Rᵉ)
      ( set-quotient-vector-Setᵉ nᵉ Aᵉ Rᵉ)
      ( reflecting-map-quotient-vector-mapᵉ nᵉ Aᵉ Rᵉ)
      ( Xᵉ)) ∘ᵉ
    ( inv-precomp-vector-set-quotientᵉ nᵉ Aᵉ Rᵉ Xᵉ) ~ᵉ
    ( idᵉ)
  is-section-inv-precomp-vector-set-quotientᵉ {lᵉ} {l1ᵉ} {l2ᵉ} 0 Aᵉ Rᵉ Xᵉ fᵉ =
    eq-pair-Σᵉ
      ( eq-htpyᵉ (λ where (map-raiseᵉ starᵉ) → reflᵉ))
      ( eq-is-propᵉ
        ( is-prop-reflects-equivalence-relationᵉ
          ( raise-indiscrete-equivalence-relationᵉ l2ᵉ (raise-unitᵉ l1ᵉ))
          ( Xᵉ)
          ( map-reflecting-map-equivalence-relationᵉ _ fᵉ)))
  is-section-inv-precomp-vector-set-quotientᵉ (succ-ℕᵉ nᵉ) Aᵉ Rᵉ Xᵉ fᵉ =
    eq-pair-Σᵉ
      ( eq-htpyᵉ
        ( λ (a0ᵉ ,ᵉ aᵉ) →
          ( apᵉ
            ( inv-precomp-set-quotient-product-set-quotientᵉ
              ( Rᵉ (inrᵉ starᵉ))
              ( all-sim-equivalence-relationᵉ nᵉ
                ( tail-functional-vecᵉ nᵉ Aᵉ)
                ( λ xᵉ → Rᵉ (inlᵉ xᵉ))) Xᵉ fᵉ)
            ( eq-pair-eq-fiberᵉ
              ( map-equiv-equiv-set-quotient-vector-quotient-mapᵉ nᵉ _ _ aᵉ)) ∙ᵉ
          ( htpy-eqᵉ
            ( apᵉ
              ( map-reflecting-map-equivalence-relationᵉ _)
              ( is-section-inv-precomp-set-quotient-product-set-quotientᵉ
                ( Rᵉ (inrᵉ starᵉ))
                ( all-sim-equivalence-relationᵉ nᵉ
                  ( tail-functional-vecᵉ nᵉ Aᵉ)
                  ( λ xᵉ → Rᵉ (inlᵉ xᵉ))) Xᵉ fᵉ))
            ( a0ᵉ ,ᵉ aᵉ)))))
      ( eq-is-propᵉ
        ( is-prop-reflects-equivalence-relationᵉ
          ( all-sim-equivalence-relationᵉ (succ-ℕᵉ nᵉ) Aᵉ Rᵉ)
          ( Xᵉ)
          ( map-reflecting-map-equivalence-relationᵉ _ fᵉ)))

section-precomp-vector-set-quotientᵉ :
  { lᵉ l1ᵉ l2ᵉ : Level}
  ( nᵉ : ℕᵉ)
  ( Aᵉ : functional-vecᵉ (UUᵉ l1ᵉ) nᵉ)
  ( Rᵉ : (iᵉ : Finᵉ nᵉ) → equivalence-relationᵉ l2ᵉ (Aᵉ iᵉ)) →
  ( Xᵉ : Setᵉ lᵉ) →
  ( sectionᵉ
    ( precomp-Set-Quotientᵉ
      ( all-sim-equivalence-relationᵉ nᵉ Aᵉ Rᵉ)
      ( set-quotient-vector-Setᵉ nᵉ Aᵉ Rᵉ)
      ( reflecting-map-quotient-vector-mapᵉ nᵉ Aᵉ Rᵉ)
      ( Xᵉ)))
pr1ᵉ (section-precomp-vector-set-quotientᵉ nᵉ Aᵉ Rᵉ Xᵉ) =
  inv-precomp-vector-set-quotientᵉ nᵉ Aᵉ Rᵉ Xᵉ
pr2ᵉ (section-precomp-vector-set-quotientᵉ nᵉ Aᵉ Rᵉ Xᵉ) =
  is-section-inv-precomp-vector-set-quotientᵉ nᵉ Aᵉ Rᵉ Xᵉ

abstract
  is-retraction-inv-precomp-vector-set-quotientᵉ :
    { lᵉ l1ᵉ l2ᵉ : Level}
    ( nᵉ : ℕᵉ)
    ( Aᵉ : functional-vecᵉ (UUᵉ l1ᵉ) nᵉ)
    ( Rᵉ : (iᵉ : Finᵉ nᵉ) → equivalence-relationᵉ l2ᵉ (Aᵉ iᵉ)) →
    ( Xᵉ : Setᵉ lᵉ) →
    ( retractionᵉ
      ( precomp-Set-Quotientᵉ
        ( all-sim-equivalence-relationᵉ nᵉ Aᵉ Rᵉ)
        ( set-quotient-vector-Setᵉ nᵉ Aᵉ Rᵉ)
        ( reflecting-map-quotient-vector-mapᵉ nᵉ Aᵉ Rᵉ)
        ( Xᵉ)))
  pr1ᵉ (is-retraction-inv-precomp-vector-set-quotientᵉ nᵉ Aᵉ Rᵉ Xᵉ) =
    inv-precomp-vector-set-quotientᵉ nᵉ Aᵉ Rᵉ Xᵉ
  pr2ᵉ (is-retraction-inv-precomp-vector-set-quotientᵉ zero-ℕᵉ Aᵉ Rᵉ Xᵉ) fᵉ =
    eq-htpyᵉ (λ where (map-raiseᵉ starᵉ) → reflᵉ)
  pr2ᵉ (is-retraction-inv-precomp-vector-set-quotientᵉ (succ-ℕᵉ nᵉ) Aᵉ Rᵉ Xᵉ) fᵉ =
    apᵉ (_∘ᵉ set-quotient-vector-product-set-quotientᵉ)
      is-inv-map-inv-equiv-fᵉ ∙ᵉ lemma-fᵉ
    where
    precomp-fᵉ :
      reflecting-map-equivalence-relationᵉ
        ( product-equivalence-relationᵉ (Rᵉ (inrᵉ starᵉ))
        ( all-sim-equivalence-relationᵉ nᵉ
          ( tail-functional-vecᵉ nᵉ Aᵉ)
          ( λ xᵉ → Rᵉ (inlᵉ xᵉ))))
        ( type-Setᵉ Xᵉ)
    precomp-fᵉ =
      precomp-Set-Quotientᵉ
        ( product-equivalence-relationᵉ (Rᵉ (inrᵉ starᵉ))
        ( all-sim-equivalence-relationᵉ nᵉ
          ( tail-functional-vecᵉ nᵉ Aᵉ)
          ( λ xᵉ → Rᵉ (inlᵉ xᵉ))))
        ( set-quotient-vector-Setᵉ (succ-ℕᵉ nᵉ) Aᵉ Rᵉ)
        ( reflecting-map-quotient-vector-mapᵉ (succ-ℕᵉ nᵉ) Aᵉ Rᵉ) Xᵉ fᵉ

    set-quotient-vector-product-set-quotientᵉ :
      ( set-quotient-vectorᵉ (succ-ℕᵉ nᵉ) Aᵉ Rᵉ) →
      ( product-set-quotientᵉ
        ( Rᵉ (inrᵉ starᵉ))
        ( all-sim-equivalence-relationᵉ nᵉ
          ( tail-functional-vecᵉ nᵉ Aᵉ)
          ( λ xᵉ → Rᵉ (inlᵉ xᵉ))))
    set-quotient-vector-product-set-quotientᵉ (qa0'ᵉ ,ᵉ qa'ᵉ) =
      (qa0'ᵉ ,ᵉ map-equivᵉ (equiv-set-quotient-vectorᵉ nᵉ _ _) qa'ᵉ)

    map-inv-equiv-fᵉ :
      ( product-set-quotientᵉ
        ( Rᵉ (inrᵉ starᵉ))
        ( all-sim-equivalence-relationᵉ nᵉ
          ( tail-functional-vecᵉ nᵉ Aᵉ)
          ( λ xᵉ → Rᵉ (inlᵉ xᵉ)))) →
      ( type-Setᵉ Xᵉ)
    map-inv-equiv-fᵉ (qa0ᵉ ,ᵉ qaᵉ) =
      fᵉ (qa0ᵉ ,ᵉ map-inv-equivᵉ (equiv-set-quotient-vectorᵉ nᵉ _ _) qaᵉ)

    lemma-fᵉ : (map-inv-equiv-fᵉ ∘ᵉ set-quotient-vector-product-set-quotientᵉ) ＝ᵉ fᵉ
    lemma-fᵉ =
      eq-htpyᵉ
        ( λ (qa0ᵉ ,ᵉ qaᵉ) →
          ( apᵉ fᵉ
            ( eq-pair-eq-fiberᵉ
              ( is-retraction-map-inv-equivᵉ
                ( equiv-set-quotient-vectorᵉ nᵉ _ _)
                ( qaᵉ)))))

    is-retraction-inv-precomp-fᵉ :
      ( inv-precomp-set-quotient-product-set-quotientᵉ
        ( Rᵉ (inrᵉ starᵉ))
        ( all-sim-equivalence-relationᵉ nᵉ
          ( tail-functional-vecᵉ nᵉ Aᵉ)
          ( λ xᵉ → Rᵉ (inlᵉ xᵉ)))
        ( Xᵉ)
        ( precomp-Set-Quotientᵉ
          ( product-equivalence-relationᵉ (Rᵉ (inrᵉ starᵉ))
          ( all-sim-equivalence-relationᵉ nᵉ
            ( tail-functional-vecᵉ nᵉ Aᵉ)
            ( λ xᵉ → Rᵉ (inlᵉ xᵉ))))
          ( product-set-quotient-Setᵉ
            ( Rᵉ (inrᵉ starᵉ))
            ( all-sim-equivalence-relationᵉ nᵉ
              ( tail-functional-vecᵉ nᵉ Aᵉ)
              ( λ xᵉ → Rᵉ (inlᵉ xᵉ))))
            ( reflecting-map-product-quotient-mapᵉ (Rᵉ (inrᵉ starᵉ))
            ( all-sim-equivalence-relationᵉ nᵉ
              ( tail-functional-vecᵉ nᵉ Aᵉ)
              ( λ xᵉ → Rᵉ (inlᵉ xᵉ))))
            ( Xᵉ)
            ( map-inv-equiv-fᵉ))) ＝ᵉ
      map-inv-equiv-fᵉ
    is-retraction-inv-precomp-fᵉ =
      is-retraction-inv-precomp-set-quotient-product-set-quotientᵉ
        ( Rᵉ (inrᵉ starᵉ))
        ( all-sim-equivalence-relationᵉ nᵉ
          ( tail-functional-vecᵉ nᵉ Aᵉ)
          ( λ xᵉ → Rᵉ (inlᵉ xᵉ)))
        ( Xᵉ)
        ( map-inv-equiv-fᵉ)

    is-inv-map-inv-equiv-fᵉ :
      ( inv-precomp-set-quotient-product-set-quotientᵉ
      ( Rᵉ (inrᵉ starᵉ))
      ( all-sim-equivalence-relationᵉ nᵉ
        ( tail-functional-vecᵉ nᵉ Aᵉ)
        ( λ xᵉ → Rᵉ (inlᵉ xᵉ)))
        ( Xᵉ)
        ( precomp-fᵉ)) ＝ᵉ
        map-inv-equiv-fᵉ
    is-inv-map-inv-equiv-fᵉ =
      apᵉ
        ( inv-precomp-set-quotient-product-set-quotientᵉ
          ( Rᵉ (inrᵉ starᵉ))
          ( all-sim-equivalence-relationᵉ nᵉ (tail-functional-vecᵉ nᵉ Aᵉ)
          ( λ xᵉ → Rᵉ (inlᵉ xᵉ)))
          ( Xᵉ))
        ( eq-pair-Σᵉ
          ( apᵉ ( _∘ᵉ quotient-vector-mapᵉ _ Aᵉ Rᵉ) (invᵉ lemma-fᵉ) ∙ᵉ
            ( apᵉ
              ( map-inv-equiv-fᵉ ∘ᵉ_)
              ( eq-htpyᵉ
                ( λ (a0ᵉ ,ᵉ aᵉ) →
                  ( eq-pair-eq-fiberᵉ
                    ( map-equiv-equiv-set-quotient-vector-quotient-mapᵉ
                      _ _ _ aᵉ))))))
          ( eq-is-propᵉ
            ( is-prop-reflects-equivalence-relationᵉ
              ( product-equivalence-relationᵉ
                ( Rᵉ (inrᵉ starᵉ))
                ( all-sim-equivalence-relationᵉ nᵉ _ _))
              ( Xᵉ) _))) ∙ᵉ
        is-retraction-inv-precomp-fᵉ

is-set-quotient-vector-set-quotientᵉ :
  { l1ᵉ l2ᵉ : Level}
  ( nᵉ : ℕᵉ)
  ( Aᵉ : functional-vecᵉ (UUᵉ l1ᵉ) nᵉ)
  ( Rᵉ : (iᵉ : Finᵉ nᵉ) → equivalence-relationᵉ l2ᵉ (Aᵉ iᵉ)) →
  is-set-quotientᵉ
    ( all-sim-equivalence-relationᵉ nᵉ Aᵉ Rᵉ)
    ( set-quotient-vector-Setᵉ nᵉ Aᵉ Rᵉ)
    ( reflecting-map-quotient-vector-mapᵉ nᵉ Aᵉ Rᵉ)
pr1ᵉ (is-set-quotient-vector-set-quotientᵉ nᵉ Aᵉ Rᵉ Xᵉ) =
  section-precomp-vector-set-quotientᵉ nᵉ Aᵉ Rᵉ Xᵉ
pr2ᵉ (is-set-quotient-vector-set-quotientᵉ nᵉ Aᵉ Rᵉ Xᵉ) =
  is-retraction-inv-precomp-vector-set-quotientᵉ nᵉ Aᵉ Rᵉ Xᵉ
```