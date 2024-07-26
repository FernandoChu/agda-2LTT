# Equality of cartesian product types

```agda
module foundation.equality-cartesian-product-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Identificationsᵉ `Idᵉ (pairᵉ xᵉ yᵉ) (pairᵉ x'ᵉ y')`ᵉ in aᵉ cartesianᵉ productᵉ areᵉ
equivalentlyᵉ describedᵉ asᵉ pairsᵉ ofᵉ identificationsᵉ `Idᵉ xᵉ x'`ᵉ andᵉ `Idᵉ yᵉ y'`.ᵉ Thisᵉ
providesᵉ usᵉ with aᵉ characterizationᵉ ofᵉ theᵉ identityᵉ typeᵉ ofᵉ cartesianᵉ productᵉ
types.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  Eq-productᵉ : (sᵉ tᵉ : Aᵉ ×ᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  Eq-productᵉ sᵉ tᵉ = ((pr1ᵉ sᵉ) ＝ᵉ (pr1ᵉ tᵉ)) ×ᵉ ((pr2ᵉ sᵉ) ＝ᵉ (pr2ᵉ tᵉ))
```

## Properties

### The type `Eq-product s t` is equivalent to `Id s t`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  eq-pair'ᵉ : {sᵉ tᵉ : Aᵉ ×ᵉ Bᵉ} → Eq-productᵉ sᵉ tᵉ → sᵉ ＝ᵉ tᵉ
  eq-pair'ᵉ {pairᵉ xᵉ yᵉ} {pairᵉ .xᵉ .yᵉ} (pairᵉ reflᵉ reflᵉ) = reflᵉ

  eq-pairᵉ :
    {sᵉ tᵉ : Aᵉ ×ᵉ Bᵉ} → (pr1ᵉ sᵉ) ＝ᵉ (pr1ᵉ tᵉ) → (pr2ᵉ sᵉ) ＝ᵉ (pr2ᵉ tᵉ) → sᵉ ＝ᵉ tᵉ
  eq-pairᵉ pᵉ qᵉ = eq-pair'ᵉ (pairᵉ pᵉ qᵉ)

  pair-eqᵉ : {sᵉ tᵉ : Aᵉ ×ᵉ Bᵉ} → sᵉ ＝ᵉ tᵉ → Eq-productᵉ sᵉ tᵉ
  pr1ᵉ (pair-eqᵉ αᵉ) = apᵉ pr1ᵉ αᵉ
  pr2ᵉ (pair-eqᵉ αᵉ) = apᵉ pr2ᵉ αᵉ

  is-retraction-pair-eqᵉ :
    {sᵉ tᵉ : Aᵉ ×ᵉ Bᵉ} → ((pair-eqᵉ {sᵉ} {tᵉ}) ∘ᵉ (eq-pair'ᵉ {sᵉ} {tᵉ})) ~ᵉ idᵉ
  is-retraction-pair-eqᵉ {pairᵉ xᵉ yᵉ} {pairᵉ .xᵉ .yᵉ} (pairᵉ reflᵉ reflᵉ) = reflᵉ

  is-section-pair-eqᵉ :
    {sᵉ tᵉ : Aᵉ ×ᵉ Bᵉ} → ((eq-pair'ᵉ {sᵉ} {tᵉ}) ∘ᵉ (pair-eqᵉ {sᵉ} {tᵉ})) ~ᵉ idᵉ
  is-section-pair-eqᵉ {pairᵉ xᵉ yᵉ} {pairᵉ .xᵉ .yᵉ} reflᵉ = reflᵉ

  abstract
    is-equiv-eq-pairᵉ :
      (sᵉ tᵉ : Aᵉ ×ᵉ Bᵉ) → is-equivᵉ (eq-pair'ᵉ {sᵉ} {tᵉ})
    is-equiv-eq-pairᵉ sᵉ tᵉ =
      is-equiv-is-invertibleᵉ pair-eqᵉ is-section-pair-eqᵉ is-retraction-pair-eqᵉ

  equiv-eq-pairᵉ :
    (sᵉ tᵉ : Aᵉ ×ᵉ Bᵉ) → Eq-productᵉ sᵉ tᵉ ≃ᵉ (sᵉ ＝ᵉ tᵉ)
  pr1ᵉ (equiv-eq-pairᵉ sᵉ tᵉ) = eq-pair'ᵉ
  pr2ᵉ (equiv-eq-pairᵉ sᵉ tᵉ) = is-equiv-eq-pairᵉ sᵉ tᵉ

  abstract
    is-equiv-pair-eqᵉ :
      (sᵉ tᵉ : Aᵉ ×ᵉ Bᵉ) → is-equivᵉ (pair-eqᵉ {sᵉ} {tᵉ})
    is-equiv-pair-eqᵉ sᵉ tᵉ =
      is-equiv-is-invertibleᵉ eq-pair'ᵉ is-retraction-pair-eqᵉ is-section-pair-eqᵉ

  equiv-pair-eqᵉ :
    (sᵉ tᵉ : Aᵉ ×ᵉ Bᵉ) → (sᵉ ＝ᵉ tᵉ) ≃ᵉ Eq-productᵉ sᵉ tᵉ
  pr1ᵉ (equiv-pair-eqᵉ sᵉ tᵉ) = pair-eqᵉ
  pr2ᵉ (equiv-pair-eqᵉ sᵉ tᵉ) = is-equiv-pair-eqᵉ sᵉ tᵉ
```

### Commuting triangles for `eq-pair`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  triangle-eq-pairᵉ :
    {a0ᵉ a1ᵉ : Aᵉ} {b0ᵉ b1ᵉ : Bᵉ} (pᵉ : a0ᵉ ＝ᵉ a1ᵉ) (qᵉ : b0ᵉ ＝ᵉ b1ᵉ) →
    eq-pairᵉ pᵉ qᵉ ＝ᵉ ((eq-pairᵉ pᵉ reflᵉ) ∙ᵉ (eq-pairᵉ reflᵉ qᵉ))
  triangle-eq-pairᵉ reflᵉ reflᵉ = reflᵉ

  triangle-eq-pair'ᵉ :
    {a0ᵉ a1ᵉ : Aᵉ} {b0ᵉ b1ᵉ : Bᵉ} (pᵉ : a0ᵉ ＝ᵉ a1ᵉ) (qᵉ : b0ᵉ ＝ᵉ b1ᵉ) →
    eq-pairᵉ pᵉ qᵉ ＝ᵉ ((eq-pairᵉ reflᵉ qᵉ) ∙ᵉ (eq-pairᵉ pᵉ reflᵉ))
  triangle-eq-pair'ᵉ reflᵉ reflᵉ = reflᵉ
```

### `eq-pair` preserves concatenation

```agda
eq-pair-concatᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {xᵉ x'ᵉ x''ᵉ : Aᵉ} {yᵉ y'ᵉ y''ᵉ : Bᵉ}
  (pᵉ : xᵉ ＝ᵉ x'ᵉ) (p'ᵉ : x'ᵉ ＝ᵉ x''ᵉ) (qᵉ : yᵉ ＝ᵉ y'ᵉ) (q'ᵉ : y'ᵉ ＝ᵉ y''ᵉ) →
  ( eq-pairᵉ {sᵉ = pairᵉ xᵉ yᵉ} {tᵉ = pairᵉ x''ᵉ y''ᵉ} (pᵉ ∙ᵉ p'ᵉ) (qᵉ ∙ᵉ q'ᵉ)) ＝ᵉ
  ( ( eq-pairᵉ {sᵉ = pairᵉ xᵉ yᵉ} {tᵉ = pairᵉ x'ᵉ y'ᵉ} pᵉ qᵉ) ∙ᵉ
    ( eq-pairᵉ p'ᵉ q'ᵉ))
eq-pair-concatᵉ reflᵉ p'ᵉ reflᵉ q'ᵉ = reflᵉ
```

### `eq-pair` computes in the expected way when the action on paths of the projections is applies

```agda
ap-pr1-eq-pairᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ x'ᵉ) {yᵉ y'ᵉ : Bᵉ} (qᵉ : yᵉ ＝ᵉ y'ᵉ) →
  apᵉ pr1ᵉ (eq-pairᵉ {sᵉ = pairᵉ xᵉ yᵉ} {pairᵉ x'ᵉ y'ᵉ} pᵉ qᵉ) ＝ᵉ pᵉ
ap-pr1-eq-pairᵉ reflᵉ reflᵉ = reflᵉ

ap-pr2-eq-pairᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ x'ᵉ) {yᵉ y'ᵉ : Bᵉ} (qᵉ : yᵉ ＝ᵉ y'ᵉ) →
  apᵉ pr2ᵉ (eq-pairᵉ {sᵉ = pairᵉ xᵉ yᵉ} {pairᵉ x'ᵉ y'ᵉ} pᵉ qᵉ) ＝ᵉ qᵉ
ap-pr2-eq-pairᵉ reflᵉ reflᵉ = reflᵉ
```

#### Computing transport along a path of the form `eq-pair`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {a0ᵉ a1ᵉ : Aᵉ} {b0ᵉ b1ᵉ : Bᵉ}
  where

  tr-eq-pairᵉ :
    (Cᵉ : Aᵉ ×ᵉ Bᵉ → UUᵉ l3ᵉ) (pᵉ : a0ᵉ ＝ᵉ a1ᵉ) (qᵉ : b0ᵉ ＝ᵉ b1ᵉ) (uᵉ : Cᵉ (a0ᵉ ,ᵉ b0ᵉ)) →
    trᵉ Cᵉ (eq-pairᵉ pᵉ qᵉ) uᵉ ＝ᵉ
    trᵉ (λ xᵉ → Cᵉ (a1ᵉ ,ᵉ xᵉ)) qᵉ (trᵉ (λ xᵉ → Cᵉ (xᵉ ,ᵉ b0ᵉ)) pᵉ uᵉ)
  tr-eq-pairᵉ Cᵉ reflᵉ reflᵉ uᵉ = reflᵉ
```

#### Computing transport along a path of the form `eq-pair` When one of the paths is `refl`

```agda
  left-unit-law-tr-eq-pairᵉ :
    (Cᵉ : Aᵉ ×ᵉ Bᵉ → UUᵉ l3ᵉ) (qᵉ : b0ᵉ ＝ᵉ b1ᵉ) (uᵉ : Cᵉ (a0ᵉ ,ᵉ b0ᵉ)) →
    (trᵉ Cᵉ (eq-pairᵉ reflᵉ qᵉ) uᵉ) ＝ᵉ trᵉ (λ xᵉ → Cᵉ (a0ᵉ ,ᵉ xᵉ)) qᵉ uᵉ
  left-unit-law-tr-eq-pairᵉ Cᵉ reflᵉ uᵉ = reflᵉ

  right-unit-law-tr-eq-pairᵉ :
    (Cᵉ : Aᵉ ×ᵉ Bᵉ → UUᵉ l3ᵉ) (pᵉ : a0ᵉ ＝ᵉ a1ᵉ) (uᵉ : Cᵉ (a0ᵉ ,ᵉ b0ᵉ)) →
    (trᵉ Cᵉ (eq-pairᵉ pᵉ reflᵉ) uᵉ) ＝ᵉ trᵉ (λ xᵉ → Cᵉ (xᵉ ,ᵉ b0ᵉ)) pᵉ uᵉ
  right-unit-law-tr-eq-pairᵉ Cᵉ reflᵉ uᵉ = reflᵉ
```

#### Computing transport along a path of the form `eq-pair` when both paths are identical

```agda
tr-eq-pair-diagonalᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {a0ᵉ a1ᵉ : Aᵉ} (Cᵉ : Aᵉ ×ᵉ Aᵉ → UUᵉ l2ᵉ)
  (pᵉ : a0ᵉ ＝ᵉ a1ᵉ) (uᵉ : Cᵉ (a0ᵉ ,ᵉ a0ᵉ)) →
  trᵉ Cᵉ (eq-pairᵉ pᵉ pᵉ) uᵉ ＝ᵉ trᵉ (λ aᵉ → Cᵉ (aᵉ ,ᵉ aᵉ)) pᵉ uᵉ
tr-eq-pair-diagonalᵉ Cᵉ reflᵉ uᵉ = reflᵉ
```

## See also

-ᵉ Equalityᵉ proofsᵉ in dependentᵉ pairᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in dependentᵉ productᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in coproductᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-coproduct-types`](foundation.equality-coproduct-types.md).ᵉ