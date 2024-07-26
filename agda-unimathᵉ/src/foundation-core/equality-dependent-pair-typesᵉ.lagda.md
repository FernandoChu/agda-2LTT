# Equality of dependent pair types

```agda
module foundation-core.equality-dependent-pair-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.dependent-identificationsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Anᵉ identificationᵉ `(pairᵉ xᵉ yᵉ) ＝ᵉ (pairᵉ x'ᵉ y')`ᵉ in aᵉ dependentᵉ pairᵉ typeᵉ `Σᵉ Aᵉ B`ᵉ
isᵉ equivalentlyᵉ describedᵉ asᵉ aᵉ pairᵉ `pairᵉ αᵉ β`ᵉ consistingᵉ ofᵉ anᵉ identificationᵉ
`αᵉ : xᵉ ＝ᵉ x'`ᵉ andᵉ anᵉ identificationᵉ `βᵉ : (trᵉ Bᵉ αᵉ yᵉ) ＝ᵉ y'`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  Eq-Σᵉ : (sᵉ tᵉ : Σᵉ Aᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  Eq-Σᵉ sᵉ tᵉ =
    Σᵉ (pr1ᵉ sᵉ ＝ᵉ pr1ᵉ tᵉ) (λ αᵉ → dependent-identificationᵉ Bᵉ αᵉ (pr2ᵉ sᵉ) (pr2ᵉ tᵉ))
```

## Properties

### The type `Id s t` is equivalent to `Eq-Σ s t` for any `s t : Σ A B`

```agda
  refl-Eq-Σᵉ : (sᵉ : Σᵉ Aᵉ Bᵉ) → Eq-Σᵉ sᵉ sᵉ
  pr1ᵉ (refl-Eq-Σᵉ (pairᵉ aᵉ bᵉ)) = reflᵉ
  pr2ᵉ (refl-Eq-Σᵉ (pairᵉ aᵉ bᵉ)) = reflᵉ

  pair-eq-Σᵉ : {sᵉ tᵉ : Σᵉ Aᵉ Bᵉ} → sᵉ ＝ᵉ tᵉ → Eq-Σᵉ sᵉ tᵉ
  pair-eq-Σᵉ {sᵉ} reflᵉ = refl-Eq-Σᵉ sᵉ

  eq-pair-eq-baseᵉ :
    {xᵉ yᵉ : Aᵉ} {sᵉ : Bᵉ xᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → (xᵉ ,ᵉ sᵉ) ＝ᵉ (yᵉ ,ᵉ trᵉ Bᵉ pᵉ sᵉ)
  eq-pair-eq-baseᵉ reflᵉ = reflᵉ

  eq-pair-eq-base'ᵉ :
    {xᵉ yᵉ : Aᵉ} {tᵉ : Bᵉ yᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → (xᵉ ,ᵉ trᵉ Bᵉ (invᵉ pᵉ) tᵉ) ＝ᵉ (yᵉ ,ᵉ tᵉ)
  eq-pair-eq-base'ᵉ reflᵉ = reflᵉ

  eq-pair-eq-fiberᵉ :
    {xᵉ : Aᵉ} {sᵉ tᵉ : Bᵉ xᵉ} → sᵉ ＝ᵉ tᵉ → (xᵉ ,ᵉ sᵉ) ＝ᵉ (xᵉ ,ᵉ tᵉ)
  eq-pair-eq-fiberᵉ {xᵉ} = apᵉ {Bᵉ = Σᵉ Aᵉ Bᵉ} (pairᵉ xᵉ)

  eq-pair-Σᵉ :
    {sᵉ tᵉ : Σᵉ Aᵉ Bᵉ}
    (αᵉ : pr1ᵉ sᵉ ＝ᵉ pr1ᵉ tᵉ) →
    dependent-identificationᵉ Bᵉ αᵉ (pr2ᵉ sᵉ) (pr2ᵉ tᵉ) → sᵉ ＝ᵉ tᵉ
  eq-pair-Σᵉ reflᵉ = eq-pair-eq-fiberᵉ

  eq-pair-Σ'ᵉ : {sᵉ tᵉ : Σᵉ Aᵉ Bᵉ} → Eq-Σᵉ sᵉ tᵉ → sᵉ ＝ᵉ tᵉ
  eq-pair-Σ'ᵉ pᵉ = eq-pair-Σᵉ (pr1ᵉ pᵉ) (pr2ᵉ pᵉ)

  ap-pr1-eq-pair-eq-fiberᵉ :
    {xᵉ : Aᵉ} {sᵉ tᵉ : Bᵉ xᵉ} (pᵉ : sᵉ ＝ᵉ tᵉ) → apᵉ pr1ᵉ (eq-pair-eq-fiberᵉ pᵉ) ＝ᵉ reflᵉ
  ap-pr1-eq-pair-eq-fiberᵉ reflᵉ = reflᵉ

  is-retraction-pair-eq-Σᵉ :
    (sᵉ tᵉ : Σᵉ Aᵉ Bᵉ) → pair-eq-Σᵉ {sᵉ} {tᵉ} ∘ᵉ eq-pair-Σ'ᵉ {sᵉ} {tᵉ} ~ᵉ idᵉ {Aᵉ = Eq-Σᵉ sᵉ tᵉ}
  is-retraction-pair-eq-Σᵉ (pairᵉ xᵉ yᵉ) (pairᵉ .xᵉ .yᵉ) (pairᵉ reflᵉ reflᵉ) = reflᵉ

  is-section-pair-eq-Σᵉ :
    (sᵉ tᵉ : Σᵉ Aᵉ Bᵉ) → ((eq-pair-Σ'ᵉ {sᵉ} {tᵉ}) ∘ᵉ (pair-eq-Σᵉ {sᵉ} {tᵉ})) ~ᵉ idᵉ
  is-section-pair-eq-Σᵉ (pairᵉ xᵉ yᵉ) .(pairᵉ xᵉ yᵉ) reflᵉ = reflᵉ

  abstract
    is-equiv-eq-pair-Σᵉ : (sᵉ tᵉ : Σᵉ Aᵉ Bᵉ) → is-equivᵉ (eq-pair-Σ'ᵉ {sᵉ} {tᵉ})
    is-equiv-eq-pair-Σᵉ sᵉ tᵉ =
      is-equiv-is-invertibleᵉ
        ( pair-eq-Σᵉ)
        ( is-section-pair-eq-Σᵉ sᵉ tᵉ)
        ( is-retraction-pair-eq-Σᵉ sᵉ tᵉ)

  equiv-eq-pair-Σᵉ : (sᵉ tᵉ : Σᵉ Aᵉ Bᵉ) → Eq-Σᵉ sᵉ tᵉ ≃ᵉ (sᵉ ＝ᵉ tᵉ)
  pr1ᵉ (equiv-eq-pair-Σᵉ sᵉ tᵉ) = eq-pair-Σ'ᵉ
  pr2ᵉ (equiv-eq-pair-Σᵉ sᵉ tᵉ) = is-equiv-eq-pair-Σᵉ sᵉ tᵉ

  abstract
    is-equiv-pair-eq-Σᵉ : (sᵉ tᵉ : Σᵉ Aᵉ Bᵉ) → is-equivᵉ (pair-eq-Σᵉ {sᵉ} {tᵉ})
    is-equiv-pair-eq-Σᵉ sᵉ tᵉ =
      is-equiv-is-invertibleᵉ
        ( eq-pair-Σ'ᵉ)
        ( is-retraction-pair-eq-Σᵉ sᵉ tᵉ)
        ( is-section-pair-eq-Σᵉ sᵉ tᵉ)

  equiv-pair-eq-Σᵉ : (sᵉ tᵉ : Σᵉ Aᵉ Bᵉ) → (sᵉ ＝ᵉ tᵉ) ≃ᵉ Eq-Σᵉ sᵉ tᵉ
  pr1ᵉ (equiv-pair-eq-Σᵉ sᵉ tᵉ) = pair-eq-Σᵉ
  pr2ᵉ (equiv-pair-eq-Σᵉ sᵉ tᵉ) = is-equiv-pair-eq-Σᵉ sᵉ tᵉ

  η-pairᵉ : (tᵉ : Σᵉ Aᵉ Bᵉ) → (pairᵉ (pr1ᵉ tᵉ) (pr2ᵉ tᵉ)) ＝ᵉ tᵉ
  η-pairᵉ tᵉ = reflᵉ

  eq-base-eq-pair-Σᵉ : {sᵉ tᵉ : Σᵉ Aᵉ Bᵉ} → (sᵉ ＝ᵉ tᵉ) → (pr1ᵉ sᵉ ＝ᵉ pr1ᵉ tᵉ)
  eq-base-eq-pair-Σᵉ pᵉ = pr1ᵉ (pair-eq-Σᵉ pᵉ)

  dependent-eq-family-eq-pair-Σᵉ :
    {sᵉ tᵉ : Σᵉ Aᵉ Bᵉ} → (pᵉ : sᵉ ＝ᵉ tᵉ) →
    dependent-identificationᵉ Bᵉ (eq-base-eq-pair-Σᵉ pᵉ) (pr2ᵉ sᵉ) (pr2ᵉ tᵉ)
  dependent-eq-family-eq-pair-Σᵉ pᵉ = pr2ᵉ (pair-eq-Σᵉ pᵉ)
```

### Lifting equality to the total space

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  lift-eq-Σᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (bᵉ : Bᵉ xᵉ) → (pairᵉ xᵉ bᵉ) ＝ᵉ (pairᵉ yᵉ (trᵉ Bᵉ pᵉ bᵉ))
  lift-eq-Σᵉ reflᵉ bᵉ = reflᵉ
```

### Transport in a family of dependent pair types

```agda
tr-Σᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {a0ᵉ a1ᵉ : Aᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ) (pᵉ : a0ᵉ ＝ᵉ a1ᵉ) (zᵉ : Σᵉ (Bᵉ a0ᵉ) (λ xᵉ → Cᵉ a0ᵉ xᵉ)) →
  trᵉ (λ aᵉ → (Σᵉ (Bᵉ aᵉ) (Cᵉ aᵉ))) pᵉ zᵉ ＝ᵉ
  pairᵉ (trᵉ Bᵉ pᵉ (pr1ᵉ zᵉ)) (trᵉ (ind-Σᵉ Cᵉ) (eq-pair-Σᵉ pᵉ reflᵉ) (pr2ᵉ zᵉ))
tr-Σᵉ Cᵉ reflᵉ zᵉ = reflᵉ
```

### Transport in a family over a dependent pair type

```agda
tr-eq-pair-Σᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {a0ᵉ a1ᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {b0ᵉ : Bᵉ a0ᵉ} {b1ᵉ : Bᵉ a1ᵉ} (Cᵉ : (Σᵉ Aᵉ Bᵉ) → UUᵉ l3ᵉ)
  (pᵉ : a0ᵉ ＝ᵉ a1ᵉ) (qᵉ : dependent-identificationᵉ Bᵉ pᵉ b0ᵉ b1ᵉ) (uᵉ : Cᵉ (a0ᵉ ,ᵉ b0ᵉ)) →
  trᵉ Cᵉ (eq-pair-Σᵉ pᵉ qᵉ) uᵉ ＝ᵉ
  trᵉ (λ xᵉ → Cᵉ (a1ᵉ ,ᵉ xᵉ)) qᵉ (trᵉ Cᵉ (eq-pair-Σᵉ pᵉ reflᵉ) uᵉ)
tr-eq-pair-Σᵉ Cᵉ reflᵉ reflᵉ uᵉ = reflᵉ
```

## See also

-ᵉ Equalityᵉ proofsᵉ in cartesianᵉ productᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in dependentᵉ functionᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in theᵉ fiberᵉ ofᵉ aᵉ mapᵉ areᵉ characterizedᵉ in
  [`foundation.equality-fibers-of-maps`](foundation.equality-fibers-of-maps.md).ᵉ