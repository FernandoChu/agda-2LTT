# Coproduct types

```agda
module foundation.coproduct-typesᵉ where

open import foundation-core.coproduct-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.noncontractible-typesᵉ
open import foundation.subuniversesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.negationᵉ
open import foundation-core.propositionsᵉ
```

</details>

### The predicates of being in the left and in the right summand

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  where

  is-left-Propᵉ : Xᵉ +ᵉ Yᵉ → Propᵉ lzero
  is-left-Propᵉ (inlᵉ xᵉ) = unit-Propᵉ
  is-left-Propᵉ (inrᵉ xᵉ) = empty-Propᵉ

  is-leftᵉ : Xᵉ +ᵉ Yᵉ → UUᵉ lzero
  is-leftᵉ xᵉ = type-Propᵉ (is-left-Propᵉ xᵉ)

  is-prop-is-leftᵉ : (xᵉ : Xᵉ +ᵉ Yᵉ) → is-propᵉ (is-leftᵉ xᵉ)
  is-prop-is-leftᵉ xᵉ = is-prop-type-Propᵉ (is-left-Propᵉ xᵉ)

  is-right-Propᵉ : Xᵉ +ᵉ Yᵉ → Propᵉ lzero
  is-right-Propᵉ (inlᵉ xᵉ) = empty-Propᵉ
  is-right-Propᵉ (inrᵉ xᵉ) = unit-Propᵉ

  is-rightᵉ : Xᵉ +ᵉ Yᵉ → UUᵉ lzero
  is-rightᵉ xᵉ = type-Propᵉ (is-right-Propᵉ xᵉ)

  is-prop-is-rightᵉ : (xᵉ : Xᵉ +ᵉ Yᵉ) → is-propᵉ (is-rightᵉ xᵉ)
  is-prop-is-rightᵉ xᵉ = is-prop-type-Propᵉ (is-right-Propᵉ xᵉ)

  is-left-or-is-rightᵉ : (xᵉ : Xᵉ +ᵉ Yᵉ) → is-leftᵉ xᵉ +ᵉ is-rightᵉ xᵉ
  is-left-or-is-rightᵉ (inlᵉ xᵉ) = inlᵉ starᵉ
  is-left-or-is-rightᵉ (inrᵉ xᵉ) = inrᵉ starᵉ
```

### The predicate that a subuniverse is closed under coproducts

Weᵉ formulateᵉ aᵉ variantᵉ with threeᵉ subuniversesᵉ andᵉ theᵉ moreᵉ traditionalᵉ variantᵉ
using aᵉ singleᵉ subuniverseᵉ

```agda
is-closed-under-coproducts-subuniversesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : subuniverseᵉ l3ᵉ l4ᵉ) →
  subuniverseᵉ (l1ᵉ ⊔ l3ᵉ) l5ᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
is-closed-under-coproducts-subuniversesᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} Pᵉ Qᵉ Rᵉ =
  {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l3ᵉ} →
  is-in-subuniverseᵉ Pᵉ Xᵉ → is-in-subuniverseᵉ Qᵉ Yᵉ → is-in-subuniverseᵉ Rᵉ (Xᵉ +ᵉ Yᵉ)

is-closed-under-coproducts-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
is-closed-under-coproducts-subuniverseᵉ Pᵉ =
  is-closed-under-coproducts-subuniversesᵉ Pᵉ Pᵉ Pᵉ
```

## Properties

### The left and right inclusions are injective

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-injective-inlᵉ : is-injectiveᵉ {Bᵉ = Aᵉ +ᵉ Bᵉ} inlᵉ
  is-injective-inlᵉ reflᵉ = reflᵉ

  is-injective-inrᵉ : is-injectiveᵉ {Bᵉ = Aᵉ +ᵉ Bᵉ} inrᵉ
  is-injective-inrᵉ reflᵉ = reflᵉ

  neq-inl-inrᵉ : {xᵉ : Aᵉ} {yᵉ : Bᵉ} → inlᵉ xᵉ ≠ᵉ inrᵉ yᵉ
  neq-inl-inrᵉ ()

  neq-inr-inlᵉ : {xᵉ : Bᵉ} {yᵉ : Aᵉ} → inrᵉ xᵉ ≠ᵉ inlᵉ yᵉ
  neq-inr-inlᵉ ()
```

### The type of left elements is equivalent to the left summand

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  where

  map-equiv-left-summandᵉ : Σᵉ (Xᵉ +ᵉ Yᵉ) is-leftᵉ → Xᵉ
  map-equiv-left-summandᵉ (inlᵉ xᵉ ,ᵉ starᵉ) = xᵉ
  map-equiv-left-summandᵉ (inrᵉ xᵉ ,ᵉ ())

  map-inv-equiv-left-summandᵉ : Xᵉ → Σᵉ (Xᵉ +ᵉ Yᵉ) is-leftᵉ
  pr1ᵉ (map-inv-equiv-left-summandᵉ xᵉ) = inlᵉ xᵉ
  pr2ᵉ (map-inv-equiv-left-summandᵉ xᵉ) = starᵉ

  is-section-map-inv-equiv-left-summandᵉ :
    (map-equiv-left-summandᵉ ∘ᵉ map-inv-equiv-left-summandᵉ) ~ᵉ idᵉ
  is-section-map-inv-equiv-left-summandᵉ xᵉ = reflᵉ

  is-retraction-map-inv-equiv-left-summandᵉ :
    (map-inv-equiv-left-summandᵉ ∘ᵉ map-equiv-left-summandᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-equiv-left-summandᵉ (inlᵉ xᵉ ,ᵉ starᵉ) = reflᵉ
  is-retraction-map-inv-equiv-left-summandᵉ (inrᵉ xᵉ ,ᵉ ())

  equiv-left-summandᵉ : (Σᵉ (Xᵉ +ᵉ Yᵉ) is-leftᵉ) ≃ᵉ Xᵉ
  pr1ᵉ equiv-left-summandᵉ = map-equiv-left-summandᵉ
  pr2ᵉ equiv-left-summandᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-equiv-left-summandᵉ
      is-section-map-inv-equiv-left-summandᵉ
      is-retraction-map-inv-equiv-left-summandᵉ
```

### The type of right elements is equivalent to the right summand

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  where

  map-equiv-right-summandᵉ : Σᵉ (Xᵉ +ᵉ Yᵉ) is-rightᵉ → Yᵉ
  map-equiv-right-summandᵉ (inlᵉ xᵉ ,ᵉ ())
  map-equiv-right-summandᵉ (inrᵉ xᵉ ,ᵉ starᵉ) = xᵉ

  map-inv-equiv-right-summandᵉ : Yᵉ → Σᵉ (Xᵉ +ᵉ Yᵉ) is-rightᵉ
  pr1ᵉ (map-inv-equiv-right-summandᵉ yᵉ) = inrᵉ yᵉ
  pr2ᵉ (map-inv-equiv-right-summandᵉ yᵉ) = starᵉ

  is-section-map-inv-equiv-right-summandᵉ :
    map-equiv-right-summandᵉ ∘ᵉ map-inv-equiv-right-summandᵉ ~ᵉ idᵉ
  is-section-map-inv-equiv-right-summandᵉ yᵉ = reflᵉ

  is-retraction-map-inv-equiv-right-summandᵉ :
    map-inv-equiv-right-summandᵉ ∘ᵉ map-equiv-right-summandᵉ ~ᵉ idᵉ
  is-retraction-map-inv-equiv-right-summandᵉ (inlᵉ xᵉ ,ᵉ ())
  is-retraction-map-inv-equiv-right-summandᵉ (inrᵉ xᵉ ,ᵉ starᵉ) = reflᵉ

  equiv-right-summandᵉ : Σᵉ (Xᵉ +ᵉ Yᵉ) is-rightᵉ ≃ᵉ Yᵉ
  pr1ᵉ equiv-right-summandᵉ = map-equiv-right-summandᵉ
  pr2ᵉ equiv-right-summandᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-equiv-right-summandᵉ
      is-section-map-inv-equiv-right-summandᵉ
      is-retraction-map-inv-equiv-right-summandᵉ
```

### Coproducts of contractible types are not contractible

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-not-contractible-coproduct-is-contrᵉ :
      is-contrᵉ Aᵉ → is-contrᵉ Bᵉ → is-not-contractibleᵉ (Aᵉ +ᵉ Bᵉ)
    is-not-contractible-coproduct-is-contrᵉ HAᵉ HBᵉ HABᵉ =
      neq-inl-inrᵉ {xᵉ = centerᵉ HAᵉ} {yᵉ = centerᵉ HBᵉ} (eq-is-contrᵉ HABᵉ)
```

### Coproducts of mutually exclusive propositions are propositions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Pᵉ : UUᵉ l1ᵉ} {Qᵉ : UUᵉ l2ᵉ}
  where

  abstract
    all-elements-equal-coproductᵉ :
      (Pᵉ → ¬ᵉ Qᵉ) → all-elements-equalᵉ Pᵉ → all-elements-equalᵉ Qᵉ →
      all-elements-equalᵉ (Pᵉ +ᵉ Qᵉ)
    all-elements-equal-coproductᵉ fᵉ is-prop-Pᵉ is-prop-Qᵉ (inlᵉ pᵉ) (inlᵉ p'ᵉ) =
      apᵉ inlᵉ (is-prop-Pᵉ pᵉ p'ᵉ)
    all-elements-equal-coproductᵉ fᵉ is-prop-Pᵉ is-prop-Qᵉ (inlᵉ pᵉ) (inrᵉ q'ᵉ) =
      ex-falsoᵉ (fᵉ pᵉ q'ᵉ)
    all-elements-equal-coproductᵉ fᵉ is-prop-Pᵉ is-prop-Qᵉ (inrᵉ qᵉ) (inlᵉ p'ᵉ) =
      ex-falsoᵉ (fᵉ p'ᵉ qᵉ)
    all-elements-equal-coproductᵉ fᵉ is-prop-Pᵉ is-prop-Qᵉ (inrᵉ qᵉ) (inrᵉ q'ᵉ) =
      apᵉ inrᵉ (is-prop-Qᵉ qᵉ q'ᵉ)

  abstract
    is-prop-coproductᵉ : (Pᵉ → ¬ᵉ Qᵉ) → is-propᵉ Pᵉ → is-propᵉ Qᵉ → is-propᵉ (Pᵉ +ᵉ Qᵉ)
    is-prop-coproductᵉ fᵉ is-prop-Pᵉ is-prop-Qᵉ =
      is-prop-all-elements-equalᵉ
        ( all-elements-equal-coproductᵉ fᵉ
          ( eq-is-prop'ᵉ is-prop-Pᵉ)
          ( eq-is-prop'ᵉ is-prop-Qᵉ))

coproduct-Propᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ) →
  (type-Propᵉ Pᵉ → ¬ᵉ (type-Propᵉ Qᵉ)) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (coproduct-Propᵉ Pᵉ Qᵉ Hᵉ) =
  type-Propᵉ Pᵉ +ᵉ type-Propᵉ Qᵉ
pr2ᵉ (coproduct-Propᵉ Pᵉ Qᵉ Hᵉ) =
  is-prop-coproductᵉ Hᵉ (is-prop-type-Propᵉ Pᵉ) (is-prop-type-Propᵉ Qᵉ)
```