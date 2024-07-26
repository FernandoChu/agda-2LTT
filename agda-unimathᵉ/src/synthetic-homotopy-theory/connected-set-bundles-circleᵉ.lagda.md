# Connected set bundles over the circle

```agda
module synthetic-homotopy-theory.connected-set-bundles-circleᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.automorphismsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.transitive-higher-group-actionsᵉ

open import structured-types.sets-equipped-with-automorphismsᵉ

open import synthetic-homotopy-theory.circleᵉ
```

</details>

## Idea

Aᵉ **connectedᵉ setᵉ bundle**ᵉ overᵉ theᵉ
[circle](synthetic-homotopy-theory.circle.mdᵉ) isᵉ aᵉ familyᵉ ofᵉ setsᵉ `Xᵉ : 𝕊¹ᵉ → Set`ᵉ
suchᵉ thatᵉ theᵉ totalᵉ spaceᵉ `Σᵉ 𝕊¹ᵉ (type-Setᵉ ∘ᵉ X)`ᵉ isᵉ
[connected](foundation.connected-types.md).ᵉ Theᵉ connectedᵉ setᵉ bundlesᵉ overᵉ theᵉ
circleᵉ formᵉ aᵉ [largeᵉ category](category-theory.large-categories.md),ᵉ whichᵉ canᵉ
beᵉ thoughtᵉ ofᵉ asᵉ theᵉ categorificationᵉ ofᵉ theᵉ [poset](order-theory.posets.mdᵉ) ofᵉ
[naturalᵉ numbersᵉ orderedᵉ byᵉ divisibility](elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility.md).ᵉ

## Definitions

### The predicate of being a connected set bundle over the circle

```agda
is-connected-prop-set-bundle-𝕊¹ᵉ :
  {lᵉ : Level} → (𝕊¹ᵉ → Setᵉ lᵉ) → Propᵉ lᵉ
is-connected-prop-set-bundle-𝕊¹ᵉ Xᵉ =
  is-0-connected-Propᵉ (Σᵉ 𝕊¹ᵉ (type-Setᵉ ∘ᵉ Xᵉ))

is-connected-set-bundle-𝕊¹ᵉ : {lᵉ : Level} (Xᵉ : 𝕊¹ᵉ → Setᵉ lᵉ) → UUᵉ lᵉ
is-connected-set-bundle-𝕊¹ᵉ Xᵉ =
  type-Propᵉ (is-connected-prop-set-bundle-𝕊¹ᵉ Xᵉ)

is-prop-is-connected-set-bundle-𝕊¹ᵉ :
  {lᵉ : Level} (Xᵉ : 𝕊¹ᵉ → Setᵉ lᵉ) → is-propᵉ (is-connected-set-bundle-𝕊¹ᵉ Xᵉ)
is-prop-is-connected-set-bundle-𝕊¹ᵉ Xᵉ =
  is-prop-type-Propᵉ (is-connected-prop-set-bundle-𝕊¹ᵉ Xᵉ)
```

### Connected set bundles over the circle

```agda
connected-set-bundle-𝕊¹ᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
connected-set-bundle-𝕊¹ᵉ lᵉ = type-subtypeᵉ is-connected-prop-set-bundle-𝕊¹ᵉ

module _
  {lᵉ : Level} (Xᵉ : connected-set-bundle-𝕊¹ᵉ lᵉ)
  where

  set-bundle-connected-set-bundle-𝕊¹ᵉ : 𝕊¹ᵉ → Setᵉ lᵉ
  set-bundle-connected-set-bundle-𝕊¹ᵉ = pr1ᵉ Xᵉ

  bundle-connected-set-bundle-𝕊¹ᵉ : 𝕊¹ᵉ → UUᵉ lᵉ
  bundle-connected-set-bundle-𝕊¹ᵉ =
    type-Setᵉ ∘ᵉ set-bundle-connected-set-bundle-𝕊¹ᵉ

  set-connected-set-bundle-𝕊¹ᵉ : Setᵉ lᵉ
  set-connected-set-bundle-𝕊¹ᵉ =
    set-bundle-connected-set-bundle-𝕊¹ᵉ base-𝕊¹ᵉ

  type-connected-set-bundle-𝕊¹ᵉ : UUᵉ lᵉ
  type-connected-set-bundle-𝕊¹ᵉ = type-Setᵉ set-connected-set-bundle-𝕊¹ᵉ

  total-space-connected-set-bundle-𝕊¹ᵉ : UUᵉ lᵉ
  total-space-connected-set-bundle-𝕊¹ᵉ = Σᵉ 𝕊¹ᵉ bundle-connected-set-bundle-𝕊¹ᵉ

  is-connected-connected-set-bundle-𝕊¹ᵉ :
    is-connected-set-bundle-𝕊¹ᵉ set-bundle-connected-set-bundle-𝕊¹ᵉ
  is-connected-connected-set-bundle-𝕊¹ᵉ = pr2ᵉ Xᵉ

  mere-eq-total-space-connected-set-bundle-𝕊¹ᵉ :
    (xᵉ yᵉ : total-space-connected-set-bundle-𝕊¹ᵉ) →
    mere-eqᵉ xᵉ yᵉ
  mere-eq-total-space-connected-set-bundle-𝕊¹ᵉ =
    mere-eq-is-0-connectedᵉ is-connected-connected-set-bundle-𝕊¹ᵉ

  transitive-action-connected-set-bundle-𝕊¹ᵉ :
    transitive-action-∞-Groupᵉ lᵉ 𝕊¹-∞-Groupᵉ
  pr1ᵉ transitive-action-connected-set-bundle-𝕊¹ᵉ =
    bundle-connected-set-bundle-𝕊¹ᵉ
  pr2ᵉ transitive-action-connected-set-bundle-𝕊¹ᵉ =
    is-connected-connected-set-bundle-𝕊¹ᵉ

  is-abstractly-transitive-action-connected-set-bundle-𝕊¹ᵉ :
    is-abstractly-transitive-action-∞-Groupᵉ
      ( 𝕊¹-∞-Groupᵉ)
      ( bundle-connected-set-bundle-𝕊¹ᵉ)
  is-abstractly-transitive-action-connected-set-bundle-𝕊¹ᵉ =
    is-abstractly-transitive-transitive-action-∞-Groupᵉ
      ( 𝕊¹-∞-Groupᵉ)
      ( transitive-action-connected-set-bundle-𝕊¹ᵉ)

  is-inhabited-connected-set-bundle-𝕊¹ᵉ :
    is-inhabitedᵉ type-connected-set-bundle-𝕊¹ᵉ
  is-inhabited-connected-set-bundle-𝕊¹ᵉ =
    is-inhabited-transitive-action-∞-Groupᵉ
      ( 𝕊¹-∞-Groupᵉ)
      ( transitive-action-connected-set-bundle-𝕊¹ᵉ)

  is-surjective-tr-connected-set-bundle-𝕊¹ᵉ :
    (tᵉ : 𝕊¹ᵉ) (xᵉ : type-connected-set-bundle-𝕊¹ᵉ) →
    is-surjectiveᵉ (λ (pᵉ : base-𝕊¹ᵉ ＝ᵉ tᵉ) → trᵉ bundle-connected-set-bundle-𝕊¹ᵉ pᵉ xᵉ)
  is-surjective-tr-connected-set-bundle-𝕊¹ᵉ =
    is-surjective-tr-is-abstractly-transitive-action-∞-Groupᵉ
      ( 𝕊¹-∞-Groupᵉ)
      ( bundle-connected-set-bundle-𝕊¹ᵉ)
      ( is-abstractly-transitive-action-connected-set-bundle-𝕊¹ᵉ)

  inhabited-type-connected-set-bundle-𝕊¹ᵉ : Inhabited-Typeᵉ lᵉ
  inhabited-type-connected-set-bundle-𝕊¹ᵉ =
    inhabited-type-transitive-action-∞-Groupᵉ
      ( 𝕊¹-∞-Groupᵉ)
      ( transitive-action-connected-set-bundle-𝕊¹ᵉ)

  aut-connected-set-bundle-𝕊¹ᵉ : Autᵉ type-connected-set-bundle-𝕊¹ᵉ
  aut-connected-set-bundle-𝕊¹ᵉ =
    equiv-trᵉ bundle-connected-set-bundle-𝕊¹ᵉ loop-𝕊¹ᵉ

  map-aut-connected-set-bundle-𝕊¹ᵉ :
    type-connected-set-bundle-𝕊¹ᵉ → type-connected-set-bundle-𝕊¹ᵉ
  map-aut-connected-set-bundle-𝕊¹ᵉ =
    map-equivᵉ aut-connected-set-bundle-𝕊¹ᵉ

  set-with-automorphism-connected-set-bundle-𝕊¹ᵉ : Set-With-Automorphismᵉ lᵉ
  pr1ᵉ set-with-automorphism-connected-set-bundle-𝕊¹ᵉ =
    set-connected-set-bundle-𝕊¹ᵉ
  pr2ᵉ set-with-automorphism-connected-set-bundle-𝕊¹ᵉ =
    aut-connected-set-bundle-𝕊¹ᵉ
```

## Properties

### Connected set bundles over the circle are cyclic sets

#### The set equipped with an automorphism obtained from a connected set bundle over the circle is a cyclic set

Thisᵉ remainsᵉ to beᵉ shown.ᵉ

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}