# Free higher group actions

```agda
module higher-group-theory.free-higher-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.embeddingsᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-mapsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.regensburg-extension-fundamental-theorem-of-identity-typesᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-group-actionsᵉ
open import higher-group-theory.higher-groupsᵉ
open import higher-group-theory.orbits-higher-group-actionsᵉ
```

</details>

## Idea

Considerᵉ anᵉ [∞-group](higher-group-theory.higher-groups.mdᵉ) `G`ᵉ andᵉ anᵉ
[∞-groupᵉ action](higher-group-theory.higher-group-actions.mdᵉ) ofᵉ `G`ᵉ onᵉ `X`.ᵉ Weᵉ
sayᵉ thatᵉ `X`ᵉ isᵉ **free**ᵉ ifᵉ itsᵉ typeᵉ ofᵉ
[orbits](higher-group-theory.orbits-higher-group-actions.mdᵉ) isᵉ aᵉ
[set](foundation.sets.md).ᵉ

[Equivalently](foundation.logical-equivalences.md),ᵉ weᵉ sayᵉ thatᵉ `X`ᵉ isᵉ
**abstractlyᵉ free**ᵉ ifᵉ forᵉ anyᵉ elementᵉ `xᵉ : Xᵉ (shᵉ G)`ᵉ ofᵉ theᵉ underlyingᵉ typeᵉ ofᵉ
`X`ᵉ theᵉ actionᵉ mapᵉ

```text
  gᵉ ↦ᵉ mul-action-∞-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ
```

isᵉ anᵉ [embedding](foundation.embeddings.md).ᵉ Theᵉ equivalenceᵉ ofᵉ theseᵉ twoᵉ
conditionsᵉ isᵉ establishedᵉ viaᵉ theᵉ
[Regensburgᵉ extensionᵉ ofᵉ theᵉ fundamentalᵉ theoremᵉ ofᵉ identityᵉ types](foundation.regensburg-extension-fundamental-theorem-of-identity-types.md).ᵉ

## Definition

### The predicate of being a free group action

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Xᵉ : action-∞-Groupᵉ l2ᵉ Gᵉ)
  where

  is-free-prop-action-∞-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-free-prop-action-∞-Groupᵉ = is-set-Propᵉ (orbit-action-∞-Groupᵉ Gᵉ Xᵉ)

  is-free-action-∞-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-free-action-∞-Groupᵉ = type-Propᵉ is-free-prop-action-∞-Groupᵉ

  is-prop-is-free-action-∞-Groupᵉ : is-propᵉ is-free-action-∞-Groupᵉ
  is-prop-is-free-action-∞-Groupᵉ = is-prop-type-Propᵉ is-free-prop-action-∞-Groupᵉ
```

### The predicate of being an abstractly free ∞-group action

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Xᵉ : action-∞-Groupᵉ l2ᵉ Gᵉ)
  where

  is-abstractly-free-prop-action-∞-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-abstractly-free-prop-action-∞-Groupᵉ =
    Π-Propᵉ
      ( type-action-∞-Groupᵉ Gᵉ Xᵉ)
      ( λ xᵉ → is-emb-Propᵉ (λ gᵉ → mul-action-∞-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ))

  is-abstractly-free-action-∞-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-abstractly-free-action-∞-Groupᵉ =
    type-Propᵉ is-abstractly-free-prop-action-∞-Groupᵉ

  is-prop-is-abstractly-free-action-∞-Groupᵉ :
    is-propᵉ is-abstractly-free-action-∞-Groupᵉ
  is-prop-is-abstractly-free-action-∞-Groupᵉ =
    is-prop-type-Propᵉ is-abstractly-free-prop-action-∞-Groupᵉ
```

### Free group actions

```agda
free-action-∞-Groupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → ∞-Groupᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
free-action-∞-Groupᵉ l2ᵉ Gᵉ =
  type-subtypeᵉ (is-free-prop-action-∞-Groupᵉ {l2ᵉ = l2ᵉ} Gᵉ)
```

## Property

### Any transport function of an abstractly free higher group action is an embedding

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Xᵉ : action-∞-Groupᵉ l2ᵉ Gᵉ)
  where

  abstract
    is-emb-tr-is-abstractly-free-action-∞-Groupᵉ :
      is-abstractly-free-action-∞-Groupᵉ Gᵉ Xᵉ →
      (uᵉ : classifying-type-∞-Groupᵉ Gᵉ)
      (xᵉ : type-action-∞-Groupᵉ Gᵉ Xᵉ) →
      is-embᵉ (λ (pᵉ : shape-∞-Groupᵉ Gᵉ ＝ᵉ uᵉ) → trᵉ Xᵉ pᵉ xᵉ)
    is-emb-tr-is-abstractly-free-action-∞-Groupᵉ Hᵉ uᵉ xᵉ =
      apply-universal-property-trunc-Propᵉ
        ( mere-eq-classifying-type-∞-Groupᵉ Gᵉ (shape-∞-Groupᵉ Gᵉ) uᵉ)
        ( is-emb-Propᵉ _)
        ( λ where reflᵉ → Hᵉ xᵉ)
```

### A higher group action `X` is free if and only if it is abstractly free

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Xᵉ : action-∞-Groupᵉ l2ᵉ Gᵉ)
  where

  abstract
    is-free-is-abstractly-free-action-∞-Groupᵉ :
      is-abstractly-free-action-∞-Groupᵉ Gᵉ Xᵉ →
      is-free-action-∞-Groupᵉ Gᵉ Xᵉ
    is-free-is-abstractly-free-action-∞-Groupᵉ Hᵉ =
      forward-implication-extended-fundamental-theorem-id-truncatedᵉ
        ( neg-one-𝕋ᵉ)
        ( shape-∞-Groupᵉ Gᵉ)
        ( is-0-connected-classifying-type-∞-Groupᵉ Gᵉ)
        ( λ fᵉ uᵉ →
          is-prop-map-is-embᵉ
            ( is-emb-htpyᵉ
              ( compute-map-out-of-identity-typeᵉ fᵉ uᵉ)
              ( is-emb-tr-is-abstractly-free-action-∞-Groupᵉ Gᵉ Xᵉ Hᵉ uᵉ
                ( fᵉ (shape-∞-Groupᵉ Gᵉ) (unit-∞-Groupᵉ Gᵉ)))))

  abstract
    is-abstractly-free-is-free-action-∞-Groupᵉ :
      is-free-action-∞-Groupᵉ Gᵉ Xᵉ →
      is-abstractly-free-action-∞-Groupᵉ Gᵉ Xᵉ
    is-abstractly-free-is-free-action-∞-Groupᵉ Hᵉ xᵉ =
      is-emb-is-prop-mapᵉ
        ( backward-implication-extended-fundamental-theorem-id-truncatedᵉ
          ( neg-one-𝕋ᵉ)
          ( shape-∞-Groupᵉ Gᵉ)
          ( Hᵉ)
          ( λ uᵉ pᵉ → trᵉ Xᵉ pᵉ xᵉ)
          ( shape-∞-Groupᵉ Gᵉ))
```