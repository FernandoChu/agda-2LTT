# Morphisms of concrete group actions

```agda
module group-theory.homomorphisms-concrete-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-group-actionsᵉ
open import group-theory.concrete-groupsᵉ
```

</details>

## Definition

### Morphisms of concrete group actions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  (Yᵉ : action-Concrete-Groupᵉ l3ᵉ Gᵉ)
  where

  hom-action-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  hom-action-Concrete-Groupᵉ =
    (xᵉ : classifying-type-Concrete-Groupᵉ Gᵉ) → type-Setᵉ (Xᵉ xᵉ) → type-Setᵉ (Yᵉ xᵉ)

  map-hom-action-Concrete-Groupᵉ :
    hom-action-Concrete-Groupᵉ →
    type-action-Concrete-Groupᵉ Gᵉ Xᵉ → type-action-Concrete-Groupᵉ Gᵉ Yᵉ
  map-hom-action-Concrete-Groupᵉ fᵉ =
    fᵉ (shape-Concrete-Groupᵉ Gᵉ)

  preserves-tr-hom-action-Concrete-Groupᵉ :
    (fᵉ : hom-action-Concrete-Groupᵉ) {uᵉ vᵉ : classifying-type-Concrete-Groupᵉ Gᵉ}
    (pᵉ : uᵉ ＝ᵉ vᵉ) (xᵉ : type-Setᵉ (Xᵉ uᵉ)) →
    fᵉ vᵉ (trᵉ (type-Setᵉ ∘ᵉ Xᵉ) pᵉ xᵉ) ＝ᵉ trᵉ (type-Setᵉ ∘ᵉ Yᵉ) pᵉ (fᵉ uᵉ xᵉ)
  preserves-tr-hom-action-Concrete-Groupᵉ fᵉ reflᵉ xᵉ = reflᵉ

  preserves-mul-hom-action-Concrete-Groupᵉ :
    (fᵉ : hom-action-Concrete-Groupᵉ) (gᵉ : type-Concrete-Groupᵉ Gᵉ)
    (xᵉ : type-action-Concrete-Groupᵉ Gᵉ Xᵉ) →
    map-hom-action-Concrete-Groupᵉ fᵉ (mul-action-Concrete-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ) ＝ᵉ
    mul-action-Concrete-Groupᵉ Gᵉ Yᵉ gᵉ (map-hom-action-Concrete-Groupᵉ fᵉ xᵉ)
  preserves-mul-hom-action-Concrete-Groupᵉ fᵉ =
    preserves-tr-hom-action-Concrete-Groupᵉ fᵉ
```

### Homotopies of morphisms of concrete group actions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  (Yᵉ : action-Concrete-Groupᵉ l3ᵉ Gᵉ) (fᵉ : hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)
  where

  htpy-hom-action-Concrete-Groupᵉ :
    (gᵉ : hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  htpy-hom-action-Concrete-Groupᵉ gᵉ =
    map-hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ ~ᵉ
    map-hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ gᵉ

  refl-htpy-hom-action-Concrete-Groupᵉ : htpy-hom-action-Concrete-Groupᵉ fᵉ
  refl-htpy-hom-action-Concrete-Groupᵉ = refl-htpyᵉ

  extensionality-hom-action-Concrete-Groupᵉ :
    (gᵉ : hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-action-Concrete-Groupᵉ gᵉ
  extensionality-hom-action-Concrete-Groupᵉ gᵉ =
    ( equiv-dependent-universal-property-is-0-connectedᵉ
      ( shape-Concrete-Groupᵉ Gᵉ)
      ( is-0-connected-classifying-type-Concrete-Groupᵉ Gᵉ)
      ( λ uᵉ →
        Π-Propᵉ
          ( type-Setᵉ (Xᵉ uᵉ))
          ( λ xᵉ → Id-Propᵉ (Yᵉ uᵉ) (fᵉ uᵉ xᵉ) (gᵉ uᵉ xᵉ)))) ∘eᵉ
    ( extensionality-Πᵉ fᵉ (λ uᵉ gᵉ → (fᵉ uᵉ) ~ᵉ gᵉ) (λ uᵉ gᵉ → equiv-funextᵉ) gᵉ)

  htpy-eq-hom-action-Concrete-Groupᵉ :
    (gᵉ : hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    (fᵉ ＝ᵉ gᵉ) → htpy-hom-action-Concrete-Groupᵉ gᵉ
  htpy-eq-hom-action-Concrete-Groupᵉ gᵉ =
    map-equivᵉ (extensionality-hom-action-Concrete-Groupᵉ gᵉ)

  eq-htpy-hom-action-Concrete-Groupᵉ :
    (gᵉ : hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    htpy-hom-action-Concrete-Groupᵉ gᵉ → (fᵉ ＝ᵉ gᵉ)
  eq-htpy-hom-action-Concrete-Groupᵉ gᵉ =
    map-inv-equivᵉ (extensionality-hom-action-Concrete-Groupᵉ gᵉ)
```

## Properties

### The type of homotopies between morphisms of concrete group actions is a set

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  (Yᵉ : action-Concrete-Groupᵉ l3ᵉ Gᵉ) (fᵉ gᵉ : hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)
  where

  is-prop-htpy-hom-action-Concrete-Groupᵉ :
    is-propᵉ (htpy-hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ gᵉ)
  is-prop-htpy-hom-action-Concrete-Groupᵉ =
    is-prop-Πᵉ
      ( λ xᵉ →
        is-set-type-action-Concrete-Groupᵉ Gᵉ Yᵉ
          ( map-hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ xᵉ)
          ( map-hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ gᵉ xᵉ))
```