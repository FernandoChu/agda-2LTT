# Equivalences of concrete group actions

```agda
module group-theory.equivalences-concrete-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-group-actionsᵉ
open import group-theory.concrete-groupsᵉ
open import group-theory.homomorphisms-concrete-group-actionsᵉ
```

</details>

## Idea

Anᵉ equivalenceᵉ ofᵉ concreteᵉ groupᵉ actionsᵉ fromᵉ `X`ᵉ to `Y`ᵉ isᵉ aᵉ familyᵉ ofᵉ
equivalencesᵉ fromᵉ `Xᵉ u`ᵉ to `Yᵉ u`ᵉ indexedᵉ byᵉ `uᵉ : BG`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  where

  equiv-action-Concrete-Groupᵉ :
    {l3ᵉ : Level} (Yᵉ : action-Concrete-Groupᵉ l3ᵉ Gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  equiv-action-Concrete-Groupᵉ Yᵉ =
    (uᵉ : classifying-type-Concrete-Groupᵉ Gᵉ) → equiv-Setᵉ (Xᵉ uᵉ) (Yᵉ uᵉ)

  id-equiv-action-Concrete-Groupᵉ : equiv-action-Concrete-Groupᵉ Xᵉ
  id-equiv-action-Concrete-Groupᵉ uᵉ = id-equivᵉ

  extensionality-action-Concrete-Groupᵉ :
    (Yᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ) → (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-action-Concrete-Groupᵉ Yᵉ
  extensionality-action-Concrete-Groupᵉ =
    extensionality-Πᵉ Xᵉ
      ( λ uᵉ → equiv-Setᵉ (Xᵉ uᵉ))
      ( λ uᵉ → extensionality-Setᵉ (Xᵉ uᵉ))

  equiv-eq-action-Concrete-Groupᵉ :
    (Yᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ) → (Xᵉ ＝ᵉ Yᵉ) → equiv-action-Concrete-Groupᵉ Yᵉ
  equiv-eq-action-Concrete-Groupᵉ Yᵉ =
    map-equivᵉ (extensionality-action-Concrete-Groupᵉ Yᵉ)

  eq-equiv-action-Concrete-Groupᵉ :
    (Yᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ) → equiv-action-Concrete-Groupᵉ Yᵉ → (Xᵉ ＝ᵉ Yᵉ)
  eq-equiv-action-Concrete-Groupᵉ Yᵉ =
    map-inv-equivᵉ (extensionality-action-Concrete-Groupᵉ Yᵉ)

  is-torsorial-equiv-action-Concrete-Groupᵉ :
    is-torsorialᵉ equiv-action-Concrete-Groupᵉ
  is-torsorial-equiv-action-Concrete-Groupᵉ =
    is-torsorial-Eq-Πᵉ (λ uᵉ → is-torsorial-equiv-Setᵉ (Xᵉ uᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  (Yᵉ : action-Concrete-Groupᵉ l3ᵉ Gᵉ)
  where

  emb-hom-equiv-action-Concrete-Groupᵉ :
    equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ ↪ᵉ hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ
  emb-hom-equiv-action-Concrete-Groupᵉ = emb-Πᵉ (λ uᵉ → emb-map-equivᵉ)

  hom-equiv-action-Concrete-Groupᵉ :
    equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ → hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ
  hom-equiv-action-Concrete-Groupᵉ = map-embᵉ emb-hom-equiv-action-Concrete-Groupᵉ

  is-emb-hom-equiv-action-Concrete-Groupᵉ :
    is-embᵉ hom-equiv-action-Concrete-Groupᵉ
  is-emb-hom-equiv-action-Concrete-Groupᵉ =
    is-emb-map-embᵉ emb-hom-equiv-action-Concrete-Groupᵉ

  map-equiv-action-Concrete-Groupᵉ :
    equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ →
    type-action-Concrete-Groupᵉ Gᵉ Xᵉ → type-action-Concrete-Groupᵉ Gᵉ Yᵉ
  map-equiv-action-Concrete-Groupᵉ eᵉ =
    map-hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ (hom-equiv-action-Concrete-Groupᵉ eᵉ)

  preserves-mul-equiv-action-Concrete-Groupᵉ :
    (eᵉ : equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ) (gᵉ : type-Concrete-Groupᵉ Gᵉ)
    (xᵉ : type-action-Concrete-Groupᵉ Gᵉ Xᵉ) →
    ( map-equiv-action-Concrete-Groupᵉ eᵉ (mul-action-Concrete-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ)) ＝ᵉ
    ( mul-action-Concrete-Groupᵉ Gᵉ Yᵉ gᵉ (map-equiv-action-Concrete-Groupᵉ eᵉ xᵉ))
  preserves-mul-equiv-action-Concrete-Groupᵉ eᵉ =
    preserves-mul-hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ
      ( hom-equiv-action-Concrete-Groupᵉ eᵉ)

  htpy-equiv-action-Concrete-Groupᵉ :
    (eᵉ fᵉ : equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  htpy-equiv-action-Concrete-Groupᵉ eᵉ fᵉ =
    htpy-hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ
      ( hom-equiv-action-Concrete-Groupᵉ eᵉ)
      ( hom-equiv-action-Concrete-Groupᵉ fᵉ)

  extensionality-equiv-action-Concrete-Groupᵉ :
    (eᵉ fᵉ : equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    (eᵉ ＝ᵉ fᵉ) ≃ᵉ htpy-equiv-action-Concrete-Groupᵉ eᵉ fᵉ
  extensionality-equiv-action-Concrete-Groupᵉ eᵉ fᵉ =
    ( extensionality-hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ
      ( hom-equiv-action-Concrete-Groupᵉ eᵉ)
      ( hom-equiv-action-Concrete-Groupᵉ fᵉ)) ∘eᵉ
    ( equiv-ap-embᵉ emb-hom-equiv-action-Concrete-Groupᵉ)

  eq-htpy-equiv-action-Concrete-Groupᵉ :
    (eᵉ fᵉ : equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    htpy-equiv-action-Concrete-Groupᵉ eᵉ fᵉ → (eᵉ ＝ᵉ fᵉ)
  eq-htpy-equiv-action-Concrete-Groupᵉ eᵉ fᵉ =
    map-inv-equivᵉ (extensionality-equiv-action-Concrete-Groupᵉ eᵉ fᵉ)
```

## Properties

### The type of equivalences between concrete group actions is a set

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  (Yᵉ : action-Concrete-Groupᵉ l3ᵉ Gᵉ)
  where

  is-prop-htpy-equiv-action-Concrete-Groupᵉ :
    (eᵉ fᵉ : equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    is-propᵉ (htpy-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ fᵉ)
  is-prop-htpy-equiv-action-Concrete-Groupᵉ eᵉ fᵉ =
    is-prop-htpy-hom-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ
      ( hom-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ)
      ( hom-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ)

  htpy-prop-equiv-action-Concrete-Groupᵉ :
    (eᵉ fᵉ : equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ) → Propᵉ (l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ (htpy-prop-equiv-action-Concrete-Groupᵉ eᵉ fᵉ) =
    htpy-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ fᵉ
  pr2ᵉ (htpy-prop-equiv-action-Concrete-Groupᵉ eᵉ fᵉ) =
    is-prop-htpy-equiv-action-Concrete-Groupᵉ eᵉ fᵉ

  is-set-equiv-action-Concrete-Groupᵉ :
    is-setᵉ (equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)
  is-set-equiv-action-Concrete-Groupᵉ eᵉ fᵉ =
    is-prop-equivᵉ
      ( extensionality-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ fᵉ)
      ( is-prop-htpy-equiv-action-Concrete-Groupᵉ eᵉ fᵉ)
```

### The type of concrete group actions is a 1-type

```agda
is-1-type-action-Concrete-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) →
  is-1-typeᵉ (action-Concrete-Groupᵉ l2ᵉ Gᵉ)
is-1-type-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ =
  is-set-equivᵉ
    ( equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)
    ( extensionality-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)
    ( is-set-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)
```