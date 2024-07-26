# Homomorphisms of higher group actions

```agda
module higher-group-theory.homomorphisms-higher-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-group-actionsᵉ
open import higher-group-theory.higher-groupsᵉ
```

</details>

## Definition

### Homomorphisms of higher group actions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Xᵉ : action-∞-Groupᵉ l2ᵉ Gᵉ)
  (Yᵉ : action-∞-Groupᵉ l3ᵉ Gᵉ)
  where

  hom-action-∞-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  hom-action-∞-Groupᵉ = (uᵉ : classifying-type-∞-Groupᵉ Gᵉ) → Xᵉ uᵉ → Yᵉ uᵉ

  map-hom-action-∞-Groupᵉ :
    hom-action-∞-Groupᵉ → type-action-∞-Groupᵉ Gᵉ Xᵉ → type-action-∞-Groupᵉ Gᵉ Yᵉ
  map-hom-action-∞-Groupᵉ fᵉ = fᵉ (shape-∞-Groupᵉ Gᵉ)

  preserves-mul-hom-action-∞-Groupᵉ :
    (fᵉ : hom-action-∞-Groupᵉ) (gᵉ : type-∞-Groupᵉ Gᵉ)
    (xᵉ : type-action-∞-Groupᵉ Gᵉ Xᵉ) →
    ( map-hom-action-∞-Groupᵉ fᵉ (mul-action-∞-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ)) ＝ᵉ
    ( mul-action-∞-Groupᵉ Gᵉ Yᵉ gᵉ (map-hom-action-∞-Groupᵉ fᵉ xᵉ))
  preserves-mul-hom-action-∞-Groupᵉ fᵉ gᵉ xᵉ = preserves-trᵉ fᵉ gᵉ xᵉ
```

### Homotopies of morphisms of higher group actions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Xᵉ : action-∞-Groupᵉ l2ᵉ Gᵉ)
  (Yᵉ : action-∞-Groupᵉ l3ᵉ Gᵉ) (fᵉ : hom-action-∞-Groupᵉ Gᵉ Xᵉ Yᵉ)
  where

  htpy-hom-action-∞-Groupᵉ : (gᵉ : hom-action-∞-Groupᵉ Gᵉ Xᵉ Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  htpy-hom-action-∞-Groupᵉ gᵉ = (uᵉ : classifying-type-∞-Groupᵉ Gᵉ) → (fᵉ uᵉ) ~ᵉ (gᵉ uᵉ)

  extensionality-hom-action-∞-Groupᵉ :
    (gᵉ : hom-action-∞-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-action-∞-Groupᵉ gᵉ
  extensionality-hom-action-∞-Groupᵉ =
    extensionality-Πᵉ fᵉ
      ( λ uᵉ gᵉ → fᵉ uᵉ ~ᵉ gᵉ)
      ( λ uᵉ gᵉ → equiv-funextᵉ)

  htpy-eq-hom-action-∞-Groupᵉ :
    (gᵉ : hom-action-∞-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    (fᵉ ＝ᵉ gᵉ) → htpy-hom-action-∞-Groupᵉ gᵉ
  htpy-eq-hom-action-∞-Groupᵉ gᵉ =
    map-equivᵉ (extensionality-hom-action-∞-Groupᵉ gᵉ)

  eq-htpy-hom-action-∞-Groupᵉ :
    (gᵉ : hom-action-∞-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    htpy-hom-action-∞-Groupᵉ gᵉ → (fᵉ ＝ᵉ gᵉ)
  eq-htpy-hom-action-∞-Groupᵉ gᵉ =
    map-inv-equivᵉ (extensionality-hom-action-∞-Groupᵉ gᵉ)
```