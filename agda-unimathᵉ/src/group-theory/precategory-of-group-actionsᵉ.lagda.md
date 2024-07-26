# The precategory of group actions

```agda
module group-theory.precategory-of-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.universe-levelsᵉ

open import group-theory.group-actionsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-group-actionsᵉ
```

</details>

## Idea

Theᵉ [largeᵉ precategory](category-theory.large-precategories.mdᵉ) ofᵉ
[groupᵉ actions](group-theory.group-actions.mdᵉ) consistsᵉ ofᵉ groupᵉ actionsᵉ andᵉ
[morphismsᵉ ofᵉ groupᵉ actions](group-theory.homomorphisms-group-actions.mdᵉ)
betweenᵉ them.ᵉ

## Definitions

### The large precategory of `G`-sets

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  action-Group-Large-Precategoryᵉ :
    Large-Precategoryᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  action-Group-Large-Precategoryᵉ =
    make-Large-Precategoryᵉ
      ( action-Groupᵉ Gᵉ)
      ( hom-set-action-Groupᵉ Gᵉ)
      ( λ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Xᵉ} {Yᵉ} {Zᵉ} → comp-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ Zᵉ)
      ( λ {l1ᵉ} {Xᵉ} → id-hom-action-Groupᵉ Gᵉ Xᵉ)
      ( λ {l1ᵉ} {l2ᵉ} {l3ᵉ} {l4ᵉ} {Xᵉ} {Yᵉ} {Zᵉ} {Wᵉ} →
        associative-comp-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ Zᵉ Wᵉ)
      ( λ {l1ᵉ} {l2ᵉ} {Xᵉ} {Yᵉ} → left-unit-law-comp-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ)
      ( λ {l1ᵉ} {l2ᵉ} {Xᵉ} {Yᵉ} → right-unit-law-comp-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ)
```

### The small precategory of `G`-sets

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  action-Group-Precategoryᵉ :
    (l2ᵉ : Level) → Precategoryᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  action-Group-Precategoryᵉ =
    precategory-Large-Precategoryᵉ (action-Group-Large-Precategoryᵉ Gᵉ)
```