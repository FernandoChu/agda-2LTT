# The precategory of concrete groups

```agda
module group-theory.precategory-of-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategoriesᵉ

open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.homomorphisms-concrete-groupsᵉ
```

</details>

## Definitions

### The large precategory of concrete groups

```agda
Concrete-Group-Large-Precategoryᵉ : Large-Precategoryᵉ lsuc (_⊔ᵉ_)
Concrete-Group-Large-Precategoryᵉ =
  make-Large-Precategoryᵉ
    ( Concrete-Groupᵉ)
    ( hom-set-Concrete-Groupᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Gᵉ} {Hᵉ} {Kᵉ} → comp-hom-Concrete-Groupᵉ Gᵉ Hᵉ Kᵉ)
    ( λ {lᵉ} {Gᵉ} → id-hom-Concrete-Groupᵉ Gᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {l3ᵉ} {l4ᵉ} {Gᵉ} {Hᵉ} {Kᵉ} {Lᵉ} hᵉ gᵉ fᵉ →
      eq-htpy-hom-Concrete-Groupᵉ Gᵉ Lᵉ _ _
        ( associative-comp-hom-Concrete-Groupᵉ Gᵉ Hᵉ Kᵉ Lᵉ hᵉ gᵉ fᵉ))
    ( λ {l1ᵉ} {l2ᵉ} {Gᵉ} {Hᵉ} fᵉ →
      eq-htpy-hom-Concrete-Groupᵉ Gᵉ Hᵉ _ _
        ( left-unit-law-comp-hom-Concrete-Groupᵉ Gᵉ Hᵉ fᵉ))
    ( λ {l1ᵉ} {l2ᵉ} {Gᵉ} {Hᵉ} fᵉ →
      eq-htpy-hom-Concrete-Groupᵉ Gᵉ Hᵉ _ _
        ( right-unit-law-comp-hom-Concrete-Groupᵉ Gᵉ Hᵉ fᵉ))
```