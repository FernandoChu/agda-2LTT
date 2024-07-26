# The category of groups

```agda
module group-theory.category-of-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.large-categoriesᵉ

open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.isomorphisms-groupsᵉ
open import group-theory.precategory-of-groupsᵉ
```

</details>

## Definition

```agda
is-large-category-Groupᵉ :
  is-large-category-Large-Precategoryᵉ Group-Large-Precategoryᵉ
is-large-category-Groupᵉ Gᵉ =
  fundamental-theorem-idᵉ (is-torsorial-iso-Groupᵉ Gᵉ) (iso-eq-Groupᵉ Gᵉ)

eq-iso-Groupᵉ : {lᵉ : Level} (Gᵉ Hᵉ : Groupᵉ lᵉ) → iso-Groupᵉ Gᵉ Hᵉ → Idᵉ Gᵉ Hᵉ
eq-iso-Groupᵉ Gᵉ Hᵉ = map-inv-is-equivᵉ (is-large-category-Groupᵉ Gᵉ Hᵉ)

Group-Large-Categoryᵉ : Large-Categoryᵉ lsuc (_⊔ᵉ_)
large-precategory-Large-Categoryᵉ Group-Large-Categoryᵉ = Group-Large-Precategoryᵉ
is-large-category-Large-Categoryᵉ Group-Large-Categoryᵉ = is-large-category-Groupᵉ

Group-Categoryᵉ : (lᵉ : Level) → Categoryᵉ (lsuc lᵉ) lᵉ
Group-Categoryᵉ = category-Large-Categoryᵉ Group-Large-Categoryᵉ
```