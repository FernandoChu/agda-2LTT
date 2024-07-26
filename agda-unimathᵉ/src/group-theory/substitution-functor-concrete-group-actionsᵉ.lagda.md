# The substitution functor of concrete group actions

```agda
module group-theory.substitution-functor-concrete-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import group-theory.concrete-group-actionsᵉ
open import group-theory.concrete-groupsᵉ
open import group-theory.homomorphisms-concrete-groupsᵉ
```

</details>

## Definition

### Substitution of concrete group actions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Hᵉ : Concrete-Groupᵉ l2ᵉ)
  (fᵉ : hom-Concrete-Groupᵉ Gᵉ Hᵉ)
  where

  subst-action-Concrete-Groupᵉ :
    {lᵉ : Level} →
    action-Concrete-Groupᵉ lᵉ Hᵉ → action-Concrete-Groupᵉ lᵉ Gᵉ
  subst-action-Concrete-Groupᵉ Yᵉ xᵉ =
    Yᵉ (classifying-map-hom-Concrete-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ)
```