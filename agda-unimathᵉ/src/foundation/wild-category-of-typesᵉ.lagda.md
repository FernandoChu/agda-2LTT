# The wild category of types

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module foundation.wild-category-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.isomorphisms-of-setsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ

open import structured-types.globular-typesᵉ
open import structured-types.large-globular-typesᵉ
open import structured-types.large-reflexive-globular-typesᵉ
open import structured-types.large-transitive-globular-typesᵉ
open import structured-types.reflexive-globular-typesᵉ
open import structured-types.transitive-globular-typesᵉ

open import wild-category-theory.isomorphisms-in-noncoherent-large-wild-higher-precategoriesᵉ
open import wild-category-theory.isomorphisms-in-noncoherent-wild-higher-precategoriesᵉ
open import wild-category-theory.noncoherent-large-wild-higher-precategoriesᵉ
open import wild-category-theory.noncoherent-wild-higher-precategoriesᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "wildᵉ categoryᵉ ofᵉ types"ᵉ Agda=Type-Noncoherent-Large-Wild-Higher-Precategoryᵉ}}
consistsᵉ ofᵉ typesᵉ andᵉ functionsᵉ andᵉ homotopies.ᵉ

## Definitions

### The globular structure on dependent function types

```agda
globular-structure-Πᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  globular-structureᵉ (l1ᵉ ⊔ l2ᵉ) ((xᵉ : Aᵉ) → Bᵉ xᵉ)
globular-structure-Πᵉ =
  λ where
  .1-cell-globular-structureᵉ → _~ᵉ_
  .globular-structure-1-cell-globular-structureᵉ fᵉ gᵉ → globular-structure-Πᵉ

is-reflexive-globular-structure-Πᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  is-reflexive-globular-structureᵉ (globular-structure-Πᵉ {Aᵉ = Aᵉ} {Bᵉ})
is-reflexive-globular-structure-Πᵉ =
  λ where
  .is-reflexive-1-cell-is-reflexive-globular-structureᵉ fᵉ → refl-htpyᵉ
  .is-reflexive-globular-structure-1-cell-is-reflexive-globular-structureᵉ fᵉ gᵉ →
    is-reflexive-globular-structure-Πᵉ

is-transitive-globular-structure-Πᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  is-transitive-globular-structureᵉ (globular-structure-Πᵉ {Aᵉ = Aᵉ} {Bᵉ})
is-transitive-globular-structure-Πᵉ =
  λ where
  .comp-1-cell-is-transitive-globular-structureᵉ Hᵉ Kᵉ → Kᵉ ∙hᵉ Hᵉ
  .is-transitive-globular-structure-1-cell-is-transitive-globular-structureᵉ
    Hᵉ Kᵉ →
    is-transitive-globular-structure-Πᵉ
```

### The large globular structure on types

```agda
large-globular-structure-Typeᵉ : large-globular-structureᵉ (_⊔ᵉ_) (λ lᵉ → UUᵉ lᵉ)
large-globular-structure-Typeᵉ =
  λ where
  .1-cell-large-globular-structureᵉ Xᵉ Yᵉ → (Xᵉ → Yᵉ)
  .globular-structure-1-cell-large-globular-structureᵉ Xᵉ Yᵉ → globular-structure-Πᵉ

is-reflexive-large-globular-structure-Typeᵉ :
  is-reflexive-large-globular-structureᵉ large-globular-structure-Typeᵉ
is-reflexive-large-globular-structure-Typeᵉ =
  λ where
  .is-reflexive-1-cell-is-reflexive-large-globular-structureᵉ Xᵉ → idᵉ
  .is-reflexive-globular-structure-1-cell-is-reflexive-large-globular-structureᵉ
    Xᵉ Yᵉ →
    is-reflexive-globular-structure-Πᵉ

is-transitive-large-globular-structure-Typeᵉ :
  is-transitive-large-globular-structureᵉ large-globular-structure-Typeᵉ
is-transitive-large-globular-structure-Typeᵉ =
  λ where
  .comp-1-cell-is-transitive-large-globular-structureᵉ gᵉ fᵉ → gᵉ ∘ᵉ fᵉ
  .is-transitive-globular-structure-1-cell-is-transitive-large-globular-structureᵉ
    Xᵉ Yᵉ →
    is-transitive-globular-structure-Πᵉ
```

### The noncoherent large wild higher precategory of types

```agda
Type-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
  Noncoherent-Large-Wild-Higher-Precategoryᵉ lsuc (_⊔ᵉ_)
Type-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
  λ where
  .obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ lᵉ →
    UUᵉ lᵉ
  .hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ →
    large-globular-structure-Typeᵉ
  .id-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ →
    is-reflexive-large-globular-structure-Typeᵉ
  .comp-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategoryᵉ →
    is-transitive-large-globular-structure-Typeᵉ
```