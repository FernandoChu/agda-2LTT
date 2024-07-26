# The precategory of semigroups

```agda
module group-theory.precategory-of-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategoriesᵉ

open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-semigroupsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Semigroupsᵉ andᵉ semigroupᵉ homomorphismsᵉ formᵉ aᵉ precategory.ᵉ

## Definition

### The large precategory of semigroups

```agda
Semigroup-Large-Precategoryᵉ : Large-Precategoryᵉ lsuc (_⊔ᵉ_)
Semigroup-Large-Precategoryᵉ =
  make-Large-Precategoryᵉ
    ( Semigroupᵉ)
    ( hom-set-Semigroupᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Gᵉ} {Hᵉ} {Kᵉ} → comp-hom-Semigroupᵉ Gᵉ Hᵉ Kᵉ)
    ( λ {lᵉ} {Gᵉ} → id-hom-Semigroupᵉ Gᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {l3ᵉ} {l4ᵉ} {Gᵉ} {Hᵉ} {Kᵉ} {Lᵉ} →
      associative-comp-hom-Semigroupᵉ Gᵉ Hᵉ Kᵉ Lᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {Gᵉ} {Hᵉ} → left-unit-law-comp-hom-Semigroupᵉ Gᵉ Hᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {Gᵉ} {Hᵉ} → right-unit-law-comp-hom-Semigroupᵉ Gᵉ Hᵉ)
```