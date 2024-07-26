# The precategory of finite species

```agda
module species.precategory-of-finite-speciesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategoriesᵉ

open import foundation.universe-levelsᵉ

open import species.morphisms-finite-speciesᵉ
open import species.species-of-finite-typesᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "precategoryᵉ ofᵉ finiteᵉ species"ᵉ Agda=species-𝔽-Large-Precategoryᵉ}}
consistsᵉ ofᵉ [finiteᵉ species](species.species-of-finite-types.mdᵉ) andᵉ
[homomorphismsᵉ ofᵉ finiteᵉ species](species.morphisms-finite-species.md).ᵉ

## Definition

```agda
species-𝔽-Large-Precategoryᵉ :
  (lᵉ : Level) →
  Large-Precategoryᵉ (λ l1ᵉ → lsuc lᵉ ⊔ lsuc l1ᵉ) (λ l2ᵉ l3ᵉ → lsuc lᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
species-𝔽-Large-Precategoryᵉ lᵉ =
  make-Large-Precategoryᵉ
    ( species-𝔽ᵉ lᵉ)
    ( hom-set-species-𝔽ᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Fᵉ} {Gᵉ} {Hᵉ} → comp-hom-species-𝔽ᵉ Fᵉ Gᵉ Hᵉ)
    ( λ {l1ᵉ} {Fᵉ} → id-hom-species-𝔽ᵉ Fᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {l3ᵉ} {l4ᵉ} {Fᵉ} {Gᵉ} {Hᵉ} {Kᵉ} →
      associative-comp-hom-species-𝔽ᵉ Fᵉ Gᵉ Hᵉ Kᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {Fᵉ} {Gᵉ} → left-unit-law-comp-hom-species-𝔽ᵉ Fᵉ Gᵉ)
    ( λ {l1ᵉ} {l2ᵉ} {Fᵉ} {Gᵉ} → right-unit-law-comp-hom-species-𝔽ᵉ Fᵉ Gᵉ)
```