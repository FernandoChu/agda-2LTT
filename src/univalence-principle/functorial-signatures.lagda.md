# Functorial signatures

```agda
module univalence-principle.functorial-signatures where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.inverse-precategoriesᵉ
open import category-theory.opposite-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.discrete-categoriesᵉ
open import category-theory.precategory-of-functorsᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ

open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.propositionsᵉ
open import foundation.binary-transportᵉ
open import foundation.category-of-setsᵉ
open import foundation.cofibrant-typesᵉ
open import foundation.setsᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.fibrant-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.sharp-typesᵉ
open import foundation.exotypesᵉ
open import foundation.raising-universe-levelsᵉ
```

</details>

## Idea


## Definitions

```agda
terminal-Precategoryᵉ : (l1 l2 : Level) → Precategoryᵉ l1 l2
terminal-Precategoryᵉ l1 l2 =
  make-Precategoryᵉ
    ( raise-unitᵉ l1)
    ( λ _ _ → raise-unit-Setᵉ l2)
    ( λ _ _ → raise-starᵉ)
    ( λ _ → raise-starᵉ)
    ( λ _ _ _ → reflᵉ)
    ( λ {(map-raiseᵉ starᵉ) → reflᵉ})
    ( λ {(map-raiseᵉ starᵉ) → reflᵉ})

discrete-functor-Precategoryᵉ :
  {l1 : Level} → UUᵉ l1 → (l2 : Level) →
  Precategoryᵉ (l1 ⊔ lsuc l2) (l1 ⊔ l2)
discrete-functor-Precategoryᵉ X l =
  functor-precategory-Precategoryᵉ
    ( discrete-precategory-Setᵉ (exotype-Setᵉ X))
    ( Set-Precategoryᵉ l)

FSig-Precategoryᵉ : (l1 l2 ls lU : Level) → ℕᵉ → Precategoryᵉ l1 l2
obj-FSig-Precategoryᵉ : (l1 l2 ls lU : Level) → ℕᵉ → UUᵉ (lsuc l1 ⊔ l2 ⊔ lsuc ls ⊔ lsuc lU)
hom-FSig-Precategoryᵉ :
  (l1 l2 ls lU : Level) → (n : ℕᵉ) →
  obj-FSig-Precategoryᵉ l1 l2 ls lU n →
  obj-FSig-Precategoryᵉ l1 l2 ls lU n →
  UUᵉ (lsuc l1 ⊔ l2 ⊔ lsuc ls ⊔ lsuc lU)


hom-FSig-Precategoryᵉ l1 l2 ls lU 0ᵉ 𝓛 𝓜 = raise-unitᵉ _
hom-FSig-Precategoryᵉ l1 l2 ls lU (succ-ℕᵉ n) 𝓛 𝓜 = {!!}

obj-FSig-Precategoryᵉ l1 l2 ls lU 0ᵉ = raise-unitᵉ _
obj-FSig-Precategoryᵉ l1 l2 ls lU (succ-ℕᵉ n) =
  Σᵉ (Sharp-Type l1 ls)
    ( λ 𝓛⊥ →
      functor-Precategoryᵉ
        ( functor-precategory-Precategoryᵉ
          ( discrete-precategory-Setᵉ (exotype-Setᵉ (type-Sharp-Type 𝓛⊥)))
          ( Set-Precategoryᵉ lU))
        ( FSig-Precategoryᵉ l1 l2 ls lU n))

FSig-Precategoryᵉ l1 l2 ls lU n = _
