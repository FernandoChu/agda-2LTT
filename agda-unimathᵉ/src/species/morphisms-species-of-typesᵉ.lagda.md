# Morphisms of species of types

```agda
module species.morphisms-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-typesᵉ
```

</details>

### Idea

Aᵉ homomorphismᵉ betweenᵉ twoᵉ speciesᵉ isᵉ aᵉ pointwiseᵉ familyᵉ ofᵉ mapsᵉ betweenᵉ theirᵉ
values.ᵉ

## Definitions

### Morphisms of species

```agda
hom-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} →
  species-typesᵉ l1ᵉ l2ᵉ → species-typesᵉ l1ᵉ l3ᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
hom-species-typesᵉ {l1ᵉ} Fᵉ Gᵉ = (Xᵉ : UUᵉ l1ᵉ) → Fᵉ Xᵉ → Gᵉ Xᵉ

id-hom-species-typesᵉ :
  {l1ᵉ l2ᵉ : Level} → (Fᵉ : species-typesᵉ l1ᵉ l2ᵉ) → hom-species-typesᵉ Fᵉ Fᵉ
id-hom-species-typesᵉ Fᵉ = λ Xᵉ xᵉ → xᵉ

comp-hom-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Fᵉ : species-typesᵉ l1ᵉ l2ᵉ}
  {Gᵉ : species-typesᵉ l1ᵉ l3ᵉ}
  {Hᵉ : species-typesᵉ l1ᵉ l4ᵉ} →
  hom-species-typesᵉ Gᵉ Hᵉ → hom-species-typesᵉ Fᵉ Gᵉ → hom-species-typesᵉ Fᵉ Hᵉ
comp-hom-species-typesᵉ fᵉ gᵉ Xᵉ = (fᵉ Xᵉ) ∘ᵉ (gᵉ Xᵉ)
```

### Homotopies between morphisms of species

```agda
htpy-hom-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Fᵉ : species-typesᵉ l1ᵉ l2ᵉ} {Gᵉ : species-typesᵉ l1ᵉ l3ᵉ} →
  hom-species-typesᵉ Fᵉ Gᵉ → hom-species-typesᵉ Fᵉ Gᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
htpy-hom-species-typesᵉ {l1ᵉ} fᵉ gᵉ = (Xᵉ : UUᵉ l1ᵉ) → (fᵉ Xᵉ) ~ᵉ (gᵉ Xᵉ)

refl-htpy-hom-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Fᵉ : species-typesᵉ l1ᵉ l2ᵉ} {Gᵉ : species-typesᵉ l1ᵉ l3ᵉ}
  (fᵉ : hom-species-typesᵉ Fᵉ Gᵉ) → htpy-hom-species-typesᵉ fᵉ fᵉ
refl-htpy-hom-species-typesᵉ fᵉ Xᵉ = refl-htpyᵉ
```

## Properties

### Homotopies characterize the identity type of morphisms of species

```agda
htpy-eq-hom-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Fᵉ : species-typesᵉ l1ᵉ l2ᵉ} {Gᵉ : species-typesᵉ l1ᵉ l3ᵉ}
  {fᵉ gᵉ : hom-species-typesᵉ Fᵉ Gᵉ} →
  Idᵉ fᵉ gᵉ → htpy-hom-species-typesᵉ fᵉ gᵉ
htpy-eq-hom-species-typesᵉ reflᵉ Xᵉ yᵉ = reflᵉ

is-torsorial-htpy-hom-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Fᵉ : species-typesᵉ l1ᵉ l2ᵉ} {Gᵉ : species-typesᵉ l1ᵉ l3ᵉ}
  (fᵉ : hom-species-typesᵉ Fᵉ Gᵉ) →
  is-torsorialᵉ (htpy-hom-species-typesᵉ fᵉ)
is-torsorial-htpy-hom-species-typesᵉ fᵉ =
  is-torsorial-Eq-Πᵉ (λ Xᵉ → is-torsorial-htpyᵉ (fᵉ Xᵉ))

is-equiv-htpy-eq-hom-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Fᵉ : species-typesᵉ l1ᵉ l2ᵉ} {Gᵉ : species-typesᵉ l1ᵉ l3ᵉ}
  (fᵉ gᵉ : hom-species-typesᵉ Fᵉ Gᵉ) →
  is-equivᵉ (htpy-eq-hom-species-typesᵉ {fᵉ = fᵉ} {gᵉ = gᵉ})
is-equiv-htpy-eq-hom-species-typesᵉ fᵉ =
  fundamental-theorem-idᵉ
    ( is-torsorial-htpy-hom-species-typesᵉ fᵉ)
    ( λ gᵉ → htpy-eq-hom-species-typesᵉ {fᵉ = fᵉ} {gᵉ = gᵉ})

eq-htpy-hom-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Fᵉ : species-typesᵉ l1ᵉ l2ᵉ} {Gᵉ : species-typesᵉ l1ᵉ l3ᵉ}
  {fᵉ gᵉ : hom-species-typesᵉ Fᵉ Gᵉ} → htpy-hom-species-typesᵉ fᵉ gᵉ → Idᵉ fᵉ gᵉ
eq-htpy-hom-species-typesᵉ {fᵉ = fᵉ} {gᵉ = gᵉ} =
  map-inv-is-equivᵉ (is-equiv-htpy-eq-hom-species-typesᵉ fᵉ gᵉ)
```

### Associativity of composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Fᵉ : species-typesᵉ l1ᵉ l2ᵉ} {Gᵉ : species-typesᵉ l1ᵉ l3ᵉ}
  {Hᵉ : species-typesᵉ l1ᵉ l4ᵉ} {Kᵉ : species-typesᵉ l1ᵉ l5ᵉ}
  (hᵉ : hom-species-typesᵉ Hᵉ Kᵉ)
  (gᵉ : hom-species-typesᵉ Gᵉ Hᵉ)
  (fᵉ : hom-species-typesᵉ Fᵉ Gᵉ)
  where

  associative-comp-hom-species-typesᵉ :
    comp-hom-species-typesᵉ (comp-hom-species-typesᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-species-typesᵉ hᵉ (comp-hom-species-typesᵉ gᵉ fᵉ)
  associative-comp-hom-species-typesᵉ = reflᵉ
```

### Unit laws of composition

```agda
left-unit-law-comp-hom-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Fᵉ : species-typesᵉ l1ᵉ l2ᵉ} {Gᵉ : species-typesᵉ l1ᵉ l3ᵉ}
  (fᵉ : hom-species-typesᵉ Fᵉ Gᵉ) →
  Idᵉ (comp-hom-species-typesᵉ (id-hom-species-typesᵉ Gᵉ) fᵉ) fᵉ
left-unit-law-comp-hom-species-typesᵉ fᵉ = reflᵉ

right-unit-law-comp-hom-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Fᵉ : species-typesᵉ l1ᵉ l2ᵉ} {Gᵉ : species-typesᵉ l1ᵉ l3ᵉ}
  (fᵉ : hom-species-typesᵉ Fᵉ Gᵉ) →
  Idᵉ (comp-hom-species-typesᵉ fᵉ (id-hom-species-typesᵉ Fᵉ)) fᵉ
right-unit-law-comp-hom-species-typesᵉ fᵉ = reflᵉ
```