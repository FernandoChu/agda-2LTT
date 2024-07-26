# Morphisms of finite species

```agda
module species.morphisms-finite-speciesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-finite-typesᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ homomorphismᵉ betweenᵉ twoᵉ finiteᵉ speciesᵉ isᵉ aᵉ pointwiseᵉ familyᵉ ofᵉ maps.ᵉ

## Definitions

### The type of morphisms between finite species

```agda
hom-species-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} → species-𝔽ᵉ l1ᵉ l2ᵉ → species-𝔽ᵉ l1ᵉ l3ᵉ →
  UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
hom-species-𝔽ᵉ {l1ᵉ} Fᵉ Gᵉ = (Xᵉ : 𝔽ᵉ l1ᵉ) → type-𝔽ᵉ (Fᵉ Xᵉ) → type-𝔽ᵉ (Gᵉ Xᵉ)
```

### The identity morphisms of finite species

```agda
id-hom-species-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Fᵉ : species-𝔽ᵉ l1ᵉ l2ᵉ) → hom-species-𝔽ᵉ Fᵉ Fᵉ
id-hom-species-𝔽ᵉ Fᵉ = λ Xᵉ xᵉ → xᵉ
```

### Composition of morphisms of finite species

```agda
comp-hom-species-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Fᵉ : species-𝔽ᵉ l1ᵉ l2ᵉ) (Gᵉ : species-𝔽ᵉ l1ᵉ l3ᵉ)
  (Hᵉ : species-𝔽ᵉ l1ᵉ l4ᵉ) → hom-species-𝔽ᵉ Gᵉ Hᵉ →
  hom-species-𝔽ᵉ Fᵉ Gᵉ → hom-species-𝔽ᵉ Fᵉ Hᵉ
comp-hom-species-𝔽ᵉ Fᵉ Gᵉ Hᵉ fᵉ gᵉ Xᵉ = (fᵉ Xᵉ) ∘ᵉ (gᵉ Xᵉ)
```

### Homotopies of morphisms of finite species

```agda
htpy-hom-species-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Fᵉ : species-𝔽ᵉ l1ᵉ l2ᵉ) (Gᵉ : species-𝔽ᵉ l1ᵉ l3ᵉ) →
  (hom-species-𝔽ᵉ Fᵉ Gᵉ) → (hom-species-𝔽ᵉ Fᵉ Gᵉ) →
  UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
htpy-hom-species-𝔽ᵉ {l1ᵉ} Fᵉ Gᵉ fᵉ gᵉ = (Xᵉ : 𝔽ᵉ l1ᵉ) → (fᵉ Xᵉ) ~ᵉ (gᵉ Xᵉ)

refl-htpy-hom-species-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Fᵉ : species-𝔽ᵉ l1ᵉ l2ᵉ) (Gᵉ : species-𝔽ᵉ l1ᵉ l3ᵉ) →
  (fᵉ : hom-species-𝔽ᵉ Fᵉ Gᵉ) → htpy-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ fᵉ
refl-htpy-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ Xᵉ = refl-htpyᵉ
```

## Properties

### Associativity of composition of homomorphisms of finite species

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  (Fᵉ : species-𝔽ᵉ l1ᵉ l2ᵉ) (Gᵉ : species-𝔽ᵉ l1ᵉ l3ᵉ)
  (Hᵉ : species-𝔽ᵉ l1ᵉ l4ᵉ) (Kᵉ : species-𝔽ᵉ l1ᵉ l5ᵉ)
  where

  associative-comp-hom-species-𝔽ᵉ :
    (hᵉ : hom-species-𝔽ᵉ Hᵉ Kᵉ) (gᵉ : hom-species-𝔽ᵉ Gᵉ Hᵉ) (fᵉ : hom-species-𝔽ᵉ Fᵉ Gᵉ) →
    comp-hom-species-𝔽ᵉ Fᵉ Gᵉ Kᵉ (comp-hom-species-𝔽ᵉ Gᵉ Hᵉ Kᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-species-𝔽ᵉ Fᵉ Hᵉ Kᵉ hᵉ (comp-hom-species-𝔽ᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ)
  associative-comp-hom-species-𝔽ᵉ hᵉ gᵉ fᵉ = reflᵉ
```

### The unit laws for composition of homomorphisms of finite species

```agda
left-unit-law-comp-hom-species-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Fᵉ : species-𝔽ᵉ l1ᵉ l2ᵉ) (Gᵉ : species-𝔽ᵉ l1ᵉ l3ᵉ)
  (fᵉ : hom-species-𝔽ᵉ Fᵉ Gᵉ) →
  Idᵉ (comp-hom-species-𝔽ᵉ Fᵉ Gᵉ Gᵉ (id-hom-species-𝔽ᵉ Gᵉ) fᵉ) fᵉ
left-unit-law-comp-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ = reflᵉ

right-unit-law-comp-hom-species-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Fᵉ : species-𝔽ᵉ l1ᵉ l2ᵉ) (Gᵉ : species-𝔽ᵉ l1ᵉ l3ᵉ)
  (fᵉ : hom-species-𝔽ᵉ Fᵉ Gᵉ) →
  Idᵉ (comp-hom-species-𝔽ᵉ Fᵉ Fᵉ Gᵉ fᵉ (id-hom-species-𝔽ᵉ Fᵉ)) fᵉ
right-unit-law-comp-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ = reflᵉ
```

### Characterization of the identity type of homomorphisms of finite species

```agda
htpy-eq-hom-species-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Fᵉ : species-𝔽ᵉ l1ᵉ l2ᵉ) (Gᵉ : species-𝔽ᵉ l1ᵉ l3ᵉ)
  (fᵉ gᵉ : hom-species-𝔽ᵉ Fᵉ Gᵉ) →
  Idᵉ fᵉ gᵉ → htpy-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ gᵉ
htpy-eq-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ gᵉ reflᵉ Xᵉ yᵉ = reflᵉ

is-torsorial-htpy-hom-species-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Fᵉ : species-𝔽ᵉ l1ᵉ l2ᵉ) (Gᵉ : species-𝔽ᵉ l1ᵉ l3ᵉ)
  (fᵉ : hom-species-𝔽ᵉ Fᵉ Gᵉ) → is-torsorialᵉ (htpy-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ)
is-torsorial-htpy-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ =
  is-torsorial-Eq-Πᵉ (λ Xᵉ → is-torsorial-htpyᵉ (fᵉ Xᵉ))

is-equiv-htpy-eq-hom-species-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Fᵉ : species-𝔽ᵉ l1ᵉ l2ᵉ) (Gᵉ : species-𝔽ᵉ l1ᵉ l3ᵉ)
  (fᵉ gᵉ : hom-species-𝔽ᵉ Fᵉ Gᵉ) →
    is-equivᵉ (htpy-eq-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ gᵉ)
is-equiv-htpy-eq-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ =
  fundamental-theorem-idᵉ
    ( is-torsorial-htpy-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ)
    ( λ gᵉ → htpy-eq-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ gᵉ)

extensionality-hom-species-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Fᵉ : species-𝔽ᵉ l1ᵉ l2ᵉ) (Gᵉ : species-𝔽ᵉ l1ᵉ l3ᵉ)
  (fᵉ gᵉ : hom-species-𝔽ᵉ Fᵉ Gᵉ) →
  Idᵉ fᵉ gᵉ ≃ᵉ htpy-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ gᵉ
pr1ᵉ (extensionality-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ gᵉ) =
  htpy-eq-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ gᵉ
pr2ᵉ (extensionality-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ gᵉ) =
  is-equiv-htpy-eq-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ gᵉ
```

### The type of homomorphisms of finite species is a set

```agda
is-set-hom-species-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Fᵉ : species-𝔽ᵉ l1ᵉ l2ᵉ) (Gᵉ : species-𝔽ᵉ l1ᵉ l3ᵉ) →
  is-setᵉ (hom-species-𝔽ᵉ Fᵉ Gᵉ)
is-set-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ gᵉ =
  is-prop-equivᵉ
    ( extensionality-hom-species-𝔽ᵉ Fᵉ Gᵉ fᵉ gᵉ)
    ( is-prop-Πᵉ
      ( λ Xᵉ →
        is-prop-Πᵉ
          ( λ xᵉ pᵉ qᵉ →
            is-set-is-finiteᵉ (is-finite-type-𝔽ᵉ (Gᵉ Xᵉ)) (fᵉ Xᵉ xᵉ) (gᵉ Xᵉ xᵉ) pᵉ qᵉ)))

hom-set-species-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Fᵉ : species-𝔽ᵉ l1ᵉ l2ᵉ) (Gᵉ : species-𝔽ᵉ l1ᵉ l3ᵉ) →
  Setᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
pr1ᵉ (hom-set-species-𝔽ᵉ Fᵉ Gᵉ) = hom-species-𝔽ᵉ Fᵉ Gᵉ
pr2ᵉ (hom-set-species-𝔽ᵉ Fᵉ Gᵉ) = is-set-hom-species-𝔽ᵉ Fᵉ Gᵉ
```