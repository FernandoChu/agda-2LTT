# Equivalences of cubes

```agda
module univalent-combinatorics.equivalences-cubesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.cubesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Definitions

### Equivalences of cubes

```agda
equiv-cubeᵉ : (kᵉ : ℕᵉ) → cubeᵉ kᵉ → cubeᵉ kᵉ → UUᵉ lzero
equiv-cubeᵉ kᵉ Xᵉ Yᵉ =
  Σᵉ ( (dim-cubeᵉ kᵉ Xᵉ) ≃ᵉ (dim-cubeᵉ kᵉ Yᵉ))
    ( λ eᵉ →
      (xᵉ : dim-cubeᵉ kᵉ Xᵉ) → (axis-cubeᵉ kᵉ Xᵉ xᵉ) ≃ᵉ (axis-cubeᵉ kᵉ Yᵉ (map-equivᵉ eᵉ xᵉ)))

dim-equiv-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ Yᵉ : cubeᵉ kᵉ) → equiv-cubeᵉ kᵉ Xᵉ Yᵉ → dim-cubeᵉ kᵉ Xᵉ ≃ᵉ dim-cubeᵉ kᵉ Yᵉ
dim-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ = pr1ᵉ eᵉ

map-dim-equiv-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ Yᵉ : cubeᵉ kᵉ) → equiv-cubeᵉ kᵉ Xᵉ Yᵉ → dim-cubeᵉ kᵉ Xᵉ → dim-cubeᵉ kᵉ Yᵉ
map-dim-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ = map-equivᵉ (dim-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ)

axis-equiv-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ Yᵉ : cubeᵉ kᵉ) (eᵉ : equiv-cubeᵉ kᵉ Xᵉ Yᵉ) (dᵉ : dim-cubeᵉ kᵉ Xᵉ) →
  axis-cubeᵉ kᵉ Xᵉ dᵉ ≃ᵉ axis-cubeᵉ kᵉ Yᵉ (map-dim-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ dᵉ)
axis-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ = pr2ᵉ eᵉ

map-axis-equiv-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ Yᵉ : cubeᵉ kᵉ) (eᵉ : equiv-cubeᵉ kᵉ Xᵉ Yᵉ) (dᵉ : dim-cubeᵉ kᵉ Xᵉ) →
  axis-cubeᵉ kᵉ Xᵉ dᵉ → axis-cubeᵉ kᵉ Yᵉ (map-dim-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ dᵉ)
map-axis-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ dᵉ =
  map-equivᵉ (axis-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ dᵉ)

id-equiv-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ : cubeᵉ kᵉ) → equiv-cubeᵉ kᵉ Xᵉ Xᵉ
id-equiv-cubeᵉ kᵉ Xᵉ = pairᵉ id-equivᵉ (λ xᵉ → id-equivᵉ)

equiv-eq-cubeᵉ :
  (kᵉ : ℕᵉ) {Xᵉ Yᵉ : cubeᵉ kᵉ} → Idᵉ Xᵉ Yᵉ → equiv-cubeᵉ kᵉ Xᵉ Yᵉ
equiv-eq-cubeᵉ kᵉ {Xᵉ} reflᵉ = id-equiv-cubeᵉ kᵉ Xᵉ

is-torsorial-equiv-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ : cubeᵉ kᵉ) → is-torsorialᵉ (equiv-cubeᵉ kᵉ Xᵉ)
is-torsorial-equiv-cubeᵉ kᵉ Xᵉ =
  is-torsorial-Eq-structureᵉ
    ( is-torsorial-equiv-UU-Finᵉ {kᵉ = kᵉ} (dim-cube-UU-Finᵉ kᵉ Xᵉ))
    ( pairᵉ
      ( dim-cube-UU-Finᵉ kᵉ Xᵉ)
      ( id-equiv-UU-Finᵉ {kᵉ = kᵉ} (dim-cube-UU-Finᵉ kᵉ Xᵉ)))
    ( is-torsorial-Eq-Πᵉ
      ( λ iᵉ → is-torsorial-equiv-UU-Finᵉ {kᵉ = 2ᵉ} (axis-cube-UU-2ᵉ kᵉ Xᵉ iᵉ)))

is-equiv-equiv-eq-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ Yᵉ : cubeᵉ kᵉ) → is-equivᵉ (equiv-eq-cubeᵉ kᵉ {Xᵉ} {Yᵉ})
is-equiv-equiv-eq-cubeᵉ kᵉ Xᵉ =
  fundamental-theorem-idᵉ
    ( is-torsorial-equiv-cubeᵉ kᵉ Xᵉ)
    ( λ Yᵉ → equiv-eq-cubeᵉ kᵉ {Xᵉ = Xᵉ} {Yᵉ})

eq-equiv-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ Yᵉ : cubeᵉ kᵉ) → equiv-cubeᵉ kᵉ Xᵉ Yᵉ → Idᵉ Xᵉ Yᵉ
eq-equiv-cubeᵉ kᵉ Xᵉ Yᵉ =
  map-inv-is-equivᵉ (is-equiv-equiv-eq-cubeᵉ kᵉ Xᵉ Yᵉ)

comp-equiv-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ Yᵉ Zᵉ : cubeᵉ kᵉ) →
  equiv-cubeᵉ kᵉ Yᵉ Zᵉ → equiv-cubeᵉ kᵉ Xᵉ Yᵉ → equiv-cubeᵉ kᵉ Xᵉ Zᵉ
comp-equiv-cubeᵉ kᵉ Xᵉ Yᵉ Zᵉ (pairᵉ dim-fᵉ axis-fᵉ) (pairᵉ dim-eᵉ axis-eᵉ) =
  pairᵉ (dim-fᵉ ∘eᵉ dim-eᵉ) (λ dᵉ → axis-fᵉ (map-equivᵉ (dim-eᵉ) dᵉ) ∘eᵉ axis-eᵉ dᵉ)

htpy-equiv-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ Yᵉ : cubeᵉ kᵉ) (eᵉ fᵉ : equiv-cubeᵉ kᵉ Xᵉ Yᵉ) → UUᵉ lzero
htpy-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ fᵉ =
  Σᵉ ( map-dim-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ ~ᵉ map-dim-equiv-cubeᵉ kᵉ Xᵉ Yᵉ fᵉ)
    ( λ Hᵉ →
      ( dᵉ : dim-cubeᵉ kᵉ Xᵉ) →
      ( trᵉ (axis-cubeᵉ kᵉ Yᵉ) (Hᵉ dᵉ) ∘ᵉ map-axis-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ dᵉ) ~ᵉ
      ( map-axis-equiv-cubeᵉ kᵉ Xᵉ Yᵉ fᵉ dᵉ))

refl-htpy-equiv-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ Yᵉ : cubeᵉ kᵉ) (eᵉ : equiv-cubeᵉ kᵉ Xᵉ Yᵉ) → htpy-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ eᵉ
refl-htpy-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ = pairᵉ refl-htpyᵉ (λ dᵉ → refl-htpyᵉ)

htpy-eq-equiv-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ Yᵉ : cubeᵉ kᵉ) (eᵉ fᵉ : equiv-cubeᵉ kᵉ Xᵉ Yᵉ) →
  Idᵉ eᵉ fᵉ → htpy-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ fᵉ
htpy-eq-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ .eᵉ reflᵉ = refl-htpy-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ

is-torsorial-htpy-equiv-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ Yᵉ : cubeᵉ kᵉ) (eᵉ : equiv-cubeᵉ kᵉ Xᵉ Yᵉ) →
  is-torsorialᵉ (htpy-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ)
is-torsorial-htpy-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ =
  is-torsorial-Eq-structureᵉ

    ( is-torsorial-htpy-equivᵉ (dim-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ))
    ( pairᵉ (dim-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ) refl-htpyᵉ)
    ( is-torsorial-Eq-Πᵉ
      ( λ dᵉ → is-torsorial-htpy-equivᵉ (axis-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ dᵉ)))

is-equiv-htpy-eq-equiv-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ Yᵉ : cubeᵉ kᵉ) (eᵉ fᵉ : equiv-cubeᵉ kᵉ Xᵉ Yᵉ) →
  is-equivᵉ (htpy-eq-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ fᵉ)
is-equiv-htpy-eq-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ =
  fundamental-theorem-idᵉ
    ( is-torsorial-htpy-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ)
    ( htpy-eq-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ)

eq-htpy-equiv-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ Yᵉ : cubeᵉ kᵉ) (eᵉ fᵉ : equiv-cubeᵉ kᵉ Xᵉ Yᵉ) →
  htpy-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ fᵉ → Idᵉ eᵉ fᵉ
eq-htpy-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ fᵉ =
  map-inv-is-equivᵉ (is-equiv-htpy-eq-equiv-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ fᵉ)
```

### Labelings of cubes

```agda
labelling-cubeᵉ : (kᵉ : ℕᵉ) (Xᵉ : cubeᵉ kᵉ) → UUᵉ lzero
labelling-cubeᵉ kᵉ Xᵉ = equiv-cubeᵉ kᵉ (standard-cubeᵉ kᵉ) Xᵉ
```