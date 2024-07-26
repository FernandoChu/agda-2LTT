# Equivalences of inverse sequential diagrams of types

```agda
module foundation.equivalences-inverse-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.inverse-sequential-diagramsᵉ
open import foundation.morphisms-inverse-sequential-diagramsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Anᵉ
{{#conceptᵉ "equivalenceᵉ ofᵉ inverseᵉ sequentialᵉ diagrams"ᵉ Agda=equiv-inverse-sequential-diagramᵉ}}
`Aᵉ ≃ᵉ B`ᵉ isᵉ aᵉ commutingᵉ diagramᵉ ofᵉ theᵉ formᵉ

```text
  ⋯ᵉ ---->ᵉ Aₙ₊₁ᵉ ---->ᵉ Aₙᵉ ---->ᵉ ⋯ᵉ ---->ᵉ A₁ᵉ ---->ᵉ A₀ᵉ
           |         |       |       |        |
  ⋯ᵉ        |         |       ⋯ᵉ       |        |
           ∨ᵉ         ∨ᵉ       ∨ᵉ       ∨ᵉ        ∨ᵉ
  ⋯ᵉ ---->ᵉ Bₙ₊₁ᵉ ---->ᵉ Bₙᵉ ---->ᵉ ⋯ᵉ ---->ᵉ B₁ᵉ ---->ᵉ B₀.ᵉ
```

where everyᵉ verticalᵉ mapᵉ isᵉ anᵉ [equivalence](foundation-core.equivalences.md).ᵉ

## Definitions

```agda
equiv-inverse-sequential-diagramᵉ :
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ)
  (Bᵉ : inverse-sequential-diagramᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
equiv-inverse-sequential-diagramᵉ Aᵉ Bᵉ =
  Σᵉ ( (nᵉ : ℕᵉ) →
      family-inverse-sequential-diagramᵉ Aᵉ nᵉ ≃ᵉ
      family-inverse-sequential-diagramᵉ Bᵉ nᵉ)
    ( λ eᵉ →
      (nᵉ : ℕᵉ) → naturality-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ (map-equivᵉ ∘ᵉ eᵉ) nᵉ)

hom-equiv-inverse-sequential-diagramᵉ :
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ)
  (Bᵉ : inverse-sequential-diagramᵉ l2ᵉ) →
  equiv-inverse-sequential-diagramᵉ Aᵉ Bᵉ →
  hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ
pr1ᵉ (hom-equiv-inverse-sequential-diagramᵉ Aᵉ Bᵉ eᵉ) nᵉ = pr1ᵉ (pr1ᵉ eᵉ nᵉ)
pr2ᵉ (hom-equiv-inverse-sequential-diagramᵉ Aᵉ Bᵉ eᵉ) = pr2ᵉ eᵉ
```

## Properties

### Characterizing equality of inverse sequential diagrams

```agda
id-equiv-inverse-sequential-diagramᵉ :
  {lᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ lᵉ) →
  equiv-inverse-sequential-diagramᵉ Aᵉ Aᵉ
pr1ᵉ (id-equiv-inverse-sequential-diagramᵉ Aᵉ) nᵉ = id-equivᵉ
pr2ᵉ (id-equiv-inverse-sequential-diagramᵉ Aᵉ) nᵉ = refl-htpyᵉ

equiv-eq-inverse-sequential-diagramᵉ :
  {lᵉ : Level} (Aᵉ Bᵉ : inverse-sequential-diagramᵉ lᵉ) →
  Aᵉ ＝ᵉ Bᵉ → equiv-inverse-sequential-diagramᵉ Aᵉ Bᵉ
equiv-eq-inverse-sequential-diagramᵉ Aᵉ .Aᵉ reflᵉ =
  id-equiv-inverse-sequential-diagramᵉ Aᵉ

is-torsorial-equiv-inverse-sequential-diagramᵉ :
  {lᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ lᵉ) →
  is-torsorialᵉ (equiv-inverse-sequential-diagramᵉ Aᵉ)
is-torsorial-equiv-inverse-sequential-diagramᵉ Aᵉ =
  is-torsorial-Eq-structureᵉ
    ( is-torsorial-Eq-Πᵉ
      ( λ nᵉ → is-torsorial-equivᵉ (family-inverse-sequential-diagramᵉ Aᵉ nᵉ)))
    ( family-inverse-sequential-diagramᵉ Aᵉ ,ᵉ λ nᵉ → id-equivᵉ)
    ( is-torsorial-Eq-Πᵉ
      ( λ nᵉ → is-torsorial-htpyᵉ (map-inverse-sequential-diagramᵉ Aᵉ nᵉ)))

is-equiv-equiv-eq-inverse-sequential-diagramᵉ :
  {lᵉ : Level} (Aᵉ Bᵉ : inverse-sequential-diagramᵉ lᵉ) →
  is-equivᵉ (equiv-eq-inverse-sequential-diagramᵉ Aᵉ Bᵉ)
is-equiv-equiv-eq-inverse-sequential-diagramᵉ Aᵉ =
  fundamental-theorem-idᵉ
    ( is-torsorial-equiv-inverse-sequential-diagramᵉ Aᵉ)
    ( equiv-eq-inverse-sequential-diagramᵉ Aᵉ)

eq-equiv-inverse-sequential-diagramᵉ :
  {lᵉ : Level} {Aᵉ Bᵉ : inverse-sequential-diagramᵉ lᵉ} →
  equiv-inverse-sequential-diagramᵉ Aᵉ Bᵉ → Aᵉ ＝ᵉ Bᵉ
eq-equiv-inverse-sequential-diagramᵉ {Aᵉ = Aᵉ} {Bᵉ} =
  map-inv-is-equivᵉ (is-equiv-equiv-eq-inverse-sequential-diagramᵉ Aᵉ Bᵉ)
```

## Table of files about sequential limits

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ sequentialᵉ limitsᵉ asᵉ aᵉ generalᵉ
concept.ᵉ

{{#includeᵉ tables/sequential-limits.mdᵉ}}