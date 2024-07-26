# Homomorphisms of semigroups

```agda
module group-theory.homomorphisms-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.semigroupsᵉ
```

</details>

## Idea

Aᵉ homomorphismᵉ betweenᵉ twoᵉ semigroupsᵉ isᵉ aᵉ mapᵉ betweenᵉ theirᵉ underlyingᵉ typesᵉ
thatᵉ preservesᵉ theᵉ binaryᵉ operation.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  preserves-mulᵉ : (μAᵉ : Aᵉ → Aᵉ → Aᵉ) (μBᵉ : Bᵉ → Bᵉ → Bᵉ) → (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-mulᵉ μAᵉ μBᵉ fᵉ = {xᵉ yᵉ : Aᵉ} → fᵉ (μAᵉ xᵉ yᵉ) ＝ᵉ μBᵉ (fᵉ xᵉ) (fᵉ yᵉ)

  preserves-mul'ᵉ : (μAᵉ : Aᵉ → Aᵉ → Aᵉ) (μBᵉ : Bᵉ → Bᵉ → Bᵉ) → (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-mul'ᵉ μAᵉ μBᵉ fᵉ = (xᵉ yᵉ : Aᵉ) → fᵉ (μAᵉ xᵉ yᵉ) ＝ᵉ μBᵉ (fᵉ xᵉ) (fᵉ yᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ)
  where

  preserves-mul-prop-Semigroupᵉ :
    (type-Semigroupᵉ Gᵉ → type-Semigroupᵉ Hᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-mul-prop-Semigroupᵉ fᵉ =
    implicit-Π-Propᵉ
      ( type-Semigroupᵉ Gᵉ)
      ( λ xᵉ →
        implicit-Π-Propᵉ
          ( type-Semigroupᵉ Gᵉ)
          ( λ yᵉ →
            Id-Propᵉ
              ( set-Semigroupᵉ Hᵉ)
              ( fᵉ (mul-Semigroupᵉ Gᵉ xᵉ yᵉ))
              ( mul-Semigroupᵉ Hᵉ (fᵉ xᵉ) (fᵉ yᵉ))))

  preserves-mul-prop-Semigroup'ᵉ :
    (type-Semigroupᵉ Gᵉ → type-Semigroupᵉ Hᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-mul-prop-Semigroup'ᵉ fᵉ =
    implicit-Π-Propᵉ
      ( type-Semigroupᵉ Gᵉ)
      ( λ xᵉ →
        implicit-Π-Propᵉ
          ( type-Semigroupᵉ Gᵉ)
          ( λ yᵉ →
            Id-Propᵉ
              ( set-Semigroupᵉ Hᵉ)
              ( fᵉ (mul-Semigroup'ᵉ Gᵉ xᵉ yᵉ))
              ( mul-Semigroupᵉ Hᵉ (fᵉ xᵉ) (fᵉ yᵉ))))

  preserves-mul-Semigroupᵉ :
    (type-Semigroupᵉ Gᵉ → type-Semigroupᵉ Hᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-mul-Semigroupᵉ fᵉ =
    type-Propᵉ (preserves-mul-prop-Semigroupᵉ fᵉ)

  preserves-mul-Semigroup'ᵉ :
    (type-Semigroupᵉ Gᵉ → type-Semigroupᵉ Hᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-mul-Semigroup'ᵉ fᵉ =
    type-Propᵉ (preserves-mul-prop-Semigroup'ᵉ fᵉ)

  is-prop-preserves-mul-Semigroupᵉ :
    (fᵉ : type-Semigroupᵉ Gᵉ → type-Semigroupᵉ Hᵉ) →
    is-propᵉ (preserves-mul-Semigroupᵉ fᵉ)
  is-prop-preserves-mul-Semigroupᵉ fᵉ =
    is-prop-type-Propᵉ (preserves-mul-prop-Semigroupᵉ fᵉ)

  is-prop-preserves-mul-Semigroup'ᵉ :
    (fᵉ : type-Semigroupᵉ Gᵉ → type-Semigroupᵉ Hᵉ) →
    is-propᵉ (preserves-mul-Semigroup'ᵉ fᵉ)
  is-prop-preserves-mul-Semigroup'ᵉ fᵉ =
    is-prop-type-Propᵉ (preserves-mul-prop-Semigroup'ᵉ fᵉ)

  hom-Semigroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Semigroupᵉ =
    Σᵉ ( type-Semigroupᵉ Gᵉ → type-Semigroupᵉ Hᵉ)
      ( preserves-mul-Semigroupᵉ)

  map-hom-Semigroupᵉ :
    hom-Semigroupᵉ → type-Semigroupᵉ Gᵉ → type-Semigroupᵉ Hᵉ
  map-hom-Semigroupᵉ fᵉ = pr1ᵉ fᵉ

  preserves-mul-hom-Semigroupᵉ :
    (fᵉ : hom-Semigroupᵉ) → preserves-mul-Semigroupᵉ (map-hom-Semigroupᵉ fᵉ)
  preserves-mul-hom-Semigroupᵉ fᵉ = pr2ᵉ fᵉ
```

### Characterizing the identity type of semigroup homomorphisms

```agda
  htpy-hom-Semigroupᵉ : (fᵉ gᵉ : hom-Semigroupᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-Semigroupᵉ fᵉ gᵉ = map-hom-Semigroupᵉ fᵉ ~ᵉ map-hom-Semigroupᵉ gᵉ

  refl-htpy-hom-Semigroupᵉ : (fᵉ : hom-Semigroupᵉ) → htpy-hom-Semigroupᵉ fᵉ fᵉ
  refl-htpy-hom-Semigroupᵉ fᵉ = refl-htpyᵉ

  htpy-eq-hom-Semigroupᵉ :
    (fᵉ gᵉ : hom-Semigroupᵉ) → Idᵉ fᵉ gᵉ → htpy-hom-Semigroupᵉ fᵉ gᵉ
  htpy-eq-hom-Semigroupᵉ fᵉ .fᵉ reflᵉ = refl-htpy-hom-Semigroupᵉ fᵉ

  abstract
    is-torsorial-htpy-hom-Semigroupᵉ :
      (fᵉ : hom-Semigroupᵉ) → is-torsorialᵉ (htpy-hom-Semigroupᵉ fᵉ)
    is-torsorial-htpy-hom-Semigroupᵉ fᵉ =
      is-torsorial-Eq-subtypeᵉ
        ( is-torsorial-htpyᵉ (map-hom-Semigroupᵉ fᵉ))
        ( is-prop-preserves-mul-Semigroupᵉ)
        ( map-hom-Semigroupᵉ fᵉ)
        ( refl-htpyᵉ)
        ( preserves-mul-hom-Semigroupᵉ fᵉ)

  abstract
    is-equiv-htpy-eq-hom-Semigroupᵉ :
      (fᵉ gᵉ : hom-Semigroupᵉ) → is-equivᵉ (htpy-eq-hom-Semigroupᵉ fᵉ gᵉ)
    is-equiv-htpy-eq-hom-Semigroupᵉ fᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-htpy-hom-Semigroupᵉ fᵉ)
        ( htpy-eq-hom-Semigroupᵉ fᵉ)

  eq-htpy-hom-Semigroupᵉ :
    {fᵉ gᵉ : hom-Semigroupᵉ} → htpy-hom-Semigroupᵉ fᵉ gᵉ → Idᵉ fᵉ gᵉ
  eq-htpy-hom-Semigroupᵉ {fᵉ} {gᵉ} =
    map-inv-is-equivᵉ (is-equiv-htpy-eq-hom-Semigroupᵉ fᵉ gᵉ)

  is-set-hom-Semigroupᵉ : is-setᵉ hom-Semigroupᵉ
  is-set-hom-Semigroupᵉ fᵉ gᵉ =
    is-prop-is-equivᵉ
      ( is-equiv-htpy-eq-hom-Semigroupᵉ fᵉ gᵉ)
      ( is-prop-Πᵉ
        ( λ xᵉ →
          is-set-type-Semigroupᵉ Hᵉ
            ( map-hom-Semigroupᵉ fᵉ xᵉ)
            ( map-hom-Semigroupᵉ gᵉ xᵉ)))

  hom-set-Semigroupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ hom-set-Semigroupᵉ = hom-Semigroupᵉ
  pr2ᵉ hom-set-Semigroupᵉ = is-set-hom-Semigroupᵉ

preserves-mul-id-Semigroupᵉ :
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ) → preserves-mul-Semigroupᵉ Gᵉ Gᵉ idᵉ
preserves-mul-id-Semigroupᵉ Gᵉ = reflᵉ
```

### The identity homomorphism of semigroups

```agda
id-hom-Semigroupᵉ :
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ) → hom-Semigroupᵉ Gᵉ Gᵉ
pr1ᵉ (id-hom-Semigroupᵉ Gᵉ) = idᵉ
pr2ᵉ (id-hom-Semigroupᵉ Gᵉ) = preserves-mul-id-Semigroupᵉ Gᵉ
```

### Composition of morphisms of semigroups

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ) (Kᵉ : Semigroupᵉ l3ᵉ)
  (gᵉ : hom-Semigroupᵉ Hᵉ Kᵉ) (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ)
  where

  map-comp-hom-Semigroupᵉ : type-Semigroupᵉ Gᵉ → type-Semigroupᵉ Kᵉ
  map-comp-hom-Semigroupᵉ =
    (map-hom-Semigroupᵉ Hᵉ Kᵉ gᵉ) ∘ᵉ (map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ)

  preserves-mul-comp-hom-Semigroupᵉ :
    preserves-mul-Semigroupᵉ Gᵉ Kᵉ map-comp-hom-Semigroupᵉ
  preserves-mul-comp-hom-Semigroupᵉ =
    ( apᵉ
      ( map-hom-Semigroupᵉ Hᵉ Kᵉ gᵉ)
      ( preserves-mul-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ)) ∙ᵉ
    ( preserves-mul-hom-Semigroupᵉ Hᵉ Kᵉ gᵉ)

  comp-hom-Semigroupᵉ : hom-Semigroupᵉ Gᵉ Kᵉ
  pr1ᵉ comp-hom-Semigroupᵉ = map-comp-hom-Semigroupᵉ
  pr2ᵉ comp-hom-Semigroupᵉ = preserves-mul-comp-hom-Semigroupᵉ
```

### Associativity of composition of homomorphisms of semigroups

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ) (Kᵉ : Semigroupᵉ l3ᵉ) (Lᵉ : Semigroupᵉ l4ᵉ)
  (hᵉ : hom-Semigroupᵉ Kᵉ Lᵉ) (gᵉ : hom-Semigroupᵉ Hᵉ Kᵉ) (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ)
  where

  associative-comp-hom-Semigroupᵉ :
    comp-hom-Semigroupᵉ Gᵉ Hᵉ Lᵉ (comp-hom-Semigroupᵉ Hᵉ Kᵉ Lᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Semigroupᵉ Gᵉ Kᵉ Lᵉ hᵉ (comp-hom-Semigroupᵉ Gᵉ Hᵉ Kᵉ gᵉ fᵉ)
  associative-comp-hom-Semigroupᵉ = eq-htpy-hom-Semigroupᵉ Gᵉ Lᵉ refl-htpyᵉ
```

### The left and right unit laws for composition of homomorphisms of semigroups

```agda
left-unit-law-comp-hom-Semigroupᵉ :
  { l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ)
  ( fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ) →
  Idᵉ ( comp-hom-Semigroupᵉ Gᵉ Hᵉ Hᵉ (id-hom-Semigroupᵉ Hᵉ) fᵉ) fᵉ
left-unit-law-comp-hom-Semigroupᵉ Gᵉ
  (pairᵉ (pairᵉ Hᵉ is-set-Hᵉ) (pairᵉ μ-Hᵉ associative-Hᵉ)) (pairᵉ fᵉ μ-fᵉ) =
  eq-htpy-hom-Semigroupᵉ Gᵉ
    ( pairᵉ (pairᵉ Hᵉ is-set-Hᵉ) (pairᵉ μ-Hᵉ associative-Hᵉ))
    ( refl-htpyᵉ)

right-unit-law-comp-hom-Semigroupᵉ :
  { l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ)
  ( fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ) →
  Idᵉ ( comp-hom-Semigroupᵉ Gᵉ Gᵉ Hᵉ fᵉ (id-hom-Semigroupᵉ Gᵉ)) fᵉ
right-unit-law-comp-hom-Semigroupᵉ
  (pairᵉ (pairᵉ Gᵉ is-set-Gᵉ) (pairᵉ μ-Gᵉ associative-Gᵉ)) Hᵉ (pairᵉ fᵉ μ-fᵉ) =
  eq-htpy-hom-Semigroupᵉ
    ( pairᵉ (pairᵉ Gᵉ is-set-Gᵉ) (pairᵉ μ-Gᵉ associative-Gᵉ)) Hᵉ refl-htpyᵉ
```