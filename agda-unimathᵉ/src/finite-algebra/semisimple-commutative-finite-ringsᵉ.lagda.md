# Semisimple commutative finite rings

```agda
module finite-algebra.semisimple-commutative-finite-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import finite-algebra.commutative-finite-ringsᵉ
open import finite-algebra.dependent-products-commutative-finite-ringsᵉ
open import finite-algebra.finite-fieldsᵉ
open import finite-algebra.homomorphisms-commutative-finite-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ **semisimpleᵉ commutativeᵉ finiteᵉ rings**ᵉ isᵉ aᵉ commutativeᵉ finieᵉ ringsᵉ wichᵉ isᵉ
merelyᵉ equivalentᵉ to anᵉ iteratedᵉ cartesianᵉ productᵉ ofᵉ finiteᵉ fields.ᵉ

## Definitions

### Semisimple commutative finite rings

```agda
is-semisimple-Commutative-Ring-𝔽ᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → Commutative-Ring-𝔽ᵉ l1ᵉ →
  UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
is-semisimple-Commutative-Ring-𝔽ᵉ l2ᵉ Rᵉ =
  existsᵉ
    ( ℕᵉ)
    ( λ nᵉ →
      ∃ᵉ ( Finᵉ nᵉ → Field-𝔽ᵉ l2ᵉ)
        ( λ Aᵉ →
          trunc-Propᵉ
            ( hom-Commutative-Ring-𝔽ᵉ
              ( Rᵉ)
              ( Π-Commutative-Ring-𝔽ᵉ
                ( Finᵉ nᵉ ,ᵉ is-finite-Finᵉ nᵉ)
                ( commutative-finite-ring-Field-𝔽ᵉ ∘ᵉ Aᵉ)))))

Semisimple-Commutative-Ring-𝔽ᵉ :
  (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Semisimple-Commutative-Ring-𝔽ᵉ l1ᵉ l2ᵉ =
  Σᵉ (Commutative-Ring-𝔽ᵉ l1ᵉ) (is-semisimple-Commutative-Ring-𝔽ᵉ l2ᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Semisimple-Commutative-Ring-𝔽ᵉ l1ᵉ l2ᵉ)
  where

  commutative-finite-ring-Semisimple-Commutative-Ring-𝔽ᵉ :
    Commutative-Ring-𝔽ᵉ l1ᵉ
  commutative-finite-ring-Semisimple-Commutative-Ring-𝔽ᵉ = pr1ᵉ Aᵉ
```

## Properties

### The number of ways to equip a finite type with the structure of a semisimple commutative ring is finite

```agda
module _
  {l1ᵉ : Level}
  (l2ᵉ : Level)
  (Xᵉ : 𝔽ᵉ l1ᵉ)
  where

  structure-semisimple-commutative-ring-𝔽ᵉ :
    UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  structure-semisimple-commutative-ring-𝔽ᵉ =
    Σᵉ ( structure-commutative-ring-𝔽ᵉ Xᵉ)
      ( λ rᵉ →
        is-semisimple-Commutative-Ring-𝔽ᵉ
          ( l2ᵉ)
          ( finite-commutative-ring-structure-commutative-ring-𝔽ᵉ Xᵉ rᵉ))

  finite-semisimple-commutative-ring-structure-semisimple-commutative-ring-𝔽ᵉ :
    structure-semisimple-commutative-ring-𝔽ᵉ →
    Semisimple-Commutative-Ring-𝔽ᵉ l1ᵉ l2ᵉ
  finite-semisimple-commutative-ring-structure-semisimple-commutative-ring-𝔽ᵉ =
    map-Σ-map-baseᵉ
      ( finite-commutative-ring-structure-commutative-ring-𝔽ᵉ Xᵉ)
      ( is-semisimple-Commutative-Ring-𝔽ᵉ l2ᵉ)
```