# Equivalences between semigroups

```agda
module group-theory.equivalences-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-semigroupsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Anᵉ equivalenceᵉ betweenᵉ semigroupsᵉ isᵉ anᵉ equivalenceᵉ betweenᵉ theirᵉ underlyingᵉ
typesᵉ thatᵉ preservesᵉ theᵉ binaryᵉ operation.ᵉ

## Definition

### Equivalences preserving binary operations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  preserves-mul-equivᵉ :
    (μAᵉ : Aᵉ → Aᵉ → Aᵉ) (μBᵉ : Bᵉ → Bᵉ → Bᵉ) → (Aᵉ ≃ᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-mul-equivᵉ μAᵉ μBᵉ eᵉ = preserves-mulᵉ μAᵉ μBᵉ (map-equivᵉ eᵉ)
```

### Equivalences of semigroups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ)
  where

  preserves-mul-equiv-Semigroupᵉ :
    (type-Semigroupᵉ Gᵉ ≃ᵉ type-Semigroupᵉ Hᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-mul-equiv-Semigroupᵉ eᵉ =
    preserves-mul-equivᵉ (mul-Semigroupᵉ Gᵉ) (mul-Semigroupᵉ Hᵉ) eᵉ

  equiv-Semigroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-Semigroupᵉ =
    Σᵉ (type-Semigroupᵉ Gᵉ ≃ᵉ type-Semigroupᵉ Hᵉ) preserves-mul-equiv-Semigroupᵉ

  is-equiv-hom-Semigroupᵉ : hom-Semigroupᵉ Gᵉ Hᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-equiv-hom-Semigroupᵉ fᵉ = is-equivᵉ (map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ)
```

## Properties

### The total space of all equivalences of semigroups with domain `G` is contractible

```agda
module _
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ)
  where

  center-total-preserves-mul-id-Semigroupᵉ :
    Σᵉ ( has-associative-mulᵉ (type-Semigroupᵉ Gᵉ))
      ( λ μᵉ → preserves-mul-Semigroupᵉ Gᵉ (pairᵉ (set-Semigroupᵉ Gᵉ) μᵉ) idᵉ)
  pr1ᵉ (pr1ᵉ (center-total-preserves-mul-id-Semigroupᵉ)) = mul-Semigroupᵉ Gᵉ
  pr2ᵉ (pr1ᵉ (center-total-preserves-mul-id-Semigroupᵉ)) =
    associative-mul-Semigroupᵉ Gᵉ
  pr2ᵉ (center-total-preserves-mul-id-Semigroupᵉ) = reflᵉ

  contraction-total-preserves-mul-id-Semigroupᵉ :
    ( tᵉ : Σᵉ ( has-associative-mulᵉ (type-Semigroupᵉ Gᵉ))
            ( λ μᵉ →
              preserves-mul-Semigroupᵉ Gᵉ (pairᵉ (set-Semigroupᵉ Gᵉ) μᵉ) idᵉ)) →
    Idᵉ center-total-preserves-mul-id-Semigroupᵉ tᵉ
  contraction-total-preserves-mul-id-Semigroupᵉ
    ( (μ-G'ᵉ ,ᵉ associative-G'ᵉ) ,ᵉ μ-idᵉ) =
    eq-type-subtypeᵉ
      ( λ μᵉ →
        preserves-mul-prop-Semigroupᵉ Gᵉ (pairᵉ (set-Semigroupᵉ Gᵉ) μᵉ) idᵉ)
      ( eq-type-subtypeᵉ
        ( λ μᵉ →
          Π-Propᵉ
            ( type-Semigroupᵉ Gᵉ)
            ( λ xᵉ →
              Π-Propᵉ
                ( type-Semigroupᵉ Gᵉ)
                ( λ yᵉ →
                  Π-Propᵉ
                    ( type-Semigroupᵉ Gᵉ)
                    ( λ zᵉ →
                      Id-Propᵉ
                        ( set-Semigroupᵉ Gᵉ)
                        ( μᵉ (μᵉ xᵉ yᵉ) zᵉ) (μᵉ xᵉ (μᵉ yᵉ zᵉ))))))
        ( eq-htpyᵉ (λ xᵉ → eq-htpyᵉ (λ yᵉ → μ-idᵉ))))

  is-torsorial-preserves-mul-id-Semigroupᵉ :
    is-torsorialᵉ
      ( λ (μᵉ : has-associative-mulᵉ (type-Semigroupᵉ Gᵉ)) →
        preserves-mulᵉ (mul-Semigroupᵉ Gᵉ) (pr1ᵉ μᵉ) idᵉ)
  pr1ᵉ is-torsorial-preserves-mul-id-Semigroupᵉ =
    center-total-preserves-mul-id-Semigroupᵉ
  pr2ᵉ is-torsorial-preserves-mul-id-Semigroupᵉ =
    contraction-total-preserves-mul-id-Semigroupᵉ

  is-torsorial-equiv-Semigroupᵉ :
    is-torsorialᵉ (equiv-Semigroupᵉ Gᵉ)
  is-torsorial-equiv-Semigroupᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-Eq-subtypeᵉ
        ( is-torsorial-equivᵉ (type-Semigroupᵉ Gᵉ))
        ( is-prop-is-setᵉ)
        ( type-Semigroupᵉ Gᵉ)
        ( id-equivᵉ)
        ( is-set-type-Semigroupᵉ Gᵉ))
      ( pairᵉ (set-Semigroupᵉ Gᵉ) id-equivᵉ)
      ( is-torsorial-preserves-mul-id-Semigroupᵉ)
```