# Decidable equivalence relations on finite types

```agda
module univalent-combinatorics.decidable-equivalence-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.binary-relationsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-equivalence-relationsᵉ
open import foundation.decidable-relationsᵉ
open import foundation.decidable-typesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.cartesian-product-typesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.decidable-propositionsᵉ
open import univalent-combinatorics.dependent-function-typesᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.function-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
open import univalent-combinatorics.surjective-mapsᵉ
```

</details>

## Idea

Aᵉ **decidableᵉ equivalenceᵉ relation**ᵉ onᵉ aᵉ
[finiteᵉ type](univalent-combinatorics.finite-types.mdᵉ) isᵉ anᵉ
[equivalenceᵉ relation](foundation-core.equivalence-relations.mdᵉ) `R`ᵉ suchᵉ thatᵉ
eachᵉ `Rᵉ xᵉ y`ᵉ isᵉ aᵉ
[decidableᵉ proposition](foundation-core.decidable-propositions.md).ᵉ

## Definition

```agda
Decidable-equivalence-relation-𝔽ᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Xᵉ : 𝔽ᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Decidable-equivalence-relation-𝔽ᵉ l2ᵉ Xᵉ =
  Decidable-equivalence-relationᵉ l2ᵉ (type-𝔽ᵉ Xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Rᵉ : Decidable-equivalence-relation-𝔽ᵉ l2ᵉ Xᵉ)
  where

  decidable-relation-Decidable-equivalence-relation-𝔽ᵉ :
    Decidable-Relationᵉ l2ᵉ (type-𝔽ᵉ Xᵉ)
  decidable-relation-Decidable-equivalence-relation-𝔽ᵉ =
    decidable-relation-Decidable-equivalence-relationᵉ Rᵉ

  relation-Decidable-equivalence-relation-𝔽ᵉ :
    type-𝔽ᵉ Xᵉ → type-𝔽ᵉ Xᵉ → Propᵉ l2ᵉ
  relation-Decidable-equivalence-relation-𝔽ᵉ =
    relation-Decidable-equivalence-relationᵉ Rᵉ

  sim-Decidable-equivalence-relation-𝔽ᵉ : type-𝔽ᵉ Xᵉ → type-𝔽ᵉ Xᵉ → UUᵉ l2ᵉ
  sim-Decidable-equivalence-relation-𝔽ᵉ =
    sim-Decidable-equivalence-relationᵉ Rᵉ

  is-prop-sim-Decidable-equivalence-relation-𝔽ᵉ :
    (xᵉ yᵉ : type-𝔽ᵉ Xᵉ) → is-propᵉ (sim-Decidable-equivalence-relation-𝔽ᵉ xᵉ yᵉ)
  is-prop-sim-Decidable-equivalence-relation-𝔽ᵉ =
    is-prop-sim-Decidable-equivalence-relationᵉ Rᵉ

  is-decidable-sim-Decidable-equivalence-relation-𝔽ᵉ :
    (xᵉ yᵉ : type-𝔽ᵉ Xᵉ) → is-decidableᵉ (sim-Decidable-equivalence-relation-𝔽ᵉ xᵉ yᵉ)
  is-decidable-sim-Decidable-equivalence-relation-𝔽ᵉ =
    is-decidable-sim-Decidable-equivalence-relationᵉ Rᵉ

  is-equivalence-relation-Decidable-equivalence-relation-𝔽ᵉ :
    is-equivalence-relationᵉ relation-Decidable-equivalence-relation-𝔽ᵉ
  is-equivalence-relation-Decidable-equivalence-relation-𝔽ᵉ =
    is-equivalence-relation-Decidable-equivalence-relationᵉ Rᵉ

  equivalence-relation-Decidable-equivalence-relation-𝔽ᵉ :
    equivalence-relationᵉ l2ᵉ (type-𝔽ᵉ Xᵉ)
  equivalence-relation-Decidable-equivalence-relation-𝔽ᵉ =
    equivalence-relation-Decidable-equivalence-relationᵉ Rᵉ

  refl-Decidable-equivalence-relation-𝔽ᵉ :
    is-reflexiveᵉ sim-Decidable-equivalence-relation-𝔽ᵉ
  refl-Decidable-equivalence-relation-𝔽ᵉ =
    refl-Decidable-equivalence-relationᵉ Rᵉ

  symmetric-Decidable-equivalence-relation-𝔽ᵉ :
    is-symmetricᵉ sim-Decidable-equivalence-relation-𝔽ᵉ
  symmetric-Decidable-equivalence-relation-𝔽ᵉ =
    symmetric-Decidable-equivalence-relationᵉ Rᵉ

  transitive-Decidable-equivalence-relation-𝔽ᵉ :
    is-transitiveᵉ sim-Decidable-equivalence-relation-𝔽ᵉ
  transitive-Decidable-equivalence-relation-𝔽ᵉ =
    transitive-Decidable-equivalence-relationᵉ Rᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) (Rᵉ : Decidable-Relationᵉ l2ᵉ (type-𝔽ᵉ Aᵉ))
  where

  is-finite-relation-Decidable-Relation-𝔽ᵉ :
    (xᵉ : type-𝔽ᵉ Aᵉ) → (yᵉ : type-𝔽ᵉ Aᵉ) → is-finiteᵉ (rel-Decidable-Relationᵉ Rᵉ xᵉ yᵉ)
  is-finite-relation-Decidable-Relation-𝔽ᵉ xᵉ yᵉ =
    unit-trunc-Propᵉ
      ( count-Decidable-Propᵉ
        ( relation-Decidable-Relationᵉ Rᵉ xᵉ yᵉ)
        ( is-decidable-Decidable-Relationᵉ Rᵉ xᵉ yᵉ))

  is-finite-is-reflexive-Dec-Relation-Prop-𝔽ᵉ :
    is-finiteᵉ (is-reflexive-Relation-Propᵉ (relation-Decidable-Relationᵉ Rᵉ))
  is-finite-is-reflexive-Dec-Relation-Prop-𝔽ᵉ =
    is-finite-Πᵉ
      ( is-finite-type-𝔽ᵉ Aᵉ)
      (λ xᵉ → is-finite-relation-Decidable-Relation-𝔽ᵉ xᵉ xᵉ)

  is-finite-is-symmetric-Dec-Relation-Prop-𝔽ᵉ :
    is-finiteᵉ (is-symmetric-Relation-Propᵉ (relation-Decidable-Relationᵉ Rᵉ))
  is-finite-is-symmetric-Dec-Relation-Prop-𝔽ᵉ =
    is-finite-Πᵉ
      ( is-finite-type-𝔽ᵉ Aᵉ)
      ( λ xᵉ →
        is-finite-Πᵉ
          ( is-finite-type-𝔽ᵉ Aᵉ)
          ( λ yᵉ →
            is-finite-function-typeᵉ
              ( is-finite-relation-Decidable-Relation-𝔽ᵉ xᵉ yᵉ)
              ( is-finite-relation-Decidable-Relation-𝔽ᵉ yᵉ xᵉ)))

  is-finite-is-transitive-Dec-Relation-Prop-𝔽ᵉ :
    is-finiteᵉ (is-transitive-Relation-Propᵉ (relation-Decidable-Relationᵉ Rᵉ))
  is-finite-is-transitive-Dec-Relation-Prop-𝔽ᵉ =
    is-finite-Πᵉ
      ( is-finite-type-𝔽ᵉ Aᵉ)
      ( λ xᵉ →
        is-finite-Πᵉ
          ( is-finite-type-𝔽ᵉ Aᵉ)
          ( λ yᵉ →
            is-finite-Πᵉ
              ( is-finite-type-𝔽ᵉ Aᵉ)
              ( λ zᵉ →
                is-finite-function-typeᵉ
                  ( is-finite-relation-Decidable-Relation-𝔽ᵉ yᵉ zᵉ)
                  ( is-finite-function-typeᵉ
                    ( is-finite-relation-Decidable-Relation-𝔽ᵉ xᵉ yᵉ)
                    ( is-finite-relation-Decidable-Relation-𝔽ᵉ xᵉ zᵉ)))))

  is-finite-is-equivalence-Dec-Relation-Prop-𝔽ᵉ :
    is-finiteᵉ (is-equivalence-relationᵉ (relation-Decidable-Relationᵉ Rᵉ))
  is-finite-is-equivalence-Dec-Relation-Prop-𝔽ᵉ =
    is-finite-productᵉ
      ( is-finite-is-reflexive-Dec-Relation-Prop-𝔽ᵉ)
      ( is-finite-productᵉ
          is-finite-is-symmetric-Dec-Relation-Prop-𝔽ᵉ
          is-finite-is-transitive-Dec-Relation-Prop-𝔽ᵉ)
```

## Properties

#### The type of decidable equivalence relations on `A` is equivalent to the type of surjections from `A` into a finite type

```agda
equiv-Surjection-𝔽-Decidable-equivalence-relation-𝔽ᵉ :
  {l1ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) →
  Decidable-equivalence-relation-𝔽ᵉ l1ᵉ Aᵉ ≃ᵉ
  Surjection-𝔽ᵉ l1ᵉ Aᵉ
equiv-Surjection-𝔽-Decidable-equivalence-relation-𝔽ᵉ {l1ᵉ} Aᵉ =
  ( equiv-Σ-equiv-baseᵉ
      ( λ Xᵉ → (type-𝔽ᵉ Aᵉ) ↠ᵉ (type-𝔽ᵉ Xᵉ))
      ( equiv-Σᵉ
          ( is-finiteᵉ)
          ( id-equivᵉ)
          ( λ Xᵉ →
            inv-equivᵉ is-finite-iff-∃-surjection-has-decidable-equalityᵉ)) ∘eᵉ
    ( ( inv-associative-Σᵉ
          ( UUᵉ l1ᵉ)
          ( λ Xᵉ →
              has-decidable-equalityᵉ Xᵉ ×ᵉ
              type-trunc-Propᵉ (Σᵉ ℕᵉ (λ nᵉ → Finᵉ nᵉ ↠ᵉ Xᵉ)))
          ( λ Xᵉ → type-𝔽ᵉ Aᵉ ↠ᵉ pr1ᵉ Xᵉ)) ∘eᵉ
      ( ( equiv-Σᵉ
            (λ Xᵉ →
                Σᵉ ( has-decidable-equalityᵉ Xᵉ ×ᵉ
                    type-trunc-Propᵉ (Σᵉ ℕᵉ (λ nᵉ → Finᵉ nᵉ ↠ᵉ Xᵉ)))
                  ( λ _ → pr1ᵉ Aᵉ ↠ᵉ Xᵉ))
            ( id-equivᵉ)
            ( λ Xᵉ →
              ( ( inv-equivᵉ
                  ( associative-productᵉ
                    ( has-decidable-equalityᵉ Xᵉ)
                    ( type-trunc-Propᵉ (Σᵉ ℕᵉ (λ nᵉ → Finᵉ nᵉ ↠ᵉ Xᵉ)))
                    ( type-𝔽ᵉ Aᵉ ↠ᵉ Xᵉ))) ∘eᵉ
                ( ( equiv-productᵉ id-equivᵉ commutative-productᵉ) ∘eᵉ
                  ( ( associative-productᵉ
                      ( has-decidable-equalityᵉ (map-equivᵉ id-equivᵉ Xᵉ))
                      ( type-𝔽ᵉ Aᵉ ↠ᵉ Xᵉ)
                      ( type-trunc-Propᵉ (Σᵉ ℕᵉ (λ nᵉ → Finᵉ nᵉ ↠ᵉ Xᵉ)))) ∘eᵉ
                  ( ( equiv-productᵉ commutative-productᵉ id-equivᵉ) ∘eᵉ
                    ( ( equiv-add-redundant-propᵉ
                        ( is-prop-type-trunc-Propᵉ)
                        ( λ xᵉ →
                          apply-universal-property-trunc-Propᵉ
                            ( is-finite-type-𝔽ᵉ Aᵉ)
                            ( trunc-Propᵉ ( Σᵉ ℕᵉ (λ nᵉ → Finᵉ nᵉ ↠ᵉ Xᵉ)))
                            ( λ count-Aᵉ →
                              unit-trunc-Propᵉ
                                ( number-of-elements-countᵉ count-Aᵉ ,ᵉ
                                  ( ( map-surjectionᵉ (pr1ᵉ xᵉ) ∘ᵉ
                                      map-equiv-countᵉ count-Aᵉ) ,ᵉ
                                    is-surjective-precomp-equivᵉ
                                      ( is-surjective-map-surjectionᵉ (pr1ᵉ xᵉ))
                                      ( equiv-countᵉ count-Aᵉ)))))))))))) ∘eᵉ
        ( equiv-Surjection-Into-Set-Decidable-equivalence-relationᵉ
          ( type-𝔽ᵉ Aᵉ))))))
```

### The type of decidable equivalence relations on a finite type is finite

```agda
is-finite-Decidable-Relation-𝔽ᵉ :
  {l1ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) →
  is-finiteᵉ (Decidable-Relationᵉ l1ᵉ (type-𝔽ᵉ Aᵉ))
is-finite-Decidable-Relation-𝔽ᵉ Aᵉ =
  is-finite-Πᵉ
    ( is-finite-type-𝔽ᵉ Aᵉ)
    ( λ aᵉ →
      is-finite-Πᵉ
        ( is-finite-type-𝔽ᵉ Aᵉ)
        ( λ bᵉ → is-finite-Decidable-Propᵉ))

is-finite-Decidable-equivalence-relation-𝔽ᵉ :
  {l1ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) →
  is-finiteᵉ (Decidable-equivalence-relation-𝔽ᵉ l1ᵉ Aᵉ)
is-finite-Decidable-equivalence-relation-𝔽ᵉ Aᵉ =
  is-finite-Σᵉ
    ( is-finite-Decidable-Relation-𝔽ᵉ Aᵉ)
    ( is-finite-is-equivalence-Dec-Relation-Prop-𝔽ᵉ Aᵉ)
```

### The number of decidable equivalence relations on a finite type is a Stirling number of the second kind

Thisᵉ remainsᵉ to beᵉ characterized.ᵉ
[#745](https://github.com/UniMath/agda-unimath/issues/745ᵉ)