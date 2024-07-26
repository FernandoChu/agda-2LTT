# The groupoid of main classes of Latin hypercubes

```agda
module univalent-combinatorics.main-classes-of-latin-hypercubesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.contractible-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.products-unordered-tuples-of-typesᵉ
open import foundation.set-truncationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-tuplesᵉ

open import univalent-combinatorics.complements-isolated-elementsᵉ
open import univalent-combinatorics.decidable-subtypesᵉ
open import univalent-combinatorics.dependent-function-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.pi-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Definition

```agda
Main-Class-Latin-Hypercubeᵉ : (l1ᵉ l2ᵉ : Level) (nᵉ : ℕᵉ) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Main-Class-Latin-Hypercubeᵉ l1ᵉ l2ᵉ nᵉ =
  Σᵉ ( unordered-tupleᵉ (succ-ℕᵉ nᵉ) (Inhabited-Typeᵉ l1ᵉ))
    ( λ Aᵉ →
      Σᵉ ( product-unordered-tuple-typesᵉ (succ-ℕᵉ nᵉ)
          ( map-unordered-tupleᵉ (succ-ℕᵉ nᵉ) type-Inhabited-Typeᵉ Aᵉ) → UUᵉ l2ᵉ)
        ( λ Rᵉ →
          ( iᵉ : type-unordered-tupleᵉ (succ-ℕᵉ nᵉ) Aᵉ)
          ( fᵉ : product-unordered-tuple-typesᵉ nᵉ
                ( unordered-tuple-complement-point-type-unordered-tupleᵉ nᵉ
                  ( map-unordered-tupleᵉ (succ-ℕᵉ nᵉ) type-Inhabited-Typeᵉ Aᵉ)
                  ( iᵉ))) →
          is-contrᵉ
            ( Σᵉ ( type-Inhabited-Typeᵉ (element-unordered-tupleᵉ (succ-ℕᵉ nᵉ) Aᵉ iᵉ))
                ( λ aᵉ →
                  Rᵉ ( map-equiv-pr-product-unordered-tuple-typesᵉ nᵉ
                      ( map-unordered-tupleᵉ (succ-ℕᵉ nᵉ) type-Inhabited-Typeᵉ Aᵉ)
                      ( iᵉ)
                      ( fᵉ)
                      ( aᵉ))))))
```

### The groupoid of main classes of Latin hypercubes of fixed finite order

```agda
Main-Class-Latin-Hypercube-of-Orderᵉ : (nᵉ mᵉ : ℕᵉ) → UUᵉ (lsuc lzero)
Main-Class-Latin-Hypercube-of-Orderᵉ nᵉ mᵉ =
  Σᵉ ( unordered-tupleᵉ (succ-ℕᵉ nᵉ) (UU-Finᵉ lzero mᵉ))
    ( λ Aᵉ →
      Σᵉ ( product-unordered-tuple-typesᵉ (succ-ℕᵉ nᵉ)
          ( map-unordered-tupleᵉ (succ-ℕᵉ nᵉ) (type-UU-Finᵉ mᵉ) Aᵉ) →
          Decidable-Propᵉ lzero)
        ( λ Rᵉ →
          (iᵉ : type-unordered-tupleᵉ (succ-ℕᵉ nᵉ) Aᵉ)
          (fᵉ :
            product-unordered-tuple-typesᵉ nᵉ
              ( unordered-tuple-complement-point-type-unordered-tupleᵉ nᵉ
                ( map-unordered-tupleᵉ (succ-ℕᵉ nᵉ) (type-UU-Finᵉ mᵉ) Aᵉ)
                ( iᵉ))) →
          is-contrᵉ
            ( Σᵉ ( type-UU-Finᵉ mᵉ (element-unordered-tupleᵉ (succ-ℕᵉ nᵉ) Aᵉ iᵉ))
                ( λ aᵉ →
                  type-Decidable-Propᵉ
                    ( Rᵉ ( map-equiv-pr-product-unordered-tuple-typesᵉ nᵉ
                          ( map-unordered-tupleᵉ (succ-ℕᵉ nᵉ) (type-UU-Finᵉ mᵉ) Aᵉ)
                          ( iᵉ)
                          ( fᵉ)
                          ( aᵉ)))))))
```

## Properties

### The groupoid of main classes of Latin hypercubes of finite order is π-finite

```agda
is-π-finite-Main-Class-Latin-Hypercube-of-Orderᵉ :
  (kᵉ nᵉ mᵉ : ℕᵉ) → is-π-finiteᵉ kᵉ (Main-Class-Latin-Hypercube-of-Orderᵉ nᵉ mᵉ)
is-π-finite-Main-Class-Latin-Hypercube-of-Orderᵉ kᵉ nᵉ mᵉ =
  is-π-finite-Σᵉ kᵉ
    ( is-π-finite-Σᵉ
      ( succ-ℕᵉ kᵉ)
      ( is-π-finite-UU-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) (succ-ℕᵉ nᵉ))
      ( λ Xᵉ →
        is-π-finite-Πᵉ
          ( succ-ℕᵉ kᵉ)
          ( is-finite-type-UU-Finᵉ (succ-ℕᵉ nᵉ) Xᵉ)
          ( λ iᵉ → is-π-finite-UU-Finᵉ (succ-ℕᵉ kᵉ) mᵉ)))
    ( λ Aᵉ →
      is-π-finite-Σᵉ kᵉ
        ( is-π-finite-is-finiteᵉ
          ( succ-ℕᵉ kᵉ)
          ( is-finite-Πᵉ
            ( is-finite-Πᵉ
              ( is-finite-type-UU-Finᵉ
                ( succ-ℕᵉ nᵉ)
                ( type-unordered-tuple-UU-Finᵉ (succ-ℕᵉ nᵉ) Aᵉ))
              ( λ iᵉ →
                is-finite-type-UU-Finᵉ mᵉ
                  ( element-unordered-tupleᵉ (succ-ℕᵉ nᵉ) Aᵉ iᵉ)))
            ( λ fᵉ → is-finite-Decidable-Propᵉ)))
        ( λ Rᵉ →
          is-π-finite-is-finiteᵉ kᵉ
            ( is-finite-Πᵉ
              ( is-finite-type-UU-Finᵉ
                ( succ-ℕᵉ nᵉ)
                ( type-unordered-tuple-UU-Finᵉ (succ-ℕᵉ nᵉ) Aᵉ))
              ( λ iᵉ →
                is-finite-Πᵉ
                  ( is-finite-Πᵉ
                    ( is-finite-has-cardinalityᵉ nᵉ
                      ( has-cardinality-type-complement-element-UU-Finᵉ nᵉ
                        ( pairᵉ (type-unordered-tuple-UU-Finᵉ (succ-ℕᵉ nᵉ) Aᵉ) iᵉ)))
                    ( λ jᵉ →
                      is-finite-type-UU-Finᵉ mᵉ
                        ( element-unordered-tupleᵉ (succ-ℕᵉ nᵉ) Aᵉ (pr1ᵉ jᵉ))))
                  ( λ fᵉ →
                    is-finite-is-decidable-Propᵉ
                      ( is-contr-Propᵉ _)
                      ( is-decidable-is-contr-is-finiteᵉ
                        ( is-finite-type-decidable-subtypeᵉ
                          ( λ xᵉ →
                            Rᵉ ( map-equiv-pr-product-unordered-tuple-typesᵉ nᵉ
                                ( map-unordered-tupleᵉ
                                  ( succ-ℕᵉ nᵉ)
                                  ( type-UU-Finᵉ mᵉ)
                                  ( Aᵉ))
                                ( iᵉ)
                                ( fᵉ)
                                ( xᵉ)))
                          ( is-finite-type-UU-Finᵉ mᵉ
                            ( element-unordered-tupleᵉ (succ-ℕᵉ nᵉ) Aᵉ iᵉ)))))))))
```

### The sequence of main classes of Latin hypercubes of fixed finite order

```agda
number-of-main-classes-of-Latin-hypercubes-of-orderᵉ : ℕᵉ → ℕᵉ → ℕᵉ
number-of-main-classes-of-Latin-hypercubes-of-orderᵉ nᵉ mᵉ =
  number-of-elements-is-finiteᵉ
    ( is-π-finite-Main-Class-Latin-Hypercube-of-Orderᵉ 0 nᵉ mᵉ)

mere-equiv-number-of-main-classes-of-Latin-hypercubes-of-orderᵉ :
  (nᵉ mᵉ : ℕᵉ) →
  mere-equivᵉ
    ( Finᵉ (number-of-main-classes-of-Latin-hypercubes-of-orderᵉ nᵉ mᵉ))
    ( type-trunc-Setᵉ
      ( Main-Class-Latin-Hypercube-of-Orderᵉ nᵉ mᵉ))
mere-equiv-number-of-main-classes-of-Latin-hypercubes-of-orderᵉ nᵉ mᵉ =
  mere-equiv-is-finiteᵉ
    ( is-π-finite-Main-Class-Latin-Hypercube-of-Orderᵉ 0 nᵉ mᵉ)
```