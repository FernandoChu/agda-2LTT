# Counting the elements of decidable subtypes

```agda
module univalent-combinatorics.counting-decidable-subtypesᵉ where

open import foundation.decidable-subtypesᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-embeddingsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-mapsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.decidable-propositionsᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Properties

### The elements of a decidable subtype of a type equipped with a counting can be counted

```agda
abstract
  count-decidable-subtype'ᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : decidable-subtypeᵉ l2ᵉ Xᵉ) →
    (kᵉ : ℕᵉ) (eᵉ : Finᵉ kᵉ ≃ᵉ Xᵉ) → countᵉ (type-decidable-subtypeᵉ Pᵉ)
  count-decidable-subtype'ᵉ Pᵉ zero-ℕᵉ eᵉ =
    count-is-emptyᵉ
      ( is-empty-is-zero-number-of-elements-countᵉ (pairᵉ zero-ℕᵉ eᵉ) reflᵉ ∘ᵉ pr1ᵉ)
  count-decidable-subtype'ᵉ Pᵉ (succ-ℕᵉ kᵉ) eᵉ
    with is-decidable-decidable-subtypeᵉ Pᵉ (map-equivᵉ eᵉ (inrᵉ starᵉ))
  ... | inlᵉ pᵉ =
    count-equivᵉ
      ( equiv-Σᵉ (is-in-decidable-subtypeᵉ Pᵉ) eᵉ (λ xᵉ → id-equivᵉ))
      ( count-equiv'ᵉ
        ( right-distributive-Σ-coproductᵉ
          ( Finᵉ kᵉ)
          ( unitᵉ)
          ( λ xᵉ → is-in-decidable-subtypeᵉ Pᵉ (map-equivᵉ eᵉ xᵉ)))
        ( pairᵉ
          ( succ-ℕᵉ
            ( number-of-elements-countᵉ
              ( count-decidable-subtype'ᵉ
                ( λ xᵉ → Pᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ)))
                ( kᵉ)
                ( id-equivᵉ))))
          ( equiv-coproductᵉ
            ( equiv-countᵉ
              ( count-decidable-subtype'ᵉ
                ( λ xᵉ → Pᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ)))
                ( kᵉ)
                ( id-equivᵉ)))
            ( equiv-is-contrᵉ
              ( is-contr-unitᵉ)
              ( is-contr-Σᵉ
                ( is-contr-unitᵉ)
                ( starᵉ)
                ( is-proof-irrelevant-is-propᵉ
                  ( is-prop-is-in-decidable-subtypeᵉ Pᵉ
                    ( map-equivᵉ eᵉ (inrᵉ starᵉ)))
                  ( pᵉ)))))))
  ... | inrᵉ fᵉ =
    count-equivᵉ
      ( equiv-Σᵉ (is-in-decidable-subtypeᵉ Pᵉ) eᵉ (λ xᵉ → id-equivᵉ))
      ( count-equiv'ᵉ
        ( right-distributive-Σ-coproductᵉ
          ( Finᵉ kᵉ)
          ( unitᵉ)
          ( λ xᵉ → is-in-decidable-subtypeᵉ Pᵉ (map-equivᵉ eᵉ xᵉ)))
        ( count-equiv'ᵉ
          ( right-unit-law-coproduct-is-emptyᵉ
            ( Σᵉ ( Finᵉ kᵉ)
                ( λ xᵉ → is-in-decidable-subtypeᵉ Pᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ))))
            ( Σᵉ ( unitᵉ)
                ( λ xᵉ → is-in-decidable-subtypeᵉ Pᵉ (map-equivᵉ eᵉ (inrᵉ xᵉ))))
            ( λ where (starᵉ ,ᵉ pᵉ) → fᵉ pᵉ))
          ( count-decidable-subtype'ᵉ
            ( λ xᵉ → Pᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ)))
            ( kᵉ)
            ( id-equivᵉ))))

count-decidable-subtypeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : decidable-subtypeᵉ l2ᵉ Xᵉ) →
  (countᵉ Xᵉ) → countᵉ (type-decidable-subtypeᵉ Pᵉ)
count-decidable-subtypeᵉ Pᵉ eᵉ =
  count-decidable-subtype'ᵉ Pᵉ
    ( number-of-elements-countᵉ eᵉ)
    ( equiv-countᵉ eᵉ)
```

### The elements in the domain of a decidable embedding can be counted if the elements of the codomain can be counted

```agda
count-decidable-embᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ ↪ᵈᵉ Yᵉ) → countᵉ Yᵉ → countᵉ Xᵉ
count-decidable-embᵉ fᵉ eᵉ =
  count-equivᵉ
    ( equiv-total-fiberᵉ (map-decidable-embᵉ fᵉ))
    ( count-decidable-subtypeᵉ (decidable-subtype-decidable-embᵉ fᵉ) eᵉ)
```

### If the elements of a subtype of a type equipped with a counting can be counted, then the subtype is decidable

```agda
is-decidable-count-subtypeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l2ᵉ Xᵉ) → countᵉ Xᵉ →
  countᵉ (type-subtypeᵉ Pᵉ) → (xᵉ : Xᵉ) → is-decidableᵉ (type-Propᵉ (Pᵉ xᵉ))
is-decidable-count-subtypeᵉ Pᵉ eᵉ fᵉ xᵉ =
  is-decidable-countᵉ
    ( count-equivᵉ
      ( equiv-fiber-pr1ᵉ (type-Propᵉ ∘ᵉ Pᵉ) xᵉ)
      ( count-decidable-subtypeᵉ
        ( λ yᵉ →
          pairᵉ
            ( Idᵉ (pr1ᵉ yᵉ) xᵉ)
            ( pairᵉ
              ( is-set-countᵉ eᵉ (pr1ᵉ yᵉ) xᵉ)
              ( has-decidable-equality-countᵉ eᵉ (pr1ᵉ yᵉ) xᵉ)))
        ( fᵉ)))
```

### If a subtype of a type equipped with a counting is finite, then its elements can be counted

```agda
count-type-subtype-is-finite-type-subtypeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (eᵉ : countᵉ Aᵉ) (Pᵉ : subtypeᵉ l2ᵉ Aᵉ) →
  is-finiteᵉ (type-subtypeᵉ Pᵉ) → countᵉ (type-subtypeᵉ Pᵉ)
count-type-subtype-is-finite-type-subtypeᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} eᵉ Pᵉ fᵉ =
  count-decidable-subtypeᵉ
    ( λ xᵉ → pairᵉ (type-Propᵉ (Pᵉ xᵉ)) (pairᵉ (is-prop-type-Propᵉ (Pᵉ xᵉ)) (dᵉ xᵉ)))
    ( eᵉ)
  where
  dᵉ : (xᵉ : Aᵉ) → is-decidableᵉ (type-Propᵉ (Pᵉ xᵉ))
  dᵉ xᵉ =
    apply-universal-property-trunc-Propᵉ fᵉ
      ( is-decidable-Propᵉ (Pᵉ xᵉ))
      ( λ gᵉ → is-decidable-count-subtypeᵉ Pᵉ eᵉ gᵉ xᵉ)
```

### For any embedding `B ↪ A` into a type `A` equipped with a counting, if `B` is finite then its elements can be counted

```agda
count-domain-emb-is-finite-domain-embᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (eᵉ : countᵉ Aᵉ) {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Bᵉ ↪ᵉ Aᵉ) →
  is-finiteᵉ Bᵉ → countᵉ Bᵉ
count-domain-emb-is-finite-domain-embᵉ eᵉ fᵉ Hᵉ =
  count-equivᵉ
    ( equiv-total-fiberᵉ (map-embᵉ fᵉ))
    ( count-type-subtype-is-finite-type-subtypeᵉ eᵉ
      ( λ xᵉ → pairᵉ (fiberᵉ (map-embᵉ fᵉ) xᵉ) (is-prop-map-embᵉ fᵉ xᵉ))
      ( is-finite-equiv'ᵉ
        ( equiv-total-fiberᵉ (map-embᵉ fᵉ))
        ( Hᵉ)))
```