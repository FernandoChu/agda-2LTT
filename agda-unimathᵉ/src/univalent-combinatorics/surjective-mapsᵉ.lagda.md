# Surjective maps between finite types

```agda
module univalent-combinatorics.surjective-mapsᵉ where

open import foundation.surjective-mapsᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.decidable-embeddingsᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.counting-decidable-subtypesᵉ
open import univalent-combinatorics.counting-dependent-pair-typesᵉ
open import univalent-combinatorics.decidable-dependent-function-typesᵉ
open import univalent-combinatorics.embeddingsᵉ
open import univalent-combinatorics.fibers-of-mapsᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Definition

```agda
Surjection-𝔽ᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → 𝔽ᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Surjection-𝔽ᵉ l2ᵉ Aᵉ =
  Σᵉ (𝔽ᵉ l2ᵉ) (λ Bᵉ → (type-𝔽ᵉ Aᵉ) ↠ᵉ (type-𝔽ᵉ Bᵉ))
```

## Properties

```agda
is-decidable-is-surjective-is-finiteᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-finiteᵉ Aᵉ → is-finiteᵉ Bᵉ → is-decidableᵉ (is-surjectiveᵉ fᵉ)
is-decidable-is-surjective-is-finiteᵉ fᵉ HAᵉ HBᵉ =
  is-decidable-Π-is-finiteᵉ HBᵉ
    ( λ yᵉ → is-decidable-type-trunc-Prop-is-finiteᵉ (is-finite-fiberᵉ fᵉ HAᵉ HBᵉ yᵉ))
```

### If `X` has decidable equality and there exist a surjection `Fin-n ↠ X` then `X` has a counting

```agda
module _
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ}
  where

  count-surjection-has-decidable-equalityᵉ :
    (nᵉ : ℕᵉ) → (has-decidable-equalityᵉ Xᵉ) → (Finᵉ nᵉ ↠ᵉ Xᵉ) →
    countᵉ (Xᵉ)
  count-surjection-has-decidable-equalityᵉ nᵉ dec-Xᵉ fᵉ =
    count-decidable-embᵉ
      ( ( map-equivᵉ
          ( equiv-precomp-decidable-emb-equivᵉ
            ( inv-equivᵉ
              ( right-unit-law-Σ-is-contrᵉ
                ( λ xᵉ →
                  is-proof-irrelevant-is-propᵉ
                    ( is-prop-type-trunc-Propᵉ)
                    ( is-surjective-map-surjectionᵉ fᵉ xᵉ))))
            (Σᵉ _ (fiberᵉ (pr1ᵉ fᵉ))))
          ( decidable-emb-tot-trunc-Prop-countᵉ
            { Pᵉ = fiberᵉ (map-surjectionᵉ fᵉ)}
            ( count-fiber-count-Σᵉ
              dec-Xᵉ
              ( count-equivᵉ
                ( inv-equiv-total-fiberᵉ (map-surjectionᵉ fᵉ)) (count-Finᵉ nᵉ))))))
      ( count-equivᵉ (inv-equiv-total-fiberᵉ (map-surjectionᵉ fᵉ)) (count-Finᵉ nᵉ))
```

### A type `X` is finite if and only if it has decidable equality and there exists a surjection from a finite type to `X`

```agda
  is-finite-if-∃-surjection-has-decidable-equalityᵉ :
    is-finiteᵉ Xᵉ →
    ( has-decidable-equalityᵉ Xᵉ ×ᵉ type-trunc-Propᵉ (Σᵉ ℕᵉ (λ nᵉ → Finᵉ nᵉ ↠ᵉ Xᵉ)))
  is-finite-if-∃-surjection-has-decidable-equalityᵉ fin-Xᵉ =
    apply-universal-property-trunc-Propᵉ
      ( fin-Xᵉ)
      ( product-Propᵉ (has-decidable-equality-Propᵉ Xᵉ) (trunc-Propᵉ _))
      ( λ count-Xᵉ →
        ( has-decidable-equality-countᵉ count-Xᵉ ,ᵉ
          unit-trunc-Propᵉ
          ( pr1ᵉ count-Xᵉ ,ᵉ
            ( map-equivᵉ (pr2ᵉ count-Xᵉ)) ,ᵉ
            ( is-surjective-map-equivᵉ (pr2ᵉ count-Xᵉ)))))

  ∃-surjection-has-decidable-equality-if-is-finiteᵉ :
    ( has-decidable-equalityᵉ Xᵉ ×ᵉ type-trunc-Propᵉ (Σᵉ ℕᵉ (λ nᵉ → Finᵉ nᵉ ↠ᵉ Xᵉ))) →
    is-finiteᵉ Xᵉ
  ∃-surjection-has-decidable-equality-if-is-finiteᵉ dec-X-surjᵉ =
    apply-universal-property-trunc-Propᵉ
          ( pr2ᵉ dec-X-surjᵉ)
          ( is-finite-Propᵉ Xᵉ)
          ( λ n-surjᵉ →
            unit-trunc-Propᵉ
              ( count-surjection-has-decidable-equalityᵉ
                ( pr1ᵉ n-surjᵉ)
                ( pr1ᵉ dec-X-surjᵉ)
                ( pr2ᵉ n-surjᵉ)))

  is-finite-iff-∃-surjection-has-decidable-equalityᵉ :
    is-finiteᵉ Xᵉ ≃ᵉ
    ( has-decidable-equalityᵉ Xᵉ ×ᵉ type-trunc-Propᵉ (Σᵉ ℕᵉ (λ nᵉ → Finᵉ nᵉ ↠ᵉ Xᵉ)))
  is-finite-iff-∃-surjection-has-decidable-equalityᵉ =
    equiv-iff-is-propᵉ
      ( is-prop-is-finiteᵉ Xᵉ)
      ( is-prop-productᵉ is-prop-has-decidable-equalityᵉ is-prop-type-trunc-Propᵉ)
      ( λ fin-Xᵉ → is-finite-if-∃-surjection-has-decidable-equalityᵉ fin-Xᵉ)
      ( λ dec-X-surjᵉ →
        ∃-surjection-has-decidable-equality-if-is-finiteᵉ dec-X-surjᵉ)
```