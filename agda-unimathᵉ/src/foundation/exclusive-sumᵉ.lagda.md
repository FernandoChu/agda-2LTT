# Exclusive sums

```agda
module foundation.exclusive-sumᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunctionᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.negationᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.symmetric-operationsᵉ
open import foundation.universal-quantificationᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.decidable-propositionsᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.transport-along-identificationsᵉ

open import univalent-combinatorics.2-element-typesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "exclusiveᵉ sum"ᵉ Disambiguation="ofᵉ types"ᵉ Agda=exclusive-sumᵉ}} ofᵉ
twoᵉ typesᵉ `A`ᵉ andᵉ `B`,ᵉ isᵉ theᵉ typeᵉ consistingᵉ ofᵉ

-ᵉ elementsᵉ ofᵉ `A`ᵉ togetherᵉ with aᵉ proofᵉ thatᵉ `B`ᵉ isᵉ
  [empty](foundation-core.empty-types.md),ᵉ orᵉ
-ᵉ elementsᵉ ofᵉ `B`ᵉ togetherᵉ with aᵉ proofᵉ thatᵉ `A`ᵉ isᵉ empty.ᵉ

Theᵉ
{{#conceptᵉ "exclusiveᵉ sum"ᵉ Disambiguation="ofᵉ propositions"ᵉ Agda=exclusive-sum-Propᵉ}}
ofᵉ [propositions](foundation-core.propositions.mdᵉ) `P`ᵉ andᵉ `Q`ᵉ isᵉ likewiseᵉ theᵉ
[proposition](foundation-core.propositions.mdᵉ) thatᵉ `P`ᵉ holdsᵉ andᵉ `Q`ᵉ doesᵉ notᵉ
hold,ᵉ orᵉ `P`ᵉ doesᵉ notᵉ holdᵉ andᵉ `Q`ᵉ holds.ᵉ Theᵉ exclusiveᵉ sumᵉ ofᵉ twoᵉ propositionsᵉ
isᵉ equivalentᵉ to theᵉ
[exclusiveᵉ disjunction](foundation.exclusive-disjunction.md),ᵉ whichᵉ isᵉ shownᵉ
there.ᵉ

## Definitions

### The exclusive sum of types

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  exclusive-sumᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  exclusive-sumᵉ = (Aᵉ ×ᵉ ¬ᵉ Bᵉ) +ᵉ (Bᵉ ×ᵉ ¬ᵉ Aᵉ)
```

### The exclusive sum of propositions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ)
  where

  exclusive-sum-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  exclusive-sum-Propᵉ =
    coproduct-Propᵉ
      ( Pᵉ ∧ᵉ (¬'ᵉ Qᵉ))
      ( Qᵉ ∧ᵉ (¬'ᵉ Pᵉ))
      ( λ pᵉ qᵉ → pr2ᵉ qᵉ (pr1ᵉ pᵉ))

  type-exclusive-sum-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-exclusive-sum-Propᵉ = type-Propᵉ exclusive-sum-Propᵉ

  abstract
    is-prop-type-exclusive-sum-Propᵉ : is-propᵉ type-exclusive-sum-Propᵉ
    is-prop-type-exclusive-sum-Propᵉ = is-prop-type-Propᵉ exclusive-sum-Propᵉ
```

### The canonical inclusion of the exclusive sum into the coproduct

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  map-coproduct-exclusive-sumᵉ : exclusive-sumᵉ Aᵉ Bᵉ → Aᵉ +ᵉ Bᵉ
  map-coproduct-exclusive-sumᵉ (inlᵉ (aᵉ ,ᵉ _)) = inlᵉ aᵉ
  map-coproduct-exclusive-sumᵉ (inrᵉ (bᵉ ,ᵉ _)) = inrᵉ bᵉ
```

### The symmetric operation of exclusive sum

```agda
predicate-symmetric-exclusive-sumᵉ :
  {lᵉ : Level} (pᵉ : unordered-pairᵉ (UUᵉ lᵉ)) → type-unordered-pairᵉ pᵉ → UUᵉ lᵉ
predicate-symmetric-exclusive-sumᵉ pᵉ xᵉ =
  ( element-unordered-pairᵉ pᵉ xᵉ) ×ᵉ (¬ᵉ (other-element-unordered-pairᵉ pᵉ xᵉ))

symmetric-exclusive-sumᵉ : {lᵉ : Level} → symmetric-operationᵉ (UUᵉ lᵉ) (UUᵉ lᵉ)
symmetric-exclusive-sumᵉ pᵉ =
  Σᵉ (type-unordered-pairᵉ pᵉ) (predicate-symmetric-exclusive-sumᵉ pᵉ)
```

### The symmetric operation of the exclusive sum of propositions

```agda
predicate-symmetric-exclusive-sum-Propᵉ :
  {lᵉ : Level} (pᵉ : unordered-pairᵉ (Propᵉ lᵉ)) →
  type-unordered-pairᵉ pᵉ → UUᵉ lᵉ
predicate-symmetric-exclusive-sum-Propᵉ pᵉ =
  predicate-symmetric-exclusive-sumᵉ (map-unordered-pairᵉ type-Propᵉ pᵉ)

type-symmetric-exclusive-sum-Propᵉ :
  {lᵉ : Level} → symmetric-operationᵉ (Propᵉ lᵉ) (UUᵉ lᵉ)
type-symmetric-exclusive-sum-Propᵉ pᵉ =
  symmetric-exclusive-sumᵉ (map-unordered-pairᵉ type-Propᵉ pᵉ)

all-elements-equal-type-symmetric-exclusive-sum-Propᵉ :
  {lᵉ : Level} (pᵉ : unordered-pairᵉ (Propᵉ lᵉ)) →
  all-elements-equalᵉ (type-symmetric-exclusive-sum-Propᵉ pᵉ)
all-elements-equal-type-symmetric-exclusive-sum-Propᵉ (Xᵉ ,ᵉ Pᵉ) xᵉ yᵉ =
  cases-is-prop-type-symmetric-exclusive-sum-Propᵉ
    ( has-decidable-equality-is-finiteᵉ
      ( is-finite-type-UU-Finᵉ 2 Xᵉ)
      ( pr1ᵉ xᵉ)
      ( pr1ᵉ yᵉ))
  where
  cases-is-prop-type-symmetric-exclusive-sum-Propᵉ :
    is-decidableᵉ (pr1ᵉ xᵉ ＝ᵉ pr1ᵉ yᵉ) → xᵉ ＝ᵉ yᵉ
  cases-is-prop-type-symmetric-exclusive-sum-Propᵉ (inlᵉ pᵉ) =
    eq-pair-Σᵉ
      ( pᵉ)
      ( eq-is-propᵉ
        ( is-prop-product-Propᵉ
          ( Pᵉ (pr1ᵉ yᵉ))
          ( neg-type-Propᵉ
            ( other-element-unordered-pairᵉ
              ( map-unordered-pairᵉ (type-Propᵉ) (Xᵉ ,ᵉ Pᵉ))
              ( pr1ᵉ yᵉ)))))
  cases-is-prop-type-symmetric-exclusive-sum-Propᵉ (inrᵉ npᵉ) =
    ex-falsoᵉ
      ( trᵉ
        ( λ zᵉ → ¬ᵉ (type-Propᵉ (Pᵉ zᵉ)))
        ( compute-swap-2-Element-Typeᵉ Xᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ) npᵉ)
        ( pr2ᵉ (pr2ᵉ xᵉ))
        ( pr1ᵉ (pr2ᵉ yᵉ)))

is-prop-type-symmetric-exclusive-sum-Propᵉ :
  {lᵉ : Level} (pᵉ : unordered-pairᵉ (Propᵉ lᵉ)) →
  is-propᵉ (type-symmetric-exclusive-sum-Propᵉ pᵉ)
is-prop-type-symmetric-exclusive-sum-Propᵉ pᵉ =
  is-prop-all-elements-equalᵉ
    ( all-elements-equal-type-symmetric-exclusive-sum-Propᵉ pᵉ)

symmetric-exclusive-sum-Propᵉ :
  {lᵉ : Level} → symmetric-operationᵉ (Propᵉ lᵉ) (Propᵉ lᵉ)
pr1ᵉ (symmetric-exclusive-sum-Propᵉ Eᵉ) = type-symmetric-exclusive-sum-Propᵉ Eᵉ
pr2ᵉ (symmetric-exclusive-sum-Propᵉ Eᵉ) =
  is-prop-type-symmetric-exclusive-sum-Propᵉ Eᵉ
```

## Properties

### The symmetric exclusive sum at a standard unordered pair

```agda
module _
  {lᵉ : Level} {Aᵉ Bᵉ : UUᵉ lᵉ}
  where

  exclusive-sum-symmetric-exclusive-sumᵉ :
    symmetric-exclusive-sumᵉ (standard-unordered-pairᵉ Aᵉ Bᵉ) → exclusive-sumᵉ Aᵉ Bᵉ
  exclusive-sum-symmetric-exclusive-sumᵉ (pairᵉ (inlᵉ (inrᵉ _)) (pᵉ ,ᵉ nqᵉ)) =
    inlᵉ
      ( pairᵉ pᵉ
        ( trᵉ
          ( λ tᵉ → ¬ᵉ (element-unordered-pairᵉ (standard-unordered-pairᵉ Aᵉ Bᵉ) tᵉ))
          ( compute-swap-Fin-two-ℕᵉ (zero-Finᵉ 1ᵉ))
          ( nqᵉ)))
  exclusive-sum-symmetric-exclusive-sumᵉ (pairᵉ (inrᵉ _) (qᵉ ,ᵉ npᵉ)) =
    inrᵉ
      ( pairᵉ
        ( qᵉ)
        ( trᵉ
          ( λ tᵉ → ¬ᵉ (element-unordered-pairᵉ (standard-unordered-pairᵉ Aᵉ Bᵉ) tᵉ))
          ( compute-swap-Fin-two-ℕᵉ (one-Finᵉ 1ᵉ))
          ( npᵉ)))

  symmetric-exclusive-sum-exclusive-sumᵉ :
    exclusive-sumᵉ Aᵉ Bᵉ → symmetric-exclusive-sumᵉ (standard-unordered-pairᵉ Aᵉ Bᵉ)
  pr1ᵉ (symmetric-exclusive-sum-exclusive-sumᵉ (inlᵉ (aᵉ ,ᵉ nbᵉ))) = (zero-Finᵉ 1ᵉ)
  pr1ᵉ (pr2ᵉ (symmetric-exclusive-sum-exclusive-sumᵉ (inlᵉ (aᵉ ,ᵉ nbᵉ)))) = aᵉ
  pr2ᵉ (pr2ᵉ (symmetric-exclusive-sum-exclusive-sumᵉ (inlᵉ (aᵉ ,ᵉ nbᵉ)))) =
    trᵉ
      ( λ tᵉ → ¬ᵉ (element-unordered-pairᵉ (standard-unordered-pairᵉ Aᵉ Bᵉ) tᵉ))
      ( invᵉ (compute-swap-Fin-two-ℕᵉ (zero-Finᵉ 1ᵉ)))
      ( nbᵉ)
  pr1ᵉ (symmetric-exclusive-sum-exclusive-sumᵉ (inrᵉ (naᵉ ,ᵉ bᵉ))) = (one-Finᵉ 1ᵉ)
  pr1ᵉ (pr2ᵉ (symmetric-exclusive-sum-exclusive-sumᵉ (inrᵉ (bᵉ ,ᵉ naᵉ)))) = bᵉ
  pr2ᵉ (pr2ᵉ (symmetric-exclusive-sum-exclusive-sumᵉ (inrᵉ (bᵉ ,ᵉ naᵉ)))) =
    trᵉ
      ( λ tᵉ → ¬ᵉ (element-unordered-pairᵉ (standard-unordered-pairᵉ Aᵉ Bᵉ) tᵉ))
      ( invᵉ (compute-swap-Fin-two-ℕᵉ (one-Finᵉ 1ᵉ)))
      ( naᵉ)
```

```text
  eq-equiv-Propᵉ
    ( ( ( equiv-coproductᵉ
          ( ( ( left-unit-law-coproductᵉ (type-Propᵉ (Pᵉ ∧ᵉ (¬'ᵉ Qᵉ)))) ∘eᵉ
              ( equiv-coproductᵉ
                ( left-absorption-Σᵉ
                  ( λ xᵉ →
                    ( type-Propᵉ
                      ( pr2ᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ) (inlᵉ (inlᵉ xᵉ)))) ×ᵉ
                      ( ¬ᵉ ( type-Propᵉ
                            ( pr2ᵉ
                              ( standard-unordered-pairᵉ Pᵉ Qᵉ)
                              ( map-swap-2-Element-Typeᵉ
                                ( pr1ᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ))
                                ( inlᵉ (inlᵉ xᵉ))))))))
                ( ( equiv-productᵉ
                    ( id-equivᵉ)
                    ( trᵉ
                      ( λ bᵉ →
                        ( ¬ᵉ (type-Propᵉ (pr2ᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ) bᵉ))) ≃ᵉ
                        ( ¬ᵉ (type-Propᵉ Qᵉ)))
                      ( invᵉ (compute-swap-Fin-two-ℕᵉ (zero-Finᵉ ?ᵉ)))
                      ( id-equivᵉ))) ∘eᵉ
                    ( left-unit-law-Σᵉ
                      ( λ yᵉ →
                        ( type-Propᵉ
                          ( pr2ᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ) (inlᵉ (inrᵉ yᵉ)))) ×ᵉ
                        ( ¬ᵉ ( type-Propᵉ
                              ( pr2ᵉ
                                ( standard-unordered-pairᵉ Pᵉ Qᵉ)
                                ( map-swap-2-Element-Typeᵉ
                                  ( pr1ᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ))
                                  ( inlᵉ (inrᵉ yᵉ))))))))))) ∘eᵉ
          ( ( right-distributive-Σ-coproductᵉ
              ( Finᵉ 0ᵉ)
              ( unitᵉ)
              ( λ xᵉ →
                ( type-Propᵉ (pr2ᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ) (inlᵉ xᵉ))) ×ᵉ
                ( ¬ᵉ ( type-Propᵉ
                      ( pr2ᵉ
                        ( standard-unordered-pairᵉ Pᵉ Qᵉ)
                        ( map-swap-2-Element-Typeᵉ
                          ( pr1ᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ)) (inlᵉ xᵉ)))))))))
        ( ( equiv-productᵉ
            ( trᵉ
              ( λ bᵉ →
                ¬ᵉ (type-Propᵉ (pr2ᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ) bᵉ)) ≃ᵉ
                ¬ᵉ (type-Propᵉ Pᵉ))
              ( invᵉ (compute-swap-Fin-two-ℕᵉ (one-Finᵉ ?ᵉ)))
              ( id-equivᵉ))
            ( id-equivᵉ)) ∘eᵉ
          ( ( commutative-productᵉ) ∘eᵉ
            ( left-unit-law-Σᵉ
              ( λ yᵉ →
                ( type-Propᵉ (pr2ᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ) (inrᵉ yᵉ))) ×ᵉ
                ( ¬ᵉ ( type-Propᵉ
                      ( pr2ᵉ
                        ( standard-unordered-pairᵉ Pᵉ Qᵉ)
                        ( map-swap-2-Element-Typeᵉ
                          ( pr1ᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ))
                          ( inrᵉ yᵉ)))))))))) ∘eᵉ
      ( right-distributive-Σ-coproductᵉ
        ( Finᵉ 1ᵉ)
        ( unitᵉ)
        ( λ xᵉ →
          ( type-Propᵉ (pr2ᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ) xᵉ)) ×ᵉ
          ( ¬ᵉ ( type-Propᵉ
                ( pr2ᵉ
                  ( standard-unordered-pairᵉ Pᵉ Qᵉ)
                  ( map-swap-2-Element-Typeᵉ
                    ( pr1ᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ))
                    ( xᵉ)))))))))
```

```agda
module _
  {lᵉ : Level} (Pᵉ Qᵉ : Propᵉ lᵉ)
  where

  exclusive-sum-symmetric-exclusive-sum-Propᵉ :
    type-hom-Propᵉ
      ( symmetric-exclusive-sum-Propᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ))
      ( exclusive-sum-Propᵉ Pᵉ Qᵉ)
  exclusive-sum-symmetric-exclusive-sum-Propᵉ (pairᵉ (inlᵉ (inrᵉ _)) (pᵉ ,ᵉ nqᵉ)) =
    inlᵉ
      ( pairᵉ pᵉ
        ( trᵉ
          ( λ tᵉ →
            ¬ᵉ ( type-Propᵉ
                ( element-unordered-pairᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ) tᵉ)))
          ( compute-swap-Fin-two-ℕᵉ (zero-Finᵉ 1ᵉ))
          ( nqᵉ)))
  exclusive-sum-symmetric-exclusive-sum-Propᵉ (pairᵉ (inrᵉ _) (qᵉ ,ᵉ npᵉ)) =
    inrᵉ
      ( pairᵉ qᵉ
        ( trᵉ
          ( λ tᵉ →
            ¬ᵉ ( type-Propᵉ
                ( element-unordered-pairᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ) tᵉ)))
          ( compute-swap-Fin-two-ℕᵉ (one-Finᵉ 1ᵉ))
          ( npᵉ)))

  symmetric-exclusive-sum-exclusive-sum-Propᵉ :
    type-hom-Propᵉ
      ( exclusive-sum-Propᵉ Pᵉ Qᵉ)
      ( symmetric-exclusive-sum-Propᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ))
  pr1ᵉ (symmetric-exclusive-sum-exclusive-sum-Propᵉ (inlᵉ (pᵉ ,ᵉ nqᵉ))) = zero-Finᵉ 1
  pr1ᵉ (pr2ᵉ (symmetric-exclusive-sum-exclusive-sum-Propᵉ (inlᵉ (pᵉ ,ᵉ nqᵉ)))) = pᵉ
  pr2ᵉ (pr2ᵉ (symmetric-exclusive-sum-exclusive-sum-Propᵉ (inlᵉ (pᵉ ,ᵉ nqᵉ)))) =
    trᵉ
      ( λ tᵉ →
        ¬ᵉ (type-Propᵉ (element-unordered-pairᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ) tᵉ)))
      ( invᵉ (compute-swap-Fin-two-ℕᵉ (zero-Finᵉ 1ᵉ)))
      ( nqᵉ)
  pr1ᵉ (symmetric-exclusive-sum-exclusive-sum-Propᵉ (inrᵉ (qᵉ ,ᵉ npᵉ))) = one-Finᵉ 1
  pr1ᵉ (pr2ᵉ (symmetric-exclusive-sum-exclusive-sum-Propᵉ (inrᵉ (qᵉ ,ᵉ npᵉ)))) = qᵉ
  pr2ᵉ (pr2ᵉ (symmetric-exclusive-sum-exclusive-sum-Propᵉ (inrᵉ (qᵉ ,ᵉ npᵉ)))) =
    trᵉ
      ( λ tᵉ →
        ¬ᵉ (type-Propᵉ (element-unordered-pairᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ) tᵉ)))
      ( invᵉ (compute-swap-Fin-two-ℕᵉ (one-Finᵉ 1ᵉ)))
      ( npᵉ)

eq-commmutative-exclusive-sum-exclusive-sumᵉ :
  {lᵉ : Level} (Pᵉ Qᵉ : Propᵉ lᵉ) →
  symmetric-exclusive-sum-Propᵉ (standard-unordered-pairᵉ Pᵉ Qᵉ) ＝ᵉ
  exclusive-sum-Propᵉ Pᵉ Qᵉ
eq-commmutative-exclusive-sum-exclusive-sumᵉ Pᵉ Qᵉ =
  eq-iffᵉ
    ( exclusive-sum-symmetric-exclusive-sum-Propᵉ Pᵉ Qᵉ)
    ( symmetric-exclusive-sum-exclusive-sum-Propᵉ Pᵉ Qᵉ)
```

### The exclusive sum of decidable types is decidable

```agda
is-decidable-exclusive-sumᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-decidableᵉ Aᵉ → is-decidableᵉ Bᵉ → is-decidableᵉ (exclusive-sumᵉ Aᵉ Bᵉ)
is-decidable-exclusive-sumᵉ dᵉ eᵉ =
  is-decidable-coproductᵉ
    ( is-decidable-productᵉ dᵉ (is-decidable-negᵉ eᵉ))
    ( is-decidable-productᵉ eᵉ (is-decidable-negᵉ dᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Decidable-Propᵉ l1ᵉ) (Qᵉ : Decidable-Propᵉ l2ᵉ)
  where

  is-decidable-exclusive-sum-Decidable-Propᵉ :
    is-decidableᵉ
      ( type-exclusive-sum-Propᵉ (prop-Decidable-Propᵉ Pᵉ) (prop-Decidable-Propᵉ Qᵉ))
  is-decidable-exclusive-sum-Decidable-Propᵉ =
      is-decidable-coproductᵉ
      ( is-decidable-productᵉ
        ( is-decidable-Decidable-Propᵉ Pᵉ)
        ( is-decidable-negᵉ (is-decidable-Decidable-Propᵉ Qᵉ)))
      ( is-decidable-productᵉ
        ( is-decidable-Decidable-Propᵉ Qᵉ)
        ( is-decidable-negᵉ (is-decidable-Decidable-Propᵉ Pᵉ)))

  exclusive-sum-Decidable-Propᵉ : Decidable-Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ exclusive-sum-Decidable-Propᵉ =
    type-exclusive-sum-Propᵉ (prop-Decidable-Propᵉ Pᵉ) (prop-Decidable-Propᵉ Qᵉ)
  pr1ᵉ (pr2ᵉ exclusive-sum-Decidable-Propᵉ) =
    is-prop-type-exclusive-sum-Propᵉ
      ( prop-Decidable-Propᵉ Pᵉ)
      ( prop-Decidable-Propᵉ Qᵉ)
  pr2ᵉ (pr2ᵉ exclusive-sum-Decidable-Propᵉ) =
    is-decidable-exclusive-sum-Decidable-Propᵉ
```

## Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}