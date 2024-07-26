# The binomial types

```agda
module univalent-combinatorics.binomial-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.binomial-coefficientsᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.booleansᵉ
open import foundation.connected-components-universesᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-embeddingsᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-maybeᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-function-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.maybeᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.negationᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-empty-typeᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universal-property-maybeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.coproduct-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ binomialᵉ typesᵉ areᵉ aᵉ categorificationᵉ ofᵉ theᵉ binomialᵉ coefficients.ᵉ Theᵉ
binomialᵉ typeᵉ `(Aᵉ chooseᵉ B)`ᵉ isᵉ theᵉ typeᵉ ofᵉ decidableᵉ embeddingsᵉ fromᵉ typesᵉ
merelyᵉ equalᵉ to `B`ᵉ intoᵉ `A`.ᵉ

## Definitions

```agda
binomial-type-Levelᵉ :
  (lᵉ : Level) {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : UUᵉ l2ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
binomial-type-Levelᵉ lᵉ Xᵉ Yᵉ =
  Σᵉ (component-UU-Levelᵉ lᵉ Yᵉ) (λ Zᵉ → type-component-UU-Levelᵉ Zᵉ ↪ᵈᵉ Xᵉ)

type-binomial-type-Levelᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
  binomial-type-Levelᵉ l3ᵉ Xᵉ Yᵉ → UUᵉ l3ᵉ
type-binomial-type-Levelᵉ Zᵉ = type-component-UU-Levelᵉ (pr1ᵉ Zᵉ)

abstract
  mere-compute-binomial-type-Levelᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
    (Zᵉ : binomial-type-Levelᵉ l3ᵉ Xᵉ Yᵉ) →
    mere-equivᵉ Yᵉ (type-binomial-type-Levelᵉ Zᵉ)
  mere-compute-binomial-type-Levelᵉ Zᵉ = mere-equiv-component-UU-Levelᵉ (pr1ᵉ Zᵉ)

decidable-emb-binomial-type-Levelᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Zᵉ : binomial-type-Levelᵉ l3ᵉ Xᵉ Yᵉ) →
  type-binomial-type-Levelᵉ Zᵉ ↪ᵈᵉ Xᵉ
decidable-emb-binomial-type-Levelᵉ Zᵉ = pr2ᵉ Zᵉ

map-decidable-emb-binomial-type-Levelᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Zᵉ : binomial-type-Levelᵉ l3ᵉ Xᵉ Yᵉ) →
  type-binomial-type-Levelᵉ Zᵉ → Xᵉ
map-decidable-emb-binomial-type-Levelᵉ Zᵉ =
  map-decidable-embᵉ (decidable-emb-binomial-type-Levelᵉ Zᵉ)

abstract
  is-emb-map-emb-binomial-type-Levelᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
    (Zᵉ : binomial-type-Levelᵉ l3ᵉ Xᵉ Yᵉ) →
    is-embᵉ (map-decidable-emb-binomial-type-Levelᵉ Zᵉ)
  is-emb-map-emb-binomial-type-Levelᵉ Zᵉ =
    is-emb-map-decidable-embᵉ (decidable-emb-binomial-type-Levelᵉ Zᵉ)
```

### The standard binomial types

Weᵉ nowᵉ defineᵉ theᵉ standardᵉ binomialᵉ types.ᵉ

```agda
binomial-typeᵉ : {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : UUᵉ l2ᵉ) → UUᵉ (lsuc (l1ᵉ ⊔ l2ᵉ))
binomial-typeᵉ {l1ᵉ} {l2ᵉ} Xᵉ Yᵉ = binomial-type-Levelᵉ (l1ᵉ ⊔ l2ᵉ) Xᵉ Yᵉ

type-binomial-typeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} → binomial-typeᵉ Xᵉ Yᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-binomial-typeᵉ Zᵉ = type-component-UU-Levelᵉ (pr1ᵉ Zᵉ)

abstract
  mere-compute-binomial-typeᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Zᵉ : binomial-typeᵉ Xᵉ Yᵉ) →
    mere-equivᵉ Yᵉ (type-binomial-typeᵉ Zᵉ)
  mere-compute-binomial-typeᵉ Zᵉ = mere-equiv-component-UU-Levelᵉ (pr1ᵉ Zᵉ)

decidable-emb-binomial-typeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Zᵉ : binomial-typeᵉ Xᵉ Yᵉ) →
  type-binomial-typeᵉ Zᵉ ↪ᵈᵉ Xᵉ
decidable-emb-binomial-typeᵉ Zᵉ = pr2ᵉ Zᵉ

map-decidable-emb-binomial-typeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Zᵉ : binomial-typeᵉ Xᵉ Yᵉ) →
  type-binomial-typeᵉ Zᵉ → Xᵉ
map-decidable-emb-binomial-typeᵉ Zᵉ =
  map-decidable-embᵉ (decidable-emb-binomial-typeᵉ Zᵉ)

abstract
  is-emb-map-emb-binomial-typeᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Zᵉ : binomial-typeᵉ Xᵉ Yᵉ) →
    is-embᵉ (map-decidable-emb-binomial-typeᵉ Zᵉ)
  is-emb-map-emb-binomial-typeᵉ Zᵉ =
    is-emb-map-decidable-embᵉ (decidable-emb-binomial-typeᵉ Zᵉ)
```

### Proposition 17.5.6

```agda
binomial-type-Level'ᵉ :
  (lᵉ : Level) {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
binomial-type-Level'ᵉ lᵉ Aᵉ Bᵉ =
  Σᵉ ( Aᵉ → Decidable-Propᵉ lᵉ)
    ( λ Pᵉ → mere-equivᵉ Bᵉ (Σᵉ Aᵉ (type-Decidable-Propᵉ ∘ᵉ Pᵉ)))

compute-binomial-type-Levelᵉ :
  (lᵉ : Level) {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) →
  binomial-type-Levelᵉ (l1ᵉ ⊔ lᵉ) Aᵉ Bᵉ ≃ᵉ binomial-type-Level'ᵉ (l1ᵉ ⊔ lᵉ) Aᵉ Bᵉ
compute-binomial-type-Levelᵉ lᵉ {l1ᵉ} {l2ᵉ} Aᵉ Bᵉ =
  ( ( ( equiv-Σᵉ
        ( λ Pᵉ → mere-equivᵉ Bᵉ (Σᵉ Aᵉ (type-Decidable-Propᵉ ∘ᵉ Pᵉ)))
        ( equiv-Fiber-Decidable-Propᵉ lᵉ Aᵉ)
        ( λ eᵉ →
          equiv-trunc-Propᵉ
            ( equiv-postcomp-equivᵉ
              ( inv-equivᵉ (equiv-total-fiberᵉ (pr1ᵉ (pr2ᵉ eᵉ)))) Bᵉ))) ∘eᵉ
      ( inv-associative-Σᵉ
        ( UUᵉ (l1ᵉ ⊔ lᵉ))
        ( λ Xᵉ → Xᵉ ↪ᵈᵉ Aᵉ)
        ( λ Xᵉ → mere-equivᵉ Bᵉ (pr1ᵉ Xᵉ)))) ∘eᵉ
    ( equiv-totᵉ (λ Xᵉ → commutative-productᵉ))) ∘eᵉ
  ( associative-Σᵉ (UUᵉ (l1ᵉ ⊔ lᵉ)) (λ Xᵉ → mere-equivᵉ Bᵉ Xᵉ) (λ Xᵉ → (pr1ᵉ Xᵉ) ↪ᵈᵉ Aᵉ))

binomial-type'ᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (lsuc (l1ᵉ ⊔ l2ᵉ))
binomial-type'ᵉ {l1ᵉ} {l2ᵉ} Aᵉ Bᵉ = binomial-type-Level'ᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ Bᵉ

compute-binomial-typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) →
  binomial-typeᵉ Aᵉ Bᵉ ≃ᵉ binomial-type'ᵉ Aᵉ Bᵉ
compute-binomial-typeᵉ {l1ᵉ} {l2ᵉ} Aᵉ Bᵉ =
  compute-binomial-type-Levelᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ Bᵉ
```

### Remark 17.5.7

Noteᵉ thatᵉ theᵉ universeᵉ levelᵉ ofᵉ `small-binomial-type`ᵉ isᵉ lower.ᵉ

```agda
small-binomial-typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
small-binomial-typeᵉ Aᵉ Bᵉ =
  Σᵉ (Aᵉ → boolᵉ) (λ fᵉ → mere-equivᵉ Bᵉ (fiberᵉ fᵉ trueᵉ))

compute-small-binomial-typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) →
  binomial-typeᵉ Aᵉ Bᵉ ≃ᵉ small-binomial-typeᵉ Aᵉ Bᵉ
compute-small-binomial-typeᵉ Aᵉ Bᵉ =
  ( equiv-Σᵉ
    ( λ fᵉ → mere-equivᵉ Bᵉ (fiberᵉ fᵉ trueᵉ))
    ( equiv-postcompᵉ Aᵉ equiv-bool-Decidable-Propᵉ)
    ( λ Pᵉ →
      equiv-trunc-Propᵉ
        ( equiv-postcomp-equivᵉ
          ( equiv-totᵉ (λ aᵉ → compute-equiv-bool-Decidable-Propᵉ (Pᵉ aᵉ)))
          ( Bᵉ)))) ∘eᵉ
  ( compute-binomial-typeᵉ Aᵉ Bᵉ)
```

```agda
abstract
  binomial-type-over-emptyᵉ :
    {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → is-contrᵉ (binomial-typeᵉ Xᵉ emptyᵉ)
  binomial-type-over-emptyᵉ {lᵉ} {Xᵉ} =
    is-contr-equivᵉ
      ( raise-emptyᵉ lᵉ ↪ᵈᵉ Xᵉ)
      ( left-unit-law-Σ-is-contrᵉ
        ( is-contr-component-UU-Level-emptyᵉ lᵉ)
        ( Fin-UU-Finᵉ lᵉ zero-ℕᵉ))
      ( is-contr-equivᵉ
        ( emptyᵉ ↪ᵈᵉ Xᵉ)
        ( equiv-precomp-decidable-emb-equivᵉ (compute-raise-emptyᵉ lᵉ) Xᵉ)
        ( is-contr-equivᵉ
          ( is-decidable-embᵉ ex-falsoᵉ)
          ( left-unit-law-Σ-is-contrᵉ (universal-property-empty'ᵉ Xᵉ) ex-falsoᵉ)
          ( is-proof-irrelevant-is-propᵉ
            ( is-prop-is-decidable-embᵉ ex-falsoᵉ)
            ( is-decidable-emb-ex-falsoᵉ))))

abstract
  binomial-type-empty-underᵉ :
    {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} →
    type-trunc-Propᵉ Xᵉ → is-emptyᵉ (binomial-typeᵉ emptyᵉ Xᵉ)
  binomial-type-empty-underᵉ Hᵉ Yᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ empty-Propᵉ
      ( λ xᵉ →
        apply-universal-property-trunc-Propᵉ (pr2ᵉ (pr1ᵉ Yᵉ)) empty-Propᵉ
          ( λ eᵉ → map-decidable-embᵉ (pr2ᵉ Yᵉ) (map-equivᵉ eᵉ xᵉ)))

abstract
  recursion-binomial-type'ᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) →
    binomial-type'ᵉ (Maybeᵉ Aᵉ) (Maybeᵉ Bᵉ) ≃ᵉ
    (binomial-type'ᵉ Aᵉ Bᵉ +ᵉ binomial-type'ᵉ Aᵉ (Maybeᵉ Bᵉ))
  recursion-binomial-type'ᵉ Aᵉ Bᵉ =
    ( ( ( left-distributive-Σ-coproductᵉ
          ( Aᵉ → Decidable-Propᵉ _)
          ( λ Pᵉ → mere-equivᵉ Bᵉ (Σᵉ Aᵉ _))
          ( λ Pᵉ → mere-equivᵉ (Maybeᵉ Bᵉ) (Σᵉ Aᵉ _))) ∘eᵉ
        ( equiv-totᵉ
          ( λ Pᵉ →
            ( ( equiv-coproductᵉ
                ( ( ( equiv-iffᵉ
                      ( mere-equiv-Propᵉ (Maybeᵉ Bᵉ) (Maybeᵉ (Σᵉ Aᵉ _)))
                      ( mere-equiv-Propᵉ Bᵉ (Σᵉ Aᵉ _))
                      ( map-trunc-Propᵉ (equiv-equiv-Maybeᵉ))
                      ( map-trunc-Propᵉ
                        ( λ eᵉ → equiv-coproductᵉ eᵉ id-equivᵉ))) ∘eᵉ
                    ( equiv-trunc-Propᵉ
                      ( equiv-postcomp-equivᵉ
                        ( equiv-coproductᵉ
                          ( id-equivᵉ)
                          ( equiv-is-contrᵉ is-contr-raise-unitᵉ is-contr-unitᵉ))
                        ( Maybeᵉ Bᵉ)))) ∘eᵉ
                  ( left-unit-law-Σ-is-contrᵉ
                    ( is-torsorial-true-Propᵉ)
                    ( pairᵉ (raise-unit-Propᵉ _) raise-starᵉ)))
                ( ( equiv-trunc-Propᵉ
                    ( equiv-postcomp-equivᵉ
                      ( right-unit-law-coproduct-is-emptyᵉ
                        ( Σᵉ Aᵉ _)
                        ( raise-emptyᵉ _)
                        ( is-empty-raise-emptyᵉ))
                      ( Maybeᵉ Bᵉ))) ∘eᵉ
                  ( left-unit-law-Σ-is-contrᵉ
                    ( is-torsorial-false-Propᵉ)
                    ( pairᵉ (raise-empty-Propᵉ _) map-inv-raiseᵉ)))) ∘eᵉ
              ( right-distributive-Σ-coproductᵉ
                ( Σᵉ (Propᵉ _) type-Propᵉ)
                ( Σᵉ (Propᵉ _) (¬ᵉ_ ∘ᵉ type-Propᵉ))
                ( ind-coproductᵉ _
                  ( λ Qᵉ →
                    mere-equivᵉ (Maybeᵉ Bᵉ) ((Σᵉ Aᵉ _) +ᵉ (type-Propᵉ (pr1ᵉ Qᵉ))))
                  ( λ Qᵉ →
                    mere-equivᵉ
                      ( Maybeᵉ Bᵉ)
                      ( (Σᵉ Aᵉ _) +ᵉ (type-Propᵉ (pr1ᵉ Qᵉ))))))) ∘eᵉ
            ( equiv-Σᵉ
              ( ind-coproductᵉ _
                ( λ Qᵉ →
                  mere-equivᵉ
                    ( Maybeᵉ Bᵉ)
                    ( ( Σᵉ Aᵉ (λ aᵉ → type-Decidable-Propᵉ (Pᵉ aᵉ))) +ᵉ
                      ( type-Propᵉ (pr1ᵉ Qᵉ))))
                ( λ Qᵉ →
                  mere-equivᵉ
                    ( Maybeᵉ Bᵉ)
                    ( ( Σᵉ Aᵉ (λ aᵉ → type-Decidable-Propᵉ (Pᵉ aᵉ))) +ᵉ
                      ( type-Propᵉ (pr1ᵉ Qᵉ)))))
              ( split-Decidable-Propᵉ)
              ( ind-Σᵉ
                ( λ Qᵉ →
                  ind-Σᵉ
                    ( λ Hᵉ →
                      ind-coproductᵉ
                        ( _)
                        ( λ qᵉ → id-equivᵉ)
                        ( λ qᵉ → id-equivᵉ)))))))) ∘eᵉ
      ( associative-Σᵉ
        ( Aᵉ → Decidable-Propᵉ _)
        ( λ aᵉ → Decidable-Propᵉ _)
        ( λ tᵉ →
          mere-equivᵉ
            ( Maybeᵉ Bᵉ)
            ( ( Σᵉ Aᵉ (λ aᵉ → type-Decidable-Propᵉ (pr1ᵉ tᵉ aᵉ))) +ᵉ
              ( type-Decidable-Propᵉ (pr2ᵉ tᵉ)))))) ∘eᵉ
    ( equiv-Σᵉ
      ( λ pᵉ →
        mere-equivᵉ
          ( Maybeᵉ Bᵉ)
          ( ( Σᵉ Aᵉ (λ aᵉ → type-Decidable-Propᵉ (pr1ᵉ pᵉ aᵉ))) +ᵉ
            ( type-Decidable-Propᵉ (pr2ᵉ pᵉ))))
      ( equiv-universal-property-Maybeᵉ)
      ( λ uᵉ →
        equiv-trunc-Propᵉ
          ( equiv-postcomp-equivᵉ
            ( ( equiv-coproductᵉ
                ( id-equivᵉ)
                ( left-unit-law-Σᵉ (λ yᵉ → type-Decidable-Propᵉ (uᵉ (inrᵉ yᵉ))))) ∘eᵉ
              ( right-distributive-Σ-coproductᵉ Aᵉ unitᵉ
                ( λ xᵉ → type-Decidable-Propᵉ (uᵉ xᵉ))))
            ( Maybeᵉ Bᵉ))))

abstract
  binomial-type-Maybeᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) →
    binomial-typeᵉ (Maybeᵉ Aᵉ) (Maybeᵉ Bᵉ) ≃ᵉ
    (binomial-typeᵉ Aᵉ Bᵉ +ᵉ binomial-typeᵉ Aᵉ (Maybeᵉ Bᵉ))
  binomial-type-Maybeᵉ Aᵉ Bᵉ =
    ( inv-equivᵉ
      ( equiv-coproductᵉ
        ( compute-binomial-typeᵉ Aᵉ Bᵉ)
        ( compute-binomial-typeᵉ Aᵉ (Maybeᵉ Bᵉ))) ∘eᵉ
      ( recursion-binomial-type'ᵉ Aᵉ Bᵉ)) ∘eᵉ
    ( compute-binomial-typeᵉ (Maybeᵉ Aᵉ) (Maybeᵉ Bᵉ))
```

### Theorem 17.5.9

```agda
equiv-small-binomial-typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {A'ᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {B'ᵉ : UUᵉ l4ᵉ} →
  (Aᵉ ≃ᵉ A'ᵉ) → (Bᵉ ≃ᵉ B'ᵉ) → small-binomial-typeᵉ A'ᵉ B'ᵉ ≃ᵉ small-binomial-typeᵉ Aᵉ Bᵉ
equiv-small-binomial-typeᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} {l4ᵉ} {Aᵉ} {A'ᵉ} {Bᵉ} {B'ᵉ} eᵉ fᵉ =
  equiv-Σᵉ
    ( λ Pᵉ → mere-equivᵉ Bᵉ (fiberᵉ Pᵉ trueᵉ))
    ( equiv-precompᵉ eᵉ boolᵉ)
    ( λ Pᵉ →
      equiv-trunc-Propᵉ
        ( ( equiv-postcomp-equivᵉ
            ( inv-equivᵉ
              ( ( right-unit-law-Σ-is-contrᵉ
                  ( λ uᵉ →
                    is-contr-map-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) (pr1ᵉ uᵉ))) ∘eᵉ
                ( compute-fiber-compᵉ Pᵉ (map-equivᵉ eᵉ) trueᵉ))) Bᵉ) ∘eᵉ
          ( equiv-precomp-equivᵉ fᵉ (fiberᵉ Pᵉ trueᵉ))))

equiv-binomial-typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {A'ᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {B'ᵉ : UUᵉ l4ᵉ} →
  (Aᵉ ≃ᵉ A'ᵉ) → (Bᵉ ≃ᵉ B'ᵉ) → binomial-typeᵉ A'ᵉ B'ᵉ ≃ᵉ binomial-typeᵉ Aᵉ Bᵉ
equiv-binomial-typeᵉ eᵉ fᵉ =
  ( ( inv-equivᵉ (compute-small-binomial-typeᵉ _ _)) ∘eᵉ
    ( equiv-small-binomial-typeᵉ eᵉ fᵉ)) ∘eᵉ
  ( compute-small-binomial-typeᵉ _ _)

binomial-type-Finᵉ :
  (nᵉ mᵉ : ℕᵉ) → binomial-typeᵉ (Finᵉ nᵉ) (Finᵉ mᵉ) ≃ᵉ Finᵉ (binomial-coefficient-ℕᵉ nᵉ mᵉ)
binomial-type-Finᵉ zero-ℕᵉ zero-ℕᵉ =
  equiv-is-contrᵉ binomial-type-over-emptyᵉ is-contr-Fin-one-ℕᵉ
binomial-type-Finᵉ zero-ℕᵉ (succ-ℕᵉ mᵉ) =
  equiv-is-emptyᵉ (binomial-type-empty-underᵉ (unit-trunc-Propᵉ (inrᵉ starᵉ))) idᵉ
binomial-type-Finᵉ (succ-ℕᵉ nᵉ) zero-ℕᵉ =
  equiv-is-contrᵉ binomial-type-over-emptyᵉ is-contr-Fin-one-ℕᵉ
binomial-type-Finᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ mᵉ) =
  ( ( inv-equivᵉ
      ( Fin-add-ℕᵉ
        ( binomial-coefficient-ℕᵉ nᵉ mᵉ)
        ( binomial-coefficient-ℕᵉ nᵉ (succ-ℕᵉ mᵉ)))) ∘eᵉ
    ( equiv-coproductᵉ
      ( binomial-type-Finᵉ nᵉ mᵉ)
      ( binomial-type-Finᵉ nᵉ (succ-ℕᵉ mᵉ)))) ∘eᵉ
  ( binomial-type-Maybeᵉ (Finᵉ nᵉ) (Finᵉ mᵉ))

has-cardinality-binomial-typeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (nᵉ mᵉ : ℕᵉ) →
  has-cardinalityᵉ nᵉ Aᵉ → has-cardinalityᵉ mᵉ Bᵉ →
  has-cardinalityᵉ (binomial-coefficient-ℕᵉ nᵉ mᵉ) (binomial-typeᵉ Aᵉ Bᵉ)
has-cardinality-binomial-typeᵉ {Aᵉ = Aᵉ} {Bᵉ} nᵉ mᵉ Hᵉ Kᵉ =
  apply-universal-property-trunc-Propᵉ Hᵉ
    ( has-cardinality-Propᵉ (binomial-coefficient-ℕᵉ nᵉ mᵉ) (binomial-typeᵉ Aᵉ Bᵉ))
    ( λ eᵉ →
      apply-universal-property-trunc-Propᵉ Kᵉ
        ( has-cardinality-Propᵉ (binomial-coefficient-ℕᵉ nᵉ mᵉ) (binomial-typeᵉ Aᵉ Bᵉ))
        ( λ fᵉ →
          unit-trunc-Propᵉ
            ( inv-equivᵉ
              ( binomial-type-Finᵉ nᵉ mᵉ ∘eᵉ equiv-binomial-typeᵉ eᵉ fᵉ))))

binomial-type-UU-Finᵉ :
  {l1ᵉ l2ᵉ : Level} (nᵉ mᵉ : ℕᵉ) → UU-Finᵉ l1ᵉ nᵉ → UU-Finᵉ l2ᵉ mᵉ →
  UU-Finᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ) (binomial-coefficient-ℕᵉ nᵉ mᵉ)
pr1ᵉ (binomial-type-UU-Finᵉ nᵉ mᵉ Aᵉ Bᵉ) =
  binomial-typeᵉ (type-UU-Finᵉ nᵉ Aᵉ) (type-UU-Finᵉ mᵉ Bᵉ)
pr2ᵉ (binomial-type-UU-Finᵉ nᵉ mᵉ Aᵉ Bᵉ) =
  has-cardinality-binomial-typeᵉ nᵉ mᵉ
    ( has-cardinality-type-UU-Finᵉ nᵉ Aᵉ)
    ( has-cardinality-type-UU-Finᵉ mᵉ Bᵉ)

has-finite-cardinality-binomial-typeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  has-finite-cardinalityᵉ Aᵉ → has-finite-cardinalityᵉ Bᵉ →
  has-finite-cardinalityᵉ (binomial-typeᵉ Aᵉ Bᵉ)
pr1ᵉ (has-finite-cardinality-binomial-typeᵉ (pairᵉ nᵉ Hᵉ) (pairᵉ mᵉ Kᵉ)) =
  binomial-coefficient-ℕᵉ nᵉ mᵉ
pr2ᵉ (has-finite-cardinality-binomial-typeᵉ (pairᵉ nᵉ Hᵉ) (pairᵉ mᵉ Kᵉ)) =
  has-cardinality-binomial-typeᵉ nᵉ mᵉ Hᵉ Kᵉ

abstract
  is-finite-binomial-typeᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    is-finiteᵉ Aᵉ → is-finiteᵉ Bᵉ → is-finiteᵉ (binomial-typeᵉ Aᵉ Bᵉ)
  is-finite-binomial-typeᵉ Hᵉ Kᵉ =
    is-finite-has-finite-cardinalityᵉ
      ( has-finite-cardinality-binomial-typeᵉ
        ( has-finite-cardinality-is-finiteᵉ Hᵉ)
        ( has-finite-cardinality-is-finiteᵉ Kᵉ))

binomial-type-𝔽ᵉ : {l1ᵉ l2ᵉ : Level} → 𝔽ᵉ l1ᵉ → 𝔽ᵉ l2ᵉ → 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (binomial-type-𝔽ᵉ Aᵉ Bᵉ) = small-binomial-typeᵉ (type-𝔽ᵉ Aᵉ) (type-𝔽ᵉ Bᵉ)
pr2ᵉ (binomial-type-𝔽ᵉ Aᵉ Bᵉ) =
  is-finite-equivᵉ
    ( compute-small-binomial-typeᵉ (type-𝔽ᵉ Aᵉ) (type-𝔽ᵉ Bᵉ))
    ( is-finite-binomial-typeᵉ (is-finite-type-𝔽ᵉ Aᵉ) (is-finite-type-𝔽ᵉ Bᵉ))
```