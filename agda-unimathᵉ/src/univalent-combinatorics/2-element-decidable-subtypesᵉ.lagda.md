# `2`-element decidable subtypes

```agda
module univalent-combinatorics.2-element-decidable-subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.well-ordering-principle-standard-finite-typesᵉ

open import foundation.automorphismsᵉ
open import foundation.booleansᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.2-element-subtypesᵉ
open import univalent-combinatorics.2-element-typesᵉ
open import univalent-combinatorics.decidable-subtypesᵉ
open import univalent-combinatorics.dependent-function-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ 2-elementᵉ decidableᵉ subtypeᵉ ofᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ decidableᵉ subtypeᵉ ofᵉ `A`ᵉ ofᵉ
whichᵉ theᵉ underlyingᵉ typeᵉ hasᵉ 2 elements.ᵉ

## Definition

### The type of 2-element decidable subtypes

```agda
2-Element-Decidable-Subtypeᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
2-Element-Decidable-Subtypeᵉ l2ᵉ Xᵉ =
  Σᵉ (decidable-subtypeᵉ l2ᵉ Xᵉ) (λ Pᵉ → has-two-elementsᵉ (type-decidable-subtypeᵉ Pᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : 2-Element-Decidable-Subtypeᵉ l2ᵉ Xᵉ)
  where

  decidable-subtype-2-Element-Decidable-Subtypeᵉ : decidable-subtypeᵉ l2ᵉ Xᵉ
  decidable-subtype-2-Element-Decidable-Subtypeᵉ = pr1ᵉ Pᵉ

  subtype-2-Element-Decidable-Subtypeᵉ : subtypeᵉ l2ᵉ Xᵉ
  subtype-2-Element-Decidable-Subtypeᵉ =
    subtype-decidable-subtypeᵉ decidable-subtype-2-Element-Decidable-Subtypeᵉ

  is-decidable-subtype-subtype-2-Element-Decidable-Subtypeᵉ :
    is-decidable-subtypeᵉ subtype-2-Element-Decidable-Subtypeᵉ
  is-decidable-subtype-subtype-2-Element-Decidable-Subtypeᵉ =
    is-decidable-decidable-subtypeᵉ
      decidable-subtype-2-Element-Decidable-Subtypeᵉ

  is-in-2-Element-Decidable-Subtypeᵉ : Xᵉ → UUᵉ l2ᵉ
  is-in-2-Element-Decidable-Subtypeᵉ =
    is-in-decidable-subtypeᵉ decidable-subtype-2-Element-Decidable-Subtypeᵉ

  is-prop-is-in-2-Element-Decidable-Subtypeᵉ :
    (xᵉ : Xᵉ) → is-propᵉ (is-in-2-Element-Decidable-Subtypeᵉ xᵉ)
  is-prop-is-in-2-Element-Decidable-Subtypeᵉ =
    is-prop-is-in-decidable-subtypeᵉ
      decidable-subtype-2-Element-Decidable-Subtypeᵉ

  eq-is-in-2-Element-Decidable-Subtypeᵉ :
    {xᵉ : Xᵉ} {yᵉ zᵉ : is-in-2-Element-Decidable-Subtypeᵉ xᵉ} → Idᵉ yᵉ zᵉ
  eq-is-in-2-Element-Decidable-Subtypeᵉ {xᵉ} =
    eq-is-propᵉ (is-prop-is-in-2-Element-Decidable-Subtypeᵉ xᵉ)

  type-2-Element-Decidable-Subtypeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-2-Element-Decidable-Subtypeᵉ =
    type-decidable-subtypeᵉ decidable-subtype-2-Element-Decidable-Subtypeᵉ

  inclusion-2-Element-Decidable-Subtypeᵉ : type-2-Element-Decidable-Subtypeᵉ → Xᵉ
  inclusion-2-Element-Decidable-Subtypeᵉ =
    inclusion-decidable-subtypeᵉ decidable-subtype-2-Element-Decidable-Subtypeᵉ

  is-emb-inclusion-2-Element-Decidable-Subtypeᵉ :
    is-embᵉ inclusion-2-Element-Decidable-Subtypeᵉ
  is-emb-inclusion-2-Element-Decidable-Subtypeᵉ =
    is-emb-inclusion-decidable-subtypeᵉ
      decidable-subtype-2-Element-Decidable-Subtypeᵉ

  is-injective-inclusion-2-Element-Decidable-Subtypeᵉ :
    is-injectiveᵉ inclusion-2-Element-Decidable-Subtypeᵉ
  is-injective-inclusion-2-Element-Decidable-Subtypeᵉ =
    is-injective-inclusion-decidable-subtypeᵉ
      decidable-subtype-2-Element-Decidable-Subtypeᵉ

  has-two-elements-type-2-Element-Decidable-Subtypeᵉ :
    has-two-elementsᵉ type-2-Element-Decidable-Subtypeᵉ
  has-two-elements-type-2-Element-Decidable-Subtypeᵉ = pr2ᵉ Pᵉ

  2-element-type-2-Element-Decidable-Subtypeᵉ : 2-Element-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ 2-element-type-2-Element-Decidable-Subtypeᵉ =
    type-2-Element-Decidable-Subtypeᵉ
  pr2ᵉ 2-element-type-2-Element-Decidable-Subtypeᵉ =
    has-two-elements-type-2-Element-Decidable-Subtypeᵉ

  is-inhabited-type-2-Element-Decidable-Subtypeᵉ :
    type-trunc-Propᵉ type-2-Element-Decidable-Subtypeᵉ
  is-inhabited-type-2-Element-Decidable-Subtypeᵉ =
    is-inhabited-2-Element-Typeᵉ 2-element-type-2-Element-Decidable-Subtypeᵉ
```

### The standard 2-element decidable subtypes in a type with decidable equality

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (dᵉ : has-decidable-equalityᵉ Xᵉ) {xᵉ yᵉ : Xᵉ}
  (npᵉ : xᵉ ≠ᵉ yᵉ)
  where

  type-prop-standard-2-Element-Decidable-Subtypeᵉ : Xᵉ → UUᵉ lᵉ
  type-prop-standard-2-Element-Decidable-Subtypeᵉ =
    type-prop-standard-2-Element-Subtypeᵉ
      ( pairᵉ Xᵉ (is-set-has-decidable-equalityᵉ dᵉ))
      ( npᵉ)

  is-prop-type-prop-standard-2-Element-Decidable-Subtypeᵉ :
    (zᵉ : Xᵉ) → is-propᵉ (type-prop-standard-2-Element-Decidable-Subtypeᵉ zᵉ)
  is-prop-type-prop-standard-2-Element-Decidable-Subtypeᵉ =
    is-prop-type-prop-standard-2-Element-Subtypeᵉ
      ( pairᵉ Xᵉ (is-set-has-decidable-equalityᵉ dᵉ))
      ( npᵉ)

  is-decidable-type-prop-standard-2-Element-Decidable-Subtypeᵉ :
    (zᵉ : Xᵉ) → is-decidableᵉ (type-prop-standard-2-Element-Decidable-Subtypeᵉ zᵉ)
  is-decidable-type-prop-standard-2-Element-Decidable-Subtypeᵉ zᵉ =
    is-decidable-coproductᵉ (dᵉ xᵉ zᵉ) (dᵉ yᵉ zᵉ)

  subtype-standard-2-Element-Decidable-Subtypeᵉ : subtypeᵉ lᵉ Xᵉ
  subtype-standard-2-Element-Decidable-Subtypeᵉ =
    subtype-standard-2-Element-Subtypeᵉ
      ( pairᵉ Xᵉ (is-set-has-decidable-equalityᵉ dᵉ))
      ( npᵉ)

  decidable-subtype-standard-2-Element-Decidable-Subtypeᵉ :
    decidable-subtypeᵉ lᵉ Xᵉ
  pr1ᵉ (decidable-subtype-standard-2-Element-Decidable-Subtypeᵉ zᵉ) =
    type-prop-standard-2-Element-Decidable-Subtypeᵉ zᵉ
  pr1ᵉ (pr2ᵉ (decidable-subtype-standard-2-Element-Decidable-Subtypeᵉ zᵉ)) =
    is-prop-type-prop-standard-2-Element-Decidable-Subtypeᵉ zᵉ
  pr2ᵉ (pr2ᵉ (decidable-subtype-standard-2-Element-Decidable-Subtypeᵉ zᵉ)) =
    is-decidable-type-prop-standard-2-Element-Decidable-Subtypeᵉ zᵉ

  type-standard-2-Element-Decidable-Subtypeᵉ : UUᵉ lᵉ
  type-standard-2-Element-Decidable-Subtypeᵉ =
    type-standard-2-Element-Subtypeᵉ
      ( pairᵉ Xᵉ (is-set-has-decidable-equalityᵉ dᵉ))
      ( npᵉ)

  equiv-type-standard-2-Element-Decidable-Subtypeᵉ :
    Finᵉ 2 ≃ᵉ type-standard-2-Element-Decidable-Subtypeᵉ
  equiv-type-standard-2-Element-Decidable-Subtypeᵉ =
    equiv-type-standard-2-Element-Subtypeᵉ
      ( pairᵉ Xᵉ (is-set-has-decidable-equalityᵉ dᵉ))
      ( npᵉ)

  has-two-elements-type-standard-2-Element-Decidable-Subtypeᵉ :
    has-two-elementsᵉ type-standard-2-Element-Decidable-Subtypeᵉ
  has-two-elements-type-standard-2-Element-Decidable-Subtypeᵉ =
    has-two-elements-type-standard-2-Element-Subtypeᵉ
      ( pairᵉ Xᵉ (is-set-has-decidable-equalityᵉ dᵉ))
      ( npᵉ)

  2-element-type-standard-2-Element-Decidable-Subtypeᵉ : 2-Element-Typeᵉ lᵉ
  pr1ᵉ 2-element-type-standard-2-Element-Decidable-Subtypeᵉ =
    type-standard-2-Element-Decidable-Subtypeᵉ
  pr2ᵉ 2-element-type-standard-2-Element-Decidable-Subtypeᵉ =
    has-two-elements-type-standard-2-Element-Decidable-Subtypeᵉ

  standard-2-Element-Decidable-Subtypeᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ
  pr1ᵉ standard-2-Element-Decidable-Subtypeᵉ =
    decidable-subtype-standard-2-Element-Decidable-Subtypeᵉ
  pr2ᵉ standard-2-Element-Decidable-Subtypeᵉ =
    has-two-elements-type-standard-2-Element-Decidable-Subtypeᵉ

module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (dᵉ : has-decidable-equalityᵉ Xᵉ) {xᵉ yᵉ : Xᵉ}
  (npᵉ : xᵉ ≠ᵉ yᵉ)
  where

  is-commutative-standard-2-Element-Decidable-Subtypeᵉ :
    Idᵉ
      ( standard-2-Element-Decidable-Subtypeᵉ dᵉ npᵉ)
      ( standard-2-Element-Decidable-Subtypeᵉ dᵉ (λ pᵉ → npᵉ (invᵉ pᵉ)))
  is-commutative-standard-2-Element-Decidable-Subtypeᵉ =
    eq-pair-Σᵉ
      ( eq-htpyᵉ
        (λ zᵉ →
          eq-pair-Σᵉ
            ( eq-equivᵉ
              ( pairᵉ
                ( map-commutative-coproductᵉ (Idᵉ xᵉ zᵉ) (Idᵉ yᵉ zᵉ))
                ( is-equiv-map-commutative-coproductᵉ (Idᵉ xᵉ zᵉ) (Idᵉ yᵉ zᵉ))))
            ( eq-pair-Σᵉ
              ( eq-is-propᵉ
                ( is-prop-is-propᵉ
                  ( type-Decidable-Propᵉ
                    ( pr1ᵉ
                      ( standard-2-Element-Decidable-Subtypeᵉ dᵉ
                        ( λ pᵉ → npᵉ (invᵉ pᵉ)))
                      ( zᵉ)))))
              ( eq-is-propᵉ
                ( is-prop-is-decidableᵉ
                  ( is-prop-type-Decidable-Propᵉ
                    ( pr1ᵉ
                      ( standard-2-Element-Decidable-Subtypeᵉ dᵉ
                        ( λ pᵉ → npᵉ (invᵉ pᵉ)))
                      ( zᵉ))))))))
      ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)

module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (dᵉ : has-decidable-equalityᵉ Xᵉ) {xᵉ yᵉ zᵉ wᵉ : Xᵉ}
  (npᵉ : xᵉ ≠ᵉ yᵉ) (nqᵉ : zᵉ ≠ᵉ wᵉ) (rᵉ : xᵉ ＝ᵉ zᵉ) (sᵉ : yᵉ ＝ᵉ wᵉ)
  where

  eq-equal-elements-standard-2-Element-Decidable-Subtypeᵉ :
    Idᵉ
      ( standard-2-Element-Decidable-Subtypeᵉ dᵉ npᵉ)
      ( standard-2-Element-Decidable-Subtypeᵉ dᵉ nqᵉ)
  eq-equal-elements-standard-2-Element-Decidable-Subtypeᵉ =
    eq-pair-Σᵉ
      ( eq-htpyᵉ
        ( λ vᵉ →
          eq-pair-Σᵉ
            ( eq-equivᵉ
              ( equiv-coproductᵉ
                ( equiv-concatᵉ (invᵉ rᵉ) vᵉ)
                ( equiv-concatᵉ (invᵉ sᵉ) vᵉ)))
            ( eq-pair-Σᵉ
              ( eq-is-propᵉ
                ( is-prop-is-propᵉ
                  ( type-Decidable-Propᵉ
                    ( pr1ᵉ
                      ( standard-2-Element-Decidable-Subtypeᵉ dᵉ nqᵉ)
                      ( vᵉ)))))
              ( eq-is-propᵉ
                ( is-prop-is-decidableᵉ
                  ( is-prop-type-Decidable-Propᵉ
                    ( pr1ᵉ
                      ( standard-2-Element-Decidable-Subtypeᵉ dᵉ nqᵉ)
                      ( vᵉ))))))))
      ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)
```

### Swapping the elements in a 2-element subtype

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : 2-Element-Decidable-Subtypeᵉ l2ᵉ Xᵉ)
  where

  swap-2-Element-Decidable-Subtypeᵉ : Autᵉ (type-2-Element-Decidable-Subtypeᵉ Pᵉ)
  swap-2-Element-Decidable-Subtypeᵉ =
    swap-2-Element-Typeᵉ (2-element-type-2-Element-Decidable-Subtypeᵉ Pᵉ)

  map-swap-2-Element-Decidable-Subtypeᵉ :
    type-2-Element-Decidable-Subtypeᵉ Pᵉ → type-2-Element-Decidable-Subtypeᵉ Pᵉ
  map-swap-2-Element-Decidable-Subtypeᵉ =
    map-swap-2-Element-Typeᵉ (2-element-type-2-Element-Decidable-Subtypeᵉ Pᵉ)

  compute-swap-2-Element-Decidable-Subtypeᵉ :
    (xᵉ yᵉ : type-2-Element-Decidable-Subtypeᵉ Pᵉ) → xᵉ ≠ᵉ yᵉ →
    Idᵉ (map-swap-2-Element-Decidable-Subtypeᵉ xᵉ) yᵉ
  compute-swap-2-Element-Decidable-Subtypeᵉ =
    compute-swap-2-Element-Typeᵉ (2-element-type-2-Element-Decidable-Subtypeᵉ Pᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ l1ᵉ nᵉ)
  where

  is-finite-2-Element-Decidable-Subtypeᵉ :
    is-finiteᵉ (2-Element-Decidable-Subtypeᵉ l2ᵉ (type-UU-Finᵉ nᵉ Xᵉ))
  is-finite-2-Element-Decidable-Subtypeᵉ =
    is-finite-type-decidable-subtypeᵉ
      (λ Pᵉ →
        pairᵉ
          ( has-cardinalityᵉ 2
            ( Σᵉ (type-UU-Finᵉ nᵉ Xᵉ) (type-Decidable-Propᵉ ∘ᵉ Pᵉ)))
          ( pairᵉ
            ( is-prop-type-trunc-Propᵉ)
            ( is-decidable-equivᵉ
              ( equiv-has-cardinality-id-number-of-elements-is-finiteᵉ
                ( Σᵉ (type-UU-Finᵉ nᵉ Xᵉ) (type-Decidable-Propᵉ ∘ᵉ Pᵉ))
                ( is-finite-type-decidable-subtypeᵉ Pᵉ
                  ( is-finite-type-UU-Finᵉ nᵉ Xᵉ))
                ( 2ᵉ))
              ( has-decidable-equality-ℕᵉ
                ( number-of-elements-is-finiteᵉ
                  ( is-finite-type-decidable-subtypeᵉ Pᵉ
                    ( is-finite-type-UU-Finᵉ nᵉ Xᵉ)))
                ( 2ᵉ)))))
      ( is-finite-Πᵉ
        ( is-finite-type-UU-Finᵉ nᵉ Xᵉ)
        ( λ xᵉ →
          is-finite-equivᵉ
            ( inv-equivᵉ equiv-bool-Decidable-Propᵉ ∘eᵉ equiv-bool-Fin-two-ℕᵉ)
            ( is-finite-Finᵉ 2ᵉ)))
```

### 2-element decidable subtypes are closed under precomposition with an equivalence

```agda
precomp-equiv-2-Element-Decidable-Subtypeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} → Xᵉ ≃ᵉ Yᵉ →
    2-Element-Decidable-Subtypeᵉ l3ᵉ Yᵉ → 2-Element-Decidable-Subtypeᵉ l3ᵉ Xᵉ
pr1ᵉ (precomp-equiv-2-Element-Decidable-Subtypeᵉ eᵉ (pairᵉ Pᵉ Hᵉ)) =
  Pᵉ ∘ᵉ (map-equivᵉ eᵉ)
pr2ᵉ (precomp-equiv-2-Element-Decidable-Subtypeᵉ eᵉ (pairᵉ Pᵉ Hᵉ)) =
  transitive-mere-equivᵉ
    ( Finᵉ 2ᵉ)
    ( type-subtypeᵉ (prop-Decidable-Propᵉ ∘ᵉ Pᵉ))
    ( type-subtypeᵉ (prop-Decidable-Propᵉ ∘ᵉ (Pᵉ ∘ᵉ pr1ᵉ eᵉ)))
    ( unit-trunc-Propᵉ
      ( equiv-subtype-equivᵉ
        ( inv-equivᵉ eᵉ)
        ( subtype-decidable-subtypeᵉ Pᵉ)
        ( subtype-decidable-subtypeᵉ (Pᵉ ∘ᵉ (map-equivᵉ eᵉ)))
        ( λ xᵉ →
          iff-equivᵉ
            ( trᵉ
              ( λ gᵉ →
                ( type-Decidable-Propᵉ (Pᵉ xᵉ)) ≃ᵉ
                ( type-Decidable-Propᵉ (Pᵉ (map-equivᵉ gᵉ xᵉ))))
              ( invᵉ (right-inverse-law-equivᵉ eᵉ))
              ( id-equivᵉ)))))
    ( Hᵉ)

preserves-comp-precomp-equiv-2-Element-Decidable-Subtypeᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Zᵉ : UUᵉ l3ᵉ} (eᵉ : Xᵉ ≃ᵉ Yᵉ) →
  ( fᵉ : Yᵉ ≃ᵉ Zᵉ) →
  Idᵉ
    ( precomp-equiv-2-Element-Decidable-Subtypeᵉ {l3ᵉ = l4ᵉ} (fᵉ ∘eᵉ eᵉ))
    ( ( precomp-equiv-2-Element-Decidable-Subtypeᵉ eᵉ) ∘ᵉ
      ( precomp-equiv-2-Element-Decidable-Subtypeᵉ fᵉ))
preserves-comp-precomp-equiv-2-Element-Decidable-Subtypeᵉ eᵉ fᵉ =
  eq-htpyᵉ
    ( λ (pairᵉ Pᵉ Hᵉ) →
      eq-pair-eq-fiberᵉ
        ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))
```

## Properties

### Any 2-element decidable subtype of a standard finite type is a standard 2-element decidable subtype

```agda
module _
  {lᵉ : Level} {nᵉ : ℕᵉ} (Pᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ (Finᵉ nᵉ))
  where

  element-subtype-2-element-decidable-subtype-Finᵉ :
    type-2-Element-Decidable-Subtypeᵉ Pᵉ
  element-subtype-2-element-decidable-subtype-Finᵉ =
    ε-operator-decidable-subtype-Finᵉ nᵉ
      ( decidable-subtype-2-Element-Decidable-Subtypeᵉ Pᵉ)
      ( is-inhabited-type-2-Element-Decidable-Subtypeᵉ Pᵉ)

  element-2-element-decidable-subtype-Finᵉ : Finᵉ nᵉ
  element-2-element-decidable-subtype-Finᵉ =
    pr1ᵉ element-subtype-2-element-decidable-subtype-Finᵉ

  in-subtype-element-2-element-decidable-subtype-Finᵉ :
    is-in-2-Element-Decidable-Subtypeᵉ Pᵉ
      element-2-element-decidable-subtype-Finᵉ
  in-subtype-element-2-element-decidable-subtype-Finᵉ =
    pr2ᵉ element-subtype-2-element-decidable-subtype-Finᵉ

  other-element-subtype-2-element-decidable-subtype-Finᵉ :
    type-2-Element-Decidable-Subtypeᵉ Pᵉ
  other-element-subtype-2-element-decidable-subtype-Finᵉ =
    map-swap-2-Element-Typeᵉ
      ( 2-element-type-2-Element-Decidable-Subtypeᵉ Pᵉ)
      ( element-subtype-2-element-decidable-subtype-Finᵉ)

  other-element-2-element-decidable-subtype-Finᵉ : Finᵉ nᵉ
  other-element-2-element-decidable-subtype-Finᵉ =
    pr1ᵉ other-element-subtype-2-element-decidable-subtype-Finᵉ

  in-subtype-other-element-2-element-decidable-subtype-Finᵉ :
    is-in-2-Element-Decidable-Subtypeᵉ Pᵉ
      other-element-2-element-decidable-subtype-Finᵉ
  in-subtype-other-element-2-element-decidable-subtype-Finᵉ =
    pr2ᵉ other-element-subtype-2-element-decidable-subtype-Finᵉ

  abstract
    unequal-elements-2-element-decidable-subtype-Finᵉ :
      ¬ᵉ ( Idᵉ
          ( element-2-element-decidable-subtype-Finᵉ)
          ( other-element-2-element-decidable-subtype-Finᵉ))
    unequal-elements-2-element-decidable-subtype-Finᵉ pᵉ =
      has-no-fixed-points-swap-2-Element-Typeᵉ
        ( 2-element-type-2-Element-Decidable-Subtypeᵉ Pᵉ)
        { element-subtype-2-element-decidable-subtype-Finᵉ}
        ( eq-type-subtypeᵉ
          ( subtype-2-Element-Decidable-Subtypeᵉ Pᵉ)
          ( invᵉ pᵉ))
```

### Types of decidable subtypes of any universe level are equivalent

```agda
module _
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ)
  where

  equiv-universes-2-Element-Decidable-Subtypeᵉ :
    (lᵉ l'ᵉ : Level) →
    2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ ≃ᵉ 2-Element-Decidable-Subtypeᵉ l'ᵉ Xᵉ
  equiv-universes-2-Element-Decidable-Subtypeᵉ lᵉ l'ᵉ =
    equiv-subtype-equivᵉ
      ( equiv-universes-decidable-subtypeᵉ Xᵉ lᵉ l'ᵉ)
      ( λ Pᵉ →
        pairᵉ
          ( has-two-elementsᵉ (type-decidable-subtypeᵉ Pᵉ))
          ( is-prop-type-trunc-Propᵉ))
      ( λ Pᵉ →
        pairᵉ
          ( has-two-elementsᵉ (type-decidable-subtypeᵉ Pᵉ))
          ( is-prop-type-trunc-Propᵉ))
      ( λ Sᵉ →
        pairᵉ
          ( λ hᵉ →
            map-trunc-Propᵉ
              ( λ h'ᵉ →
                equiv-Σᵉ
                  ( λ xᵉ →
                    type-Decidable-Propᵉ
                      ( map-equivᵉ
                        ( equiv-universes-decidable-subtypeᵉ Xᵉ lᵉ l'ᵉ)
                        ( Sᵉ)
                        ( xᵉ)))
                  ( id-equivᵉ)
                  ( λ xᵉ →
                    equiv-iff'ᵉ
                      ( prop-Decidable-Propᵉ (Sᵉ xᵉ))
                      ( prop-Decidable-Propᵉ
                        ( map-equivᵉ
                          ( equiv-universes-decidable-subtypeᵉ Xᵉ lᵉ l'ᵉ)
                          ( Sᵉ)
                          ( xᵉ)))
                      ( iff-universes-decidable-subtypeᵉ Xᵉ lᵉ l'ᵉ Sᵉ xᵉ)) ∘eᵉ
                  ( h'ᵉ))
              ( hᵉ))
          ( λ hᵉ →
            map-trunc-Propᵉ
              ( λ h'ᵉ →
                equiv-Σᵉ
                  ( λ xᵉ → type-Decidable-Propᵉ (Sᵉ xᵉ))
                  ( id-equivᵉ)
                  ( λ xᵉ →
                    inv-equivᵉ
                      ( equiv-iff'ᵉ
                        ( prop-Decidable-Propᵉ (Sᵉ xᵉ))
                        ( prop-Decidable-Propᵉ
                          ( map-equivᵉ
                            ( equiv-universes-decidable-subtypeᵉ Xᵉ lᵉ l'ᵉ)
                            ( Sᵉ)
                            ( xᵉ)))
                        ( iff-universes-decidable-subtypeᵉ Xᵉ lᵉ l'ᵉ Sᵉ xᵉ))) ∘eᵉ
                  ( h'ᵉ))
              ( hᵉ)))
```