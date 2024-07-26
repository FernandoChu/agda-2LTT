# The well-ordering principle of the standard finite types

```agda
module elementary-number-theory.well-ordering-principle-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-typesᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.well-ordering-principle-natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-subtypesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.hilberts-epsilon-operatorsᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.decidable-dependent-pair-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ standardᵉ finiteᵉ typesᵉ inheritᵉ aᵉ well-orderingᵉ principleᵉ fromᵉ theᵉ naturalᵉ
numbers.ᵉ

## Properties

### For any decidable family `P` over `Fin n`, if `P x` doesn't hold for all `x` then there exists an `x` for which `P x` is false

```agda
exists-not-not-for-all-Finᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Pᵉ : Finᵉ kᵉ → UUᵉ lᵉ} → (is-decidable-famᵉ Pᵉ) →
  ¬ᵉ ((xᵉ : Finᵉ kᵉ) → Pᵉ xᵉ) → Σᵉ (Finᵉ kᵉ) (λ xᵉ → ¬ᵉ (Pᵉ xᵉ))
exists-not-not-for-all-Finᵉ {lᵉ} zero-ℕᵉ dᵉ Hᵉ = ex-falsoᵉ (Hᵉ ind-emptyᵉ)
exists-not-not-for-all-Finᵉ {lᵉ} (succ-ℕᵉ kᵉ) {Pᵉ} dᵉ Hᵉ with dᵉ (inrᵉ starᵉ)
... | inlᵉ pᵉ =
  Tᵉ ( exists-not-not-for-all-Finᵉ kᵉ
      ( λ xᵉ → dᵉ (inlᵉ xᵉ))
      ( λ fᵉ → Hᵉ (ind-coproductᵉ Pᵉ fᵉ (ind-unitᵉ pᵉ))))
  where
  Tᵉ : Σᵉ (Finᵉ kᵉ) (λ xᵉ → ¬ᵉ (Pᵉ (inlᵉ xᵉ))) → Σᵉ (Finᵉ (succ-ℕᵉ kᵉ)) (λ xᵉ → ¬ᵉ (Pᵉ xᵉ))
  Tᵉ zᵉ = pairᵉ (inlᵉ (pr1ᵉ zᵉ)) (pr2ᵉ zᵉ)
... | inrᵉ fᵉ = pairᵉ (inrᵉ starᵉ) fᵉ

exists-not-not-for-all-countᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : Xᵉ → UUᵉ l2ᵉ) →
  (is-decidable-famᵉ Pᵉ) → countᵉ Xᵉ →
  ¬ᵉ ((xᵉ : Xᵉ) → Pᵉ xᵉ) → Σᵉ Xᵉ (λ xᵉ → ¬ᵉ (Pᵉ xᵉ))
exists-not-not-for-all-countᵉ {l1ᵉ} {l2ᵉ} {Xᵉ} Pᵉ pᵉ eᵉ =
  ( gᵉ) ∘ᵉ
  ( ( exists-not-not-for-all-Finᵉ
      ( number-of-elements-countᵉ eᵉ)
      ( pᵉ ∘ᵉ map-equiv-countᵉ eᵉ)) ∘ᵉ fᵉ)
  where
  kᵉ : ℕᵉ
  kᵉ = number-of-elements-countᵉ eᵉ
  P'ᵉ : Finᵉ kᵉ → UUᵉ l2ᵉ
  P'ᵉ = Pᵉ ∘ᵉ map-equivᵉ (pr2ᵉ eᵉ)
  fᵉ : ¬ᵉ ((xᵉ : Xᵉ) → Pᵉ xᵉ) → ¬ᵉ ((xᵉ : Finᵉ kᵉ) → P'ᵉ xᵉ)
  fᵉ nfᵉ f'ᵉ =
    nfᵉ
      ( λ xᵉ →
        trᵉ
          ( Pᵉ)
          ( htpy-eq-equivᵉ (right-inverse-law-equivᵉ (pr2ᵉ eᵉ)) xᵉ)
          ( f'ᵉ (map-inv-equivᵉ (pr2ᵉ eᵉ) xᵉ)))
  gᵉ : Σᵉ (Finᵉ kᵉ) (λ xᵉ → ¬ᵉ (P'ᵉ xᵉ)) → Σᵉ Xᵉ (λ xᵉ → ¬ᵉ (Pᵉ xᵉ))
  pr1ᵉ (gᵉ (pairᵉ lᵉ npᵉ)) = map-equivᵉ (pr2ᵉ eᵉ) lᵉ
  pr2ᵉ (gᵉ (pairᵉ lᵉ npᵉ)) xᵉ = npᵉ xᵉ
```

```agda
is-lower-bound-Finᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : Finᵉ kᵉ → UUᵉ lᵉ) → Finᵉ kᵉ → UUᵉ lᵉ
is-lower-bound-Finᵉ kᵉ Pᵉ xᵉ = (yᵉ : Finᵉ kᵉ) → Pᵉ yᵉ → leq-Finᵉ kᵉ xᵉ yᵉ

abstract
  is-prop-is-lower-bound-Finᵉ :
    {lᵉ : Level} (kᵉ : ℕᵉ) {Pᵉ : Finᵉ kᵉ → UUᵉ lᵉ} (xᵉ : Finᵉ kᵉ) →
    is-propᵉ (is-lower-bound-Finᵉ kᵉ Pᵉ xᵉ)
  is-prop-is-lower-bound-Finᵉ kᵉ xᵉ =
    is-prop-Πᵉ (λ yᵉ → is-prop-function-typeᵉ (is-prop-leq-Finᵉ kᵉ xᵉ yᵉ))

  is-lower-bound-fin-Propᵉ :
    {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : Finᵉ kᵉ → UUᵉ lᵉ) (xᵉ : Finᵉ kᵉ) → Propᵉ lᵉ
  pr1ᵉ (is-lower-bound-fin-Propᵉ kᵉ Pᵉ xᵉ) = is-lower-bound-Finᵉ kᵉ Pᵉ xᵉ
  pr2ᵉ (is-lower-bound-fin-Propᵉ kᵉ Pᵉ xᵉ) = is-prop-is-lower-bound-Finᵉ kᵉ xᵉ

minimal-element-Finᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : Finᵉ kᵉ → UUᵉ lᵉ) → UUᵉ lᵉ
minimal-element-Finᵉ kᵉ Pᵉ =
  Σᵉ (Finᵉ kᵉ) (λ xᵉ → (Pᵉ xᵉ) ×ᵉ is-lower-bound-Finᵉ kᵉ Pᵉ xᵉ)

abstract
  all-elements-equal-minimal-element-Finᵉ :
    {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : subtypeᵉ lᵉ (Finᵉ kᵉ)) →
    all-elements-equalᵉ (minimal-element-Finᵉ kᵉ (is-in-subtypeᵉ Pᵉ))
  all-elements-equal-minimal-element-Finᵉ kᵉ Pᵉ
    (pairᵉ xᵉ (pairᵉ pᵉ lᵉ)) (pairᵉ yᵉ (pairᵉ qᵉ mᵉ)) =
    eq-type-subtypeᵉ
      ( λ tᵉ →
        product-Propᵉ (Pᵉ tᵉ) (is-lower-bound-fin-Propᵉ kᵉ (is-in-subtypeᵉ Pᵉ) tᵉ))
      ( antisymmetric-leq-Finᵉ kᵉ xᵉ yᵉ (lᵉ yᵉ qᵉ) (mᵉ xᵉ pᵉ))

abstract
  is-prop-minimal-element-Finᵉ :
    {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : subtypeᵉ lᵉ (Finᵉ kᵉ)) →
    is-propᵉ (minimal-element-Finᵉ kᵉ (is-in-subtypeᵉ Pᵉ))
  is-prop-minimal-element-Finᵉ kᵉ Pᵉ =
    is-prop-all-elements-equalᵉ (all-elements-equal-minimal-element-Finᵉ kᵉ Pᵉ)

minimal-element-Fin-Propᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : subtypeᵉ lᵉ (Finᵉ kᵉ)) → Propᵉ lᵉ
pr1ᵉ (minimal-element-Fin-Propᵉ kᵉ Pᵉ) = minimal-element-Finᵉ kᵉ (is-in-subtypeᵉ Pᵉ)
pr2ᵉ (minimal-element-Fin-Propᵉ kᵉ Pᵉ) = is-prop-minimal-element-Finᵉ kᵉ Pᵉ

is-lower-bound-inl-Finᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Pᵉ : Finᵉ (succ-ℕᵉ kᵉ) → UUᵉ lᵉ} {xᵉ : Finᵉ kᵉ} →
  is-lower-bound-Finᵉ kᵉ (Pᵉ ∘ᵉ inlᵉ) xᵉ →
  is-lower-bound-Finᵉ (succ-ℕᵉ kᵉ) Pᵉ (inl-Finᵉ kᵉ xᵉ)
is-lower-bound-inl-Finᵉ kᵉ Hᵉ (inlᵉ yᵉ) pᵉ = Hᵉ yᵉ pᵉ
is-lower-bound-inl-Finᵉ kᵉ {Pᵉ} {xᵉ} Hᵉ (inrᵉ starᵉ) pᵉ =
  ( leq-neg-one-Finᵉ kᵉ (inlᵉ xᵉ))

well-ordering-principle-Σ-Finᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Pᵉ : Finᵉ kᵉ → UUᵉ lᵉ} → ((xᵉ : Finᵉ kᵉ) → is-decidableᵉ (Pᵉ xᵉ)) →
  Σᵉ (Finᵉ kᵉ) Pᵉ → minimal-element-Finᵉ kᵉ Pᵉ
pr1ᵉ (well-ordering-principle-Σ-Finᵉ (succ-ℕᵉ kᵉ) dᵉ (pairᵉ (inlᵉ xᵉ) pᵉ)) =
  inlᵉ (pr1ᵉ (well-ordering-principle-Σ-Finᵉ kᵉ (λ x'ᵉ → dᵉ (inlᵉ x'ᵉ)) (pairᵉ xᵉ pᵉ)))
pr1ᵉ (pr2ᵉ (well-ordering-principle-Σ-Finᵉ (succ-ℕᵉ kᵉ) dᵉ (pairᵉ (inlᵉ xᵉ) pᵉ))) =
  pr1ᵉ (pr2ᵉ (well-ordering-principle-Σ-Finᵉ kᵉ (λ x'ᵉ → dᵉ (inlᵉ x'ᵉ)) (pairᵉ xᵉ pᵉ)))
pr2ᵉ (pr2ᵉ (well-ordering-principle-Σ-Finᵉ (succ-ℕᵉ kᵉ) dᵉ (pairᵉ (inlᵉ xᵉ) pᵉ))) =
  is-lower-bound-inl-Finᵉ kᵉ (pr2ᵉ (pr2ᵉ mᵉ))
  where
  mᵉ = well-ordering-principle-Σ-Finᵉ kᵉ (λ x'ᵉ → dᵉ (inlᵉ x'ᵉ)) (pairᵉ xᵉ pᵉ)
well-ordering-principle-Σ-Finᵉ (succ-ℕᵉ kᵉ) {Pᵉ} dᵉ (pairᵉ (inrᵉ starᵉ) pᵉ)
  with
  is-decidable-Σ-Finᵉ kᵉ (λ tᵉ → dᵉ (inlᵉ tᵉ))
... | inlᵉ tᵉ =
  pairᵉ
    ( inlᵉ (pr1ᵉ mᵉ))
    ( pairᵉ (pr1ᵉ (pr2ᵉ mᵉ)) (is-lower-bound-inl-Finᵉ kᵉ (pr2ᵉ (pr2ᵉ mᵉ))))
  where
  mᵉ = well-ordering-principle-Σ-Finᵉ kᵉ (λ x'ᵉ → dᵉ (inlᵉ x'ᵉ)) tᵉ
... | inrᵉ fᵉ =
  pairᵉ
    ( inrᵉ starᵉ)
    ( pairᵉ pᵉ gᵉ)
  where
  gᵉ : (yᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → Pᵉ yᵉ → leq-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ) yᵉ
  gᵉ (inlᵉ yᵉ) qᵉ = ex-falsoᵉ (fᵉ (pairᵉ yᵉ qᵉ))
  gᵉ (inrᵉ starᵉ) qᵉ = refl-leq-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ)

well-ordering-principle-∃-Finᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : decidable-subtypeᵉ lᵉ (Finᵉ kᵉ)) →
  existsᵉ (Finᵉ kᵉ) (subtype-decidable-subtypeᵉ Pᵉ) →
  minimal-element-Finᵉ kᵉ (is-in-decidable-subtypeᵉ Pᵉ)
well-ordering-principle-∃-Finᵉ kᵉ Pᵉ Hᵉ =
  apply-universal-property-trunc-Propᵉ Hᵉ
    ( minimal-element-Fin-Propᵉ kᵉ (subtype-decidable-subtypeᵉ Pᵉ))
    ( well-ordering-principle-Σ-Finᵉ kᵉ
      ( is-decidable-decidable-subtypeᵉ Pᵉ))
```

### Hilbert's `ε`-operator for decidable subtypes of standard finite types

```agda
ε-operator-decidable-subtype-Finᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : decidable-subtypeᵉ lᵉ (Finᵉ kᵉ)) →
  ε-operator-Hilbertᵉ (type-decidable-subtypeᵉ Pᵉ)
ε-operator-decidable-subtype-Finᵉ {lᵉ} zero-ℕᵉ Pᵉ tᵉ =
  ex-falsoᵉ (apply-universal-property-trunc-Propᵉ tᵉ empty-Propᵉ pr1ᵉ)
ε-operator-decidable-subtype-Finᵉ {lᵉ} (succ-ℕᵉ kᵉ) Pᵉ tᵉ =
  map-Σᵉ
    ( is-in-decidable-subtypeᵉ Pᵉ)
    ( mod-succ-ℕᵉ kᵉ)
    ( λ xᵉ → idᵉ)
    ( ε-operator-total-Qᵉ
      ( map-trunc-Propᵉ
        ( map-Σᵉ
          ( type-Propᵉ ∘ᵉ Qᵉ)
          ( nat-Finᵉ (succ-ℕᵉ kᵉ))
          ( λ xᵉ →
            trᵉ (is-in-decidable-subtypeᵉ Pᵉ) (invᵉ (is-section-nat-Finᵉ kᵉ xᵉ))))
        ( tᵉ)))
  where
  Qᵉ : ℕᵉ → Propᵉ lᵉ
  Qᵉ nᵉ = subtype-decidable-subtypeᵉ Pᵉ (mod-succ-ℕᵉ kᵉ nᵉ)
  is-decidable-Qᵉ : (nᵉ : ℕᵉ) → is-decidableᵉ (type-Propᵉ (Qᵉ nᵉ))
  is-decidable-Qᵉ nᵉ =
    is-decidable-decidable-subtypeᵉ Pᵉ (mod-succ-ℕᵉ kᵉ nᵉ)
  ε-operator-total-Qᵉ : ε-operator-Hilbertᵉ (type-subtypeᵉ Qᵉ)
  ε-operator-total-Qᵉ =
    ε-operator-decidable-subtype-ℕᵉ Qᵉ is-decidable-Qᵉ
```

```agda
abstract
  elim-trunc-decidable-fam-Finᵉ :
    {l1ᵉ : Level} {kᵉ : ℕᵉ} {Bᵉ : Finᵉ kᵉ → UUᵉ l1ᵉ} →
    ((xᵉ : Finᵉ kᵉ) → is-decidableᵉ (Bᵉ xᵉ)) →
    type-trunc-Propᵉ (Σᵉ (Finᵉ kᵉ) Bᵉ) → Σᵉ (Finᵉ kᵉ) Bᵉ
  elim-trunc-decidable-fam-Finᵉ {l1ᵉ} {zero-ℕᵉ} {Bᵉ} dᵉ yᵉ =
    ex-falsoᵉ (is-empty-type-trunc-Propᵉ pr1ᵉ yᵉ)
  elim-trunc-decidable-fam-Finᵉ {l1ᵉ} {succ-ℕᵉ kᵉ} {Bᵉ} dᵉ yᵉ
    with dᵉ (inrᵉ starᵉ)
  ... | inlᵉ xᵉ = pairᵉ (inrᵉ starᵉ) xᵉ
  ... | inrᵉ fᵉ =
    map-Σ-map-baseᵉ inlᵉ Bᵉ
      ( elim-trunc-decidable-fam-Finᵉ {l1ᵉ} {kᵉ} {Bᵉ ∘ᵉ inlᵉ}
        ( λ xᵉ → dᵉ (inlᵉ xᵉ))
        ( map-equiv-trunc-Propᵉ
          ( ( ( right-unit-law-coproduct-is-emptyᵉ
                ( Σᵉ (Finᵉ kᵉ) (Bᵉ ∘ᵉ inlᵉ))
                ( Bᵉ (inrᵉ starᵉ)) fᵉ) ∘eᵉ
              ( equiv-coproductᵉ id-equivᵉ (left-unit-law-Σᵉ (Bᵉ ∘ᵉ inrᵉ)))) ∘eᵉ
            ( right-distributive-Σ-coproductᵉ (Finᵉ kᵉ) unitᵉ Bᵉ))
          ( yᵉ)))
```