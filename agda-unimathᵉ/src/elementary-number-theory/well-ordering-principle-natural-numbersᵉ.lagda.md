# The Well-Ordering Principle of the natural numbers

```agda
module elementary-number-theory.well-ordering-principle-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.lower-bounds-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.hilberts-epsilon-operatorsᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ well-orderingᵉ principleᵉ ofᵉ theᵉ naturalᵉ numbersᵉ assertsᵉ thatᵉ forᵉ everyᵉ familyᵉ
ofᵉ decidableᵉ typesᵉ overᵉ ℕᵉ equippedᵉ with aᵉ naturalᵉ numberᵉ `n`ᵉ andᵉ anᵉ elementᵉ
`pᵉ : Pᵉ n`,ᵉ weᵉ canᵉ findᵉ aᵉ leastᵉ naturalᵉ numberᵉ `n₀`ᵉ with anᵉ elementᵉ `p₀ᵉ : Pᵉ n₀`.ᵉ

## Theorem

```agda
minimal-element-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) → UUᵉ lᵉ
minimal-element-ℕᵉ Pᵉ = Σᵉ ℕᵉ (λ nᵉ → (Pᵉ nᵉ) ×ᵉ (is-lower-bound-ℕᵉ Pᵉ nᵉ))

module _
  {l1ᵉ : Level} (Pᵉ : ℕᵉ → Propᵉ l1ᵉ)
  where

  all-elements-equal-minimal-element-ℕᵉ :
    all-elements-equalᵉ (minimal-element-ℕᵉ (λ nᵉ → type-Propᵉ (Pᵉ nᵉ)))
  all-elements-equal-minimal-element-ℕᵉ
    (pairᵉ xᵉ (pairᵉ pᵉ lᵉ)) (pairᵉ yᵉ (pairᵉ qᵉ kᵉ)) =
    eq-type-subtypeᵉ
      ( λ nᵉ →
        product-Propᵉ
          ( pairᵉ _ (is-prop-type-Propᵉ (Pᵉ nᵉ)))
          ( is-lower-bound-ℕ-Propᵉ nᵉ))
      ( antisymmetric-leq-ℕᵉ xᵉ yᵉ (lᵉ yᵉ qᵉ) (kᵉ xᵉ pᵉ))

  is-prop-minimal-element-ℕᵉ :
    is-propᵉ (minimal-element-ℕᵉ (λ nᵉ → type-Propᵉ (Pᵉ nᵉ)))
  is-prop-minimal-element-ℕᵉ =
    is-prop-all-elements-equalᵉ all-elements-equal-minimal-element-ℕᵉ

  minimal-element-ℕ-Propᵉ : Propᵉ l1ᵉ
  pr1ᵉ minimal-element-ℕ-Propᵉ = minimal-element-ℕᵉ (λ nᵉ → type-Propᵉ (Pᵉ nᵉ))
  pr2ᵉ minimal-element-ℕ-Propᵉ = is-prop-minimal-element-ℕᵉ

is-minimal-element-succ-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (dᵉ : is-decidable-famᵉ Pᵉ)
  (mᵉ : ℕᵉ) (pmᵉ : Pᵉ (succ-ℕᵉ mᵉ))
  (is-lower-bound-mᵉ : is-lower-bound-ℕᵉ (λ xᵉ → Pᵉ (succ-ℕᵉ xᵉ)) mᵉ) →
  ¬ᵉ (Pᵉ zero-ℕᵉ) → is-lower-bound-ℕᵉ Pᵉ (succ-ℕᵉ mᵉ)
is-minimal-element-succ-ℕᵉ Pᵉ dᵉ mᵉ pmᵉ is-lower-bound-mᵉ neg-p0ᵉ zero-ℕᵉ p0ᵉ =
  ex-falsoᵉ (neg-p0ᵉ p0ᵉ)
is-minimal-element-succ-ℕᵉ
  Pᵉ dᵉ zero-ℕᵉ pmᵉ is-lower-bound-mᵉ neg-p0ᵉ (succ-ℕᵉ nᵉ) psuccnᵉ =
  leq-zero-ℕᵉ nᵉ
is-minimal-element-succ-ℕᵉ
  Pᵉ dᵉ (succ-ℕᵉ mᵉ) pmᵉ is-lower-bound-mᵉ neg-p0ᵉ (succ-ℕᵉ nᵉ) psuccnᵉ =
  is-lower-bound-mᵉ nᵉ psuccnᵉ

well-ordering-principle-succ-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (dᵉ : is-decidable-famᵉ Pᵉ)
  (nᵉ : ℕᵉ) (pᵉ : Pᵉ (succ-ℕᵉ nᵉ)) →
  is-decidableᵉ (Pᵉ zero-ℕᵉ) →
  minimal-element-ℕᵉ (λ mᵉ → Pᵉ (succ-ℕᵉ mᵉ)) → minimal-element-ℕᵉ Pᵉ
well-ordering-principle-succ-ℕᵉ Pᵉ dᵉ nᵉ pᵉ (inlᵉ p0ᵉ) uᵉ =
  ( 0 ,ᵉ p0ᵉ ,ᵉ λ mᵉ qᵉ → leq-zero-ℕᵉ mᵉ)
well-ordering-principle-succ-ℕᵉ Pᵉ dᵉ nᵉ pᵉ (inrᵉ neg-p0ᵉ) (mᵉ ,ᵉ pmᵉ ,ᵉ is-min-mᵉ) =
  ( succ-ℕᵉ mᵉ ,ᵉ pmᵉ ,ᵉ is-minimal-element-succ-ℕᵉ Pᵉ dᵉ mᵉ pmᵉ is-min-mᵉ neg-p0ᵉ)

well-ordering-principle-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (dᵉ : is-decidable-famᵉ Pᵉ) →
  Σᵉ ℕᵉ Pᵉ → minimal-element-ℕᵉ Pᵉ
pr1ᵉ (well-ordering-principle-ℕᵉ Pᵉ dᵉ (pairᵉ zero-ℕᵉ pᵉ)) = zero-ℕᵉ
pr1ᵉ (pr2ᵉ (well-ordering-principle-ℕᵉ Pᵉ dᵉ (pairᵉ zero-ℕᵉ pᵉ))) = pᵉ
pr2ᵉ (pr2ᵉ (well-ordering-principle-ℕᵉ Pᵉ dᵉ (pairᵉ zero-ℕᵉ pᵉ))) mᵉ qᵉ = leq-zero-ℕᵉ mᵉ
well-ordering-principle-ℕᵉ Pᵉ dᵉ (pairᵉ (succ-ℕᵉ nᵉ) pᵉ) =
  well-ordering-principle-succ-ℕᵉ Pᵉ dᵉ nᵉ pᵉ (dᵉ zero-ℕᵉ)
    ( well-ordering-principle-ℕᵉ
      ( λ mᵉ → Pᵉ (succ-ℕᵉ mᵉ))
      ( λ mᵉ → dᵉ (succ-ℕᵉ mᵉ))
      ( pairᵉ nᵉ pᵉ))

number-well-ordering-principle-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (dᵉ : is-decidable-famᵉ Pᵉ) (nPᵉ : Σᵉ ℕᵉ Pᵉ) → ℕᵉ
number-well-ordering-principle-ℕᵉ Pᵉ dᵉ nPᵉ =
  pr1ᵉ (well-ordering-principle-ℕᵉ Pᵉ dᵉ nPᵉ)
```

### The well-ordering principle returns `0` if `P 0` holds

Thisᵉ isᵉ independentlyᵉ ofᵉ theᵉ inputᵉ `(pairᵉ nᵉ pᵉ) : Σᵉ ℕᵉ P`.ᵉ

```agda
is-zero-well-ordering-principle-succ-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (dᵉ : is-decidable-famᵉ Pᵉ)
  (nᵉ : ℕᵉ) (pᵉ : Pᵉ (succ-ℕᵉ nᵉ)) (d0ᵉ : is-decidableᵉ (Pᵉ zero-ℕᵉ)) →
  (xᵉ : minimal-element-ℕᵉ (λ mᵉ → Pᵉ (succ-ℕᵉ mᵉ))) (p0ᵉ : Pᵉ zero-ℕᵉ) →
  pr1ᵉ (well-ordering-principle-succ-ℕᵉ Pᵉ dᵉ nᵉ pᵉ d0ᵉ xᵉ) ＝ᵉ zero-ℕᵉ
is-zero-well-ordering-principle-succ-ℕᵉ Pᵉ dᵉ nᵉ pᵉ (inlᵉ p0ᵉ) xᵉ q0ᵉ =
  reflᵉ
is-zero-well-ordering-principle-succ-ℕᵉ Pᵉ dᵉ nᵉ pᵉ (inrᵉ np0ᵉ) xᵉ q0ᵉ =
  ex-falsoᵉ (np0ᵉ q0ᵉ)

is-zero-well-ordering-principle-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (dᵉ : is-decidable-famᵉ Pᵉ) →
  (xᵉ : Σᵉ ℕᵉ Pᵉ) → Pᵉ zero-ℕᵉ → is-zero-ℕᵉ (number-well-ordering-principle-ℕᵉ Pᵉ dᵉ xᵉ)
is-zero-well-ordering-principle-ℕᵉ Pᵉ dᵉ (pairᵉ zero-ℕᵉ pᵉ) p0ᵉ = reflᵉ
is-zero-well-ordering-principle-ℕᵉ Pᵉ dᵉ (pairᵉ (succ-ℕᵉ mᵉ) pᵉ) =
  is-zero-well-ordering-principle-succ-ℕᵉ Pᵉ dᵉ mᵉ pᵉ (dᵉ zero-ℕᵉ)
    ( well-ordering-principle-ℕᵉ
      ( λ zᵉ → Pᵉ (succ-ℕᵉ zᵉ))
      ( λ xᵉ → dᵉ (succ-ℕᵉ xᵉ))
      ( pairᵉ mᵉ pᵉ))
```

### The ε-operator for decidable subtypes of ℕ

```agda
ε-operator-decidable-subtype-ℕᵉ :
  {l1ᵉ : Level} (Pᵉ : ℕᵉ → Propᵉ l1ᵉ)
  (dᵉ : (xᵉ : ℕᵉ) → is-decidableᵉ (type-Propᵉ (Pᵉ xᵉ))) →
  ε-operator-Hilbertᵉ (type-subtypeᵉ Pᵉ)
ε-operator-decidable-subtype-ℕᵉ {l1ᵉ} Pᵉ dᵉ tᵉ =
  totᵉ ( λ xᵉ → pr1ᵉ)
      ( apply-universal-property-trunc-Propᵉ tᵉ
        ( minimal-element-ℕ-Propᵉ Pᵉ)
        ( well-ordering-principle-ℕᵉ (λ xᵉ → type-Propᵉ (Pᵉ xᵉ)) dᵉ))
```