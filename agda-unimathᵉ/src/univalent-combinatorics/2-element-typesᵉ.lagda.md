# `2`-element types

```agda
module univalent-combinatorics.2-element-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.automorphismsᵉ
open import foundation.connected-components-universesᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-negationᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-systemsᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.involutionsᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.setsᵉ
open import foundation.subuniversesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-identity-systemsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.equivalencesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

**`2`-elementᵉ types**ᵉ areᵉ typesᵉ thatᵉ areᵉ
[merelyᵉ equivalent](foundation.mere-equivalences.mdᵉ) to theᵉ
[standardᵉ 2-elementᵉ type](univalent-combinatorics.standard-finite-types.mdᵉ)
`Finᵉ 2`.ᵉ

## Definition

### The condition that a type has two elements

```agda
has-two-elements-Propᵉ : {lᵉ : Level} → UUᵉ lᵉ → Propᵉ lᵉ
has-two-elements-Propᵉ Xᵉ = has-cardinality-Propᵉ 2 Xᵉ

has-two-elementsᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
has-two-elementsᵉ Xᵉ = type-Propᵉ (has-two-elements-Propᵉ Xᵉ)

is-prop-has-two-elementsᵉ : {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → is-propᵉ (has-two-elementsᵉ Xᵉ)
is-prop-has-two-elementsᵉ {lᵉ} {Xᵉ} = is-prop-type-Propᵉ (has-two-elements-Propᵉ Xᵉ)
```

### The type of all `2`-element types of universe level `l`

```agda
2-Element-Typeᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
2-Element-Typeᵉ lᵉ = UU-Finᵉ lᵉ 2

type-2-Element-Typeᵉ : {lᵉ : Level} → 2-Element-Typeᵉ lᵉ → UUᵉ lᵉ
type-2-Element-Typeᵉ = pr1ᵉ

has-two-elements-type-2-Element-Typeᵉ :
  {lᵉ : Level} (Xᵉ : 2-Element-Typeᵉ lᵉ) → has-two-elementsᵉ (type-2-Element-Typeᵉ Xᵉ)
has-two-elements-type-2-Element-Typeᵉ = pr2ᵉ

is-finite-type-2-Element-Typeᵉ :
  {lᵉ : Level} (Xᵉ : 2-Element-Typeᵉ lᵉ) → is-finiteᵉ (type-2-Element-Typeᵉ Xᵉ)
is-finite-type-2-Element-Typeᵉ Xᵉ =
  is-finite-has-cardinalityᵉ 2 (has-two-elements-type-2-Element-Typeᵉ Xᵉ)

finite-type-2-Element-Typeᵉ : {lᵉ : Level} → 2-Element-Typeᵉ lᵉ → 𝔽ᵉ lᵉ
pr1ᵉ (finite-type-2-Element-Typeᵉ Xᵉ) = type-2-Element-Typeᵉ Xᵉ
pr2ᵉ (finite-type-2-Element-Typeᵉ Xᵉ) = is-finite-type-2-Element-Typeᵉ Xᵉ

standard-2-Element-Typeᵉ : (lᵉ : Level) → 2-Element-Typeᵉ lᵉ
standard-2-Element-Typeᵉ lᵉ = Fin-UU-Finᵉ lᵉ 2

type-standard-2-Element-Typeᵉ : (lᵉ : Level) → UUᵉ lᵉ
type-standard-2-Element-Typeᵉ lᵉ = type-2-Element-Typeᵉ (standard-2-Element-Typeᵉ lᵉ)

zero-standard-2-Element-Typeᵉ :
  {lᵉ : Level} → type-standard-2-Element-Typeᵉ lᵉ
zero-standard-2-Element-Typeᵉ = map-raiseᵉ (zero-Finᵉ 1ᵉ)

one-standard-2-Element-Typeᵉ :
  {lᵉ : Level} → type-standard-2-Element-Typeᵉ lᵉ
one-standard-2-Element-Typeᵉ = map-raiseᵉ (one-Finᵉ 1ᵉ)
```

## Properties

### The condition of having two elements is closed under equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  where

  has-two-elements-equivᵉ : Xᵉ ≃ᵉ Yᵉ → has-two-elementsᵉ Xᵉ → has-two-elementsᵉ Yᵉ
  has-two-elements-equivᵉ eᵉ Hᵉ =
    transitive-mere-equivᵉ (Finᵉ 2ᵉ) Xᵉ Yᵉ (unit-trunc-Propᵉ eᵉ) Hᵉ

  has-two-elements-equiv'ᵉ : Xᵉ ≃ᵉ Yᵉ → has-two-elementsᵉ Yᵉ → has-two-elementsᵉ Xᵉ
  has-two-elements-equiv'ᵉ eᵉ Hᵉ =
    transitive-mere-equivᵉ (Finᵉ 2ᵉ) Yᵉ Xᵉ (unit-trunc-Propᵉ (inv-equivᵉ eᵉ)) Hᵉ
```

### Any `2`-element type is inhabited

```agda
is-inhabited-2-Element-Typeᵉ :
  {lᵉ : Level} (Xᵉ : 2-Element-Typeᵉ lᵉ) → type-trunc-Propᵉ (type-2-Element-Typeᵉ Xᵉ)
is-inhabited-2-Element-Typeᵉ Xᵉ =
  apply-universal-property-trunc-Propᵉ
    ( has-two-elements-type-2-Element-Typeᵉ Xᵉ)
    ( trunc-Propᵉ (type-2-Element-Typeᵉ Xᵉ))
    ( λ eᵉ → unit-trunc-Propᵉ (map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ)))
```

### Any `2`-element type is a set

```agda
is-set-has-two-elementsᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → has-two-elementsᵉ Xᵉ → is-setᵉ Xᵉ
is-set-has-two-elementsᵉ Hᵉ = is-set-has-cardinalityᵉ 2 Hᵉ

is-set-type-2-Element-Typeᵉ :
  {lᵉ : Level} (Xᵉ : 2-Element-Typeᵉ lᵉ) → is-setᵉ (type-2-Element-Typeᵉ Xᵉ)
is-set-type-2-Element-Typeᵉ Xᵉ =
  is-set-has-cardinalityᵉ 2 (has-two-elements-type-2-Element-Typeᵉ Xᵉ)

set-2-Element-Typeᵉ :
  {lᵉ : Level} → 2-Element-Typeᵉ lᵉ → Setᵉ lᵉ
pr1ᵉ (set-2-Element-Typeᵉ Xᵉ) = type-2-Element-Typeᵉ Xᵉ
pr2ᵉ (set-2-Element-Typeᵉ Xᵉ) = is-set-type-2-Element-Typeᵉ Xᵉ
```

### Characterizing identifications between general `2`-element types

```agda
equiv-2-Element-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} → 2-Element-Typeᵉ l1ᵉ → 2-Element-Typeᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
equiv-2-Element-Typeᵉ Xᵉ Yᵉ = equiv-UU-Finᵉ 2 Xᵉ Yᵉ

id-equiv-2-Element-Typeᵉ :
  {l1ᵉ : Level} (Xᵉ : 2-Element-Typeᵉ l1ᵉ) → equiv-2-Element-Typeᵉ Xᵉ Xᵉ
id-equiv-2-Element-Typeᵉ Xᵉ = id-equivᵉ

equiv-eq-2-Element-Typeᵉ :
  {l1ᵉ : Level} (Xᵉ Yᵉ : 2-Element-Typeᵉ l1ᵉ) → Xᵉ ＝ᵉ Yᵉ → equiv-2-Element-Typeᵉ Xᵉ Yᵉ
equiv-eq-2-Element-Typeᵉ Xᵉ Yᵉ = equiv-eq-component-UU-Levelᵉ

abstract
  is-torsorial-equiv-2-Element-Typeᵉ :
    {l1ᵉ : Level} (Xᵉ : 2-Element-Typeᵉ l1ᵉ) →
    is-torsorialᵉ (λ (Yᵉ : 2-Element-Typeᵉ l1ᵉ) → equiv-2-Element-Typeᵉ Xᵉ Yᵉ)
  is-torsorial-equiv-2-Element-Typeᵉ Xᵉ =
    is-torsorial-equiv-component-UU-Levelᵉ Xᵉ

abstract
  is-equiv-equiv-eq-2-Element-Typeᵉ :
    {l1ᵉ : Level} (Xᵉ Yᵉ : 2-Element-Typeᵉ l1ᵉ) →
    is-equivᵉ (equiv-eq-2-Element-Typeᵉ Xᵉ Yᵉ)
  is-equiv-equiv-eq-2-Element-Typeᵉ = is-equiv-equiv-eq-component-UU-Levelᵉ

eq-equiv-2-Element-Typeᵉ :
  {l1ᵉ : Level} (Xᵉ Yᵉ : 2-Element-Typeᵉ l1ᵉ) → equiv-2-Element-Typeᵉ Xᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
eq-equiv-2-Element-Typeᵉ Xᵉ Yᵉ =
  map-inv-is-equivᵉ (is-equiv-equiv-eq-2-Element-Typeᵉ Xᵉ Yᵉ)

extensionality-2-Element-Typeᵉ :
  {l1ᵉ : Level} (Xᵉ Yᵉ : 2-Element-Typeᵉ l1ᵉ) → (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-2-Element-Typeᵉ Xᵉ Yᵉ
pr1ᵉ (extensionality-2-Element-Typeᵉ Xᵉ Yᵉ) = equiv-eq-2-Element-Typeᵉ Xᵉ Yᵉ
pr2ᵉ (extensionality-2-Element-Typeᵉ Xᵉ Yᵉ) = is-equiv-equiv-eq-2-Element-Typeᵉ Xᵉ Yᵉ
```

### Characterization the identifications of `Fin 2` with a `2`-element type `X`

#### Evaluating an equivalence and an automorphism at `0 : Fin 2`

```agda
ev-zero-equiv-Fin-two-ℕᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → (Finᵉ 2 ≃ᵉ Xᵉ) → Xᵉ
ev-zero-equiv-Fin-two-ℕᵉ eᵉ = map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ)

ev-zero-aut-Fin-two-ℕᵉ : (Finᵉ 2 ≃ᵉ Finᵉ 2ᵉ) → Finᵉ 2
ev-zero-aut-Fin-two-ℕᵉ = ev-zero-equiv-Fin-two-ℕᵉ
```

#### Evaluating an automorphism at `0 : Fin 2` is an equivalence

```agda
aut-point-Fin-two-ℕᵉ :
  Finᵉ 2 → (Finᵉ 2 ≃ᵉ Finᵉ 2ᵉ)
aut-point-Fin-two-ℕᵉ (inlᵉ (inrᵉ starᵉ)) = id-equivᵉ
aut-point-Fin-two-ℕᵉ (inrᵉ starᵉ) = equiv-succ-Finᵉ 2

abstract
  is-section-aut-point-Fin-two-ℕᵉ :
    (ev-zero-aut-Fin-two-ℕᵉ ∘ᵉ aut-point-Fin-two-ℕᵉ) ~ᵉ idᵉ
  is-section-aut-point-Fin-two-ℕᵉ (inlᵉ (inrᵉ starᵉ)) = reflᵉ
  is-section-aut-point-Fin-two-ℕᵉ (inrᵉ starᵉ) = reflᵉ

  is-retraction-aut-point-Fin-two-ℕ'ᵉ :
    (eᵉ : Finᵉ 2 ≃ᵉ Finᵉ 2ᵉ) (xᵉ yᵉ : Finᵉ 2ᵉ) →
    map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ) ＝ᵉ xᵉ →
    map-equivᵉ eᵉ (one-Finᵉ 1ᵉ) ＝ᵉ yᵉ → htpy-equivᵉ (aut-point-Fin-two-ℕᵉ xᵉ) eᵉ
  is-retraction-aut-point-Fin-two-ℕ'ᵉ eᵉ
    (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inrᵉ starᵉ)) pᵉ qᵉ (inlᵉ (inrᵉ starᵉ)) = invᵉ pᵉ
  is-retraction-aut-point-Fin-two-ℕ'ᵉ eᵉ
    (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inrᵉ starᵉ)) pᵉ qᵉ (inrᵉ starᵉ) =
    ex-falsoᵉ (Eq-Fin-eqᵉ 2 (is-injective-equivᵉ eᵉ (pᵉ ∙ᵉ invᵉ qᵉ)))
  is-retraction-aut-point-Fin-two-ℕ'ᵉ eᵉ
    (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) pᵉ qᵉ (inlᵉ (inrᵉ starᵉ)) = invᵉ pᵉ
  is-retraction-aut-point-Fin-two-ℕ'ᵉ eᵉ
    (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) pᵉ qᵉ (inrᵉ starᵉ) = invᵉ qᵉ
  is-retraction-aut-point-Fin-two-ℕ'ᵉ eᵉ
    (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)) pᵉ qᵉ (inlᵉ (inrᵉ starᵉ)) = invᵉ pᵉ
  is-retraction-aut-point-Fin-two-ℕ'ᵉ eᵉ
    (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)) pᵉ qᵉ (inrᵉ starᵉ) = invᵉ qᵉ
  is-retraction-aut-point-Fin-two-ℕ'ᵉ eᵉ
    (inrᵉ starᵉ) (inrᵉ starᵉ) pᵉ qᵉ (inlᵉ (inrᵉ starᵉ)) =
    ex-falsoᵉ (Eq-Fin-eqᵉ 2 (is-injective-equivᵉ eᵉ (pᵉ ∙ᵉ invᵉ qᵉ)))
  is-retraction-aut-point-Fin-two-ℕ'ᵉ eᵉ
    (inrᵉ starᵉ) (inrᵉ starᵉ) pᵉ qᵉ (inrᵉ starᵉ) =
    ex-falsoᵉ (Eq-Fin-eqᵉ 2 (is-injective-equivᵉ eᵉ (pᵉ ∙ᵉ invᵉ qᵉ)))

  is-retraction-aut-point-Fin-two-ℕᵉ :
    (aut-point-Fin-two-ℕᵉ ∘ᵉ ev-zero-aut-Fin-two-ℕᵉ) ~ᵉ idᵉ
  is-retraction-aut-point-Fin-two-ℕᵉ eᵉ =
    eq-htpy-equivᵉ
      ( is-retraction-aut-point-Fin-two-ℕ'ᵉ eᵉ
        ( map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ))
        ( map-equivᵉ eᵉ (one-Finᵉ 1ᵉ))
        ( reflᵉ)
        ( reflᵉ))

abstract
  is-equiv-ev-zero-aut-Fin-two-ℕᵉ : is-equivᵉ ev-zero-aut-Fin-two-ℕᵉ
  is-equiv-ev-zero-aut-Fin-two-ℕᵉ =
    is-equiv-is-invertibleᵉ
      aut-point-Fin-two-ℕᵉ
      is-section-aut-point-Fin-two-ℕᵉ
      is-retraction-aut-point-Fin-two-ℕᵉ

equiv-ev-zero-aut-Fin-two-ℕᵉ : (Finᵉ 2 ≃ᵉ Finᵉ 2ᵉ) ≃ᵉ Finᵉ 2
pr1ᵉ equiv-ev-zero-aut-Fin-two-ℕᵉ = ev-zero-aut-Fin-two-ℕᵉ
pr2ᵉ equiv-ev-zero-aut-Fin-two-ℕᵉ = is-equiv-ev-zero-aut-Fin-two-ℕᵉ
```

#### If `X` is a `2`-element type, then evaluating an equivalence `Fin 2 ≃ X` at `0` is an equivalence

```agda
module _
  {l1ᵉ : Level} (Xᵉ : 2-Element-Typeᵉ l1ᵉ)
  where

  abstract
    is-equiv-ev-zero-equiv-Fin-two-ℕᵉ :
      is-equivᵉ (ev-zero-equiv-Fin-two-ℕᵉ {l1ᵉ} {type-2-Element-Typeᵉ Xᵉ})
    is-equiv-ev-zero-equiv-Fin-two-ℕᵉ =
      apply-universal-property-trunc-Propᵉ
        ( has-two-elements-type-2-Element-Typeᵉ Xᵉ)
        ( is-equiv-Propᵉ (ev-zero-equiv-Fin-two-ℕᵉ))
        ( λ αᵉ →
          is-equiv-left-factorᵉ
            ( ev-zero-equiv-Fin-two-ℕᵉ)
            ( map-equivᵉ (equiv-postcomp-equivᵉ αᵉ (Finᵉ 2ᵉ)))
            ( is-equiv-compᵉ
              ( map-equivᵉ αᵉ)
              ( ev-zero-equiv-Fin-two-ℕᵉ)
              ( is-equiv-ev-zero-aut-Fin-two-ℕᵉ)
              ( is-equiv-map-equivᵉ αᵉ))
            ( is-equiv-postcomp-equiv-equivᵉ αᵉ))

  equiv-ev-zero-equiv-Fin-two-ℕᵉ :
    (Finᵉ 2 ≃ᵉ type-2-Element-Typeᵉ Xᵉ) ≃ᵉ type-2-Element-Typeᵉ Xᵉ
  pr1ᵉ equiv-ev-zero-equiv-Fin-two-ℕᵉ = ev-zero-equiv-Fin-two-ℕᵉ
  pr2ᵉ equiv-ev-zero-equiv-Fin-two-ℕᵉ = is-equiv-ev-zero-equiv-Fin-two-ℕᵉ

  equiv-point-2-Element-Typeᵉ :
    type-2-Element-Typeᵉ Xᵉ → Finᵉ 2 ≃ᵉ type-2-Element-Typeᵉ Xᵉ
  equiv-point-2-Element-Typeᵉ =
    map-inv-equivᵉ equiv-ev-zero-equiv-Fin-two-ℕᵉ

  map-equiv-point-2-Element-Typeᵉ :
    type-2-Element-Typeᵉ Xᵉ → Finᵉ 2 → type-2-Element-Typeᵉ Xᵉ
  map-equiv-point-2-Element-Typeᵉ xᵉ = map-equivᵉ (equiv-point-2-Element-Typeᵉ xᵉ)

  map-inv-equiv-point-2-Element-Typeᵉ :
    type-2-Element-Typeᵉ Xᵉ → type-2-Element-Typeᵉ Xᵉ → Finᵉ 2
  map-inv-equiv-point-2-Element-Typeᵉ xᵉ =
    map-inv-equivᵉ (equiv-point-2-Element-Typeᵉ xᵉ)

  is-section-map-inv-equiv-point-2-Element-Typeᵉ :
    (xᵉ : type-2-Element-Typeᵉ Xᵉ) →
    (map-equiv-point-2-Element-Typeᵉ xᵉ ∘ᵉ map-inv-equiv-point-2-Element-Typeᵉ xᵉ) ~ᵉ
    idᵉ
  is-section-map-inv-equiv-point-2-Element-Typeᵉ xᵉ =
    is-section-map-inv-equivᵉ (equiv-point-2-Element-Typeᵉ xᵉ)

  is-retraction-map-inv-equiv-point-2-Element-Typeᵉ :
    (xᵉ : type-2-Element-Typeᵉ Xᵉ) →
    (map-inv-equiv-point-2-Element-Typeᵉ xᵉ ∘ᵉ map-equiv-point-2-Element-Typeᵉ xᵉ) ~ᵉ
    idᵉ
  is-retraction-map-inv-equiv-point-2-Element-Typeᵉ xᵉ =
    is-retraction-map-inv-equivᵉ (equiv-point-2-Element-Typeᵉ xᵉ)

  compute-map-equiv-point-2-Element-Typeᵉ :
    (xᵉ : type-2-Element-Typeᵉ Xᵉ) →
    map-equiv-point-2-Element-Typeᵉ xᵉ (zero-Finᵉ 1ᵉ) ＝ᵉ xᵉ
  compute-map-equiv-point-2-Element-Typeᵉ =
    is-section-map-inv-equivᵉ equiv-ev-zero-equiv-Fin-two-ℕᵉ

  is-unique-equiv-point-2-Element-Typeᵉ :
    (eᵉ : Finᵉ 2 ≃ᵉ type-2-Element-Typeᵉ Xᵉ) →
    htpy-equivᵉ (equiv-point-2-Element-Typeᵉ (map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ))) eᵉ
  is-unique-equiv-point-2-Element-Typeᵉ eᵉ =
    htpy-eq-equivᵉ (is-retraction-map-inv-equivᵉ equiv-ev-zero-equiv-Fin-two-ℕᵉ eᵉ)
```

#### The type of pointed `2`-element types of any universe level is contractible

```agda
Pointed-2-Element-Typeᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Pointed-2-Element-Typeᵉ lᵉ = Σᵉ (2-Element-Typeᵉ lᵉ) type-2-Element-Typeᵉ

abstract
  is-contr-pointed-2-Element-Typeᵉ :
    {lᵉ : Level} → is-contrᵉ (Pointed-2-Element-Typeᵉ lᵉ)
  is-contr-pointed-2-Element-Typeᵉ {lᵉ} =
    is-contr-equiv'ᵉ
      ( Σᵉ ( 2-Element-Typeᵉ lᵉ)
          ( equiv-2-Element-Typeᵉ (standard-2-Element-Typeᵉ lᵉ)))
      ( equiv-totᵉ
        ( λ Xᵉ →
          ( equiv-ev-zero-equiv-Fin-two-ℕᵉ Xᵉ) ∘eᵉ
          ( equiv-precomp-equivᵉ (compute-raise-Finᵉ lᵉ 2ᵉ) (pr1ᵉ Xᵉ))))
      ( is-torsorial-equiv-subuniverseᵉ
        ( has-cardinality-Propᵉ 2ᵉ)
        ( standard-2-Element-Typeᵉ lᵉ))
```

#### Completing the characterization of the identity type of the type of `2`-element types of arbitrary universe level

```agda
point-eq-2-Element-Typeᵉ :
  {lᵉ : Level} {Xᵉ : 2-Element-Typeᵉ lᵉ} →
  standard-2-Element-Typeᵉ lᵉ ＝ᵉ Xᵉ → type-2-Element-Typeᵉ Xᵉ
point-eq-2-Element-Typeᵉ reflᵉ = map-raiseᵉ (zero-Finᵉ 1ᵉ)

abstract
  is-equiv-point-eq-2-Element-Typeᵉ :
    {lᵉ : Level} (Xᵉ : 2-Element-Typeᵉ lᵉ) →
    is-equivᵉ (point-eq-2-Element-Typeᵉ {lᵉ} {Xᵉ})
  is-equiv-point-eq-2-Element-Typeᵉ {lᵉ} =
    fundamental-theorem-idᵉ
      ( is-contr-pointed-2-Element-Typeᵉ)
      ( λ Xᵉ → point-eq-2-Element-Typeᵉ {lᵉ} {Xᵉ})

equiv-point-eq-2-Element-Typeᵉ :
  {lᵉ : Level} {Xᵉ : 2-Element-Typeᵉ lᵉ} →
  (standard-2-Element-Typeᵉ lᵉ ＝ᵉ Xᵉ) ≃ᵉ type-2-Element-Typeᵉ Xᵉ
pr1ᵉ (equiv-point-eq-2-Element-Typeᵉ {lᵉ} {Xᵉ}) =
  point-eq-2-Element-Typeᵉ
pr2ᵉ (equiv-point-eq-2-Element-Typeᵉ {lᵉ} {Xᵉ}) =
  is-equiv-point-eq-2-Element-Typeᵉ Xᵉ

eq-point-2-Element-Typeᵉ :
  {lᵉ : Level} {Xᵉ : 2-Element-Typeᵉ lᵉ} →
  type-2-Element-Typeᵉ Xᵉ → standard-2-Element-Typeᵉ lᵉ ＝ᵉ Xᵉ
eq-point-2-Element-Typeᵉ =
  map-inv-equivᵉ equiv-point-eq-2-Element-Typeᵉ

is-identity-system-type-2-Element-Typeᵉ :
  {l1ᵉ : Level} (Xᵉ : 2-Element-Typeᵉ l1ᵉ) (xᵉ : type-2-Element-Typeᵉ Xᵉ) →
  is-identity-systemᵉ (type-2-Element-Typeᵉ {l1ᵉ}) Xᵉ xᵉ
is-identity-system-type-2-Element-Typeᵉ Xᵉ xᵉ =
  is-identity-system-is-torsorialᵉ Xᵉ xᵉ (is-contr-pointed-2-Element-Typeᵉ)

dependent-universal-property-identity-system-type-2-Element-Typeᵉ :
  {l1ᵉ : Level} (Xᵉ : 2-Element-Typeᵉ l1ᵉ) (xᵉ : type-2-Element-Typeᵉ Xᵉ) →
  dependent-universal-property-identity-systemᵉ
    ( type-2-Element-Typeᵉ {l1ᵉ})
    { aᵉ = Xᵉ}
    ( xᵉ)
dependent-universal-property-identity-system-type-2-Element-Typeᵉ Xᵉ xᵉ =
  dependent-universal-property-identity-system-is-torsorialᵉ xᵉ
    ( is-contr-pointed-2-Element-Typeᵉ)
```

### For any `2`-element type `X`, the type of automorphisms on `X` is a `2`-element type

```agda
module _
  {lᵉ : Level} (Xᵉ : 2-Element-Typeᵉ lᵉ)
  where

  has-two-elements-Aut-2-Element-Typeᵉ :
    has-two-elementsᵉ (Autᵉ (type-2-Element-Typeᵉ Xᵉ))
  has-two-elements-Aut-2-Element-Typeᵉ =
    apply-universal-property-trunc-Propᵉ
      ( has-two-elements-type-2-Element-Typeᵉ Xᵉ)
      ( has-two-elements-Propᵉ (Autᵉ (type-2-Element-Typeᵉ Xᵉ)))
      ( λ eᵉ →
        has-two-elements-equivᵉ
          ( ( equiv-postcomp-equivᵉ eᵉ (type-2-Element-Typeᵉ Xᵉ)) ∘eᵉ
            ( equiv-precomp-equivᵉ (inv-equivᵉ eᵉ) (Finᵉ 2ᵉ)))
          ( unit-trunc-Propᵉ (inv-equivᵉ equiv-ev-zero-aut-Fin-two-ℕᵉ)))

  Aut-2-Element-Typeᵉ : 2-Element-Typeᵉ lᵉ
  pr1ᵉ Aut-2-Element-Typeᵉ = Autᵉ (type-2-Element-Typeᵉ Xᵉ)
  pr2ᵉ Aut-2-Element-Typeᵉ = has-two-elements-Aut-2-Element-Typeᵉ
```

### Evaluating homotopies of equivalences `e, e' : Fin 2 ≃ X` at `0` is an equivalence

```agda
module _
  {l1ᵉ : Level} (Xᵉ : 2-Element-Typeᵉ l1ᵉ)
  where

  ev-zero-htpy-equiv-Fin-two-ℕᵉ :
    (eᵉ e'ᵉ : Finᵉ 2 ≃ᵉ type-2-Element-Typeᵉ Xᵉ) → htpy-equivᵉ eᵉ e'ᵉ →
    map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ) ＝ᵉ map-equivᵉ e'ᵉ (zero-Finᵉ 1ᵉ)
  ev-zero-htpy-equiv-Fin-two-ℕᵉ eᵉ e'ᵉ Hᵉ = Hᵉ (zero-Finᵉ 1ᵉ)

  equiv-ev-zero-htpy-equiv-Fin-two-ℕ'ᵉ :
    (eᵉ e'ᵉ : Finᵉ 2 ≃ᵉ type-2-Element-Typeᵉ Xᵉ) →
    htpy-equivᵉ eᵉ e'ᵉ ≃ᵉ (map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ) ＝ᵉ map-equivᵉ e'ᵉ (zero-Finᵉ 1ᵉ))
  equiv-ev-zero-htpy-equiv-Fin-two-ℕ'ᵉ eᵉ e'ᵉ =
    ( equiv-apᵉ (equiv-ev-zero-equiv-Fin-two-ℕᵉ Xᵉ) eᵉ e'ᵉ) ∘eᵉ
    ( inv-equivᵉ (extensionality-equivᵉ eᵉ e'ᵉ))

  abstract
    is-equiv-ev-zero-htpy-equiv-Fin-two-ℕᵉ :
      (eᵉ e'ᵉ : Finᵉ 2 ≃ᵉ type-2-Element-Typeᵉ Xᵉ) →
      is-equivᵉ (ev-zero-htpy-equiv-Fin-two-ℕᵉ eᵉ e'ᵉ)
    is-equiv-ev-zero-htpy-equiv-Fin-two-ℕᵉ eᵉ =
      is-fiberwise-equiv-is-equiv-totᵉ
        ( is-equiv-is-contrᵉ
          ( totᵉ (ev-zero-htpy-equiv-Fin-two-ℕᵉ eᵉ))
          ( is-torsorial-htpy-equivᵉ eᵉ)
          ( is-contr-equivᵉ
            ( fiberᵉ (ev-zero-equiv-Fin-two-ℕᵉ) (map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ)))
            ( equiv-totᵉ
              ( λ e'ᵉ →
                equiv-invᵉ
                  ( map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ))
                  ( map-equivᵉ e'ᵉ (zero-Finᵉ 1ᵉ))))
            ( is-contr-map-is-equivᵉ
              ( is-equiv-ev-zero-equiv-Fin-two-ℕᵉ Xᵉ)
              ( map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ)))))

  equiv-ev-zero-htpy-equiv-Fin-two-ℕᵉ :
    (eᵉ e'ᵉ : Finᵉ 2 ≃ᵉ type-2-Element-Typeᵉ Xᵉ) →
    htpy-equivᵉ eᵉ e'ᵉ ≃ᵉ (map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ) ＝ᵉ map-equivᵉ e'ᵉ (zero-Finᵉ 1ᵉ))
  pr1ᵉ (equiv-ev-zero-htpy-equiv-Fin-two-ℕᵉ eᵉ e'ᵉ) =
    ev-zero-htpy-equiv-Fin-two-ℕᵉ eᵉ e'ᵉ
  pr2ᵉ (equiv-ev-zero-htpy-equiv-Fin-two-ℕᵉ eᵉ e'ᵉ) =
    is-equiv-ev-zero-htpy-equiv-Fin-two-ℕᵉ eᵉ e'ᵉ
```

### The canonical type family on the type of `2`-element types has no section

```agda
abstract
  no-section-type-2-Element-Typeᵉ :
    {lᵉ : Level} → ¬ᵉ ((Xᵉ : 2-Element-Typeᵉ lᵉ) → type-2-Element-Typeᵉ Xᵉ)
  no-section-type-2-Element-Typeᵉ {lᵉ} fᵉ =
    is-not-contractible-Finᵉ 2
      ( Eq-eq-ℕᵉ)
      ( is-contr-equivᵉ
        ( standard-2-Element-Typeᵉ lᵉ ＝ᵉ standard-2-Element-Typeᵉ lᵉ)
        ( ( inv-equivᵉ equiv-point-eq-2-Element-Typeᵉ) ∘eᵉ
          ( compute-raise-Finᵉ lᵉ 2ᵉ))
        ( is-prop-is-contrᵉ
          ( pairᵉ
            ( standard-2-Element-Typeᵉ lᵉ)
            ( λ Xᵉ → eq-point-2-Element-Typeᵉ (fᵉ Xᵉ)))
          ( standard-2-Element-Typeᵉ lᵉ)
          ( standard-2-Element-Typeᵉ lᵉ)))
```

### There is no decidability procedure that proves that an arbitrary `2`-element type is decidable

```agda
abstract
  is-not-decidable-type-2-Element-Typeᵉ :
    {lᵉ : Level} →
    ¬ᵉ ((Xᵉ : 2-Element-Typeᵉ lᵉ) → is-decidableᵉ (type-2-Element-Typeᵉ Xᵉ))
  is-not-decidable-type-2-Element-Typeᵉ {lᵉ} dᵉ =
    no-section-type-2-Element-Typeᵉ
      ( λ Xᵉ →
        map-right-unit-law-coproduct-is-emptyᵉ
          ( pr1ᵉ Xᵉ)
          ( ¬ᵉ (pr1ᵉ Xᵉ))
          ( apply-universal-property-trunc-Propᵉ
            ( pr2ᵉ Xᵉ)
            ( double-negation-type-Propᵉ (pr1ᵉ Xᵉ))
            ( λ eᵉ → intro-double-negationᵉ {lᵉ} (map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ))))
          ( dᵉ Xᵉ))
```

### Any automorphism on `Fin 2` is an involution

```agda
cases-is-involution-aut-Fin-two-ℕᵉ :
  (eᵉ : Finᵉ 2 ≃ᵉ Finᵉ 2ᵉ) (xᵉ yᵉ zᵉ : Finᵉ 2ᵉ) →
  map-equivᵉ eᵉ xᵉ ＝ᵉ yᵉ → map-equivᵉ eᵉ yᵉ ＝ᵉ zᵉ →
  map-equivᵉ (eᵉ ∘eᵉ eᵉ) xᵉ ＝ᵉ xᵉ
cases-is-involution-aut-Fin-two-ℕᵉ eᵉ (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inrᵉ starᵉ)) zᵉ pᵉ qᵉ =
  apᵉ (map-equivᵉ eᵉ) pᵉ ∙ᵉ pᵉ
cases-is-involution-aut-Fin-two-ℕᵉ eᵉ
  (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)) pᵉ qᵉ =
  apᵉ (map-equivᵉ eᵉ) pᵉ ∙ᵉ qᵉ
cases-is-involution-aut-Fin-two-ℕᵉ eᵉ (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) (inrᵉ starᵉ) pᵉ qᵉ =
  ex-falsoᵉ (neq-inr-inlᵉ (is-injective-equivᵉ eᵉ (qᵉ ∙ᵉ invᵉ pᵉ)))
cases-is-involution-aut-Fin-two-ℕᵉ eᵉ
  (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inrᵉ starᵉ)) pᵉ qᵉ =
  ex-falsoᵉ (neq-inr-inlᵉ (is-injective-equivᵉ eᵉ (pᵉ ∙ᵉ invᵉ qᵉ)))
cases-is-involution-aut-Fin-two-ℕᵉ eᵉ (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) pᵉ qᵉ =
  apᵉ (map-equivᵉ eᵉ) pᵉ ∙ᵉ qᵉ
cases-is-involution-aut-Fin-two-ℕᵉ eᵉ (inrᵉ starᵉ) (inrᵉ starᵉ) zᵉ pᵉ qᵉ =
  apᵉ (map-equivᵉ eᵉ) pᵉ ∙ᵉ pᵉ

is-involution-aut-Fin-two-ℕᵉ : (eᵉ : Finᵉ 2 ≃ᵉ Finᵉ 2ᵉ) → is-involution-autᵉ eᵉ
is-involution-aut-Fin-two-ℕᵉ eᵉ xᵉ =
  cases-is-involution-aut-Fin-two-ℕᵉ eᵉ xᵉ
    ( map-equivᵉ eᵉ xᵉ)
    ( map-equivᵉ (eᵉ ∘eᵉ eᵉ) xᵉ)
    ( reflᵉ)
    ( reflᵉ)

module _
  {lᵉ : Level} (Xᵉ : 2-Element-Typeᵉ lᵉ)
  where

  is-involution-aut-2-element-typeᵉ :
    (eᵉ : equiv-2-Element-Typeᵉ Xᵉ Xᵉ) → is-involution-autᵉ eᵉ
  is-involution-aut-2-element-typeᵉ eᵉ xᵉ =
    apply-universal-property-trunc-Propᵉ
      ( has-two-elements-type-2-Element-Typeᵉ Xᵉ)
      ( Id-Propᵉ (set-2-Element-Typeᵉ Xᵉ) (map-equivᵉ (eᵉ ∘eᵉ eᵉ) xᵉ) xᵉ)
      ( λ hᵉ →
        ( apᵉ (map-equivᵉ (eᵉ ∘eᵉ eᵉ)) (invᵉ (is-section-map-inv-equivᵉ hᵉ xᵉ))) ∙ᵉ
        ( ( apᵉ (map-equivᵉ eᵉ) (invᵉ (is-section-map-inv-equivᵉ hᵉ _))) ∙ᵉ
          ( invᵉ (is-section-map-inv-equivᵉ hᵉ _) ∙ᵉ
            ( ( apᵉ
                ( map-equivᵉ hᵉ)
                ( is-involution-aut-Fin-two-ℕᵉ (inv-equivᵉ hᵉ ∘eᵉ (eᵉ ∘eᵉ hᵉ)) _)) ∙ᵉ
              ( is-section-map-inv-equivᵉ hᵉ xᵉ)))))
```

### The swapping equivalence on arbitrary `2`-element types

```agda
module _
  {lᵉ : Level} (Xᵉ : 2-Element-Typeᵉ lᵉ)
  where

  swap-2-Element-Typeᵉ : equiv-2-Element-Typeᵉ Xᵉ Xᵉ
  swap-2-Element-Typeᵉ =
    ( equiv-ev-zero-equiv-Fin-two-ℕᵉ Xᵉ) ∘eᵉ
    ( ( equiv-precomp-equivᵉ (equiv-succ-Finᵉ 2ᵉ) (type-2-Element-Typeᵉ Xᵉ)) ∘eᵉ
      ( inv-equivᵉ (equiv-ev-zero-equiv-Fin-two-ℕᵉ Xᵉ)))

  map-swap-2-Element-Typeᵉ : type-2-Element-Typeᵉ Xᵉ → type-2-Element-Typeᵉ Xᵉ
  map-swap-2-Element-Typeᵉ = map-equivᵉ swap-2-Element-Typeᵉ

  compute-swap-2-Element-Type'ᵉ :
    (xᵉ yᵉ : type-2-Element-Typeᵉ Xᵉ) → xᵉ ≠ᵉ yᵉ → (zᵉ : Finᵉ 2ᵉ) →
    map-inv-equiv-point-2-Element-Typeᵉ Xᵉ xᵉ yᵉ ＝ᵉ zᵉ →
    map-swap-2-Element-Typeᵉ xᵉ ＝ᵉ yᵉ
  compute-swap-2-Element-Type'ᵉ xᵉ yᵉ fᵉ (inlᵉ (inrᵉ starᵉ)) qᵉ =
    ex-falsoᵉ
      ( fᵉ
        ( (invᵉ (compute-map-equiv-point-2-Element-Typeᵉ Xᵉ xᵉ)) ∙ᵉ
          ( ( apᵉ (map-equiv-point-2-Element-Typeᵉ Xᵉ xᵉ) (invᵉ qᵉ)) ∙ᵉ
            ( is-section-map-inv-equiv-point-2-Element-Typeᵉ Xᵉ xᵉ yᵉ))))
  compute-swap-2-Element-Type'ᵉ xᵉ yᵉ pᵉ (inrᵉ starᵉ) qᵉ =
    ( apᵉ (map-equiv-point-2-Element-Typeᵉ Xᵉ xᵉ) (invᵉ qᵉ)) ∙ᵉ
    ( is-section-map-inv-equiv-point-2-Element-Typeᵉ Xᵉ xᵉ yᵉ)

  compute-swap-2-Element-Typeᵉ :
    (xᵉ yᵉ : type-2-Element-Typeᵉ Xᵉ) → xᵉ ≠ᵉ yᵉ →
    map-swap-2-Element-Typeᵉ xᵉ ＝ᵉ yᵉ
  compute-swap-2-Element-Typeᵉ xᵉ yᵉ pᵉ =
    compute-swap-2-Element-Type'ᵉ xᵉ yᵉ pᵉ
      ( map-inv-equiv-point-2-Element-Typeᵉ Xᵉ xᵉ yᵉ)
      ( reflᵉ)

  compute-map-equiv-point-2-Element-Type'ᵉ :
    (xᵉ : type-2-Element-Typeᵉ Xᵉ) →
    map-equiv-point-2-Element-Typeᵉ Xᵉ xᵉ (one-Finᵉ 1ᵉ) ＝ᵉ
    map-swap-2-Element-Typeᵉ xᵉ
  compute-map-equiv-point-2-Element-Type'ᵉ xᵉ = reflᵉ

compute-swap-Fin-two-ℕᵉ :
  map-swap-2-Element-Typeᵉ (Fin-UU-Fin'ᵉ 2ᵉ) ~ᵉ succ-Finᵉ 2
compute-swap-Fin-two-ℕᵉ (inlᵉ (inrᵉ starᵉ)) =
  compute-swap-2-Element-Typeᵉ
    ( Fin-UU-Fin'ᵉ 2ᵉ)
    ( zero-Finᵉ 1ᵉ)
    ( one-Finᵉ 1ᵉ)
    ( neq-inl-inrᵉ)
compute-swap-Fin-two-ℕᵉ (inrᵉ starᵉ) =
  compute-swap-2-Element-Typeᵉ
    ( Fin-UU-Fin'ᵉ 2ᵉ)
    ( one-Finᵉ 1ᵉ)
    ( zero-Finᵉ 1ᵉ)
    ( neq-inr-inlᵉ)
```

### The swapping equivalence is not the identity equivalence

```agda
module _
  {lᵉ : Level} (Xᵉ : 2-Element-Typeᵉ lᵉ)
  where

  is-not-identity-equiv-precomp-equiv-equiv-succ-Finᵉ :
    equiv-precomp-equivᵉ (equiv-succ-Finᵉ 2ᵉ) (type-2-Element-Typeᵉ Xᵉ) ≠ᵉ id-equivᵉ
  is-not-identity-equiv-precomp-equiv-equiv-succ-Finᵉ p'ᵉ =
    apply-universal-property-trunc-Propᵉ
      ( has-two-elements-type-2-Element-Typeᵉ Xᵉ)
      ( empty-Propᵉ)
      ( λ fᵉ →
        neq-inr-inlᵉ
          ( is-injective-equivᵉ fᵉ
            ( htpy-eq-equivᵉ (htpy-eq-equivᵉ p'ᵉ fᵉ) (zero-Finᵉ 1ᵉ))))

  is-not-identity-swap-2-Element-Typeᵉ : swap-2-Element-Typeᵉ Xᵉ ≠ᵉ id-equivᵉ
  is-not-identity-swap-2-Element-Typeᵉ pᵉ =
    is-not-identity-equiv-precomp-equiv-equiv-succ-Finᵉ
      ( ( ( invᵉ (left-unit-law-equivᵉ equiv1ᵉ)) ∙ᵉ
          ( apᵉ (λ xᵉ → xᵉ ∘eᵉ equiv1ᵉ) (invᵉ (left-inverse-law-equivᵉ equiv2ᵉ)))) ∙ᵉ
        ( ( invᵉ
            ( right-unit-law-equivᵉ ((inv-equivᵉ equiv2ᵉ ∘eᵉ equiv2ᵉ) ∘eᵉ equiv1ᵉ))) ∙ᵉ
          ( ( apᵉ
              ( λ xᵉ → ((inv-equivᵉ equiv2ᵉ ∘eᵉ equiv2ᵉ) ∘eᵉ equiv1ᵉ) ∘eᵉ xᵉ)
              ( invᵉ (left-inverse-law-equivᵉ equiv2ᵉ))) ∙ᵉ
          ( ( ( eq-equiv-eq-map-equivᵉ reflᵉ) ∙ᵉ
              ( apᵉ (λ xᵉ → inv-equivᵉ equiv2ᵉ ∘eᵉ (xᵉ ∘eᵉ equiv2ᵉ)) pᵉ)) ∙ᵉ
            ( ( apᵉ
                ( λ xᵉ → inv-equivᵉ equiv2ᵉ ∘eᵉ xᵉ)
                ( left-unit-law-equivᵉ equiv2ᵉ)) ∙ᵉ
              ( left-inverse-law-equivᵉ equiv2ᵉ))))))
    where
    equiv1ᵉ : (Finᵉ 2 ≃ᵉ type-2-Element-Typeᵉ Xᵉ) ≃ᵉ (Finᵉ 2 ≃ᵉ type-2-Element-Typeᵉ Xᵉ)
    equiv1ᵉ = equiv-precomp-equivᵉ (equiv-succ-Finᵉ 2ᵉ) (type-2-Element-Typeᵉ Xᵉ)
    equiv2ᵉ : (Finᵉ 2 ≃ᵉ type-2-Element-Typeᵉ Xᵉ) ≃ᵉ type-2-Element-Typeᵉ Xᵉ
    equiv2ᵉ = equiv-ev-zero-equiv-Fin-two-ℕᵉ Xᵉ
```

### The swapping equivalence has no fixpoints

```agda
module _
  {lᵉ : Level} (Xᵉ : 2-Element-Typeᵉ lᵉ)
  where

  has-no-fixed-points-swap-2-Element-Typeᵉ :
    {xᵉ : type-2-Element-Typeᵉ Xᵉ} → map-equivᵉ (swap-2-Element-Typeᵉ Xᵉ) xᵉ ≠ᵉ xᵉ
  has-no-fixed-points-swap-2-Element-Typeᵉ {xᵉ} Pᵉ =
    apply-universal-property-trunc-Propᵉ
      ( has-two-elements-type-2-Element-Typeᵉ Xᵉ)
      ( empty-Propᵉ)
      ( λ hᵉ →
        is-not-identity-swap-2-Element-Typeᵉ Xᵉ
          (eq-htpy-equivᵉ
            (λ yᵉ →
              fᵉ
                ( inv-equivᵉ hᵉ)
                ( yᵉ)
                ( map-inv-equivᵉ hᵉ xᵉ)
                ( map-inv-equivᵉ hᵉ yᵉ)
                ( map-inv-equivᵉ hᵉ (map-equivᵉ (swap-2-Element-Typeᵉ Xᵉ) yᵉ))
                ( reflᵉ)
                ( reflᵉ)
                ( reflᵉ))))
    where
    fᵉ :
      ( hᵉ : type-2-Element-Typeᵉ Xᵉ ≃ᵉ Finᵉ 2ᵉ)
      ( yᵉ : type-2-Element-Typeᵉ Xᵉ) →
      ( k1ᵉ k2ᵉ k3ᵉ : Finᵉ 2ᵉ) →
        map-equivᵉ hᵉ xᵉ ＝ᵉ k1ᵉ → map-equivᵉ hᵉ yᵉ ＝ᵉ k2ᵉ →
        map-equivᵉ hᵉ (map-equivᵉ (swap-2-Element-Typeᵉ Xᵉ) yᵉ) ＝ᵉ k3ᵉ →
        map-equivᵉ (swap-2-Element-Typeᵉ Xᵉ) yᵉ ＝ᵉ yᵉ
    fᵉ hᵉ yᵉ (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inrᵉ starᵉ)) k3ᵉ pᵉ qᵉ rᵉ =
      trᵉ
        ( λ zᵉ → map-equivᵉ (swap-2-Element-Typeᵉ Xᵉ) zᵉ ＝ᵉ zᵉ)
        ( is-injective-equivᵉ hᵉ (pᵉ ∙ᵉ invᵉ qᵉ))
        ( Pᵉ)
    fᵉ hᵉ yᵉ (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)) pᵉ qᵉ rᵉ =
      ex-falsoᵉ
        ( neq-inl-inrᵉ
          ( invᵉ pᵉ ∙ᵉ (apᵉ (map-equivᵉ hᵉ) (invᵉ Pᵉ) ∙ᵉ
            ( apᵉ
              ( map-equivᵉ (hᵉ ∘eᵉ (swap-2-Element-Typeᵉ Xᵉ)))
              ( is-injective-equivᵉ hᵉ (pᵉ ∙ᵉ invᵉ rᵉ)) ∙ᵉ
              ( ( apᵉ
                  ( map-equivᵉ hᵉ)
                  ( is-involution-aut-2-element-typeᵉ Xᵉ
                    ( swap-2-Element-Typeᵉ Xᵉ) yᵉ)) ∙ᵉ
                ( qᵉ))))))
    fᵉ hᵉ yᵉ (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) (inrᵉ starᵉ) pᵉ qᵉ rᵉ =
      ( is-injective-equivᵉ hᵉ (rᵉ ∙ᵉ invᵉ qᵉ))
    fᵉ hᵉ yᵉ (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inrᵉ starᵉ)) pᵉ qᵉ rᵉ =
      ( is-injective-equivᵉ hᵉ (rᵉ ∙ᵉ invᵉ qᵉ))
    fᵉ hᵉ yᵉ (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) pᵉ qᵉ rᵉ =
      ex-falsoᵉ
        ( neq-inr-inlᵉ
          ( invᵉ pᵉ ∙ᵉ (apᵉ (map-equivᵉ hᵉ) (invᵉ Pᵉ) ∙ᵉ
            ( apᵉ
              ( map-equivᵉ (hᵉ ∘eᵉ (swap-2-Element-Typeᵉ Xᵉ)))
              ( is-injective-equivᵉ hᵉ (pᵉ ∙ᵉ invᵉ rᵉ)) ∙ᵉ
              ( ( apᵉ
                  ( map-equivᵉ hᵉ)
                  ( is-involution-aut-2-element-typeᵉ Xᵉ
                    ( swap-2-Element-Typeᵉ Xᵉ)
                    ( yᵉ))) ∙ᵉ
                ( qᵉ))))))
    fᵉ hᵉ yᵉ (inrᵉ starᵉ) (inrᵉ starᵉ) k3ᵉ pᵉ qᵉ rᵉ =
      trᵉ
        ( λ zᵉ → map-equivᵉ (swap-2-Element-Typeᵉ Xᵉ) zᵉ ＝ᵉ zᵉ)
        ( is-injective-equivᵉ hᵉ (pᵉ ∙ᵉ invᵉ qᵉ))
        ( Pᵉ)
```

### Evaluating an automorphism at `0 : Fin 2` is a group homomorphism

```agda
preserves-add-aut-point-Fin-two-ℕᵉ :
  (aᵉ bᵉ : Finᵉ 2ᵉ) →
  aut-point-Fin-two-ℕᵉ (add-Finᵉ 2 aᵉ bᵉ) ＝ᵉ
  ( aut-point-Fin-two-ℕᵉ aᵉ ∘eᵉ aut-point-Fin-two-ℕᵉ bᵉ)
preserves-add-aut-point-Fin-two-ℕᵉ (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inrᵉ starᵉ)) =
  eq-equiv-eq-map-equivᵉ reflᵉ
preserves-add-aut-point-Fin-two-ℕᵉ (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) =
  eq-equiv-eq-map-equivᵉ reflᵉ
preserves-add-aut-point-Fin-two-ℕᵉ (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)) =
  eq-equiv-eq-map-equivᵉ reflᵉ
preserves-add-aut-point-Fin-two-ℕᵉ (inrᵉ starᵉ) (inrᵉ starᵉ) =
  eq-htpy-equivᵉ (λ xᵉ → invᵉ (is-involution-aut-Fin-two-ℕᵉ (equiv-succ-Finᵉ 2ᵉ) xᵉ))
```

### Any Σ-type over `Fin 2` is a coproduct

```agda
is-coproduct-Σ-Fin-two-ℕᵉ :
  {lᵉ : Level} (Pᵉ : Finᵉ 2 → UUᵉ lᵉ) →
  Σᵉ (Finᵉ 2ᵉ) Pᵉ ≃ᵉ (Pᵉ (zero-Finᵉ 1ᵉ) +ᵉ Pᵉ (one-Finᵉ 1ᵉ))
is-coproduct-Σ-Fin-two-ℕᵉ Pᵉ =
  ( equiv-coproductᵉ
    ( left-unit-law-Σ-is-contrᵉ is-contr-Fin-one-ℕᵉ (zero-Finᵉ 0ᵉ))
    ( left-unit-law-Σᵉ (Pᵉ ∘ᵉ inrᵉ))) ∘eᵉ
  ( right-distributive-Σ-coproductᵉ (Finᵉ 1ᵉ) unitᵉ Pᵉ)
```

### For any equivalence `e : Fin 2 ≃ X`, any element of `X` is either `e 0` or it is `e 1`

```agda
module _
  {lᵉ : Level} (Xᵉ : 2-Element-Typeᵉ lᵉ)
  where

  abstract
    is-contr-decide-value-equiv-Fin-two-ℕᵉ :
      (eᵉ : Finᵉ 2 ≃ᵉ type-2-Element-Typeᵉ Xᵉ) (xᵉ : type-2-Element-Typeᵉ Xᵉ) →
      is-contrᵉ
        ( ( xᵉ ＝ᵉ map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ)) +ᵉ
          ( xᵉ ＝ᵉ map-equivᵉ eᵉ (one-Finᵉ 1ᵉ)))
    is-contr-decide-value-equiv-Fin-two-ℕᵉ eᵉ xᵉ =
      is-contr-equiv'ᵉ
        ( fiberᵉ (map-equivᵉ eᵉ) xᵉ)
        ( ( is-coproduct-Σ-Fin-two-ℕᵉ (λ yᵉ → xᵉ ＝ᵉ map-equivᵉ eᵉ yᵉ)) ∘eᵉ
          ( equiv-totᵉ (λ yᵉ → equiv-invᵉ (map-equivᵉ eᵉ yᵉ) xᵉ)))
        ( is-contr-map-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) xᵉ)

  decide-value-equiv-Fin-two-ℕᵉ :
    (eᵉ : Finᵉ 2 ≃ᵉ type-2-Element-Typeᵉ Xᵉ) (xᵉ : type-2-Element-Typeᵉ Xᵉ) →
    (xᵉ ＝ᵉ map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ)) +ᵉ (xᵉ ＝ᵉ map-equivᵉ eᵉ (one-Finᵉ 1ᵉ))
  decide-value-equiv-Fin-two-ℕᵉ eᵉ xᵉ =
    centerᵉ (is-contr-decide-value-equiv-Fin-two-ℕᵉ eᵉ xᵉ)
```

### There can't be three distinct elements in a `2`-element type

```agda
module _
  {lᵉ : Level} (Xᵉ : 2-Element-Typeᵉ lᵉ)
  where

  contradiction-3-distinct-element-2-Element-Typeᵉ :
    (xᵉ yᵉ zᵉ : type-2-Element-Typeᵉ Xᵉ) →
    xᵉ ≠ᵉ yᵉ → yᵉ ≠ᵉ zᵉ → xᵉ ≠ᵉ zᵉ → emptyᵉ
  contradiction-3-distinct-element-2-Element-Typeᵉ xᵉ yᵉ zᵉ npᵉ nqᵉ nrᵉ =
    apply-universal-property-trunc-Propᵉ
      ( has-two-elements-type-2-Element-Typeᵉ Xᵉ)
      ( empty-Propᵉ)
      ( λ eᵉ →
        cases-contradiction-3-distinct-element-2-Element-Typeᵉ
          ( eᵉ)
          ( decide-value-equiv-Fin-two-ℕᵉ Xᵉ eᵉ xᵉ)
          ( decide-value-equiv-Fin-two-ℕᵉ Xᵉ eᵉ yᵉ)
          ( decide-value-equiv-Fin-two-ℕᵉ Xᵉ eᵉ zᵉ))
    where
    cases-contradiction-3-distinct-element-2-Element-Typeᵉ :
      (eᵉ : Finᵉ 2 ≃ᵉ type-2-Element-Typeᵉ Xᵉ) →
      (xᵉ ＝ᵉ map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ)) +ᵉ (xᵉ ＝ᵉ map-equivᵉ eᵉ (one-Finᵉ 1ᵉ)) →
      (yᵉ ＝ᵉ map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ)) +ᵉ (yᵉ ＝ᵉ map-equivᵉ eᵉ (one-Finᵉ 1ᵉ)) →
      (zᵉ ＝ᵉ map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ)) +ᵉ (zᵉ ＝ᵉ map-equivᵉ eᵉ (one-Finᵉ 1ᵉ)) →
      emptyᵉ
    cases-contradiction-3-distinct-element-2-Element-Typeᵉ eᵉ
      (inlᵉ reflᵉ) (inlᵉ reflᵉ) c3ᵉ = npᵉ reflᵉ
    cases-contradiction-3-distinct-element-2-Element-Typeᵉ eᵉ
      (inlᵉ reflᵉ) (inrᵉ reflᵉ) (inlᵉ reflᵉ) = nrᵉ reflᵉ
    cases-contradiction-3-distinct-element-2-Element-Typeᵉ eᵉ
      (inlᵉ reflᵉ) (inrᵉ reflᵉ) (inrᵉ reflᵉ) = nqᵉ reflᵉ
    cases-contradiction-3-distinct-element-2-Element-Typeᵉ eᵉ
      (inrᵉ reflᵉ) (inlᵉ reflᵉ) (inlᵉ reflᵉ) = nqᵉ reflᵉ
    cases-contradiction-3-distinct-element-2-Element-Typeᵉ eᵉ
      (inrᵉ reflᵉ) (inlᵉ reflᵉ) (inrᵉ reflᵉ) = nrᵉ reflᵉ
    cases-contradiction-3-distinct-element-2-Element-Typeᵉ eᵉ
      (inrᵉ reflᵉ) (inrᵉ reflᵉ) c3ᵉ = npᵉ reflᵉ
```

### For any map between `2`-element types, being an equivalence is decidable

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 2-Element-Typeᵉ l1ᵉ) (Yᵉ : 2-Element-Typeᵉ l2ᵉ)
  where

  is-decidable-is-equiv-2-Element-Typeᵉ :
    (fᵉ : type-2-Element-Typeᵉ Xᵉ → type-2-Element-Typeᵉ Yᵉ) →
    is-decidableᵉ (is-equivᵉ fᵉ)
  is-decidable-is-equiv-2-Element-Typeᵉ fᵉ =
    is-decidable-is-equiv-is-finiteᵉ fᵉ
      ( is-finite-type-2-Element-Typeᵉ Xᵉ)
      ( is-finite-type-2-Element-Typeᵉ Yᵉ)
```

### A map between `2`-element types is an equivalence if and only if its image is the full subtype of the codomain

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#743](https://github.com/UniMath/agda-unimath/issues/743ᵉ)

### A map between `2`-element types is not an equivalence if and only if its image is a singleton subtype of the codomain

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#743](https://github.com/UniMath/agda-unimath/issues/743ᵉ)

### Any map between `2`-element types that is not an equivalence is constant

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#743](https://github.com/UniMath/agda-unimath/issues/743ᵉ)

```agda
{-ᵉ
  is-constant-is-not-equiv-2-Element-Typeᵉ :
    (fᵉ : type-2-Element-Typeᵉ Xᵉ → type-2-Element-Typeᵉ Yᵉ) →
    ¬ᵉ (is-equivᵉ fᵉ) →
    Σᵉ (type-2-Element-Typeᵉ Yᵉ) (λ yᵉ → fᵉ ~ᵉ constᵉ _ yᵉ)
  pr1ᵉ (is-constant-is-not-equiv-2-Element-Typeᵉ fᵉ Hᵉ) = {!!ᵉ}
  pr2ᵉ (is-constant-is-not-equiv-2-Element-Typeᵉ fᵉ Hᵉ) = {!!ᵉ}
  -ᵉ}
```

### Any map between `2`-element types is either an equivalence or it is constant

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#743](https://github.com/UniMath/agda-unimath/issues/743ᵉ)

### Coinhabited `2`-element types are equivalent

```agda
{-ᵉ
equiv-iff-2-Element-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 2-Element-Typeᵉ l1ᵉ) (Yᵉ : 2-Element-Typeᵉ l2ᵉ) →
  (type-2-Element-Typeᵉ Xᵉ ↔ᵉ type-2-Element-Typeᵉ Yᵉ) →
  (equiv-2-Element-Typeᵉ Xᵉ Yᵉ)
equiv-iff-2-Element-Typeᵉ Xᵉ Yᵉ (fᵉ ,ᵉ gᵉ) = {!is-decidable-is-equiv-is-finite!ᵉ}
-ᵉ}
```