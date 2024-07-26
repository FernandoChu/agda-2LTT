# Higher modalities

```agda
module orthogonal-factorization-systems.higher-modalitiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.precomposition-dependent-functionsᵉ
open import foundation.retractionsᵉ
open import foundation.small-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.locally-small-modal-operatorsᵉ
open import orthogonal-factorization-systems.modal-inductionᵉ
open import orthogonal-factorization-systems.modal-operatorsᵉ
open import orthogonal-factorization-systems.modal-subuniverse-inductionᵉ
open import orthogonal-factorization-systems.uniquely-eliminating-modalitiesᵉ
```

</details>

## Idea

Aᵉ **higherᵉ modality**ᵉ isᵉ aᵉ _higherᵉ modeᵉ ofᵉ logicᵉ_ definedᵉ in termsᵉ ofᵉ aᵉ monadicᵉ
[modalᵉ operator](orthogonal-factorization-systems.modal-operators.mdᵉ) `○`ᵉ
satisfyingᵉ aᵉ certainᵉ inductionᵉ principle.ᵉ

Theᵉ inductionᵉ principleᵉ statesᵉ thatᵉ forᵉ everyᵉ typeᵉ `X`ᵉ andᵉ familyᵉ
`Pᵉ : ○ᵉ Xᵉ → UU`,ᵉ to defineᵉ aᵉ dependentᵉ mapᵉ `(x'ᵉ : ○ᵉ Xᵉ) → ○ᵉ (Pᵉ x')`ᵉ itᵉ sufficesᵉ to
defineᵉ itᵉ onᵉ theᵉ imageᵉ ofᵉ theᵉ modalᵉ unit,ᵉ i.e.ᵉ `(xᵉ : Xᵉ) → ○ᵉ (Pᵉ (unit-○ᵉ x))`.ᵉ
Moreover,ᵉ itᵉ satisfiesᵉ aᵉ computationᵉ principleᵉ statingᵉ thatᵉ whenᵉ evaluatingᵉ aᵉ
mapᵉ definedᵉ in thisᵉ mannerᵉ onᵉ theᵉ imageᵉ ofᵉ theᵉ modalᵉ unit,ᵉ oneᵉ recoversᵉ theᵉ
definingᵉ mapᵉ (propositionally).ᵉ

Lastly,ᵉ higherᵉ modalitiesᵉ mustᵉ alsoᵉ beᵉ **identityᵉ closed**ᵉ in theᵉ senseᵉ thatᵉ forᵉ
everyᵉ typeᵉ `X`ᵉ theᵉ identityᵉ typesᵉ `(x'ᵉ ＝ᵉ y')`ᵉ areᵉ modalᵉ forᵉ allᵉ termsᵉ
`x'ᵉ y'ᵉ : ○ᵉ X`.ᵉ Inᵉ otherᵉ words,ᵉ `○ᵉ X`ᵉ isᵉ
[`○`-separated](foundation.separated-types.md).ᵉ Becauseᵉ ofᵉ this,ᵉ higherᵉ
modalitiesᵉ in theirᵉ mostᵉ generalᵉ formᵉ onlyᵉ makeᵉ senseᵉ forᵉ
[locallyᵉ smallᵉ modalᵉ operators](orthogonal-factorization-systems.locally-small-modal-operators.md).ᵉ

## Definition

### Closure under identity type formers

Weᵉ sayᵉ thatᵉ theᵉ [identityᵉ types](foundation-core.identity-types.mdᵉ) ofᵉ aᵉ
[locallyᵉ smallᵉ type](foundation.locally-small-types.mdᵉ) areᵉ **modal**ᵉ ifᵉ theirᵉ
[smallᵉ equivalent](foundation-core.small-types.mdᵉ) isᵉ modal.ᵉ Weᵉ sayᵉ thatᵉ aᵉ
modalityᵉ isᵉ closedᵉ underᵉ [identityᵉ type](foundation-core.identity-types.mdᵉ)
formationᵉ if,ᵉ forᵉ everyᵉ modalᵉ type,ᵉ theirᵉ identityᵉ typesᵉ areᵉ alsoᵉ modal.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  ((○ᵉ ,ᵉ is-locally-small-○ᵉ) : locally-small-operator-modalityᵉ l1ᵉ l2ᵉ l1ᵉ)
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  is-modal-small-identity-typesᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  is-modal-small-identity-typesᵉ =
    (Xᵉ : UUᵉ l1ᵉ) (xᵉ yᵉ : ○ᵉ Xᵉ) →
    is-modal-type-is-smallᵉ (unit-○ᵉ) (xᵉ ＝ᵉ yᵉ) (is-locally-small-○ᵉ Xᵉ xᵉ yᵉ)
```

### The predicate of being a higher modality

```agda
  is-higher-modalityᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  is-higher-modalityᵉ =
    induction-principle-modalityᵉ (unit-○ᵉ) ×ᵉ is-modal-small-identity-typesᵉ
```

### Components of a higher modality proof

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (locally-small-○ᵉ : locally-small-operator-modalityᵉ l1ᵉ l2ᵉ l1ᵉ)
  (unit-○ᵉ : unit-modalityᵉ (pr1ᵉ locally-small-○ᵉ))
  (hᵉ : is-higher-modalityᵉ locally-small-○ᵉ unit-○ᵉ)
  where

  induction-principle-is-higher-modalityᵉ : induction-principle-modalityᵉ unit-○ᵉ
  induction-principle-is-higher-modalityᵉ = pr1ᵉ hᵉ

  ind-is-higher-modalityᵉ : ind-modalityᵉ unit-○ᵉ
  ind-is-higher-modalityᵉ =
    ind-induction-principle-modalityᵉ
      ( unit-○ᵉ)
      ( induction-principle-is-higher-modalityᵉ)

  compute-ind-is-higher-modalityᵉ :
    compute-ind-modalityᵉ unit-○ᵉ ind-is-higher-modalityᵉ
  compute-ind-is-higher-modalityᵉ =
    compute-ind-induction-principle-modalityᵉ
      ( unit-○ᵉ)
      ( induction-principle-is-higher-modalityᵉ)

  recursion-principle-is-higher-modalityᵉ : recursion-principle-modalityᵉ unit-○ᵉ
  recursion-principle-is-higher-modalityᵉ =
    recursion-principle-induction-principle-modalityᵉ
      ( unit-○ᵉ)
      ( induction-principle-is-higher-modalityᵉ)

  rec-is-higher-modalityᵉ : rec-modalityᵉ unit-○ᵉ
  rec-is-higher-modalityᵉ =
    rec-recursion-principle-modalityᵉ
      ( unit-○ᵉ)
      ( recursion-principle-is-higher-modalityᵉ)

  compute-rec-is-higher-modalityᵉ :
    compute-rec-modalityᵉ unit-○ᵉ rec-is-higher-modalityᵉ
  compute-rec-is-higher-modalityᵉ =
    compute-rec-recursion-principle-modalityᵉ
      ( unit-○ᵉ)
      ( recursion-principle-is-higher-modalityᵉ)

  is-modal-small-identity-types-is-higher-modalityᵉ :
    is-modal-small-identity-typesᵉ locally-small-○ᵉ unit-○ᵉ
  is-modal-small-identity-types-is-higher-modalityᵉ = pr2ᵉ hᵉ
```

### The structure of a higher modality

```agda
higher-modalityᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
higher-modalityᵉ l1ᵉ l2ᵉ =
  Σᵉ ( locally-small-operator-modalityᵉ l1ᵉ l2ᵉ l1ᵉ)
    ( λ ○ᵉ →
      Σᵉ ( unit-modalityᵉ (pr1ᵉ ○ᵉ))
        ( is-higher-modalityᵉ ○ᵉ))
```

### Components of a higher modality

```agda
module _
  {l1ᵉ l2ᵉ : Level} (hᵉ : higher-modalityᵉ l1ᵉ l2ᵉ)
  where

  locally-small-operator-higher-modalityᵉ :
    locally-small-operator-modalityᵉ l1ᵉ l2ᵉ l1ᵉ
  locally-small-operator-higher-modalityᵉ = pr1ᵉ hᵉ

  operator-higher-modalityᵉ : operator-modalityᵉ l1ᵉ l2ᵉ
  operator-higher-modalityᵉ =
    operator-modality-locally-small-operator-modalityᵉ
      ( locally-small-operator-higher-modalityᵉ)

  is-locally-small-operator-higher-modalityᵉ :
    is-locally-small-operator-modalityᵉ l1ᵉ (operator-higher-modalityᵉ)
  is-locally-small-operator-higher-modalityᵉ =
    is-locally-small-locally-small-operator-modalityᵉ
      ( locally-small-operator-higher-modalityᵉ)

  unit-higher-modalityᵉ :
    unit-modalityᵉ (operator-higher-modalityᵉ)
  unit-higher-modalityᵉ = pr1ᵉ (pr2ᵉ hᵉ)

  is-higher-modality-higher-modalityᵉ :
    is-higher-modalityᵉ
      ( locally-small-operator-higher-modalityᵉ)
      ( unit-higher-modalityᵉ)
  is-higher-modality-higher-modalityᵉ = pr2ᵉ (pr2ᵉ hᵉ)

  induction-principle-higher-modalityᵉ :
    induction-principle-modalityᵉ (unit-higher-modalityᵉ)
  induction-principle-higher-modalityᵉ =
    induction-principle-is-higher-modalityᵉ
      ( locally-small-operator-higher-modalityᵉ)
      ( unit-higher-modalityᵉ)
      ( is-higher-modality-higher-modalityᵉ)

  ind-higher-modalityᵉ :
    ind-modalityᵉ (unit-higher-modalityᵉ)
  ind-higher-modalityᵉ =
    ind-induction-principle-modalityᵉ
      ( unit-higher-modalityᵉ)
      ( induction-principle-higher-modalityᵉ)

  compute-ind-higher-modalityᵉ :
    compute-ind-modalityᵉ
      ( unit-higher-modalityᵉ)
      ( ind-higher-modalityᵉ)
  compute-ind-higher-modalityᵉ =
    compute-ind-induction-principle-modalityᵉ
      ( unit-higher-modalityᵉ)
      ( induction-principle-higher-modalityᵉ)

  recursion-principle-higher-modalityᵉ :
    recursion-principle-modalityᵉ (unit-higher-modalityᵉ)
  recursion-principle-higher-modalityᵉ =
    recursion-principle-is-higher-modalityᵉ
      ( locally-small-operator-higher-modalityᵉ)
      ( unit-higher-modalityᵉ)
      ( is-higher-modality-higher-modalityᵉ)

  rec-higher-modalityᵉ :
    rec-modalityᵉ (unit-higher-modalityᵉ)
  rec-higher-modalityᵉ =
    rec-recursion-principle-modalityᵉ
      ( unit-higher-modalityᵉ)
      ( recursion-principle-higher-modalityᵉ)

  compute-rec-higher-modalityᵉ :
    compute-rec-modalityᵉ (unit-higher-modalityᵉ) (rec-higher-modalityᵉ)
  compute-rec-higher-modalityᵉ =
    compute-rec-recursion-principle-modalityᵉ
      ( unit-higher-modalityᵉ)
      ( recursion-principle-higher-modalityᵉ)

  is-modal-small-identity-type-higher-modalityᵉ :
    is-modal-small-identity-typesᵉ
      ( locally-small-operator-higher-modalityᵉ)
      ( unit-higher-modalityᵉ)
  is-modal-small-identity-type-higher-modalityᵉ =
    ( is-modal-small-identity-types-is-higher-modalityᵉ)
    ( locally-small-operator-higher-modalityᵉ)
    ( unit-higher-modalityᵉ)
    ( is-higher-modality-higher-modalityᵉ)
```

## Properties

### Subuniverse induction for higher modalities

```agda
module _
  {l1ᵉ l2ᵉ : Level} (mᵉ : higher-modalityᵉ l1ᵉ l2ᵉ)
  where

  strong-ind-subuniverse-higher-modalityᵉ :
    strong-ind-subuniverse-modalityᵉ (unit-higher-modalityᵉ mᵉ)
  strong-ind-subuniverse-higher-modalityᵉ =
    strong-ind-subuniverse-ind-modalityᵉ
      ( unit-higher-modalityᵉ mᵉ)
      ( ind-higher-modalityᵉ mᵉ)

  compute-strong-ind-subuniverse-higher-modalityᵉ :
    compute-strong-ind-subuniverse-modalityᵉ
      ( unit-higher-modalityᵉ mᵉ)
      ( strong-ind-subuniverse-higher-modalityᵉ)
  compute-strong-ind-subuniverse-higher-modalityᵉ =
    compute-strong-ind-subuniverse-ind-modalityᵉ
      ( unit-higher-modalityᵉ mᵉ)
      ( ind-higher-modalityᵉ mᵉ)
      ( compute-ind-higher-modalityᵉ mᵉ)

  ind-subuniverse-higher-modalityᵉ :
    ind-subuniverse-modalityᵉ (unit-higher-modalityᵉ mᵉ)
  ind-subuniverse-higher-modalityᵉ =
    ind-subuniverse-ind-modalityᵉ
      ( unit-higher-modalityᵉ mᵉ)
      ( ind-higher-modalityᵉ mᵉ)

  compute-ind-subuniverse-higher-modalityᵉ :
    compute-ind-subuniverse-modalityᵉ
      ( unit-higher-modalityᵉ mᵉ)
      ( ind-subuniverse-higher-modalityᵉ)
  compute-ind-subuniverse-higher-modalityᵉ =
    compute-ind-subuniverse-ind-modalityᵉ
      ( unit-higher-modalityᵉ mᵉ)
      ( ind-higher-modalityᵉ mᵉ)
      ( compute-ind-higher-modalityᵉ mᵉ)

  strong-rec-subuniverse-higher-modalityᵉ :
    strong-rec-subuniverse-modalityᵉ (unit-higher-modalityᵉ mᵉ)
  strong-rec-subuniverse-higher-modalityᵉ =
    strong-rec-subuniverse-rec-modalityᵉ
      ( unit-higher-modalityᵉ mᵉ)
      ( rec-higher-modalityᵉ mᵉ)

  compute-strong-rec-subuniverse-higher-modalityᵉ :
    compute-strong-rec-subuniverse-modalityᵉ
      ( unit-higher-modalityᵉ mᵉ)
      ( strong-rec-subuniverse-higher-modalityᵉ)
  compute-strong-rec-subuniverse-higher-modalityᵉ =
    compute-strong-rec-subuniverse-rec-modalityᵉ
      ( unit-higher-modalityᵉ mᵉ)
      ( rec-higher-modalityᵉ mᵉ)
      ( compute-rec-higher-modalityᵉ mᵉ)

  rec-subuniverse-higher-modalityᵉ :
    rec-subuniverse-modalityᵉ (unit-higher-modalityᵉ mᵉ)
  rec-subuniverse-higher-modalityᵉ =
    rec-subuniverse-rec-modalityᵉ
      ( unit-higher-modalityᵉ mᵉ)
      ( rec-higher-modalityᵉ mᵉ)

  compute-rec-subuniverse-higher-modalityᵉ :
    compute-rec-subuniverse-modalityᵉ
      ( unit-higher-modalityᵉ mᵉ)
      ( rec-subuniverse-higher-modalityᵉ)
  compute-rec-subuniverse-higher-modalityᵉ =
    compute-rec-subuniverse-rec-modalityᵉ
      ( unit-higher-modalityᵉ mᵉ)
      ( rec-higher-modalityᵉ mᵉ)
      ( compute-rec-higher-modalityᵉ mᵉ)
```

### When `l1 = l2`, the identity types are modal in the usual sense

```agda
map-inv-unit-small-Id-higher-modalityᵉ :
  {l1ᵉ l2ᵉ : Level}
  (mᵉ : higher-modalityᵉ l1ᵉ l2ᵉ)
  {Xᵉ : UUᵉ l1ᵉ} {x'ᵉ y'ᵉ : operator-higher-modalityᵉ mᵉ Xᵉ} →
  ( operator-higher-modalityᵉ mᵉ
    ( type-is-smallᵉ (is-locally-small-operator-higher-modalityᵉ mᵉ Xᵉ x'ᵉ y'ᵉ))) →
  x'ᵉ ＝ᵉ y'ᵉ
map-inv-unit-small-Id-higher-modalityᵉ mᵉ {Xᵉ} {x'ᵉ} {y'ᵉ} =
  map-inv-unit-is-modal-type-is-smallᵉ
    ( unit-higher-modalityᵉ mᵉ)
    ( x'ᵉ ＝ᵉ y'ᵉ)
    ( is-locally-small-operator-higher-modalityᵉ mᵉ Xᵉ x'ᵉ y'ᵉ)
    ( is-modal-small-identity-type-higher-modalityᵉ mᵉ Xᵉ x'ᵉ y'ᵉ)

module _
  {lᵉ : Level} (mᵉ : higher-modalityᵉ lᵉ lᵉ)
  where

  map-inv-unit-Id-higher-modalityᵉ :
    {Xᵉ : UUᵉ lᵉ} {x'ᵉ y'ᵉ : operator-higher-modalityᵉ mᵉ Xᵉ} →
    operator-higher-modalityᵉ mᵉ (x'ᵉ ＝ᵉ y'ᵉ) → x'ᵉ ＝ᵉ y'ᵉ
  map-inv-unit-Id-higher-modalityᵉ {Xᵉ} {x'ᵉ} {y'ᵉ} =
    map-inv-unit-small-Id-higher-modalityᵉ mᵉ ∘ᵉ
      ( ap-map-ind-modalityᵉ
        ( unit-higher-modalityᵉ mᵉ)
        ( ind-higher-modalityᵉ mᵉ)
        ( map-equiv-is-smallᵉ
          ( is-locally-small-operator-higher-modalityᵉ mᵉ Xᵉ x'ᵉ y'ᵉ)))

  is-section-unit-Id-higher-modalityᵉ :
    {Xᵉ : UUᵉ lᵉ} {x'ᵉ y'ᵉ : operator-higher-modalityᵉ mᵉ Xᵉ} →
    (map-inv-unit-Id-higher-modalityᵉ ∘ᵉ unit-higher-modalityᵉ mᵉ {x'ᵉ ＝ᵉ y'ᵉ}) ~ᵉ idᵉ
  is-section-unit-Id-higher-modalityᵉ {Xᵉ} {x'ᵉ} {y'ᵉ} pᵉ =
    ( apᵉ
      ( map-inv-equivᵉ
        ( equiv-unit-is-modal-type-is-smallᵉ
          ( unit-higher-modalityᵉ mᵉ)
          ( x'ᵉ ＝ᵉ y'ᵉ)
          ( is-small-x'=y'ᵉ)
          ( is-modal-small-x'=y'ᵉ)))
      ( compute-rec-higher-modalityᵉ mᵉ
        ( unit-higher-modalityᵉ mᵉ ∘ᵉ map-equiv-is-smallᵉ is-small-x'=y'ᵉ)
        ( pᵉ))) ∙ᵉ
    ( htpy-eqᵉ
      ( distributive-map-inv-comp-equivᵉ
        ( equiv-is-smallᵉ is-small-x'=y'ᵉ)
        ( unit-higher-modalityᵉ mᵉ ,ᵉ is-modal-small-x'=y'ᵉ))
      ( unit-higher-modalityᵉ mᵉ (map-equiv-is-smallᵉ is-small-x'=y'ᵉ pᵉ))) ∙ᵉ
    ( apᵉ
      ( map-inv-equiv-is-smallᵉ is-small-x'=y'ᵉ)
      ( is-retraction-map-inv-is-equivᵉ is-modal-small-x'=y'ᵉ
        ( map-equiv-is-smallᵉ is-small-x'=y'ᵉ pᵉ))) ∙ᵉ
    ( is-retraction-map-inv-equivᵉ (equiv-is-smallᵉ is-small-x'=y'ᵉ) pᵉ)
    where
      is-small-x'=y'ᵉ = is-locally-small-operator-higher-modalityᵉ mᵉ Xᵉ x'ᵉ y'ᵉ
      is-modal-small-x'=y'ᵉ =
        is-modal-small-identity-type-higher-modalityᵉ mᵉ Xᵉ x'ᵉ y'ᵉ

  retraction-unit-Id-higher-modalityᵉ :
    {Xᵉ : UUᵉ lᵉ} {x'ᵉ y'ᵉ : operator-higher-modalityᵉ mᵉ Xᵉ} →
    retractionᵉ (unit-higher-modalityᵉ mᵉ {x'ᵉ ＝ᵉ y'ᵉ})
  pr1ᵉ retraction-unit-Id-higher-modalityᵉ = map-inv-unit-Id-higher-modalityᵉ
  pr2ᵉ retraction-unit-Id-higher-modalityᵉ = is-section-unit-Id-higher-modalityᵉ
```

Weᵉ getᵉ thisᵉ retractionᵉ withoutᵉ applyingᵉ univalence,ᵉ so,ᵉ using strongᵉ subuniverseᵉ
inductionᵉ weᵉ canᵉ generallyᵉ avoidᵉ it.ᵉ However,ᵉ weᵉ appealᵉ to univalenceᵉ to getᵉ theᵉ
fullᵉ equivalence.ᵉ

```agda
  is-modal-Id-higher-modalityᵉ :
    {Xᵉ : UUᵉ lᵉ} {x'ᵉ y'ᵉ : operator-higher-modalityᵉ mᵉ Xᵉ} →
    is-modalᵉ (unit-higher-modalityᵉ mᵉ) (x'ᵉ ＝ᵉ y'ᵉ)
  is-modal-Id-higher-modalityᵉ {Xᵉ} {x'ᵉ} {y'ᵉ} =
    trᵉ
      ( is-modalᵉ (unit-higher-modalityᵉ mᵉ))
      ( eq-equivᵉ
        ( inv-equiv-is-smallᵉ
          ( is-locally-small-operator-higher-modalityᵉ mᵉ Xᵉ x'ᵉ y'ᵉ)))
      ( is-modal-small-identity-type-higher-modalityᵉ mᵉ Xᵉ x'ᵉ y'ᵉ)
```

### Subuniverse induction on identity types

```agda
module _
  {lᵉ : Level} (mᵉ : higher-modalityᵉ lᵉ lᵉ)
  where

  ind-subuniverse-Id-higher-modalityᵉ :
    {Xᵉ : UUᵉ lᵉ} {Yᵉ : operator-higher-modalityᵉ mᵉ Xᵉ → UUᵉ lᵉ}
    (fᵉ gᵉ :
      (x'ᵉ : operator-higher-modalityᵉ mᵉ Xᵉ) → operator-higher-modalityᵉ mᵉ (Yᵉ x'ᵉ)) →
    (fᵉ ∘ᵉ unit-higher-modalityᵉ mᵉ) ~ᵉ (gᵉ ∘ᵉ unit-higher-modalityᵉ mᵉ) →
    fᵉ ~ᵉ gᵉ
  ind-subuniverse-Id-higher-modalityᵉ {Xᵉ} fᵉ gᵉ =
    strong-ind-subuniverse-higher-modalityᵉ mᵉ
      ( λ x'ᵉ → fᵉ x'ᵉ ＝ᵉ gᵉ x'ᵉ)
      ( λ _ → retraction-unit-Id-higher-modalityᵉ mᵉ)

  compute-ind-subuniverse-Id-higher-modalityᵉ :
    {Xᵉ : UUᵉ lᵉ} {Yᵉ : operator-higher-modalityᵉ mᵉ Xᵉ → UUᵉ lᵉ}
    (fᵉ gᵉ :
      (x'ᵉ : operator-higher-modalityᵉ mᵉ Xᵉ) → operator-higher-modalityᵉ mᵉ (Yᵉ x'ᵉ)) →
    (Hᵉ : (fᵉ ∘ᵉ unit-higher-modalityᵉ mᵉ) ~ᵉ (gᵉ ∘ᵉ unit-higher-modalityᵉ mᵉ)) →
    (xᵉ : Xᵉ) →
    ( strong-ind-subuniverse-higher-modalityᵉ mᵉ
      ( λ x'ᵉ → fᵉ x'ᵉ ＝ᵉ gᵉ x'ᵉ)
      ( λ _ → retraction-unit-Id-higher-modalityᵉ mᵉ)
      ( Hᵉ)
      ( unit-higher-modalityᵉ mᵉ xᵉ)) ＝ᵉ
    ( Hᵉ xᵉ)
  compute-ind-subuniverse-Id-higher-modalityᵉ fᵉ gᵉ =
    compute-strong-ind-subuniverse-higher-modalityᵉ mᵉ
      ( λ xᵉ → fᵉ xᵉ ＝ᵉ gᵉ xᵉ)
      ( λ _ → retraction-unit-Id-higher-modalityᵉ mᵉ)
```

### Types in the image of the modal operator are modal

```agda
module _
  {lᵉ : Level} (mᵉ : higher-modalityᵉ lᵉ lᵉ) (Xᵉ : UUᵉ lᵉ)
  where

  map-inv-unit-higher-modalityᵉ :
    operator-higher-modalityᵉ mᵉ (operator-higher-modalityᵉ mᵉ Xᵉ) →
    operator-higher-modalityᵉ mᵉ Xᵉ
  map-inv-unit-higher-modalityᵉ = rec-higher-modalityᵉ mᵉ idᵉ

  is-retraction-map-inv-unit-higher-modalityᵉ :
    map-inv-unit-higher-modalityᵉ ∘ᵉ unit-higher-modalityᵉ mᵉ ~ᵉ idᵉ
  is-retraction-map-inv-unit-higher-modalityᵉ = compute-rec-higher-modalityᵉ mᵉ idᵉ

  is-section-map-inv-unit-higher-modalityᵉ :
    unit-higher-modalityᵉ mᵉ ∘ᵉ map-inv-unit-higher-modalityᵉ ~ᵉ idᵉ
  is-section-map-inv-unit-higher-modalityᵉ =
    ind-subuniverse-Id-higher-modalityᵉ mᵉ _ _
      ( apᵉ (unit-higher-modalityᵉ mᵉ) ∘ᵉ
        is-retraction-map-inv-unit-higher-modalityᵉ)

  is-modal-operator-type-higher-modalityᵉ :
    is-modalᵉ (unit-higher-modalityᵉ mᵉ) (operator-higher-modalityᵉ mᵉ Xᵉ)
  pr1ᵉ (pr1ᵉ is-modal-operator-type-higher-modalityᵉ) =
    map-inv-unit-higher-modalityᵉ
  pr2ᵉ (pr1ᵉ is-modal-operator-type-higher-modalityᵉ) =
    is-section-map-inv-unit-higher-modalityᵉ
  pr1ᵉ (pr2ᵉ is-modal-operator-type-higher-modalityᵉ) =
    map-inv-unit-higher-modalityᵉ
  pr2ᵉ (pr2ᵉ is-modal-operator-type-higher-modalityᵉ) =
    is-retraction-map-inv-unit-higher-modalityᵉ
```

### Higher modalities are uniquely eliminating modalities

```agda
is-section-ind-higher-modalityᵉ :
  {l1ᵉ l2ᵉ : Level} (mᵉ : higher-modalityᵉ l1ᵉ l2ᵉ)
  {Xᵉ : UUᵉ l1ᵉ} {Pᵉ : operator-higher-modalityᵉ mᵉ Xᵉ → UUᵉ l1ᵉ} →
  ( ( precomp-Πᵉ (unit-higher-modalityᵉ mᵉ) (operator-higher-modalityᵉ mᵉ ∘ᵉ Pᵉ)) ∘ᵉ
    ( ind-higher-modalityᵉ mᵉ Pᵉ)) ~ᵉ
  ( idᵉ)
is-section-ind-higher-modalityᵉ mᵉ =
  is-section-ind-modalityᵉ
    ( unit-higher-modalityᵉ mᵉ)
    ( ind-higher-modalityᵉ mᵉ)
    ( compute-ind-higher-modalityᵉ mᵉ)

module _
  {lᵉ : Level} (mᵉ : higher-modalityᵉ lᵉ lᵉ)
  where

  is-retraction-ind-higher-modalityᵉ :
    {Xᵉ : UUᵉ lᵉ} (Pᵉ : operator-higher-modalityᵉ mᵉ Xᵉ → UUᵉ lᵉ) →
    ( ind-higher-modalityᵉ mᵉ Pᵉ ∘ᵉ
      precomp-Πᵉ (unit-higher-modalityᵉ mᵉ) (operator-higher-modalityᵉ mᵉ ∘ᵉ Pᵉ)) ~ᵉ
    ( idᵉ)
  is-retraction-ind-higher-modalityᵉ Pᵉ sᵉ =
    eq-htpyᵉ
      ( ind-subuniverse-Id-higher-modalityᵉ mᵉ _ _
        ( compute-ind-higher-modalityᵉ mᵉ Pᵉ (sᵉ ∘ᵉ unit-higher-modalityᵉ mᵉ)))

  is-equiv-ind-higher-modalityᵉ :
    {Xᵉ : UUᵉ lᵉ} (Pᵉ : operator-higher-modalityᵉ mᵉ Xᵉ → UUᵉ lᵉ) →
    is-equivᵉ (ind-higher-modalityᵉ mᵉ Pᵉ)
  pr1ᵉ (pr1ᵉ (is-equiv-ind-higher-modalityᵉ Pᵉ)) =
    precomp-Πᵉ (unit-higher-modalityᵉ mᵉ) (operator-higher-modalityᵉ mᵉ ∘ᵉ Pᵉ)
  pr2ᵉ (pr1ᵉ (is-equiv-ind-higher-modalityᵉ Pᵉ)) =
    is-retraction-ind-higher-modalityᵉ Pᵉ
  pr1ᵉ (pr2ᵉ (is-equiv-ind-higher-modalityᵉ Pᵉ)) =
    precomp-Πᵉ (unit-higher-modalityᵉ mᵉ) (operator-higher-modalityᵉ mᵉ ∘ᵉ Pᵉ)
  pr2ᵉ (pr2ᵉ (is-equiv-ind-higher-modalityᵉ Pᵉ)) =
    is-section-ind-higher-modalityᵉ mᵉ

  equiv-ind-higher-modalityᵉ :
    {Xᵉ : UUᵉ lᵉ} (Pᵉ : operator-higher-modalityᵉ mᵉ Xᵉ → UUᵉ lᵉ) →
    ((xᵉ : Xᵉ) → operator-higher-modalityᵉ mᵉ (Pᵉ (unit-higher-modalityᵉ mᵉ xᵉ))) ≃ᵉ
    ((x'ᵉ : operator-higher-modalityᵉ mᵉ Xᵉ) → operator-higher-modalityᵉ mᵉ (Pᵉ x'ᵉ))
  pr1ᵉ (equiv-ind-higher-modalityᵉ Pᵉ) = ind-higher-modalityᵉ mᵉ Pᵉ
  pr2ᵉ (equiv-ind-higher-modalityᵉ Pᵉ) = is-equiv-ind-higher-modalityᵉ Pᵉ

  is-uniquely-eliminating-higher-modalityᵉ :
    is-uniquely-eliminating-modalityᵉ (unit-higher-modalityᵉ mᵉ)
  is-uniquely-eliminating-higher-modalityᵉ Pᵉ =
    is-equiv-map-inv-is-equivᵉ (is-equiv-ind-higher-modalityᵉ Pᵉ)
```

## See also

Theᵉ equivalentᵉ notionsᵉ ofᵉ

-ᵉ [Uniquelyᵉ eliminatingᵉ modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.mdᵉ)
-ᵉ [Σ-closedᵉ reflectiveᵉ modalities](orthogonal-factorization-systems.sigma-closed-reflective-modalities.mdᵉ)
-ᵉ [Σ-closedᵉ reflectiveᵉ subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.mdᵉ)
-ᵉ [Stableᵉ orthogonalᵉ factorizationᵉ systems](orthogonal-factorization-systems.stable-orthogonal-factorization-systems.mdᵉ)

## References

{{#bibliographyᵉ}} {{#referenceᵉ RSS20ᵉ}}