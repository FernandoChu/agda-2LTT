# Homomorphisms of cyclic rings

```agda
module ring-theory.homomorphisms-cyclic-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.cyclic-ringsᵉ
open import ring-theory.homomorphisms-ringsᵉ
open import ring-theory.integer-multiples-of-elements-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Aᵉ **homomorphism**ᵉ ofᵉ [cyclicᵉ rings](ring-theory.cyclic-rings.mdᵉ) isᵉ aᵉ
[ringᵉ homomorphism](ring-theory.homomorphisms-rings.mdᵉ) betweenᵉ theirᵉ underlyingᵉ
[rings](ring-theory.rings.md).ᵉ

Forᵉ anyᵉ cyclicᵉ ringᵉ `R`ᵉ andᵉ anyᵉ ringᵉ `S`,ᵉ thereᵉ existsᵉ atᵉ mostᵉ oneᵉ homomorphismᵉ
fromᵉ `R`ᵉ to `S`.ᵉ Weᵉ willᵉ useᵉ thisᵉ observationᵉ in
[`ring-theory.poset-of-cyclic-rings`](ring-theory.poset-of-cyclic-rings.mdᵉ) to
constructᵉ theᵉ [largeᵉ poset](order-theory.large-posets.mdᵉ) ofᵉ cyclicᵉ rings.ᵉ

## Definitions

### Homomorphisms of cyclic rings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Cyclic-Ringᵉ l1ᵉ) (Sᵉ : Cyclic-Ringᵉ l2ᵉ)
  where

  hom-set-Cyclic-Ringᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-set-Cyclic-Ringᵉ = hom-set-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ) (ring-Cyclic-Ringᵉ Sᵉ)

  hom-Cyclic-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Cyclic-Ringᵉ = hom-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ) (ring-Cyclic-Ringᵉ Sᵉ)

  is-set-hom-Cyclic-Ringᵉ : is-setᵉ hom-Cyclic-Ringᵉ
  is-set-hom-Cyclic-Ringᵉ =
    is-set-hom-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ) (ring-Cyclic-Ringᵉ Sᵉ)
```

### The identity homomorphism of cyclic rings

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Cyclic-Ringᵉ l1ᵉ)
  where

  id-hom-Cyclic-Ringᵉ : hom-Cyclic-Ringᵉ Rᵉ Rᵉ
  id-hom-Cyclic-Ringᵉ = id-hom-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ)
```

### Composition of homomorphisms of cyclci rings

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Rᵉ : Cyclic-Ringᵉ l1ᵉ) (Sᵉ : Cyclic-Ringᵉ l2ᵉ) (Tᵉ : Cyclic-Ringᵉ l3ᵉ)
  where

  comp-hom-Cyclic-Ringᵉ :
    (gᵉ : hom-Cyclic-Ringᵉ Sᵉ Tᵉ) (fᵉ : hom-Cyclic-Ringᵉ Rᵉ Sᵉ) →
    hom-Cyclic-Ringᵉ Rᵉ Tᵉ
  comp-hom-Cyclic-Ringᵉ =
    comp-hom-Ringᵉ
      ( ring-Cyclic-Ringᵉ Rᵉ)
      ( ring-Cyclic-Ringᵉ Sᵉ)
      ( ring-Cyclic-Ringᵉ Tᵉ)
```

## Properties

### Given a cyclic ring `R` and a ring `S`, there is at most one ring homomorphism from `R` to `S`

**Proof:**ᵉ Considerᵉ twoᵉ ringᵉ homomorphismsᵉ `fᵉ gᵉ : Rᵉ → S`.ᵉ Toᵉ showᵉ thatᵉ `fᵉ ＝ᵉ g`ᵉ
itᵉ sufficesᵉ to showᵉ thatᵉ `fᵉ xᵉ ＝ᵉ gᵉ x`ᵉ forᵉ allᵉ `xᵉ : R`.ᵉ However,ᵉ byᵉ theᵉ
assumptionᵉ thatᵉ `R`ᵉ isᵉ cyclicᵉ impliesᵉ thatᵉ `xᵉ ＝ᵉ n1`.ᵉ Furthermore,ᵉ everyᵉ ringᵉ
homomorphismᵉ preservesᵉ integerᵉ multiplication,ᵉ soᵉ itᵉ followsᵉ thatᵉ

```text
  fᵉ xᵉ ＝ᵉ fᵉ (n1ᵉ) ＝ᵉ nᵉ (fᵉ 1ᵉ) ＝ᵉ nᵉ 1 ＝ᵉ nᵉ (gᵉ 1ᵉ) ＝ᵉ gᵉ (n1ᵉ) ＝ᵉ gᵉ x.ᵉ
```

Thisᵉ completesᵉ theᵉ proof.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Cyclic-Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ)
  where

  abstract
    htpy-all-elements-equal-hom-Cyclic-Ring-Ringᵉ :
      (fᵉ gᵉ : hom-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ) Sᵉ) →
      htpy-hom-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ) Sᵉ fᵉ gᵉ
    htpy-all-elements-equal-hom-Cyclic-Ring-Ringᵉ fᵉ gᵉ xᵉ =
      apply-universal-property-trunc-Propᵉ
        ( is-surjective-initial-hom-Cyclic-Ringᵉ Rᵉ xᵉ)
        ( Id-Propᵉ
          ( set-Ringᵉ Sᵉ)
          ( map-hom-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ) Sᵉ fᵉ xᵉ)
          ( map-hom-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ) Sᵉ gᵉ xᵉ))
        ( λ where
          ( nᵉ ,ᵉ reflᵉ) →
            ( preserves-integer-multiples-hom-Ringᵉ
              ( ring-Cyclic-Ringᵉ Rᵉ)
              ( Sᵉ)
              ( fᵉ)
              ( nᵉ)
              ( one-Cyclic-Ringᵉ Rᵉ)) ∙ᵉ
            ( apᵉ
              ( integer-multiple-Ringᵉ Sᵉ nᵉ)
              ( preserves-one-hom-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ) Sᵉ fᵉ)) ∙ᵉ
            ( invᵉ
              ( apᵉ
                ( integer-multiple-Ringᵉ Sᵉ nᵉ)
                ( preserves-one-hom-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ) Sᵉ gᵉ))) ∙ᵉ
            ( invᵉ
              ( preserves-integer-multiples-hom-Ringᵉ
                ( ring-Cyclic-Ringᵉ Rᵉ)
                ( Sᵉ)
                ( gᵉ)
                ( nᵉ)
                ( one-Cyclic-Ringᵉ Rᵉ))))

  all-elements-equal-hom-Cyclic-Ring-Ringᵉ :
    all-elements-equalᵉ (hom-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ) Sᵉ)
  all-elements-equal-hom-Cyclic-Ring-Ringᵉ fᵉ gᵉ =
    eq-htpy-hom-Ringᵉ
      ( ring-Cyclic-Ringᵉ Rᵉ)
      ( Sᵉ)
      ( fᵉ)
      ( gᵉ)
      ( htpy-all-elements-equal-hom-Cyclic-Ring-Ringᵉ fᵉ gᵉ)

  is-prop-hom-Cyclic-Ring-Ringᵉ :
    is-propᵉ (hom-Ringᵉ (ring-Cyclic-Ringᵉ Rᵉ) Sᵉ)
  is-prop-hom-Cyclic-Ring-Ringᵉ =
    is-prop-all-elements-equalᵉ all-elements-equal-hom-Cyclic-Ring-Ringᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Cyclic-Ringᵉ l1ᵉ) (Sᵉ : Cyclic-Ringᵉ l2ᵉ)
  where

  is-prop-hom-Cyclic-Ringᵉ :
    is-propᵉ (hom-Cyclic-Ringᵉ Rᵉ Sᵉ)
  is-prop-hom-Cyclic-Ringᵉ =
    is-prop-hom-Cyclic-Ring-Ringᵉ Rᵉ (ring-Cyclic-Ringᵉ Sᵉ)
```

### Composition of morphisms of cyclic rings satisfies the laws of a category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Cyclic-Ringᵉ l1ᵉ) (Sᵉ : Cyclic-Ringᵉ l2ᵉ)
  (fᵉ : hom-Cyclic-Ringᵉ Rᵉ Sᵉ)
  where

  left-unit-law-comp-hom-Cyclic-Ringᵉ :
    comp-hom-Cyclic-Ringᵉ Rᵉ Sᵉ Sᵉ (id-hom-Cyclic-Ringᵉ Sᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Cyclic-Ringᵉ =
    left-unit-law-comp-hom-Ringᵉ
      ( ring-Cyclic-Ringᵉ Rᵉ)
      ( ring-Cyclic-Ringᵉ Sᵉ)
      ( fᵉ)

  right-unit-law-comp-hom-Cyclic-Ringᵉ :
    comp-hom-Cyclic-Ringᵉ Rᵉ Rᵉ Sᵉ fᵉ (id-hom-Cyclic-Ringᵉ Rᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Cyclic-Ringᵉ =
    right-unit-law-comp-hom-Ringᵉ
      ( ring-Cyclic-Ringᵉ Rᵉ)
      ( ring-Cyclic-Ringᵉ Sᵉ)
      ( fᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Rᵉ : Cyclic-Ringᵉ l1ᵉ) (Sᵉ : Cyclic-Ringᵉ l2ᵉ)
  (Tᵉ : Cyclic-Ringᵉ l3ᵉ) (Uᵉ : Cyclic-Ringᵉ l4ᵉ)
  where

  associative-comp-hom-Cyclic-Ringᵉ :
    (hᵉ : hom-Cyclic-Ringᵉ Tᵉ Uᵉ)
    (gᵉ : hom-Cyclic-Ringᵉ Sᵉ Tᵉ)
    (fᵉ : hom-Cyclic-Ringᵉ Rᵉ Sᵉ) →
    comp-hom-Cyclic-Ringᵉ Rᵉ Sᵉ Uᵉ (comp-hom-Cyclic-Ringᵉ Sᵉ Tᵉ Uᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Cyclic-Ringᵉ Rᵉ Tᵉ Uᵉ hᵉ (comp-hom-Cyclic-Ringᵉ Rᵉ Sᵉ Tᵉ gᵉ fᵉ)
  associative-comp-hom-Cyclic-Ringᵉ =
    associative-comp-hom-Ringᵉ
      ( ring-Cyclic-Ringᵉ Rᵉ)
      ( ring-Cyclic-Ringᵉ Sᵉ)
      ( ring-Cyclic-Ringᵉ Tᵉ)
      ( ring-Cyclic-Ringᵉ Uᵉ)
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}