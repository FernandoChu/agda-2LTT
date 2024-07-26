# Decidable equivalence relations

```agda
module foundation.decidable-equivalence-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-relationsᵉ
open import foundation.decidable-subtypesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.effective-maps-equivalence-relationsᵉ
open import foundation.equivalence-classesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.existential-quantificationᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.imagesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.setsᵉ
open import foundation.sliceᵉ
open import foundation.surjective-mapsᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universal-property-imageᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Aᵉ decidableᵉ equivalenceᵉ relationᵉ onᵉ aᵉ typeᵉ `X`ᵉ isᵉ anᵉ equivalenceᵉ relationᵉ `R`ᵉ onᵉ
`X`ᵉ suchᵉ thatᵉ `Rᵉ xᵉ y`ᵉ isᵉ aᵉ decidableᵉ propositionᵉ forᵉ eachᵉ `xᵉ yᵉ : X`.ᵉ

## Definitions

### Decidable equivalence relations

```agda
is-decidable-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} → {Aᵉ : UUᵉ l1ᵉ} → equivalence-relationᵉ l2ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-decidable-equivalence-relationᵉ {Aᵉ = Aᵉ} Rᵉ =
  (xᵉ yᵉ : Aᵉ) → is-decidableᵉ ( sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ)

Decidable-equivalence-relationᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Decidable-equivalence-relationᵉ l2ᵉ Xᵉ =
  Σᵉ ( Decidable-Relationᵉ l2ᵉ Xᵉ)
    ( λ Rᵉ → is-equivalence-relationᵉ (relation-Decidable-Relationᵉ Rᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Rᵉ : Decidable-equivalence-relationᵉ l2ᵉ Xᵉ)
  where

  decidable-relation-Decidable-equivalence-relationᵉ :
    Decidable-Relationᵉ l2ᵉ Xᵉ
  decidable-relation-Decidable-equivalence-relationᵉ = pr1ᵉ Rᵉ

  relation-Decidable-equivalence-relationᵉ : Xᵉ → Xᵉ → Propᵉ l2ᵉ
  relation-Decidable-equivalence-relationᵉ =
    relation-Decidable-Relationᵉ
      decidable-relation-Decidable-equivalence-relationᵉ

  sim-Decidable-equivalence-relationᵉ : Xᵉ → Xᵉ → UUᵉ l2ᵉ
  sim-Decidable-equivalence-relationᵉ =
    rel-Decidable-Relationᵉ decidable-relation-Decidable-equivalence-relationᵉ

  is-prop-sim-Decidable-equivalence-relationᵉ :
    (xᵉ yᵉ : Xᵉ) → is-propᵉ (sim-Decidable-equivalence-relationᵉ xᵉ yᵉ)
  is-prop-sim-Decidable-equivalence-relationᵉ =
    is-prop-rel-Decidable-Relationᵉ
      decidable-relation-Decidable-equivalence-relationᵉ

  is-decidable-sim-Decidable-equivalence-relationᵉ :
    (xᵉ yᵉ : Xᵉ) → is-decidableᵉ (sim-Decidable-equivalence-relationᵉ xᵉ yᵉ)
  is-decidable-sim-Decidable-equivalence-relationᵉ =
    is-decidable-Decidable-Relationᵉ
      decidable-relation-Decidable-equivalence-relationᵉ

  is-equivalence-relation-Decidable-equivalence-relationᵉ :
    is-equivalence-relationᵉ relation-Decidable-equivalence-relationᵉ
  is-equivalence-relation-Decidable-equivalence-relationᵉ = pr2ᵉ Rᵉ

  equivalence-relation-Decidable-equivalence-relationᵉ :
    equivalence-relationᵉ l2ᵉ Xᵉ
  pr1ᵉ equivalence-relation-Decidable-equivalence-relationᵉ =
    relation-Decidable-equivalence-relationᵉ
  pr2ᵉ equivalence-relation-Decidable-equivalence-relationᵉ =
    is-equivalence-relation-Decidable-equivalence-relationᵉ

  refl-Decidable-equivalence-relationᵉ :
    is-reflexiveᵉ sim-Decidable-equivalence-relationᵉ
  refl-Decidable-equivalence-relationᵉ =
    refl-equivalence-relationᵉ
      equivalence-relation-Decidable-equivalence-relationᵉ

  symmetric-Decidable-equivalence-relationᵉ :
    is-symmetricᵉ sim-Decidable-equivalence-relationᵉ
  symmetric-Decidable-equivalence-relationᵉ =
    symmetric-equivalence-relationᵉ
      equivalence-relation-Decidable-equivalence-relationᵉ

  equiv-symmetric-Decidable-equivalence-relationᵉ :
    {xᵉ yᵉ : Xᵉ} →
    sim-Decidable-equivalence-relationᵉ xᵉ yᵉ ≃ᵉ
    sim-Decidable-equivalence-relationᵉ yᵉ xᵉ
  equiv-symmetric-Decidable-equivalence-relationᵉ {xᵉ} {yᵉ} =
    equiv-iff-is-propᵉ
      ( is-prop-sim-Decidable-equivalence-relationᵉ xᵉ yᵉ)
      ( is-prop-sim-Decidable-equivalence-relationᵉ yᵉ xᵉ)
      ( symmetric-Decidable-equivalence-relationᵉ xᵉ yᵉ)
      ( symmetric-Decidable-equivalence-relationᵉ yᵉ xᵉ)

  transitive-Decidable-equivalence-relationᵉ :
    is-transitiveᵉ sim-Decidable-equivalence-relationᵉ
  transitive-Decidable-equivalence-relationᵉ =
    transitive-equivalence-relationᵉ
      equivalence-relation-Decidable-equivalence-relationᵉ

equiv-equivalence-relation-is-decidable-Dec-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} →
  Decidable-equivalence-relationᵉ l2ᵉ Xᵉ ≃ᵉ
  Σᵉ ( equivalence-relationᵉ l2ᵉ Xᵉ)
    ( λ Rᵉ → is-decidable-equivalence-relationᵉ Rᵉ)
pr1ᵉ equiv-equivalence-relation-is-decidable-Dec-equivalence-relationᵉ Rᵉ =
  ( equivalence-relation-Decidable-equivalence-relationᵉ Rᵉ ,ᵉ
    is-decidable-sim-Decidable-equivalence-relationᵉ Rᵉ)
pr2ᵉ equiv-equivalence-relation-is-decidable-Dec-equivalence-relationᵉ =
  is-equiv-is-invertibleᵉ
    ( λ (Rᵉ ,ᵉ dᵉ) →
      ( map-inv-equivᵉ
          ( equiv-relation-is-decidable-Decidable-Relationᵉ)
          ( prop-equivalence-relationᵉ Rᵉ ,ᵉ dᵉ) ,ᵉ
        is-equivalence-relation-prop-equivalence-relationᵉ Rᵉ))
    ( refl-htpyᵉ)
    ( refl-htpyᵉ)
```

### Equivalence classes of decidable equivalence relations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Rᵉ : Decidable-equivalence-relationᵉ l2ᵉ Xᵉ)
  where

  is-equivalence-class-Decidable-equivalence-relationᵉ :
    decidable-subtypeᵉ l2ᵉ Xᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-equivalence-class-Decidable-equivalence-relationᵉ Pᵉ =
    exists-structureᵉ
      ( Xᵉ)
      ( λ xᵉ → Pᵉ ＝ᵉ decidable-relation-Decidable-equivalence-relationᵉ Rᵉ xᵉ)

  equivalence-class-Decidable-equivalence-relationᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  equivalence-class-Decidable-equivalence-relationᵉ =
    imᵉ (decidable-relation-Decidable-equivalence-relationᵉ Rᵉ)

  class-Decidable-equivalence-relationᵉ :
    Xᵉ → equivalence-class-Decidable-equivalence-relationᵉ
  pr1ᵉ (class-Decidable-equivalence-relationᵉ xᵉ) =
    decidable-relation-Decidable-equivalence-relationᵉ Rᵉ xᵉ
  pr2ᵉ (class-Decidable-equivalence-relationᵉ xᵉ) =
    intro-existsᵉ xᵉ reflᵉ

  emb-equivalence-class-Decidable-equivalence-relationᵉ :
    equivalence-class-Decidable-equivalence-relationᵉ ↪ᵉ decidable-subtypeᵉ l2ᵉ Xᵉ
  emb-equivalence-class-Decidable-equivalence-relationᵉ =
    emb-imᵉ (decidable-relation-Decidable-equivalence-relationᵉ Rᵉ)

  decidable-subtype-equivalence-class-Decidable-equivalence-relationᵉ :
    equivalence-class-Decidable-equivalence-relationᵉ → decidable-subtypeᵉ l2ᵉ Xᵉ
  decidable-subtype-equivalence-class-Decidable-equivalence-relationᵉ =
    map-embᵉ emb-equivalence-class-Decidable-equivalence-relationᵉ

  subtype-equivalence-class-Decidable-equivalence-relationᵉ :
    equivalence-class-Decidable-equivalence-relationᵉ → subtypeᵉ l2ᵉ Xᵉ
  subtype-equivalence-class-Decidable-equivalence-relationᵉ =
    subtype-decidable-subtypeᵉ ∘ᵉ
    decidable-subtype-equivalence-class-Decidable-equivalence-relationᵉ

  is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ :
    equivalence-class-Decidable-equivalence-relationᵉ → Xᵉ → UUᵉ l2ᵉ
  is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ =
    is-in-subtypeᵉ ∘ᵉ subtype-equivalence-class-Decidable-equivalence-relationᵉ

  is-prop-is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ :
    (Pᵉ : equivalence-class-Decidable-equivalence-relationᵉ) (xᵉ : Xᵉ) →
    is-propᵉ (is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ Pᵉ xᵉ)
  is-prop-is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ Pᵉ =
    is-prop-is-in-subtypeᵉ
      ( subtype-equivalence-class-Decidable-equivalence-relationᵉ Pᵉ)

  is-set-equivalence-class-Decidable-equivalence-relationᵉ :
    is-setᵉ equivalence-class-Decidable-equivalence-relationᵉ
  is-set-equivalence-class-Decidable-equivalence-relationᵉ =
    is-set-imᵉ
      ( decidable-relation-Decidable-equivalence-relationᵉ Rᵉ)
      ( is-set-decidable-subtypeᵉ)

  equivalence-class-Decidable-equivalence-relation-Setᵉ : Setᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  pr1ᵉ equivalence-class-Decidable-equivalence-relation-Setᵉ =
    equivalence-class-Decidable-equivalence-relationᵉ
  pr2ᵉ equivalence-class-Decidable-equivalence-relation-Setᵉ =
    is-set-equivalence-class-Decidable-equivalence-relationᵉ

  unit-im-equivalence-class-Decidable-equivalence-relationᵉ :
    hom-sliceᵉ
      ( decidable-relation-Decidable-equivalence-relationᵉ Rᵉ)
      ( decidable-subtype-equivalence-class-Decidable-equivalence-relationᵉ)
  unit-im-equivalence-class-Decidable-equivalence-relationᵉ =
    unit-imᵉ (decidable-relation-Decidable-equivalence-relationᵉ Rᵉ)

  is-image-equivalence-class-Decidable-equivalence-relationᵉ :
    is-imageᵉ
      ( decidable-relation-Decidable-equivalence-relationᵉ Rᵉ)
      ( emb-equivalence-class-Decidable-equivalence-relationᵉ)
      ( unit-im-equivalence-class-Decidable-equivalence-relationᵉ)
  is-image-equivalence-class-Decidable-equivalence-relationᵉ =
    is-image-imᵉ (decidable-relation-Decidable-equivalence-relationᵉ Rᵉ)

  is-surjective-class-Decidable-equivalence-relationᵉ :
    is-surjectiveᵉ class-Decidable-equivalence-relationᵉ
  is-surjective-class-Decidable-equivalence-relationᵉ =
    is-surjective-map-unit-imᵉ
      ( decidable-relation-Decidable-equivalence-relationᵉ Rᵉ)
```

## Properties

### We characterize the identity type of the equivalence classes

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Decidable-equivalence-relationᵉ l2ᵉ Aᵉ) (aᵉ : Aᵉ)
  where

  abstract
    center-total-subtype-equivalence-class-Decidable-equivalence-relationᵉ :
      Σᵉ ( equivalence-class-Decidable-equivalence-relationᵉ Rᵉ)
        ( λ Pᵉ →
          is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ Rᵉ Pᵉ aᵉ)
    pr1ᵉ center-total-subtype-equivalence-class-Decidable-equivalence-relationᵉ =
      class-Decidable-equivalence-relationᵉ Rᵉ aᵉ
    pr2ᵉ center-total-subtype-equivalence-class-Decidable-equivalence-relationᵉ =
      refl-Decidable-equivalence-relationᵉ Rᵉ aᵉ

    contraction-total-subtype-equivalence-class-Decidable-equivalence-relationᵉ :
      ( tᵉ :
        Σᵉ ( equivalence-class-Decidable-equivalence-relationᵉ Rᵉ)
          ( λ Pᵉ →
            is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ
              Rᵉ Pᵉ aᵉ)) →
      center-total-subtype-equivalence-class-Decidable-equivalence-relationᵉ ＝ᵉ tᵉ
    contraction-total-subtype-equivalence-class-Decidable-equivalence-relationᵉ
      ( pairᵉ (pairᵉ Pᵉ pᵉ) Hᵉ) =
      eq-type-subtypeᵉ
        ( λ Qᵉ → subtype-equivalence-class-Decidable-equivalence-relationᵉ Rᵉ Qᵉ aᵉ)
        ( apply-universal-property-trunc-Propᵉ
          ( pᵉ)
          ( Id-Propᵉ
            ( equivalence-class-Decidable-equivalence-relation-Setᵉ Rᵉ)
            ( class-Decidable-equivalence-relationᵉ Rᵉ aᵉ)
            ( pairᵉ Pᵉ pᵉ))
          ( αᵉ))
      where
      αᵉ : fiberᵉ (pr1ᵉ Rᵉ) Pᵉ → class-Decidable-equivalence-relationᵉ Rᵉ aᵉ ＝ᵉ pairᵉ Pᵉ pᵉ
      αᵉ (pairᵉ xᵉ reflᵉ) =
        eq-type-subtypeᵉ
          ( λ zᵉ →
            trunc-Propᵉ
              ( fiberᵉ (decidable-relation-Decidable-equivalence-relationᵉ Rᵉ) zᵉ))
          ( eq-htpyᵉ
            ( λ yᵉ →
              eq-iff-Decidable-Propᵉ
                ( pr1ᵉ Rᵉ aᵉ yᵉ)
                ( pr1ᵉ Rᵉ xᵉ yᵉ)
                ( λ Kᵉ → transitive-Decidable-equivalence-relationᵉ Rᵉ xᵉ aᵉ yᵉ Kᵉ Hᵉ)
                ( λ Kᵉ → transitive-Decidable-equivalence-relationᵉ Rᵉ aᵉ xᵉ yᵉ Kᵉ
                  ( symmetric-Decidable-equivalence-relationᵉ Rᵉ xᵉ aᵉ Hᵉ))))

    is-torsorial-subtype-equivalence-class-Decidable-equivalence-relationᵉ :
      is-torsorialᵉ
        ( λ Pᵉ →
          is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ Rᵉ Pᵉ aᵉ)
    pr1ᵉ
      is-torsorial-subtype-equivalence-class-Decidable-equivalence-relationᵉ =
      center-total-subtype-equivalence-class-Decidable-equivalence-relationᵉ
    pr2ᵉ
      is-torsorial-subtype-equivalence-class-Decidable-equivalence-relationᵉ =
      contraction-total-subtype-equivalence-class-Decidable-equivalence-relationᵉ

  related-eq-quotient-Decidable-equivalence-relationᵉ :
    (qᵉ : equivalence-class-Decidable-equivalence-relationᵉ Rᵉ) →
      class-Decidable-equivalence-relationᵉ Rᵉ aᵉ ＝ᵉ qᵉ →
    is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ Rᵉ qᵉ aᵉ
  related-eq-quotient-Decidable-equivalence-relationᵉ
    .(class-Decidable-equivalence-relationᵉ Rᵉ aᵉ) reflᵉ =
    refl-Decidable-equivalence-relationᵉ Rᵉ aᵉ

  abstract
    is-equiv-related-eq-quotient-Decidable-equivalence-relationᵉ :
      (qᵉ : equivalence-class-Decidable-equivalence-relationᵉ Rᵉ) →
      is-equivᵉ (related-eq-quotient-Decidable-equivalence-relationᵉ qᵉ)
    is-equiv-related-eq-quotient-Decidable-equivalence-relationᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-subtype-equivalence-class-Decidable-equivalence-relationᵉ)
        ( related-eq-quotient-Decidable-equivalence-relationᵉ)

  abstract
    effective-quotient-Decidable-equivalence-relation'ᵉ :
      (qᵉ : equivalence-class-Decidable-equivalence-relationᵉ Rᵉ) →
      ( class-Decidable-equivalence-relationᵉ Rᵉ aᵉ ＝ᵉ qᵉ) ≃ᵉ
      ( is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ Rᵉ qᵉ aᵉ)
    pr1ᵉ (effective-quotient-Decidable-equivalence-relation'ᵉ qᵉ) =
      related-eq-quotient-Decidable-equivalence-relationᵉ qᵉ
    pr2ᵉ (effective-quotient-Decidable-equivalence-relation'ᵉ qᵉ) =
      is-equiv-related-eq-quotient-Decidable-equivalence-relationᵉ qᵉ

  abstract
    eq-effective-quotient-Decidable-equivalence-relation'ᵉ :
      (qᵉ : equivalence-class-Decidable-equivalence-relationᵉ Rᵉ) →
      is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ Rᵉ qᵉ aᵉ →
      class-Decidable-equivalence-relationᵉ Rᵉ aᵉ ＝ᵉ qᵉ
    eq-effective-quotient-Decidable-equivalence-relation'ᵉ qᵉ =
      map-inv-is-equivᵉ
        ( is-equiv-related-eq-quotient-Decidable-equivalence-relationᵉ qᵉ)
```

### The quotient map into the large set quotient is effective

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Decidable-equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  abstract
    is-effective-class-Decidable-equivalence-relationᵉ :
      is-effectiveᵉ
        ( equivalence-relation-Decidable-equivalence-relationᵉ Rᵉ)
        ( class-Decidable-equivalence-relationᵉ Rᵉ)
    is-effective-class-Decidable-equivalence-relationᵉ xᵉ yᵉ =
      ( equiv-symmetric-Decidable-equivalence-relationᵉ Rᵉ) ∘eᵉ
      ( effective-quotient-Decidable-equivalence-relation'ᵉ Rᵉ xᵉ
        ( class-Decidable-equivalence-relationᵉ Rᵉ yᵉ))

  abstract
    apply-effectiveness-class-Decidable-equivalence-relationᵉ :
      {xᵉ yᵉ : Aᵉ} →
      ( class-Decidable-equivalence-relationᵉ Rᵉ xᵉ ＝ᵉ
        class-Decidable-equivalence-relationᵉ Rᵉ yᵉ) →
      sim-Decidable-equivalence-relationᵉ Rᵉ xᵉ yᵉ
    apply-effectiveness-class-Decidable-equivalence-relationᵉ {xᵉ} {yᵉ} =
      map-equivᵉ (is-effective-class-Decidable-equivalence-relationᵉ xᵉ yᵉ)

  abstract
    apply-effectiveness-class-Decidable-equivalence-relation'ᵉ :
      {xᵉ yᵉ : Aᵉ} → sim-Decidable-equivalence-relationᵉ Rᵉ xᵉ yᵉ →
      class-Decidable-equivalence-relationᵉ Rᵉ xᵉ ＝ᵉ
      class-Decidable-equivalence-relationᵉ Rᵉ yᵉ
    apply-effectiveness-class-Decidable-equivalence-relation'ᵉ {xᵉ} {yᵉ} =
      map-inv-equivᵉ (is-effective-class-Decidable-equivalence-relationᵉ xᵉ yᵉ)
```

### The quotient map into the large set quotient is surjective and effective

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Decidable-equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  is-surjective-and-effective-class-Decidable-equivalence-relationᵉ :
    is-surjective-and-effectiveᵉ
      ( equivalence-relation-Decidable-equivalence-relationᵉ Rᵉ)
      ( class-Decidable-equivalence-relationᵉ Rᵉ)
  pr1ᵉ is-surjective-and-effective-class-Decidable-equivalence-relationᵉ =
    is-surjective-class-Decidable-equivalence-relationᵉ Rᵉ
  pr2ᵉ is-surjective-and-effective-class-Decidable-equivalence-relationᵉ =
    is-effective-class-Decidable-equivalence-relationᵉ Rᵉ
```

### The quotient map into the large set quotient is a reflecting map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Decidable-equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  quotient-reflecting-map-equivalence-class-Decidable-equivalence-relationᵉ :
    reflecting-map-equivalence-relationᵉ
      ( equivalence-relation-Decidable-equivalence-relationᵉ Rᵉ)
      ( equivalence-class-Decidable-equivalence-relationᵉ Rᵉ)
  pr1ᵉ quotient-reflecting-map-equivalence-class-Decidable-equivalence-relationᵉ =
    class-Decidable-equivalence-relationᵉ Rᵉ
  pr2ᵉ quotient-reflecting-map-equivalence-class-Decidable-equivalence-relationᵉ =
    apply-effectiveness-class-Decidable-equivalence-relation'ᵉ Rᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Decidable-equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  transitive-is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ :
    (Pᵉ : equivalence-class-Decidable-equivalence-relationᵉ Rᵉ) (aᵉ bᵉ : Aᵉ) →
    is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ Rᵉ Pᵉ aᵉ →
    sim-Decidable-equivalence-relationᵉ Rᵉ aᵉ bᵉ →
    is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ Rᵉ Pᵉ bᵉ
  transitive-is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ
    Pᵉ aᵉ bᵉ pᵉ qᵉ =
    apply-universal-property-trunc-Propᵉ
      ( pr2ᵉ Pᵉ)
      ( subtype-equivalence-class-Decidable-equivalence-relationᵉ Rᵉ Pᵉ bᵉ)
      ( λ (pairᵉ xᵉ Tᵉ) →
        trᵉ
          ( λ Zᵉ →
            is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ
              Rᵉ Zᵉ bᵉ)
          { xᵉ = class-Decidable-equivalence-relationᵉ Rᵉ xᵉ} {yᵉ = Pᵉ}
          ( eq-pair-Σᵉ
            ( Tᵉ)
            ( all-elements-equal-type-trunc-Propᵉ _ _))
          ( transitive-Decidable-equivalence-relationᵉ Rᵉ _ aᵉ bᵉ qᵉ
            ( trᵉ
              ( λ Zᵉ →
                is-in-subtype-equivalence-class-Decidable-equivalence-relationᵉ
                  Rᵉ Zᵉ aᵉ)
              { xᵉ = Pᵉ}
              { yᵉ = class-Decidable-equivalence-relationᵉ Rᵉ xᵉ}
              ( eq-pair-Σᵉ (invᵉ Tᵉ) (all-elements-equal-type-trunc-Propᵉ _ _))
              ( pᵉ))))
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  is-decidable-is-in-equivalence-class-is-decidableᵉ :
    ((aᵉ bᵉ : Aᵉ) → is-decidableᵉ (sim-equivalence-relationᵉ Rᵉ aᵉ bᵉ)) →
    (Tᵉ : equivalence-classᵉ Rᵉ) →
    (aᵉ : Aᵉ) →
    is-decidableᵉ (is-in-equivalence-classᵉ Rᵉ Tᵉ aᵉ)
  is-decidable-is-in-equivalence-class-is-decidableᵉ Fᵉ Tᵉ aᵉ =
    apply-universal-property-trunc-Propᵉ
      ( pr2ᵉ Tᵉ)
      ( is-decidable-Propᵉ
        ( subtype-equivalence-classᵉ Rᵉ Tᵉ aᵉ))
      ( λ (pairᵉ tᵉ Pᵉ) →
        is-decidable-iffᵉ
          ( backward-implicationᵉ (Pᵉ aᵉ))
          ( forward-implicationᵉ (Pᵉ aᵉ))
          ( Fᵉ tᵉ aᵉ))
```

#### The type of decidable equivalence relations on `A` is equivalent to the type of surjections from `A` into a type with decidable equality

```agda
has-decidable-equality-type-Surjection-Into-Setᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (surjᵉ : Surjection-Into-Setᵉ l1ᵉ Aᵉ) →
  ( is-decidable-equivalence-relationᵉ
    ( equivalence-relation-Surjection-Into-Setᵉ surjᵉ)) →
  has-decidable-equalityᵉ (type-Surjection-Into-Setᵉ surjᵉ)
has-decidable-equality-type-Surjection-Into-Setᵉ surjᵉ is-dec-relᵉ xᵉ yᵉ =
  apply-twice-dependent-universal-property-surjection-is-surjectiveᵉ
    ( map-Surjection-Into-Setᵉ surjᵉ)
    ( is-surjective-Surjection-Into-Setᵉ surjᵉ)
    ( λ (sᵉ tᵉ : (type-Surjection-Into-Setᵉ surjᵉ)) →
      ( is-decidableᵉ (sᵉ ＝ᵉ tᵉ) ,ᵉ
        is-prop-is-decidableᵉ ( is-set-type-Surjection-Into-Setᵉ surjᵉ sᵉ tᵉ)))
    ( λ a1ᵉ a2ᵉ → is-dec-relᵉ a1ᵉ a2ᵉ)
    ( xᵉ)
    ( yᵉ)

is-decidable-equivalence-relation-Surjection-Into-Setᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (surjᵉ : Surjection-Into-Setᵉ l1ᵉ Aᵉ) →
  has-decidable-equalityᵉ (type-Surjection-Into-Setᵉ surjᵉ) →
  is-decidable-equivalence-relationᵉ
    ( equivalence-relation-Surjection-Into-Setᵉ surjᵉ)
is-decidable-equivalence-relation-Surjection-Into-Setᵉ surjᵉ dec-eqᵉ xᵉ yᵉ =
  dec-eqᵉ (map-Surjection-Into-Setᵉ surjᵉ xᵉ) (map-Surjection-Into-Setᵉ surjᵉ yᵉ)

equiv-Surjection-Into-Set-Decidable-equivalence-relationᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) →
  Decidable-equivalence-relationᵉ l1ᵉ Aᵉ ≃ᵉ
  Σᵉ (UUᵉ l1ᵉ) (λ Xᵉ → (Aᵉ ↠ᵉ Xᵉ) ×ᵉ has-decidable-equalityᵉ Xᵉ)
equiv-Surjection-Into-Set-Decidable-equivalence-relationᵉ {l1ᵉ} Aᵉ =
  ( ( equiv-Σᵉ
      ( λ zᵉ → (Aᵉ ↠ᵉ zᵉ) ×ᵉ has-decidable-equalityᵉ zᵉ)
      ( id-equivᵉ)
      ( λ Xᵉ →
        ( equiv-productᵉ
          ( id-equivᵉ)
          ( inv-equivᵉ
              ( equiv-add-redundant-propᵉ
                ( is-prop-is-setᵉ ( Xᵉ))
                ( is-set-has-decidable-equalityᵉ)) ∘eᵉ
            commutative-productᵉ) ∘eᵉ
        ( equiv-left-swap-Σᵉ)))) ∘eᵉ
    ( ( associative-Σᵉ
        ( UUᵉ l1ᵉ)
        ( λ Xᵉ → is-setᵉ Xᵉ)
        ( λ Xᵉ → (Aᵉ ↠ᵉ pr1ᵉ Xᵉ) ×ᵉ has-decidable-equalityᵉ (pr1ᵉ Xᵉ))) ∘eᵉ
      ( ( associative-Σᵉ
          ( Setᵉ l1ᵉ)
          ( λ Xᵉ → (Aᵉ ↠ᵉ type-Setᵉ Xᵉ))
          ( λ Xᵉ → has-decidable-equalityᵉ (pr1ᵉ (pr1ᵉ Xᵉ)))) ∘eᵉ
        ( ( equiv-type-subtypeᵉ
            ( λ surjᵉ →
              is-prop-Πᵉ
                ( λ xᵉ →
                  is-prop-Πᵉ
                    ( λ yᵉ →
                      is-prop-is-decidableᵉ
                        ( is-prop-sim-equivalence-relationᵉ
                          ( equivalence-relation-Surjection-Into-Setᵉ surjᵉ)
                          ( xᵉ)
                          ( yᵉ)))))
            ( λ _ → is-prop-has-decidable-equalityᵉ)
            ( λ sᵉ → has-decidable-equality-type-Surjection-Into-Setᵉ sᵉ)
            ( λ sᵉ → is-decidable-equivalence-relation-Surjection-Into-Setᵉ sᵉ)) ∘eᵉ
          ( ( inv-equivᵉ
              ( equiv-Σ-equiv-baseᵉ
                ( λ Rᵉ → is-decidable-equivalence-relationᵉ Rᵉ)
                ( inv-equivᵉ
                  ( equiv-surjection-into-set-equivalence-relationᵉ Aᵉ)))) ∘eᵉ
            ( equiv-equivalence-relation-is-decidable-Dec-equivalence-relationᵉ))))))
```