# Equivalence classes

```agda
module foundation.equivalence-classesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunctionᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.effective-maps-equivalence-relationsᵉ
open import foundation.existential-quantificationᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.inhabited-subtypesᵉ
open import foundation.locally-small-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.sliceᵉ
open import foundation.small-typesᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universal-property-imageᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equivalence-relationsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Anᵉ equivalenceᵉ classᵉ ofᵉ anᵉ equivalenceᵉ relationᵉ `R`ᵉ onᵉ `A`ᵉ isᵉ aᵉ subtypeᵉ ofᵉ `A`ᵉ
thatᵉ isᵉ merelyᵉ equivalentᵉ to aᵉ subtypeᵉ ofᵉ theᵉ formᵉ `Rᵉ x`.ᵉ Theᵉ typeᵉ ofᵉ
equivalenceᵉ classesᵉ ofᵉ anᵉ equivalenceᵉ relationᵉ satisfiesᵉ theᵉ universalᵉ propertyᵉ
ofᵉ theᵉ setᵉ quotient.ᵉ

## Definition

### The condition on subtypes of `A` of being an equivalence class

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  is-equivalence-class-Propᵉ : subtypeᵉ l2ᵉ Aᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-equivalence-class-Propᵉ Pᵉ =
    ∃ᵉ Aᵉ (λ xᵉ → has-same-elements-subtype-Propᵉ Pᵉ (prop-equivalence-relationᵉ Rᵉ xᵉ))

  is-equivalence-classᵉ : subtypeᵉ l2ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-equivalence-classᵉ Pᵉ = type-Propᵉ (is-equivalence-class-Propᵉ Pᵉ)

  is-prop-is-equivalence-classᵉ :
    (Pᵉ : subtypeᵉ l2ᵉ Aᵉ) → is-propᵉ (is-equivalence-classᵉ Pᵉ)
  is-prop-is-equivalence-classᵉ Pᵉ =
    is-prop-type-Propᵉ (is-equivalence-class-Propᵉ Pᵉ)
```

### The condition on inhabited subtypes of `A` of being an equivalence class

```agda
  is-equivalence-class-inhabited-subtype-equivalence-relationᵉ :
    subtypeᵉ (l1ᵉ ⊔ l2ᵉ) (inhabited-subtypeᵉ l2ᵉ Aᵉ)
  is-equivalence-class-inhabited-subtype-equivalence-relationᵉ Qᵉ =
    is-equivalence-class-Propᵉ (subtype-inhabited-subtypeᵉ Qᵉ)
```

### The type of equivalence classes

```agda
  equivalence-classᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  equivalence-classᵉ = type-subtypeᵉ is-equivalence-class-Propᵉ

  classᵉ : Aᵉ → equivalence-classᵉ
  pr1ᵉ (classᵉ xᵉ) = prop-equivalence-relationᵉ Rᵉ xᵉ
  pr2ᵉ (classᵉ xᵉ) =
    unit-trunc-Propᵉ
      ( xᵉ ,ᵉ refl-has-same-elements-subtypeᵉ (prop-equivalence-relationᵉ Rᵉ xᵉ))

  emb-equivalence-classᵉ : equivalence-classᵉ ↪ᵉ subtypeᵉ l2ᵉ Aᵉ
  emb-equivalence-classᵉ = emb-subtypeᵉ is-equivalence-class-Propᵉ

  subtype-equivalence-classᵉ : equivalence-classᵉ → subtypeᵉ l2ᵉ Aᵉ
  subtype-equivalence-classᵉ = inclusion-subtypeᵉ is-equivalence-class-Propᵉ

  is-equivalence-class-equivalence-classᵉ :
    (Cᵉ : equivalence-classᵉ) → is-equivalence-classᵉ (subtype-equivalence-classᵉ Cᵉ)
  is-equivalence-class-equivalence-classᵉ =
    is-in-subtype-inclusion-subtypeᵉ is-equivalence-class-Propᵉ

  is-inhabited-subtype-equivalence-classᵉ :
    (Cᵉ : equivalence-classᵉ) → is-inhabited-subtypeᵉ (subtype-equivalence-classᵉ Cᵉ)
  is-inhabited-subtype-equivalence-classᵉ (Qᵉ ,ᵉ Hᵉ) =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( is-inhabited-subtype-Propᵉ (subtype-equivalence-classᵉ (Qᵉ ,ᵉ Hᵉ)))
      ( λ uᵉ →
        unit-trunc-Propᵉ
          ( pr1ᵉ uᵉ ,ᵉ
            backward-implicationᵉ
              ( pr2ᵉ uᵉ (pr1ᵉ uᵉ))
              ( refl-equivalence-relationᵉ Rᵉ (pr1ᵉ uᵉ))))

  inhabited-subtype-equivalence-classᵉ :
    (Cᵉ : equivalence-classᵉ) → inhabited-subtypeᵉ l2ᵉ Aᵉ
  pr1ᵉ (inhabited-subtype-equivalence-classᵉ Cᵉ) = subtype-equivalence-classᵉ Cᵉ
  pr2ᵉ (inhabited-subtype-equivalence-classᵉ Cᵉ) =
    is-inhabited-subtype-equivalence-classᵉ Cᵉ

  is-in-equivalence-classᵉ : equivalence-classᵉ → (Aᵉ → UUᵉ l2ᵉ)
  is-in-equivalence-classᵉ Pᵉ xᵉ = type-Propᵉ (subtype-equivalence-classᵉ Pᵉ xᵉ)

  abstract
    is-prop-is-in-equivalence-classᵉ :
      (xᵉ : equivalence-classᵉ) (aᵉ : Aᵉ) →
      is-propᵉ (is-in-equivalence-classᵉ xᵉ aᵉ)
    is-prop-is-in-equivalence-classᵉ Pᵉ xᵉ =
      is-prop-type-Propᵉ (subtype-equivalence-classᵉ Pᵉ xᵉ)

  is-in-equivalence-class-Propᵉ : equivalence-classᵉ → (Aᵉ → Propᵉ l2ᵉ)
  pr1ᵉ (is-in-equivalence-class-Propᵉ Pᵉ xᵉ) = is-in-equivalence-classᵉ Pᵉ xᵉ
  pr2ᵉ (is-in-equivalence-class-Propᵉ Pᵉ xᵉ) = is-prop-is-in-equivalence-classᵉ Pᵉ xᵉ

  abstract
    is-set-equivalence-classᵉ : is-setᵉ equivalence-classᵉ
    is-set-equivalence-classᵉ =
      is-set-type-subtypeᵉ is-equivalence-class-Propᵉ is-set-subtypeᵉ

  equivalence-class-Setᵉ : Setᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  pr1ᵉ equivalence-class-Setᵉ = equivalence-classᵉ
  pr2ᵉ equivalence-class-Setᵉ = is-set-equivalence-classᵉ

  unit-im-equivalence-classᵉ :
    hom-sliceᵉ (prop-equivalence-relationᵉ Rᵉ) subtype-equivalence-classᵉ
  pr1ᵉ unit-im-equivalence-classᵉ = classᵉ
  pr2ᵉ unit-im-equivalence-classᵉ xᵉ = reflᵉ

  is-surjective-classᵉ : is-surjectiveᵉ classᵉ
  is-surjective-classᵉ Cᵉ =
    map-trunc-Propᵉ
      ( totᵉ
        ( λ xᵉ pᵉ →
          invᵉ
            ( eq-type-subtypeᵉ
              ( is-equivalence-class-Propᵉ)
              ( eq-has-same-elements-subtypeᵉ
                ( pr1ᵉ Cᵉ)
                ( prop-equivalence-relationᵉ Rᵉ xᵉ)
                ( pᵉ)))))
      ( pr2ᵉ Cᵉ)

  is-image-equivalence-classᵉ :
    is-imageᵉ
      ( prop-equivalence-relationᵉ Rᵉ)
      ( emb-equivalence-classᵉ)
      ( unit-im-equivalence-classᵉ)
  is-image-equivalence-classᵉ =
    is-image-is-surjectiveᵉ
      ( prop-equivalence-relationᵉ Rᵉ)
      ( emb-equivalence-classᵉ)
      ( unit-im-equivalence-classᵉ)
      ( is-surjective-classᵉ)
```

## Properties

### Characterization of equality of equivalence classes

#### Equivalence classes are equal if they contain the same elements

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  has-same-elements-equivalence-classᵉ :
    (Cᵉ Dᵉ : equivalence-classᵉ Rᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-same-elements-equivalence-classᵉ Cᵉ Dᵉ =
    has-same-elements-subtypeᵉ
      ( subtype-equivalence-classᵉ Rᵉ Cᵉ)
      ( subtype-equivalence-classᵉ Rᵉ Dᵉ)

  refl-has-same-elements-equivalence-classᵉ :
    (Cᵉ : equivalence-classᵉ Rᵉ) → has-same-elements-equivalence-classᵉ Cᵉ Cᵉ
  refl-has-same-elements-equivalence-classᵉ Cᵉ =
    refl-has-same-elements-subtypeᵉ (subtype-equivalence-classᵉ Rᵉ Cᵉ)

  is-torsorial-has-same-elements-equivalence-classᵉ :
    (Cᵉ : equivalence-classᵉ Rᵉ) →
    is-torsorialᵉ (has-same-elements-equivalence-classᵉ Cᵉ)
  is-torsorial-has-same-elements-equivalence-classᵉ Cᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-has-same-elements-subtypeᵉ
        ( subtype-equivalence-classᵉ Rᵉ Cᵉ))
      ( is-prop-is-equivalence-classᵉ Rᵉ)
      ( subtype-equivalence-classᵉ Rᵉ Cᵉ)
      ( refl-has-same-elements-equivalence-classᵉ Cᵉ)
      ( is-equivalence-class-equivalence-classᵉ Rᵉ Cᵉ)

  has-same-elements-eq-equivalence-classᵉ :
    (Cᵉ Dᵉ : equivalence-classᵉ Rᵉ) → (Cᵉ ＝ᵉ Dᵉ) →
    has-same-elements-equivalence-classᵉ Cᵉ Dᵉ
  has-same-elements-eq-equivalence-classᵉ Cᵉ .Cᵉ reflᵉ =
    refl-has-same-elements-subtypeᵉ (subtype-equivalence-classᵉ Rᵉ Cᵉ)

  is-equiv-has-same-elements-eq-equivalence-classᵉ :
    (Cᵉ Dᵉ : equivalence-classᵉ Rᵉ) →
    is-equivᵉ (has-same-elements-eq-equivalence-classᵉ Cᵉ Dᵉ)
  is-equiv-has-same-elements-eq-equivalence-classᵉ Cᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-has-same-elements-equivalence-classᵉ Cᵉ)
      ( has-same-elements-eq-equivalence-classᵉ Cᵉ)

  extensionality-equivalence-classᵉ :
    (Cᵉ Dᵉ : equivalence-classᵉ Rᵉ) →
    (Cᵉ ＝ᵉ Dᵉ) ≃ᵉ has-same-elements-equivalence-classᵉ Cᵉ Dᵉ
  pr1ᵉ (extensionality-equivalence-classᵉ Cᵉ Dᵉ) =
    has-same-elements-eq-equivalence-classᵉ Cᵉ Dᵉ
  pr2ᵉ (extensionality-equivalence-classᵉ Cᵉ Dᵉ) =
    is-equiv-has-same-elements-eq-equivalence-classᵉ Cᵉ Dᵉ

  eq-has-same-elements-equivalence-classᵉ :
    (Cᵉ Dᵉ : equivalence-classᵉ Rᵉ) →
    has-same-elements-equivalence-classᵉ Cᵉ Dᵉ → Cᵉ ＝ᵉ Dᵉ
  eq-has-same-elements-equivalence-classᵉ Cᵉ Dᵉ =
    map-inv-equivᵉ (extensionality-equivalence-classᵉ Cᵉ Dᵉ)
```

#### Equivalence classes are equal if there exists an element contained in both

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  share-common-element-equivalence-class-Propᵉ :
    (Cᵉ Dᵉ : equivalence-classᵉ Rᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  share-common-element-equivalence-class-Propᵉ Cᵉ Dᵉ =
    ∃ᵉ ( Aᵉ)
      ( λ xᵉ →
        is-in-equivalence-class-Propᵉ Rᵉ Cᵉ xᵉ ∧ᵉ is-in-equivalence-class-Propᵉ Rᵉ Dᵉ xᵉ)

  share-common-element-equivalence-classᵉ :
    (Cᵉ Dᵉ : equivalence-classᵉ Rᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  share-common-element-equivalence-classᵉ Cᵉ Dᵉ =
    type-Propᵉ (share-common-element-equivalence-class-Propᵉ Cᵉ Dᵉ)

  abstract
    eq-share-common-element-equivalence-classᵉ :
      (Cᵉ Dᵉ : equivalence-classᵉ Rᵉ) →
      share-common-element-equivalence-classᵉ Cᵉ Dᵉ → Cᵉ ＝ᵉ Dᵉ
    eq-share-common-element-equivalence-classᵉ Cᵉ Dᵉ Hᵉ =
      apply-three-times-universal-property-trunc-Propᵉ
        ( Hᵉ)
        ( is-equivalence-class-equivalence-classᵉ Rᵉ Cᵉ)
        ( is-equivalence-class-equivalence-classᵉ Rᵉ Dᵉ)
        ( Id-Propᵉ (equivalence-class-Setᵉ Rᵉ) Cᵉ Dᵉ)
        ( λ (aᵉ ,ᵉ cᵉ ,ᵉ dᵉ) (vᵉ ,ᵉ φᵉ) (wᵉ ,ᵉ ψᵉ) →
          eq-has-same-elements-equivalence-classᵉ Rᵉ Cᵉ Dᵉ
            ( λ xᵉ →
              logical-equivalence-reasoningᵉ
                is-in-equivalence-classᵉ Rᵉ Cᵉ xᵉ
                  ↔ᵉ sim-equivalence-relationᵉ Rᵉ vᵉ xᵉ
                    byᵉ φᵉ xᵉ
                  ↔ᵉ sim-equivalence-relationᵉ Rᵉ aᵉ xᵉ
                    byᵉ iff-transitive-equivalence-relationᵉ Rᵉ
                        ( symmetric-equivalence-relationᵉ
                            Rᵉ _ _ (forward-implicationᵉ (φᵉ aᵉ) cᵉ))
                  ↔ᵉ sim-equivalence-relationᵉ Rᵉ wᵉ xᵉ
                    byᵉ iff-transitive-equivalence-relationᵉ Rᵉ
                        ( forward-implicationᵉ (ψᵉ aᵉ) dᵉ)
                  ↔ᵉ is-in-equivalence-classᵉ Rᵉ Dᵉ xᵉ
                    byᵉ inv-iffᵉ (ψᵉ xᵉ)))

  eq-class-equivalence-classᵉ :
    (Cᵉ : equivalence-classᵉ Rᵉ) {aᵉ : Aᵉ} →
    is-in-equivalence-classᵉ Rᵉ Cᵉ aᵉ → classᵉ Rᵉ aᵉ ＝ᵉ Cᵉ
  eq-class-equivalence-classᵉ Cᵉ {aᵉ} Hᵉ =
    eq-share-common-element-equivalence-classᵉ
      ( classᵉ Rᵉ aᵉ)
      ( Cᵉ)
      ( unit-trunc-Propᵉ (aᵉ ,ᵉ refl-equivalence-relationᵉ Rᵉ aᵉ ,ᵉ Hᵉ))
```

### The type of equivalence classes containing a fixed element `a : A` is contractible

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) (aᵉ : Aᵉ)
  where

  center-total-is-in-equivalence-classᵉ :
    Σᵉ (equivalence-classᵉ Rᵉ) (λ Pᵉ → is-in-equivalence-classᵉ Rᵉ Pᵉ aᵉ)
  pr1ᵉ center-total-is-in-equivalence-classᵉ = classᵉ Rᵉ aᵉ
  pr2ᵉ center-total-is-in-equivalence-classᵉ = refl-equivalence-relationᵉ Rᵉ aᵉ

  contraction-total-is-in-equivalence-classᵉ :
    ( tᵉ :
      Σᵉ ( equivalence-classᵉ Rᵉ)
        ( λ Cᵉ → is-in-equivalence-classᵉ Rᵉ Cᵉ aᵉ)) →
    center-total-is-in-equivalence-classᵉ ＝ᵉ tᵉ
  contraction-total-is-in-equivalence-classᵉ (Cᵉ ,ᵉ Hᵉ) =
    eq-type-subtypeᵉ
      ( λ Dᵉ → is-in-equivalence-class-Propᵉ Rᵉ Dᵉ aᵉ)
      ( eq-class-equivalence-classᵉ Rᵉ Cᵉ Hᵉ)

  is-torsorial-is-in-equivalence-classᵉ :
    is-torsorialᵉ (λ Pᵉ → is-in-equivalence-classᵉ Rᵉ Pᵉ aᵉ)
  pr1ᵉ is-torsorial-is-in-equivalence-classᵉ =
    center-total-is-in-equivalence-classᵉ
  pr2ᵉ is-torsorial-is-in-equivalence-classᵉ =
    contraction-total-is-in-equivalence-classᵉ

  is-in-equivalence-class-eq-equivalence-classᵉ :
    (qᵉ : equivalence-classᵉ Rᵉ) → classᵉ Rᵉ aᵉ ＝ᵉ qᵉ →
    is-in-equivalence-classᵉ Rᵉ qᵉ aᵉ
  is-in-equivalence-class-eq-equivalence-classᵉ .(classᵉ Rᵉ aᵉ) reflᵉ =
    refl-equivalence-relationᵉ Rᵉ aᵉ

  abstract
    is-equiv-is-in-equivalence-class-eq-equivalence-classᵉ :
      (qᵉ : equivalence-classᵉ Rᵉ) →
      is-equivᵉ (is-in-equivalence-class-eq-equivalence-classᵉ qᵉ)
    is-equiv-is-in-equivalence-class-eq-equivalence-classᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-is-in-equivalence-classᵉ)
        ( is-in-equivalence-class-eq-equivalence-classᵉ)
```

### The map `class : A → equivalence-class R` is an effective quotient map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  abstract
    effective-quotient'ᵉ :
      (aᵉ : Aᵉ) (qᵉ : equivalence-classᵉ Rᵉ) →
      ( classᵉ Rᵉ aᵉ ＝ᵉ qᵉ) ≃ᵉ
      ( is-in-equivalence-classᵉ Rᵉ qᵉ aᵉ)
    pr1ᵉ (effective-quotient'ᵉ aᵉ qᵉ) =
      is-in-equivalence-class-eq-equivalence-classᵉ Rᵉ aᵉ qᵉ
    pr2ᵉ (effective-quotient'ᵉ aᵉ qᵉ) =
      is-equiv-is-in-equivalence-class-eq-equivalence-classᵉ Rᵉ aᵉ qᵉ

  abstract
    eq-effective-quotient'ᵉ :
      (aᵉ : Aᵉ) (qᵉ : equivalence-classᵉ Rᵉ) → is-in-equivalence-classᵉ Rᵉ qᵉ aᵉ →
      classᵉ Rᵉ aᵉ ＝ᵉ qᵉ
    eq-effective-quotient'ᵉ aᵉ qᵉ =
      map-inv-is-equivᵉ
        ( is-equiv-is-in-equivalence-class-eq-equivalence-classᵉ Rᵉ aᵉ qᵉ)

  abstract
    is-effective-classᵉ :
      is-effectiveᵉ Rᵉ (classᵉ Rᵉ)
    is-effective-classᵉ xᵉ yᵉ =
      ( equiv-symmetric-equivalence-relationᵉ Rᵉ) ∘eᵉ
      ( effective-quotient'ᵉ xᵉ (classᵉ Rᵉ yᵉ))

  abstract
    apply-effectiveness-classᵉ :
      {xᵉ yᵉ : Aᵉ} → classᵉ Rᵉ xᵉ ＝ᵉ classᵉ Rᵉ yᵉ → sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ
    apply-effectiveness-classᵉ {xᵉ} {yᵉ} =
      map-equivᵉ (is-effective-classᵉ xᵉ yᵉ)

  abstract
    apply-effectiveness-class'ᵉ :
      {xᵉ yᵉ : Aᵉ} → sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ → classᵉ Rᵉ xᵉ ＝ᵉ classᵉ Rᵉ yᵉ
    apply-effectiveness-class'ᵉ {xᵉ} {yᵉ} =
      map-inv-equivᵉ (is-effective-classᵉ xᵉ yᵉ)
```

### The map `class` into the type of equivalence classes is surjective and effective

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  is-surjective-and-effective-classᵉ :
    is-surjective-and-effectiveᵉ Rᵉ (classᵉ Rᵉ)
  pr1ᵉ is-surjective-and-effective-classᵉ =
    is-surjective-classᵉ Rᵉ
  pr2ᵉ is-surjective-and-effective-classᵉ =
    is-effective-classᵉ Rᵉ
```

### The map `class` into the type of equivalence classes is a reflecting map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  quotient-reflecting-map-equivalence-classᵉ :
    reflecting-map-equivalence-relationᵉ Rᵉ (equivalence-classᵉ Rᵉ)
  pr1ᵉ quotient-reflecting-map-equivalence-classᵉ =
    classᵉ Rᵉ
  pr2ᵉ quotient-reflecting-map-equivalence-classᵉ =
    apply-effectiveness-class'ᵉ Rᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  transitive-is-in-equivalence-classᵉ :
    (Pᵉ : equivalence-classᵉ Rᵉ) (aᵉ bᵉ : Aᵉ) →
    is-in-equivalence-classᵉ Rᵉ Pᵉ aᵉ → sim-equivalence-relationᵉ Rᵉ aᵉ bᵉ →
    is-in-equivalence-classᵉ Rᵉ Pᵉ bᵉ
  transitive-is-in-equivalence-classᵉ Pᵉ aᵉ bᵉ pᵉ rᵉ =
    apply-universal-property-trunc-Propᵉ
      ( is-equivalence-class-equivalence-classᵉ Rᵉ Pᵉ)
      ( subtype-equivalence-classᵉ Rᵉ Pᵉ bᵉ)
      ( λ (xᵉ ,ᵉ Hᵉ) →
        backward-implicationᵉ
          ( Hᵉ bᵉ)
          ( transitive-equivalence-relationᵉ Rᵉ _ aᵉ bᵉ
            ( rᵉ)
            ( forward-implicationᵉ (Hᵉ aᵉ) pᵉ)))
```

### The type of equivalence classes is locally small

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  is-locally-small-equivalence-classᵉ :
    is-locally-smallᵉ (l1ᵉ ⊔ l2ᵉ) (equivalence-classᵉ Rᵉ)
  is-locally-small-equivalence-classᵉ Cᵉ Dᵉ =
    is-small-equivᵉ
      ( has-same-elements-equivalence-classᵉ Rᵉ Cᵉ Dᵉ)
      ( extensionality-equivalence-classᵉ Rᵉ Cᵉ Dᵉ)
      ( is-small-Πᵉ
        ( is-small'ᵉ)
        ( λ xᵉ → is-small-logical-equivalenceᵉ is-small'ᵉ is-small'ᵉ))
```

### The type of equivalence classes is small

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  is-small-equivalence-classᵉ : is-smallᵉ (l1ᵉ ⊔ l2ᵉ) (equivalence-classᵉ Rᵉ)
  is-small-equivalence-classᵉ =
    is-small-is-surjectiveᵉ
      ( is-surjective-classᵉ Rᵉ)
      ( is-small-lmaxᵉ l2ᵉ Aᵉ)
      ( is-locally-small-equivalence-classᵉ Rᵉ)

  equivalence-class-Small-Typeᵉ : Small-Typeᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ lsuc l2ᵉ)
  pr1ᵉ equivalence-class-Small-Typeᵉ = equivalence-classᵉ Rᵉ
  pr2ᵉ equivalence-class-Small-Typeᵉ = is-small-equivalence-classᵉ

  small-equivalence-classᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  small-equivalence-classᵉ =
    small-type-Small-Typeᵉ equivalence-class-Small-Typeᵉ
```