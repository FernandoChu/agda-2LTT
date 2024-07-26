# Set quotients

```agda
module foundation.set-quotientsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.effective-maps-equivalence-relationsᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalence-classesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.inhabited-subtypesᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.setsᵉ
open import foundation.sliceᵉ
open import foundation.surjective-mapsᵉ
open import foundation.uniqueness-set-quotientsᵉ
open import foundation.universal-property-imageᵉ
open import foundation.universal-property-set-quotientsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.equivalence-relationsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.small-typesᵉ
open import foundation-core.subtypesᵉ
```

</details>

## Definitions

### Set quotients

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  set-quotientᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  set-quotientᵉ = small-type-Small-Typeᵉ (equivalence-class-Small-Typeᵉ Rᵉ)

  compute-set-quotientᵉ : equivalence-classᵉ Rᵉ ≃ᵉ set-quotientᵉ
  compute-set-quotientᵉ =
    equiv-is-small-type-Small-Typeᵉ (equivalence-class-Small-Typeᵉ Rᵉ)

  set-quotient-equivalence-classᵉ : equivalence-classᵉ Rᵉ → set-quotientᵉ
  set-quotient-equivalence-classᵉ = map-equivᵉ compute-set-quotientᵉ

  equivalence-class-set-quotientᵉ : set-quotientᵉ → equivalence-classᵉ Rᵉ
  equivalence-class-set-quotientᵉ = map-inv-equivᵉ compute-set-quotientᵉ

  is-section-equivalence-class-set-quotientᵉ :
    (set-quotient-equivalence-classᵉ ∘ᵉ equivalence-class-set-quotientᵉ) ~ᵉ idᵉ
  is-section-equivalence-class-set-quotientᵉ =
    is-section-map-inv-equivᵉ compute-set-quotientᵉ

  is-retraction-equivalence-class-set-quotientᵉ :
    (equivalence-class-set-quotientᵉ ∘ᵉ set-quotient-equivalence-classᵉ) ~ᵉ idᵉ
  is-retraction-equivalence-class-set-quotientᵉ =
    is-retraction-map-inv-equivᵉ compute-set-quotientᵉ

  emb-equivalence-class-set-quotientᵉ : set-quotientᵉ ↪ᵉ equivalence-classᵉ Rᵉ
  emb-equivalence-class-set-quotientᵉ =
    emb-equivᵉ (inv-equivᵉ compute-set-quotientᵉ)

  emb-set-quotient-equivalence-classᵉ : equivalence-classᵉ Rᵉ ↪ᵉ set-quotientᵉ
  emb-set-quotient-equivalence-classᵉ = emb-equivᵉ compute-set-quotientᵉ

  quotient-mapᵉ : Aᵉ → set-quotientᵉ
  quotient-mapᵉ = set-quotient-equivalence-classᵉ ∘ᵉ classᵉ Rᵉ

  is-surjective-quotient-mapᵉ : is-surjectiveᵉ quotient-mapᵉ
  is-surjective-quotient-mapᵉ =
    is-surjective-comp-equivᵉ compute-set-quotientᵉ (is-surjective-classᵉ Rᵉ)

  surjection-quotient-mapᵉ : Aᵉ ↠ᵉ set-quotientᵉ
  pr1ᵉ surjection-quotient-mapᵉ = quotient-mapᵉ
  pr2ᵉ surjection-quotient-mapᵉ = is-surjective-quotient-mapᵉ

  emb-subtype-set-quotientᵉ : set-quotientᵉ ↪ᵉ subtypeᵉ l2ᵉ Aᵉ
  emb-subtype-set-quotientᵉ =
    comp-embᵉ (emb-equivalence-classᵉ Rᵉ) emb-equivalence-class-set-quotientᵉ

  subtype-set-quotientᵉ : set-quotientᵉ → subtypeᵉ l2ᵉ Aᵉ
  subtype-set-quotientᵉ =
    subtype-equivalence-classᵉ Rᵉ ∘ᵉ equivalence-class-set-quotientᵉ

  is-inhabited-subtype-set-quotientᵉ :
    (xᵉ : set-quotientᵉ) → is-inhabited-subtypeᵉ (subtype-set-quotientᵉ xᵉ)
  is-inhabited-subtype-set-quotientᵉ xᵉ =
    is-inhabited-subtype-equivalence-classᵉ Rᵉ (equivalence-class-set-quotientᵉ xᵉ)

  inhabited-subtype-set-quotientᵉ : set-quotientᵉ → inhabited-subtypeᵉ l2ᵉ Aᵉ
  inhabited-subtype-set-quotientᵉ =
    inhabited-subtype-equivalence-classᵉ Rᵉ ∘ᵉ equivalence-class-set-quotientᵉ

  is-in-equivalence-class-set-quotientᵉ :
    (xᵉ : set-quotientᵉ) → Aᵉ → UUᵉ l2ᵉ
  is-in-equivalence-class-set-quotientᵉ xᵉ =
    is-in-equivalence-classᵉ Rᵉ (equivalence-class-set-quotientᵉ xᵉ)

  is-prop-is-in-equivalence-class-set-quotientᵉ :
    (xᵉ : set-quotientᵉ) (aᵉ : Aᵉ) →
    is-propᵉ (is-in-equivalence-class-set-quotientᵉ xᵉ aᵉ)
  is-prop-is-in-equivalence-class-set-quotientᵉ xᵉ =
    is-prop-is-in-equivalence-classᵉ Rᵉ (equivalence-class-set-quotientᵉ xᵉ)

  is-in-equivalence-class-set-quotient-Propᵉ :
    (xᵉ : set-quotientᵉ) → (Aᵉ → Propᵉ l2ᵉ)
  is-in-equivalence-class-set-quotient-Propᵉ xᵉ =
    is-in-equivalence-class-Propᵉ Rᵉ (equivalence-class-set-quotientᵉ xᵉ)

  is-set-set-quotientᵉ : is-setᵉ set-quotientᵉ
  is-set-set-quotientᵉ =
    is-set-equiv'ᵉ
      ( equivalence-classᵉ Rᵉ)
      ( compute-set-quotientᵉ)
      ( is-set-equivalence-classᵉ Rᵉ)

  quotient-Setᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ quotient-Setᵉ = set-quotientᵉ
  pr2ᵉ quotient-Setᵉ = is-set-set-quotientᵉ

  unit-im-set-quotientᵉ :
    hom-sliceᵉ (prop-equivalence-relationᵉ Rᵉ) subtype-set-quotientᵉ
  pr1ᵉ unit-im-set-quotientᵉ = quotient-mapᵉ
  pr2ᵉ unit-im-set-quotientᵉ =
    ( ( subtype-equivalence-classᵉ Rᵉ) ·lᵉ
      ( inv-htpyᵉ is-retraction-equivalence-class-set-quotientᵉ)) ·rᵉ
    ( classᵉ Rᵉ)

  is-image-set-quotientᵉ :
    is-imageᵉ
      ( prop-equivalence-relationᵉ Rᵉ)
      ( emb-subtype-set-quotientᵉ)
      ( unit-im-set-quotientᵉ)
  is-image-set-quotientᵉ =
    is-image-is-surjectiveᵉ
      ( prop-equivalence-relationᵉ Rᵉ)
      ( emb-subtype-set-quotientᵉ)
      ( unit-im-set-quotientᵉ)
      ( is-surjective-quotient-mapᵉ)
```

### The map `class : A → equivalence-class R` is an effective quotient map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  is-effective-quotient-mapᵉ : is-effectiveᵉ Rᵉ (quotient-mapᵉ Rᵉ)
  is-effective-quotient-mapᵉ xᵉ yᵉ =
    equivalence-reasoningᵉ
      ( quotient-mapᵉ Rᵉ xᵉ ＝ᵉ quotient-mapᵉ Rᵉ yᵉ)
      ≃ᵉ ( equivalence-class-set-quotientᵉ Rᵉ (quotient-mapᵉ Rᵉ xᵉ) ＝ᵉ
          equivalence-class-set-quotientᵉ Rᵉ (quotient-mapᵉ Rᵉ yᵉ))
        byᵉ equiv-ap-embᵉ (emb-equivalence-class-set-quotientᵉ Rᵉ)
      ≃ᵉ ( classᵉ Rᵉ xᵉ ＝ᵉ equivalence-class-set-quotientᵉ Rᵉ (quotient-mapᵉ Rᵉ yᵉ))
        byᵉ
        ( equiv-concatᵉ
          ( (invᵉ ( is-retraction-equivalence-class-set-quotientᵉ Rᵉ (classᵉ Rᵉ xᵉ))))
          ( equivalence-class-set-quotientᵉ Rᵉ (quotient-mapᵉ Rᵉ yᵉ)))
      ≃ᵉ ( classᵉ Rᵉ xᵉ ＝ᵉ classᵉ Rᵉ yᵉ)
        byᵉ
        ( equiv-concat'ᵉ
          ( classᵉ Rᵉ xᵉ)
          ( is-retraction-equivalence-class-set-quotientᵉ Rᵉ (classᵉ Rᵉ yᵉ)))
      ≃ᵉ ( sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ)
        byᵉ
        ( is-effective-classᵉ Rᵉ xᵉ yᵉ)

  apply-effectiveness-quotient-mapᵉ :
    {xᵉ yᵉ : Aᵉ} → quotient-mapᵉ Rᵉ xᵉ ＝ᵉ quotient-mapᵉ Rᵉ yᵉ →
    sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ
  apply-effectiveness-quotient-mapᵉ {xᵉ} {yᵉ} =
    map-equivᵉ (is-effective-quotient-mapᵉ xᵉ yᵉ)

  apply-effectiveness-quotient-map'ᵉ :
    {xᵉ yᵉ : Aᵉ} → sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ →
    quotient-mapᵉ Rᵉ xᵉ ＝ᵉ quotient-mapᵉ Rᵉ yᵉ
  apply-effectiveness-quotient-map'ᵉ {xᵉ} {yᵉ} =
    map-inv-equivᵉ (is-effective-quotient-mapᵉ xᵉ yᵉ)

  is-surjective-and-effective-quotient-mapᵉ :
    is-surjective-and-effectiveᵉ Rᵉ (quotient-mapᵉ Rᵉ)
  pr1ᵉ is-surjective-and-effective-quotient-mapᵉ = is-surjective-quotient-mapᵉ Rᵉ
  pr2ᵉ is-surjective-and-effective-quotient-mapᵉ = is-effective-quotient-mapᵉ

  reflecting-map-quotient-mapᵉ :
    reflecting-map-equivalence-relationᵉ Rᵉ (set-quotientᵉ Rᵉ)
  pr1ᵉ reflecting-map-quotient-mapᵉ = quotient-mapᵉ Rᵉ
  pr2ᵉ reflecting-map-quotient-mapᵉ = apply-effectiveness-quotient-map'ᵉ
```

### The set quotient of `R` is a set quotient of `R`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  is-set-quotient-set-quotientᵉ :
    is-set-quotientᵉ Rᵉ (quotient-Setᵉ Rᵉ) (reflecting-map-quotient-mapᵉ Rᵉ)
  is-set-quotient-set-quotientᵉ =
    is-set-quotient-is-surjective-and-effectiveᵉ Rᵉ
      ( quotient-Setᵉ Rᵉ)
      ( reflecting-map-quotient-mapᵉ Rᵉ)
      ( is-surjective-and-effective-quotient-mapᵉ Rᵉ)

  inv-precomp-set-quotientᵉ :
    {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) →
    reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Xᵉ) →
    hom-Setᵉ (quotient-Setᵉ Rᵉ) Xᵉ
  inv-precomp-set-quotientᵉ Xᵉ =
    pr1ᵉ (pr1ᵉ (is-set-quotient-set-quotientᵉ Xᵉ))

  is-section-inv-precomp-set-quotientᵉ :
    {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) →
    (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Xᵉ)) →
    (aᵉ : Aᵉ) →
    inv-precomp-set-quotientᵉ Xᵉ fᵉ (quotient-mapᵉ Rᵉ aᵉ) ＝ᵉ
      map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ aᵉ
  is-section-inv-precomp-set-quotientᵉ Xᵉ fᵉ =
    htpy-eqᵉ
      ( apᵉ
        ( map-reflecting-map-equivalence-relationᵉ Rᵉ)
        ( is-section-map-inv-is-equivᵉ
          ( is-set-quotient-set-quotientᵉ Xᵉ)
          ( fᵉ)))

  is-retraction-inv-precomp-set-quotientᵉ :
    {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) (fᵉ : hom-Setᵉ (quotient-Setᵉ Rᵉ) Xᵉ) →
    inv-precomp-set-quotientᵉ Xᵉ
      ( precomp-Set-Quotientᵉ Rᵉ
        ( quotient-Setᵉ Rᵉ)
        ( reflecting-map-quotient-mapᵉ Rᵉ)
        ( Xᵉ)
        ( fᵉ)) ＝ᵉ
    fᵉ
  is-retraction-inv-precomp-set-quotientᵉ Xᵉ fᵉ =
    is-retraction-map-inv-is-equivᵉ (is-set-quotient-set-quotientᵉ Xᵉ) fᵉ
```

### Induction into propositions on the set quotient

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  equiv-induction-set-quotientᵉ :
    {lᵉ : Level} (Pᵉ : set-quotientᵉ Rᵉ → Propᵉ lᵉ) →
    ((yᵉ : set-quotientᵉ Rᵉ) → type-Propᵉ (Pᵉ yᵉ)) ≃ᵉ
    ((xᵉ : Aᵉ) → type-Propᵉ (Pᵉ (quotient-mapᵉ Rᵉ xᵉ)))
  equiv-induction-set-quotientᵉ =
    equiv-dependent-universal-property-surjection-is-surjectiveᵉ
      ( quotient-mapᵉ Rᵉ)
      ( is-surjective-quotient-mapᵉ Rᵉ)

  induction-set-quotientᵉ :
    {lᵉ : Level} (Pᵉ : set-quotientᵉ Rᵉ → Propᵉ lᵉ) →
    ((xᵉ : Aᵉ) → type-Propᵉ (Pᵉ (quotient-mapᵉ Rᵉ xᵉ))) →
    ((yᵉ : set-quotientᵉ Rᵉ) → type-Propᵉ (Pᵉ yᵉ))
  induction-set-quotientᵉ Pᵉ =
    map-inv-equivᵉ (equiv-induction-set-quotientᵉ Pᵉ)
```

### Double induction for set quotients

#### The most general case

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  (Pᵉ : set-quotientᵉ Rᵉ → set-quotientᵉ Sᵉ → Propᵉ l5ᵉ)
  where

  equiv-double-induction-set-quotientᵉ :
    ((xᵉ : set-quotientᵉ Rᵉ) (yᵉ : set-quotientᵉ Sᵉ) → type-Propᵉ (Pᵉ xᵉ yᵉ)) ≃ᵉ
    ( (xᵉ : Aᵉ) (yᵉ : Bᵉ) →
      type-Propᵉ (Pᵉ (quotient-mapᵉ Rᵉ xᵉ) (quotient-mapᵉ Sᵉ yᵉ)))
  equiv-double-induction-set-quotientᵉ =
    ( equiv-Π-equiv-familyᵉ
      ( λ xᵉ →
        equiv-induction-set-quotientᵉ Sᵉ (Pᵉ (quotient-mapᵉ Rᵉ xᵉ)))) ∘eᵉ
    ( equiv-induction-set-quotientᵉ Rᵉ
      ( λ xᵉ → Π-Propᵉ (set-quotientᵉ Sᵉ) (Pᵉ xᵉ)))

  double-induction-set-quotientᵉ :
    ( (xᵉ : Aᵉ) (yᵉ : Bᵉ) →
      type-Propᵉ (Pᵉ (quotient-mapᵉ Rᵉ xᵉ) (quotient-mapᵉ Sᵉ yᵉ))) →
    (xᵉ : set-quotientᵉ Rᵉ) (yᵉ : set-quotientᵉ Sᵉ) → type-Propᵉ (Pᵉ xᵉ yᵉ)
  double-induction-set-quotientᵉ =
    map-inv-equivᵉ equiv-double-induction-set-quotientᵉ
```

#### Double induction over a single set quotient

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  (Pᵉ : (xᵉ yᵉ : set-quotientᵉ Rᵉ) → Propᵉ l3ᵉ)
  where

  equiv-double-induction-set-quotient'ᵉ :
    ((xᵉ yᵉ : set-quotientᵉ Rᵉ) → type-Propᵉ (Pᵉ xᵉ yᵉ)) ≃ᵉ
    ((xᵉ yᵉ : Aᵉ) → type-Propᵉ (Pᵉ (quotient-mapᵉ Rᵉ xᵉ) (quotient-mapᵉ Rᵉ yᵉ)))
  equiv-double-induction-set-quotient'ᵉ =
    equiv-double-induction-set-quotientᵉ Rᵉ Rᵉ Pᵉ

  double-induction-set-quotient'ᵉ :
    ( (xᵉ yᵉ : Aᵉ) →
      type-Propᵉ (Pᵉ (quotient-mapᵉ Rᵉ xᵉ) (quotient-mapᵉ Rᵉ yᵉ))) →
    (xᵉ yᵉ : set-quotientᵉ Rᵉ) → type-Propᵉ (Pᵉ xᵉ yᵉ)
  double-induction-set-quotient'ᵉ =
    double-induction-set-quotientᵉ Rᵉ Rᵉ Pᵉ
```

### Triple induction for set quotients

#### The most general case

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  {Cᵉ : UUᵉ l5ᵉ} (Tᵉ : equivalence-relationᵉ l6ᵉ Cᵉ)
  (Pᵉ : set-quotientᵉ Rᵉ → set-quotientᵉ Sᵉ → set-quotientᵉ Tᵉ → Propᵉ l7ᵉ)
  where

  equiv-triple-induction-set-quotientᵉ :
    ( (xᵉ : set-quotientᵉ Rᵉ) (yᵉ : set-quotientᵉ Sᵉ) (zᵉ : set-quotientᵉ Tᵉ) →
      type-Propᵉ (Pᵉ xᵉ yᵉ zᵉ)) ≃ᵉ
    ( (xᵉ : Aᵉ) (yᵉ : Bᵉ) (zᵉ : Cᵉ) →
      type-Propᵉ
        ( Pᵉ (quotient-mapᵉ Rᵉ xᵉ) (quotient-mapᵉ Sᵉ yᵉ) (quotient-mapᵉ Tᵉ zᵉ)))
  equiv-triple-induction-set-quotientᵉ =
    ( equiv-Π-equiv-familyᵉ
      ( λ xᵉ →
        equiv-double-induction-set-quotientᵉ Sᵉ Tᵉ
          ( Pᵉ (quotient-mapᵉ Rᵉ xᵉ)))) ∘eᵉ
    ( equiv-induction-set-quotientᵉ Rᵉ
      ( λ xᵉ →
        Π-Propᵉ
          ( set-quotientᵉ Sᵉ)
          ( λ yᵉ → Π-Propᵉ (set-quotientᵉ Tᵉ) (Pᵉ xᵉ yᵉ))))

  triple-induction-set-quotientᵉ :
    ( (xᵉ : Aᵉ) (yᵉ : Bᵉ) (zᵉ : Cᵉ) →
      type-Propᵉ
        ( Pᵉ ( quotient-mapᵉ Rᵉ xᵉ)
            ( quotient-mapᵉ Sᵉ yᵉ)
            ( quotient-mapᵉ Tᵉ zᵉ))) →
    ( xᵉ : set-quotientᵉ Rᵉ) (yᵉ : set-quotientᵉ Sᵉ)
    ( zᵉ : set-quotientᵉ Tᵉ) → type-Propᵉ (Pᵉ xᵉ yᵉ zᵉ)
  triple-induction-set-quotientᵉ =
    map-inv-equivᵉ equiv-triple-induction-set-quotientᵉ
```

#### Triple induction over a single set quotient

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  (Pᵉ : (xᵉ yᵉ zᵉ : set-quotientᵉ Rᵉ) → Propᵉ l3ᵉ)
  where

  equiv-triple-induction-set-quotient'ᵉ :
    ((xᵉ yᵉ zᵉ : set-quotientᵉ Rᵉ) → type-Propᵉ (Pᵉ xᵉ yᵉ zᵉ)) ≃ᵉ
    ( (xᵉ yᵉ zᵉ : Aᵉ) →
      type-Propᵉ
        ( Pᵉ (quotient-mapᵉ Rᵉ xᵉ) (quotient-mapᵉ Rᵉ yᵉ) (quotient-mapᵉ Rᵉ zᵉ)))
  equiv-triple-induction-set-quotient'ᵉ =
    equiv-triple-induction-set-quotientᵉ Rᵉ Rᵉ Rᵉ Pᵉ

  triple-induction-set-quotient'ᵉ :
    ( (xᵉ yᵉ zᵉ : Aᵉ) →
      type-Propᵉ
        ( Pᵉ ( quotient-mapᵉ Rᵉ xᵉ)
            ( quotient-mapᵉ Rᵉ yᵉ)
            ( quotient-mapᵉ Rᵉ zᵉ))) →
    ( xᵉ yᵉ zᵉ : set-quotientᵉ Rᵉ) → type-Propᵉ (Pᵉ xᵉ yᵉ zᵉ)
  triple-induction-set-quotient'ᵉ =
    triple-induction-set-quotientᵉ Rᵉ Rᵉ Rᵉ Pᵉ
```

### Every set quotient is equivalent to the set quotient

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  (Bᵉ : Setᵉ l3ᵉ) (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ))
  (Ufᵉ : is-set-quotientᵉ Rᵉ Bᵉ fᵉ)
  where

  equiv-uniqueness-set-quotient-set-quotientᵉ :
    set-quotientᵉ Rᵉ ≃ᵉ type-Setᵉ Bᵉ
  equiv-uniqueness-set-quotient-set-quotientᵉ =
    equiv-uniqueness-set-quotientᵉ Rᵉ
      ( quotient-Setᵉ Rᵉ)
      ( reflecting-map-quotient-mapᵉ Rᵉ)
      ( is-set-quotient-set-quotientᵉ Rᵉ)
      Bᵉ fᵉ Ufᵉ
```