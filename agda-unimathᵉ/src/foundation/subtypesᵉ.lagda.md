# Subtypes

```agda
module foundation.subtypesᵉ where

open import foundation-core.subtypesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Definition

### A second definition of the type of subtypes

```agda
Subtypeᵉ : {l1ᵉ : Level} (l2ᵉ l3ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
Subtypeᵉ l2ᵉ l3ᵉ Aᵉ =
  Σᵉ ( Aᵉ → Propᵉ l2ᵉ)
    ( λ Pᵉ →
      Σᵉ ( Σᵉ (UUᵉ l3ᵉ) (λ Xᵉ → Xᵉ ↪ᵉ Aᵉ))
        ( λ iᵉ →
          Σᵉ ( pr1ᵉ iᵉ ≃ᵉ Σᵉ Aᵉ (type-Propᵉ ∘ᵉ Pᵉ))
            ( λ eᵉ → map-embᵉ (pr2ᵉ iᵉ) ~ᵉ (pr1ᵉ ∘ᵉ map-equivᵉ eᵉ))))
```

## Properties

### The inclusion of a subtype into the ambient type is injective

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : subtypeᵉ l2ᵉ Aᵉ)
  where

  is-injective-inclusion-subtypeᵉ : is-injectiveᵉ (inclusion-subtypeᵉ Bᵉ)
  is-injective-inclusion-subtypeᵉ =
    is-injective-is-embᵉ (is-emb-inclusion-subtypeᵉ Bᵉ)
```

### Equality in the type of all subtypes

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ)
  where

  has-same-elements-subtype-Propᵉ :
    {l3ᵉ : Level} → subtypeᵉ l3ᵉ Aᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-subtype-Propᵉ Qᵉ =
    Π-Propᵉ Aᵉ (λ xᵉ → iff-Propᵉ (Pᵉ xᵉ) (Qᵉ xᵉ))

  has-same-elements-subtypeᵉ : {l3ᵉ : Level} → subtypeᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-subtypeᵉ Qᵉ = type-Propᵉ (has-same-elements-subtype-Propᵉ Qᵉ)

  is-prop-has-same-elements-subtypeᵉ :
    {l3ᵉ : Level} (Qᵉ : subtypeᵉ l3ᵉ Aᵉ) →
    is-propᵉ (has-same-elements-subtypeᵉ Qᵉ)
  is-prop-has-same-elements-subtypeᵉ Qᵉ =
    is-prop-type-Propᵉ (has-same-elements-subtype-Propᵉ Qᵉ)

  refl-has-same-elements-subtypeᵉ : has-same-elements-subtypeᵉ Pᵉ
  pr1ᵉ (refl-has-same-elements-subtypeᵉ xᵉ) = idᵉ
  pr2ᵉ (refl-has-same-elements-subtypeᵉ xᵉ) = idᵉ

  is-torsorial-has-same-elements-subtypeᵉ :
    is-torsorialᵉ has-same-elements-subtypeᵉ
  is-torsorial-has-same-elements-subtypeᵉ =
    is-torsorial-Eq-Πᵉ (λ xᵉ → is-torsorial-iffᵉ (Pᵉ xᵉ))

  has-same-elements-eq-subtypeᵉ :
    (Qᵉ : subtypeᵉ l2ᵉ Aᵉ) → (Pᵉ ＝ᵉ Qᵉ) → has-same-elements-subtypeᵉ Qᵉ
  has-same-elements-eq-subtypeᵉ .Pᵉ reflᵉ =
    refl-has-same-elements-subtypeᵉ

  is-equiv-has-same-elements-eq-subtypeᵉ :
    (Qᵉ : subtypeᵉ l2ᵉ Aᵉ) → is-equivᵉ (has-same-elements-eq-subtypeᵉ Qᵉ)
  is-equiv-has-same-elements-eq-subtypeᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-has-same-elements-subtypeᵉ
      has-same-elements-eq-subtypeᵉ

  extensionality-subtypeᵉ :
    (Qᵉ : subtypeᵉ l2ᵉ Aᵉ) → (Pᵉ ＝ᵉ Qᵉ) ≃ᵉ has-same-elements-subtypeᵉ Qᵉ
  pr1ᵉ (extensionality-subtypeᵉ Qᵉ) = has-same-elements-eq-subtypeᵉ Qᵉ
  pr2ᵉ (extensionality-subtypeᵉ Qᵉ) = is-equiv-has-same-elements-eq-subtypeᵉ Qᵉ

  eq-has-same-elements-subtypeᵉ :
    (Qᵉ : subtypeᵉ l2ᵉ Aᵉ) → has-same-elements-subtypeᵉ Qᵉ → Pᵉ ＝ᵉ Qᵉ
  eq-has-same-elements-subtypeᵉ Qᵉ =
    map-inv-equivᵉ (extensionality-subtypeᵉ Qᵉ)
```

### Similarity of subtypes

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  sim-subtypeᵉ :
    {l2ᵉ l3ᵉ : Level} → subtypeᵉ l2ᵉ Aᵉ → subtypeᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  sim-subtypeᵉ Pᵉ Qᵉ = (Pᵉ ⊆ᵉ Qᵉ) ×ᵉ (Qᵉ ⊆ᵉ Pᵉ)

  has-same-elements-sim-subtypeᵉ :
    {l2ᵉ l3ᵉ : Level} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ) (Qᵉ : subtypeᵉ l3ᵉ Aᵉ) →
    sim-subtypeᵉ Pᵉ Qᵉ → has-same-elements-subtypeᵉ Pᵉ Qᵉ
  pr1ᵉ (has-same-elements-sim-subtypeᵉ Pᵉ Qᵉ sᵉ xᵉ) = pr1ᵉ sᵉ xᵉ
  pr2ᵉ (has-same-elements-sim-subtypeᵉ Pᵉ Qᵉ sᵉ xᵉ) = pr2ᵉ sᵉ xᵉ

  sim-has-same-elements-subtypeᵉ :
    {l2ᵉ l3ᵉ : Level} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ) (Qᵉ : subtypeᵉ l3ᵉ Aᵉ) →
    has-same-elements-subtypeᵉ Pᵉ Qᵉ → sim-subtypeᵉ Pᵉ Qᵉ
  pr1ᵉ (sim-has-same-elements-subtypeᵉ Pᵉ Qᵉ sᵉ) xᵉ = forward-implicationᵉ (sᵉ xᵉ)
  pr2ᵉ (sim-has-same-elements-subtypeᵉ Pᵉ Qᵉ sᵉ) xᵉ = backward-implicationᵉ (sᵉ xᵉ)
```

### The containment relation is antisymmetric

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  equiv-antisymmetric-leq-subtypeᵉ :
    {l2ᵉ l3ᵉ : Level} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ) (Qᵉ : subtypeᵉ l3ᵉ Aᵉ) → Pᵉ ⊆ᵉ Qᵉ → Qᵉ ⊆ᵉ Pᵉ →
    (xᵉ : Aᵉ) → is-in-subtypeᵉ Pᵉ xᵉ ≃ᵉ is-in-subtypeᵉ Qᵉ xᵉ
  equiv-antisymmetric-leq-subtypeᵉ Pᵉ Qᵉ Hᵉ Kᵉ xᵉ =
    equiv-iff-is-propᵉ
      ( is-prop-is-in-subtypeᵉ Pᵉ xᵉ)
      ( is-prop-is-in-subtypeᵉ Qᵉ xᵉ)
      ( Hᵉ xᵉ)
      ( Kᵉ xᵉ)

  antisymmetric-leq-subtypeᵉ :
    {l2ᵉ : Level} (Pᵉ Qᵉ : subtypeᵉ l2ᵉ Aᵉ) → Pᵉ ⊆ᵉ Qᵉ → Qᵉ ⊆ᵉ Pᵉ → Pᵉ ＝ᵉ Qᵉ
  antisymmetric-leq-subtypeᵉ Pᵉ Qᵉ Hᵉ Kᵉ =
    eq-has-same-elements-subtypeᵉ Pᵉ Qᵉ (λ xᵉ → (Hᵉ xᵉ ,ᵉ Kᵉ xᵉ))
```

### The type of all subtypes of a type is a set

```agda
is-set-subtypeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-setᵉ (subtypeᵉ l2ᵉ Aᵉ)
is-set-subtypeᵉ Pᵉ Qᵉ =
  is-prop-equivᵉ
    ( extensionality-subtypeᵉ Pᵉ Qᵉ)
    ( is-prop-has-same-elements-subtypeᵉ Pᵉ Qᵉ)

subtype-Setᵉ : {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → Setᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
pr1ᵉ (subtype-Setᵉ l2ᵉ Aᵉ) = subtypeᵉ l2ᵉ Aᵉ
pr2ᵉ (subtype-Setᵉ l2ᵉ Aᵉ) = is-set-subtypeᵉ
```

### Characterisation of embeddings into subtypes

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : subtypeᵉ l2ᵉ Aᵉ) {Xᵉ : UUᵉ l3ᵉ}
  where

  inv-emb-into-subtypeᵉ :
    (gᵉ : Xᵉ ↪ᵉ type-subtypeᵉ Bᵉ) →
    Σᵉ (Xᵉ ↪ᵉ Aᵉ) (λ fᵉ → (xᵉ : Xᵉ) → is-in-subtypeᵉ Bᵉ (map-embᵉ fᵉ xᵉ))
  pr1ᵉ (pr1ᵉ (inv-emb-into-subtypeᵉ gᵉ)) =
    inclusion-subtypeᵉ Bᵉ ∘ᵉ map-embᵉ gᵉ
  pr2ᵉ (pr1ᵉ (inv-emb-into-subtypeᵉ gᵉ)) =
    is-emb-compᵉ _ _ (is-emb-inclusion-subtypeᵉ Bᵉ) (is-emb-map-embᵉ gᵉ)
  pr2ᵉ (inv-emb-into-subtypeᵉ gᵉ) xᵉ =
    pr2ᵉ (map-embᵉ gᵉ xᵉ)

  issec-map-inv-emb-into-subtypeᵉ :
    ( ind-Σᵉ (emb-into-subtypeᵉ Bᵉ) ∘ᵉ inv-emb-into-subtypeᵉ) ~ᵉ idᵉ
  issec-map-inv-emb-into-subtypeᵉ gᵉ =
    eq-type-subtypeᵉ
      is-emb-Propᵉ
      reflᵉ

  isretr-map-inv-emb-into-subtypeᵉ :
    ( inv-emb-into-subtypeᵉ ∘ᵉ ind-Σᵉ (emb-into-subtypeᵉ Bᵉ)) ~ᵉ idᵉ
  isretr-map-inv-emb-into-subtypeᵉ (fᵉ ,ᵉ bᵉ) =
    eq-type-subtypeᵉ
      (λ fᵉ → Π-Propᵉ Xᵉ (λ xᵉ → Bᵉ (map-embᵉ fᵉ xᵉ)))
      (eq-type-subtypeᵉ
        is-emb-Propᵉ
        reflᵉ)

  equiv-emb-into-subtypeᵉ :
    Σᵉ (Xᵉ ↪ᵉ Aᵉ) (λ fᵉ →
      (xᵉ : Xᵉ) → is-in-subtypeᵉ Bᵉ (map-embᵉ fᵉ xᵉ)) ≃ᵉ (Xᵉ ↪ᵉ type-subtypeᵉ Bᵉ)
  pr1ᵉ equiv-emb-into-subtypeᵉ = ind-Σᵉ (emb-into-subtypeᵉ Bᵉ)
  pr2ᵉ equiv-emb-into-subtypeᵉ =
    is-equiv-is-invertibleᵉ
      inv-emb-into-subtypeᵉ
      issec-map-inv-emb-into-subtypeᵉ
      isretr-map-inv-emb-into-subtypeᵉ
```

## See also

-ᵉ [Imagesᵉ ofᵉ subtypes](foundation.images-subtypes.mdᵉ)
-ᵉ [Largeᵉ localeᵉ ofᵉ subtypes](foundation.large-locale-of-subtypes.mdᵉ)
-ᵉ [Powersets](foundation.powersets.mdᵉ)
-ᵉ [Pullbacksᵉ ofᵉ subtypes](foundation.pullbacks-subtypes.mdᵉ)