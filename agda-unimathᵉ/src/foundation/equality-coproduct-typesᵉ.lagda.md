# Equality of coproduct types

```agda
module foundation.equality-coproduct-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Inᵉ orderᵉ to constructᵉ anᵉ identificationᵉ `Idᵉ xᵉ y`ᵉ in aᵉ coproductᵉ `coproductᵉ Aᵉ B`,ᵉ
bothᵉ `x`ᵉ andᵉ `y`ᵉ mustᵉ beᵉ ofᵉ theᵉ formᵉ `inlᵉ _`ᵉ orᵉ ofᵉ theᵉ formᵉ `inrᵉ _`.ᵉ Ifᵉ thatᵉ isᵉ
theᵉ case,ᵉ thenᵉ anᵉ identificationᵉ canᵉ beᵉ constructedᵉ byᵉ constructinᵉ anᵉ
identificationᵉ in Aᵉ orᵉ in B,ᵉ accordingᵉ to theᵉ case.ᵉ Thisᵉ leadsᵉ to theᵉ
characterizationᵉ ofᵉ identityᵉ typesᵉ ofᵉ coproducts.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  data Eq-coproductᵉ : Aᵉ +ᵉ Bᵉ → Aᵉ +ᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    Eq-eq-coproduct-inlᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ᵉ yᵉ → Eq-coproductᵉ (inlᵉ xᵉ) (inlᵉ yᵉ)
    Eq-eq-coproduct-inrᵉ : {xᵉ yᵉ : Bᵉ} → xᵉ ＝ᵉ yᵉ → Eq-coproductᵉ (inrᵉ xᵉ) (inrᵉ yᵉ)
```

## Properties

### The type `Eq-coproduct x y` is equivalent to `Id x y`

Weᵉ willᵉ useᵉ theᵉ fundamentalᵉ theoremᵉ ofᵉ identityᵉ types.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  refl-Eq-coproductᵉ : (xᵉ : Aᵉ +ᵉ Bᵉ) → Eq-coproductᵉ xᵉ xᵉ
  refl-Eq-coproductᵉ (inlᵉ xᵉ) = Eq-eq-coproduct-inlᵉ reflᵉ
  refl-Eq-coproductᵉ (inrᵉ xᵉ) = Eq-eq-coproduct-inrᵉ reflᵉ

  Eq-eq-coproductᵉ : (xᵉ yᵉ : Aᵉ +ᵉ Bᵉ) → xᵉ ＝ᵉ yᵉ → Eq-coproductᵉ xᵉ yᵉ
  Eq-eq-coproductᵉ xᵉ .xᵉ reflᵉ = refl-Eq-coproductᵉ xᵉ

  eq-Eq-coproductᵉ : (xᵉ yᵉ : Aᵉ +ᵉ Bᵉ) → Eq-coproductᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-Eq-coproductᵉ .(inlᵉ xᵉ) .(inlᵉ xᵉ) (Eq-eq-coproduct-inlᵉ {xᵉ} {.xᵉ} reflᵉ) = reflᵉ
  eq-Eq-coproductᵉ .(inrᵉ xᵉ) .(inrᵉ xᵉ) (Eq-eq-coproduct-inrᵉ {xᵉ} {.xᵉ} reflᵉ) = reflᵉ

  is-torsorial-Eq-coproductᵉ :
    (xᵉ : Aᵉ +ᵉ Bᵉ) → is-torsorialᵉ (Eq-coproductᵉ xᵉ)
  pr1ᵉ (pr1ᵉ (is-torsorial-Eq-coproductᵉ (inlᵉ xᵉ))) = inlᵉ xᵉ
  pr2ᵉ (pr1ᵉ (is-torsorial-Eq-coproductᵉ (inlᵉ xᵉ))) = Eq-eq-coproduct-inlᵉ reflᵉ
  pr2ᵉ
    ( is-torsorial-Eq-coproductᵉ (inlᵉ xᵉ)) (.(inlᵉ xᵉ) ,ᵉ Eq-eq-coproduct-inlᵉ reflᵉ) =
    reflᵉ
  pr1ᵉ (pr1ᵉ (is-torsorial-Eq-coproductᵉ (inrᵉ xᵉ))) = inrᵉ xᵉ
  pr2ᵉ (pr1ᵉ (is-torsorial-Eq-coproductᵉ (inrᵉ xᵉ))) = Eq-eq-coproduct-inrᵉ reflᵉ
  pr2ᵉ
    ( is-torsorial-Eq-coproductᵉ (inrᵉ xᵉ)) (.(inrᵉ xᵉ) ,ᵉ Eq-eq-coproduct-inrᵉ reflᵉ) =
    reflᵉ

  is-equiv-Eq-eq-coproductᵉ : (xᵉ yᵉ : Aᵉ +ᵉ Bᵉ) → is-equivᵉ (Eq-eq-coproductᵉ xᵉ yᵉ)
  is-equiv-Eq-eq-coproductᵉ xᵉ =
    fundamental-theorem-idᵉ (is-torsorial-Eq-coproductᵉ xᵉ) (Eq-eq-coproductᵉ xᵉ)

  extensionality-coproductᵉ : (xᵉ yᵉ : Aᵉ +ᵉ Bᵉ) → (xᵉ ＝ᵉ yᵉ) ≃ᵉ Eq-coproductᵉ xᵉ yᵉ
  pr1ᵉ (extensionality-coproductᵉ xᵉ yᵉ) = Eq-eq-coproductᵉ xᵉ yᵉ
  pr2ᵉ (extensionality-coproductᵉ xᵉ yᵉ) = is-equiv-Eq-eq-coproductᵉ xᵉ yᵉ
```

Nowᵉ weᵉ useᵉ theᵉ characterizationᵉ ofᵉ theᵉ identityᵉ typeᵉ to obtainᵉ theᵉ desiredᵉ
equivalences.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  module _
    (xᵉ yᵉ : Aᵉ)
    where

    map-compute-Eq-coproduct-inl-inlᵉ :
      Eq-coproductᵉ {Bᵉ = Bᵉ} (inlᵉ xᵉ) (inlᵉ yᵉ) → (xᵉ ＝ᵉ yᵉ)
    map-compute-Eq-coproduct-inl-inlᵉ (Eq-eq-coproduct-inlᵉ pᵉ) = pᵉ

    is-section-Eq-eq-coproduct-inlᵉ :
      (map-compute-Eq-coproduct-inl-inlᵉ ∘ᵉ Eq-eq-coproduct-inlᵉ) ~ᵉ idᵉ
    is-section-Eq-eq-coproduct-inlᵉ pᵉ = reflᵉ

    is-retraction-Eq-eq-coproduct-inlᵉ :
      (Eq-eq-coproduct-inlᵉ ∘ᵉ map-compute-Eq-coproduct-inl-inlᵉ) ~ᵉ idᵉ
    is-retraction-Eq-eq-coproduct-inlᵉ (Eq-eq-coproduct-inlᵉ pᵉ) = reflᵉ

    is-equiv-map-compute-Eq-coproduct-inl-inlᵉ :
      is-equivᵉ map-compute-Eq-coproduct-inl-inlᵉ
    is-equiv-map-compute-Eq-coproduct-inl-inlᵉ =
      is-equiv-is-invertibleᵉ
        ( Eq-eq-coproduct-inlᵉ)
        ( is-section-Eq-eq-coproduct-inlᵉ)
        ( is-retraction-Eq-eq-coproduct-inlᵉ)

    compute-Eq-coproduct-inl-inlᵉ : Eq-coproductᵉ (inlᵉ xᵉ) (inlᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ yᵉ)
    pr1ᵉ compute-Eq-coproduct-inl-inlᵉ = map-compute-Eq-coproduct-inl-inlᵉ
    pr2ᵉ compute-Eq-coproduct-inl-inlᵉ = is-equiv-map-compute-Eq-coproduct-inl-inlᵉ

    compute-eq-coproduct-inl-inlᵉ : Idᵉ {Aᵉ = Aᵉ +ᵉ Bᵉ} (inlᵉ xᵉ) (inlᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ yᵉ)
    compute-eq-coproduct-inl-inlᵉ =
      compute-Eq-coproduct-inl-inlᵉ ∘eᵉ extensionality-coproductᵉ (inlᵉ xᵉ) (inlᵉ yᵉ)

    map-compute-eq-coproduct-inl-inlᵉ : Idᵉ {Aᵉ = Aᵉ +ᵉ Bᵉ} (inlᵉ xᵉ) (inlᵉ yᵉ) → xᵉ ＝ᵉ yᵉ
    map-compute-eq-coproduct-inl-inlᵉ = map-equivᵉ compute-eq-coproduct-inl-inlᵉ

  module _
    (xᵉ : Aᵉ) (yᵉ : Bᵉ)
    where

    map-compute-Eq-coproduct-inl-inrᵉ : Eq-coproductᵉ (inlᵉ xᵉ) (inrᵉ yᵉ) → emptyᵉ
    map-compute-Eq-coproduct-inl-inrᵉ ()

    is-equiv-map-compute-Eq-coproduct-inl-inrᵉ :
      is-equivᵉ map-compute-Eq-coproduct-inl-inrᵉ
    is-equiv-map-compute-Eq-coproduct-inl-inrᵉ =
      is-equiv-is-empty'ᵉ map-compute-Eq-coproduct-inl-inrᵉ

    compute-Eq-coproduct-inl-inrᵉ : Eq-coproductᵉ (inlᵉ xᵉ) (inrᵉ yᵉ) ≃ᵉ emptyᵉ
    pr1ᵉ compute-Eq-coproduct-inl-inrᵉ = map-compute-Eq-coproduct-inl-inrᵉ
    pr2ᵉ compute-Eq-coproduct-inl-inrᵉ = is-equiv-map-compute-Eq-coproduct-inl-inrᵉ

    compute-eq-coproduct-inl-inrᵉ : Idᵉ {Aᵉ = Aᵉ +ᵉ Bᵉ} (inlᵉ xᵉ) (inrᵉ yᵉ) ≃ᵉ emptyᵉ
    compute-eq-coproduct-inl-inrᵉ =
      compute-Eq-coproduct-inl-inrᵉ ∘eᵉ extensionality-coproductᵉ (inlᵉ xᵉ) (inrᵉ yᵉ)

    is-empty-eq-coproduct-inl-inrᵉ : is-emptyᵉ (Idᵉ {Aᵉ = Aᵉ +ᵉ Bᵉ} (inlᵉ xᵉ) (inrᵉ yᵉ))
    is-empty-eq-coproduct-inl-inrᵉ = map-equivᵉ compute-eq-coproduct-inl-inrᵉ

  module _
    (xᵉ : Bᵉ) (yᵉ : Aᵉ)
    where

    map-compute-Eq-coproduct-inr-inlᵉ : Eq-coproductᵉ (inrᵉ xᵉ) (inlᵉ yᵉ) → emptyᵉ
    map-compute-Eq-coproduct-inr-inlᵉ ()

    is-equiv-map-compute-Eq-coproduct-inr-inlᵉ :
      is-equivᵉ map-compute-Eq-coproduct-inr-inlᵉ
    is-equiv-map-compute-Eq-coproduct-inr-inlᵉ =
      is-equiv-is-empty'ᵉ map-compute-Eq-coproduct-inr-inlᵉ

    compute-Eq-coproduct-inr-inlᵉ : Eq-coproductᵉ (inrᵉ xᵉ) (inlᵉ yᵉ) ≃ᵉ emptyᵉ
    pr1ᵉ compute-Eq-coproduct-inr-inlᵉ = map-compute-Eq-coproduct-inr-inlᵉ
    pr2ᵉ compute-Eq-coproduct-inr-inlᵉ = is-equiv-map-compute-Eq-coproduct-inr-inlᵉ

    compute-eq-coproduct-inr-inlᵉ : Idᵉ {Aᵉ = Aᵉ +ᵉ Bᵉ} (inrᵉ xᵉ) (inlᵉ yᵉ) ≃ᵉ emptyᵉ
    compute-eq-coproduct-inr-inlᵉ =
      compute-Eq-coproduct-inr-inlᵉ ∘eᵉ extensionality-coproductᵉ (inrᵉ xᵉ) (inlᵉ yᵉ)

    is-empty-eq-coproduct-inr-inlᵉ : is-emptyᵉ (Idᵉ {Aᵉ = Aᵉ +ᵉ Bᵉ} (inrᵉ xᵉ) (inlᵉ yᵉ))
    is-empty-eq-coproduct-inr-inlᵉ = map-equivᵉ compute-eq-coproduct-inr-inlᵉ

  module _
    (xᵉ yᵉ : Bᵉ)
    where

    map-compute-Eq-coproduct-inr-inrᵉ :
      Eq-coproductᵉ {Aᵉ = Aᵉ} (inrᵉ xᵉ) (inrᵉ yᵉ) → xᵉ ＝ᵉ yᵉ
    map-compute-Eq-coproduct-inr-inrᵉ (Eq-eq-coproduct-inrᵉ pᵉ) = pᵉ

    is-section-Eq-eq-coproduct-inrᵉ :
      (map-compute-Eq-coproduct-inr-inrᵉ ∘ᵉ Eq-eq-coproduct-inrᵉ) ~ᵉ idᵉ
    is-section-Eq-eq-coproduct-inrᵉ pᵉ = reflᵉ

    is-retraction-Eq-eq-coproduct-inrᵉ :
      (Eq-eq-coproduct-inrᵉ ∘ᵉ map-compute-Eq-coproduct-inr-inrᵉ) ~ᵉ idᵉ
    is-retraction-Eq-eq-coproduct-inrᵉ (Eq-eq-coproduct-inrᵉ pᵉ) = reflᵉ

    is-equiv-map-compute-Eq-coproduct-inr-inrᵉ :
      is-equivᵉ map-compute-Eq-coproduct-inr-inrᵉ
    is-equiv-map-compute-Eq-coproduct-inr-inrᵉ =
      is-equiv-is-invertibleᵉ
        ( Eq-eq-coproduct-inrᵉ)
        ( is-section-Eq-eq-coproduct-inrᵉ)
        ( is-retraction-Eq-eq-coproduct-inrᵉ)

    compute-Eq-coproduct-inr-inrᵉ : Eq-coproductᵉ (inrᵉ xᵉ) (inrᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ yᵉ)
    pr1ᵉ compute-Eq-coproduct-inr-inrᵉ = map-compute-Eq-coproduct-inr-inrᵉ
    pr2ᵉ compute-Eq-coproduct-inr-inrᵉ = is-equiv-map-compute-Eq-coproduct-inr-inrᵉ

    compute-eq-coproduct-inr-inrᵉ : Idᵉ {Aᵉ = Aᵉ +ᵉ Bᵉ} (inrᵉ xᵉ) (inrᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ yᵉ)
    compute-eq-coproduct-inr-inrᵉ =
      compute-Eq-coproduct-inr-inrᵉ ∘eᵉ extensionality-coproductᵉ (inrᵉ xᵉ) (inrᵉ yᵉ)

    map-compute-eq-coproduct-inr-inrᵉ : Idᵉ {Aᵉ = Aᵉ +ᵉ Bᵉ} (inrᵉ xᵉ) (inrᵉ yᵉ) → xᵉ ＝ᵉ yᵉ
    map-compute-eq-coproduct-inr-inrᵉ = map-equivᵉ compute-eq-coproduct-inr-inrᵉ
```

### The left and right inclusions into a coproduct are embeddings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  abstract
    is-emb-inlᵉ : is-embᵉ (inlᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ})
    is-emb-inlᵉ xᵉ =
      fundamental-theorem-idᵉ
        ( is-contr-equivᵉ
          ( Σᵉ Aᵉ (Idᵉ xᵉ))
          ( equiv-totᵉ (compute-eq-coproduct-inl-inlᵉ xᵉ))
          ( is-torsorial-Idᵉ xᵉ))
        ( λ yᵉ → apᵉ inlᵉ)

  emb-inlᵉ : Aᵉ ↪ᵉ (Aᵉ +ᵉ Bᵉ)
  pr1ᵉ emb-inlᵉ = inlᵉ
  pr2ᵉ emb-inlᵉ = is-emb-inlᵉ

  abstract
    is-emb-inrᵉ : is-embᵉ (inrᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ})
    is-emb-inrᵉ xᵉ =
      fundamental-theorem-idᵉ
        ( is-contr-equivᵉ
          ( Σᵉ Bᵉ (Idᵉ xᵉ))
          ( equiv-totᵉ (compute-eq-coproduct-inr-inrᵉ xᵉ))
          ( is-torsorial-Idᵉ xᵉ))
        ( λ yᵉ → apᵉ inrᵉ)

  emb-inrᵉ : Bᵉ ↪ᵉ (Aᵉ +ᵉ Bᵉ)
  pr1ᵉ emb-inrᵉ = inrᵉ
  pr2ᵉ emb-inrᵉ = is-emb-inrᵉ
```

Moreover,ᵉ `is-injective-inl`ᵉ andᵉ `is-injective-inr`ᵉ areᵉ theᵉ inverses.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-retraction-is-injective-inlᵉ :
    {xᵉ yᵉ : Aᵉ} →
    is-retractionᵉ (apᵉ (inlᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ}) {xᵉ} {yᵉ}) (is-injective-inlᵉ)
  is-retraction-is-injective-inlᵉ reflᵉ = reflᵉ

  is-section-is-injective-inlᵉ :
    {xᵉ yᵉ : Aᵉ} →
    is-sectionᵉ (apᵉ (inlᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ}) {xᵉ} {yᵉ}) (is-injective-inlᵉ)
  is-section-is-injective-inlᵉ reflᵉ = reflᵉ

  is-retraction-is-injective-inrᵉ :
    {xᵉ yᵉ : Bᵉ} →
    is-retractionᵉ (apᵉ (inrᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ}) {xᵉ} {yᵉ}) (is-injective-inrᵉ)
  is-retraction-is-injective-inrᵉ reflᵉ = reflᵉ

  is-section-is-injective-inrᵉ :
    {xᵉ yᵉ : Bᵉ} →
    is-sectionᵉ (apᵉ (inrᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ}) {xᵉ} {yᵉ}) (is-injective-inrᵉ)
  is-section-is-injective-inrᵉ reflᵉ = reflᵉ
```

### A map `A + B → C` defined by maps `f : A → C` and `B → C` is an embedding if both `f` and `g` are embeddings and they don't overlap

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {fᵉ : Aᵉ → Cᵉ} {gᵉ : Bᵉ → Cᵉ}
  where

  is-emb-coproductᵉ :
    is-embᵉ fᵉ → is-embᵉ gᵉ → ((aᵉ : Aᵉ) (bᵉ : Bᵉ) → fᵉ aᵉ ≠ᵉ gᵉ bᵉ) →
    is-embᵉ (rec-coproductᵉ fᵉ gᵉ)
  is-emb-coproductᵉ Hᵉ Kᵉ Lᵉ (inlᵉ aᵉ) (inlᵉ a'ᵉ) =
    is-equiv-right-map-triangleᵉ
      ( apᵉ fᵉ)
      ( apᵉ (rec-coproductᵉ fᵉ gᵉ))
      ( apᵉ inlᵉ)
      ( ap-compᵉ (rec-coproductᵉ fᵉ gᵉ) inlᵉ)
      ( Hᵉ aᵉ a'ᵉ)
      ( is-emb-inlᵉ Aᵉ Bᵉ aᵉ a'ᵉ)
  is-emb-coproductᵉ Hᵉ Kᵉ Lᵉ (inlᵉ aᵉ) (inrᵉ b'ᵉ) =
    is-equiv-is-emptyᵉ (apᵉ (rec-coproductᵉ fᵉ gᵉ)) (Lᵉ aᵉ b'ᵉ)
  is-emb-coproductᵉ Hᵉ Kᵉ Lᵉ (inrᵉ bᵉ) (inlᵉ a'ᵉ) =
    is-equiv-is-emptyᵉ (apᵉ (rec-coproductᵉ fᵉ gᵉ)) (Lᵉ a'ᵉ bᵉ ∘ᵉ invᵉ)
  is-emb-coproductᵉ Hᵉ Kᵉ Lᵉ (inrᵉ bᵉ) (inrᵉ b'ᵉ) =
    is-equiv-right-map-triangleᵉ
      ( apᵉ gᵉ)
      ( apᵉ (rec-coproductᵉ fᵉ gᵉ))
      ( apᵉ inrᵉ)
      ( ap-compᵉ (rec-coproductᵉ fᵉ gᵉ) inrᵉ)
      ( Kᵉ bᵉ b'ᵉ)
      ( is-emb-inrᵉ Aᵉ Bᵉ bᵉ b'ᵉ)
```

### Coproducts of `k+2`-truncated types are `k+2`-truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-trunc-coproductᵉ :
      is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) Aᵉ → is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) Bᵉ →
      is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) (Aᵉ +ᵉ Bᵉ)
    is-trunc-coproductᵉ is-trunc-Aᵉ is-trunc-Bᵉ (inlᵉ xᵉ) (inlᵉ yᵉ) =
      is-trunc-equivᵉ (succ-𝕋ᵉ kᵉ)
        ( xᵉ ＝ᵉ yᵉ)
        ( compute-eq-coproduct-inl-inlᵉ xᵉ yᵉ)
        ( is-trunc-Aᵉ xᵉ yᵉ)
    is-trunc-coproductᵉ is-trunc-Aᵉ is-trunc-Bᵉ (inlᵉ xᵉ) (inrᵉ yᵉ) =
      is-trunc-is-emptyᵉ kᵉ (is-empty-eq-coproduct-inl-inrᵉ xᵉ yᵉ)
    is-trunc-coproductᵉ is-trunc-Aᵉ is-trunc-Bᵉ (inrᵉ xᵉ) (inlᵉ yᵉ) =
      is-trunc-is-emptyᵉ kᵉ (is-empty-eq-coproduct-inr-inlᵉ xᵉ yᵉ)
    is-trunc-coproductᵉ is-trunc-Aᵉ is-trunc-Bᵉ (inrᵉ xᵉ) (inrᵉ yᵉ) =
      is-trunc-equivᵉ (succ-𝕋ᵉ kᵉ)
        ( xᵉ ＝ᵉ yᵉ)
        ( compute-eq-coproduct-inr-inrᵉ xᵉ yᵉ)
        ( is-trunc-Bᵉ xᵉ yᵉ)
```

### Coproducts of sets are sets

```agda
abstract
  is-set-coproductᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    is-setᵉ Aᵉ → is-setᵉ Bᵉ → is-setᵉ (Aᵉ +ᵉ Bᵉ)
  is-set-coproductᵉ = is-trunc-coproductᵉ neg-two-𝕋ᵉ

coproduct-Setᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ) (Bᵉ : Setᵉ l2ᵉ) → Setᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (coproduct-Setᵉ (Aᵉ ,ᵉ is-set-Aᵉ) (Bᵉ ,ᵉ is-set-Bᵉ)) = Aᵉ +ᵉ Bᵉ
pr2ᵉ (coproduct-Setᵉ (Aᵉ ,ᵉ is-set-Aᵉ) (Bᵉ ,ᵉ is-set-Bᵉ)) =
  is-set-coproductᵉ is-set-Aᵉ is-set-Bᵉ
```

## See also

-ᵉ Equalityᵉ proofsᵉ in coproductᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-coproduct-types`](foundation.equality-coproduct-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in dependentᵉ pairᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).ᵉ