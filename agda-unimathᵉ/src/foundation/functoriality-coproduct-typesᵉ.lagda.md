# Functoriality of coproduct types

```agda
module foundation.functoriality-coproduct-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.equality-coproduct-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.negated-equalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.surjective-mapsᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-coproduct-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.negationᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Anyᵉ twoᵉ mapsᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ `gᵉ : Cᵉ → D`ᵉ induceᵉ aᵉ mapᵉ
`map-coproductᵉ fᵉ gᵉ : coproductᵉ Aᵉ Bᵉ → coproductᵉ Cᵉ D`.ᵉ

## Definitions

### The functorial action of the coproduct operation

```agda
module _
  {l1ᵉ l2ᵉ l1'ᵉ l2'ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ}
  where

  map-coproductᵉ : (Aᵉ → A'ᵉ) → (Bᵉ → B'ᵉ) → Aᵉ +ᵉ Bᵉ → A'ᵉ +ᵉ B'ᵉ
  map-coproductᵉ fᵉ gᵉ (inlᵉ xᵉ) = inlᵉ (fᵉ xᵉ)
  map-coproductᵉ fᵉ gᵉ (inrᵉ yᵉ) = inrᵉ (gᵉ yᵉ)
```

## Properties

### Functoriality of coproducts preserves identity maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  id-map-coproductᵉ : (map-coproductᵉ (idᵉ {Aᵉ = Aᵉ}) (idᵉ {Aᵉ = Bᵉ})) ~ᵉ idᵉ
  id-map-coproductᵉ (inlᵉ xᵉ) = reflᵉ
  id-map-coproductᵉ (inrᵉ xᵉ) = reflᵉ
```

### Functoriality of coproducts preserves composition

```agda
module _
  {l1ᵉ l2ᵉ l1'ᵉ l2'ᵉ l1''ᵉ l2''ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ}
  {A''ᵉ : UUᵉ l1''ᵉ} {B''ᵉ : UUᵉ l2''ᵉ}
  (fᵉ : Aᵉ → A'ᵉ) (f'ᵉ : A'ᵉ → A''ᵉ) (gᵉ : Bᵉ → B'ᵉ) (g'ᵉ : B'ᵉ → B''ᵉ)
  where

  preserves-comp-map-coproductᵉ :
    map-coproductᵉ (f'ᵉ ∘ᵉ fᵉ) (g'ᵉ ∘ᵉ gᵉ) ~ᵉ map-coproductᵉ f'ᵉ g'ᵉ ∘ᵉ map-coproductᵉ fᵉ gᵉ
  preserves-comp-map-coproductᵉ (inlᵉ xᵉ) = reflᵉ
  preserves-comp-map-coproductᵉ (inrᵉ yᵉ) = reflᵉ
```

### Functoriality of coproducts preserves homotopies

```agda
module _
  {l1ᵉ l2ᵉ l1'ᵉ l2'ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ}
  {fᵉ f'ᵉ : Aᵉ → A'ᵉ} (Hᵉ : fᵉ ~ᵉ f'ᵉ) {gᵉ g'ᵉ : Bᵉ → B'ᵉ} (Kᵉ : gᵉ ~ᵉ g'ᵉ)
  where

  htpy-map-coproductᵉ : map-coproductᵉ fᵉ gᵉ ~ᵉ map-coproductᵉ f'ᵉ g'ᵉ
  htpy-map-coproductᵉ (inlᵉ xᵉ) = apᵉ inlᵉ (Hᵉ xᵉ)
  htpy-map-coproductᵉ (inrᵉ yᵉ) = apᵉ inrᵉ (Kᵉ yᵉ)
```

### The fibers of `map-coproduct`

```agda
module _
  {l1ᵉ l2ᵉ l1'ᵉ l2'ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ}
  (fᵉ : A'ᵉ → Aᵉ) (gᵉ : B'ᵉ → Bᵉ)
  where

  fiber-map-coproduct-inl-fiberᵉ :
    (xᵉ : Aᵉ) → fiberᵉ fᵉ xᵉ → fiberᵉ (map-coproductᵉ fᵉ gᵉ) (inlᵉ xᵉ)
  pr1ᵉ (fiber-map-coproduct-inl-fiberᵉ xᵉ (a'ᵉ ,ᵉ pᵉ)) = inlᵉ a'ᵉ
  pr2ᵉ (fiber-map-coproduct-inl-fiberᵉ xᵉ (a'ᵉ ,ᵉ pᵉ)) = apᵉ inlᵉ pᵉ

  fiber-fiber-map-coproduct-inlᵉ :
    (xᵉ : Aᵉ) → fiberᵉ (map-coproductᵉ fᵉ gᵉ) (inlᵉ xᵉ) → fiberᵉ fᵉ xᵉ
  pr1ᵉ (fiber-fiber-map-coproduct-inlᵉ xᵉ (inlᵉ a'ᵉ ,ᵉ pᵉ)) = a'ᵉ
  pr2ᵉ (fiber-fiber-map-coproduct-inlᵉ xᵉ (inlᵉ a'ᵉ ,ᵉ pᵉ)) =
    map-compute-eq-coproduct-inl-inlᵉ (fᵉ a'ᵉ) xᵉ pᵉ
  fiber-fiber-map-coproduct-inlᵉ xᵉ (inrᵉ b'ᵉ ,ᵉ pᵉ) =
    ex-falsoᵉ (is-empty-eq-coproduct-inr-inlᵉ (gᵉ b'ᵉ) xᵉ pᵉ)

  abstract
    is-section-fiber-fiber-map-coproduct-inlᵉ :
      (xᵉ : Aᵉ) →
      fiber-map-coproduct-inl-fiberᵉ xᵉ ∘ᵉ fiber-fiber-map-coproduct-inlᵉ xᵉ ~ᵉ idᵉ
    is-section-fiber-fiber-map-coproduct-inlᵉ .(fᵉ a'ᵉ) (inlᵉ a'ᵉ ,ᵉ reflᵉ) = reflᵉ
    is-section-fiber-fiber-map-coproduct-inlᵉ xᵉ (inrᵉ b'ᵉ ,ᵉ pᵉ) =
      ex-falsoᵉ (is-empty-eq-coproduct-inr-inlᵉ (gᵉ b'ᵉ) xᵉ pᵉ)

  abstract
    is-retraction-fiber-fiber-map-coproduct-inlᵉ :
      (xᵉ : Aᵉ) →
      fiber-fiber-map-coproduct-inlᵉ xᵉ ∘ᵉ fiber-map-coproduct-inl-fiberᵉ xᵉ ~ᵉ idᵉ
    is-retraction-fiber-fiber-map-coproduct-inlᵉ .(fᵉ a'ᵉ) (a'ᵉ ,ᵉ reflᵉ) = reflᵉ

  abstract
    is-equiv-fiber-map-coproduct-inl-fiberᵉ :
      (xᵉ : Aᵉ) → is-equivᵉ (fiber-map-coproduct-inl-fiberᵉ xᵉ)
    is-equiv-fiber-map-coproduct-inl-fiberᵉ xᵉ =
      is-equiv-is-invertibleᵉ
        ( fiber-fiber-map-coproduct-inlᵉ xᵉ)
        ( is-section-fiber-fiber-map-coproduct-inlᵉ xᵉ)
        ( is-retraction-fiber-fiber-map-coproduct-inlᵉ xᵉ)

  fiber-map-coproduct-inr-fiberᵉ :
    (yᵉ : Bᵉ) → fiberᵉ gᵉ yᵉ → fiberᵉ (map-coproductᵉ fᵉ gᵉ) (inrᵉ yᵉ)
  pr1ᵉ (fiber-map-coproduct-inr-fiberᵉ yᵉ (b'ᵉ ,ᵉ pᵉ)) = inrᵉ b'ᵉ
  pr2ᵉ (fiber-map-coproduct-inr-fiberᵉ yᵉ (b'ᵉ ,ᵉ pᵉ)) = apᵉ inrᵉ pᵉ

  fiber-fiber-map-coproduct-inrᵉ :
    (yᵉ : Bᵉ) → fiberᵉ (map-coproductᵉ fᵉ gᵉ) (inrᵉ yᵉ) → fiberᵉ gᵉ yᵉ
  fiber-fiber-map-coproduct-inrᵉ yᵉ (inlᵉ a'ᵉ ,ᵉ pᵉ) =
    ex-falsoᵉ (is-empty-eq-coproduct-inl-inrᵉ (fᵉ a'ᵉ) yᵉ pᵉ)
  pr1ᵉ (fiber-fiber-map-coproduct-inrᵉ yᵉ (inrᵉ b'ᵉ ,ᵉ pᵉ)) = b'ᵉ
  pr2ᵉ (fiber-fiber-map-coproduct-inrᵉ yᵉ (inrᵉ b'ᵉ ,ᵉ pᵉ)) =
    map-compute-eq-coproduct-inr-inrᵉ (gᵉ b'ᵉ) yᵉ pᵉ

  abstract
    is-section-fiber-fiber-map-coproduct-inrᵉ :
      (yᵉ : Bᵉ) →
      (fiber-map-coproduct-inr-fiberᵉ yᵉ ∘ᵉ fiber-fiber-map-coproduct-inrᵉ yᵉ) ~ᵉ idᵉ
    is-section-fiber-fiber-map-coproduct-inrᵉ .(gᵉ b'ᵉ) (inrᵉ b'ᵉ ,ᵉ reflᵉ) = reflᵉ
    is-section-fiber-fiber-map-coproduct-inrᵉ yᵉ (inlᵉ a'ᵉ ,ᵉ pᵉ) =
      ex-falsoᵉ (is-empty-eq-coproduct-inl-inrᵉ (fᵉ a'ᵉ) yᵉ pᵉ)

  abstract
    is-retraction-fiber-fiber-map-coproduct-inrᵉ :
      (yᵉ : Bᵉ) →
      (fiber-fiber-map-coproduct-inrᵉ yᵉ ∘ᵉ fiber-map-coproduct-inr-fiberᵉ yᵉ) ~ᵉ idᵉ
    is-retraction-fiber-fiber-map-coproduct-inrᵉ .(gᵉ b'ᵉ) (b'ᵉ ,ᵉ reflᵉ) = reflᵉ

  abstract
    is-equiv-fiber-map-coproduct-inr-fiberᵉ :
      (yᵉ : Bᵉ) → is-equivᵉ (fiber-map-coproduct-inr-fiberᵉ yᵉ)
    is-equiv-fiber-map-coproduct-inr-fiberᵉ yᵉ =
      is-equiv-is-invertibleᵉ
        ( fiber-fiber-map-coproduct-inrᵉ yᵉ)
        ( is-section-fiber-fiber-map-coproduct-inrᵉ yᵉ)
        ( is-retraction-fiber-fiber-map-coproduct-inrᵉ yᵉ)
```

### Functoriality of coproducts preserves equivalences

```agda
module _
  {l1ᵉ l2ᵉ l1'ᵉ l2'ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ}
  where

  abstract
    is-equiv-map-coproductᵉ :
      {fᵉ : Aᵉ → A'ᵉ} {gᵉ : Bᵉ → B'ᵉ} →
      is-equivᵉ fᵉ → is-equivᵉ gᵉ → is-equivᵉ (map-coproductᵉ fᵉ gᵉ)
    pr1ᵉ
      ( pr1ᵉ
        ( is-equiv-map-coproductᵉ
          ( (sfᵉ ,ᵉ Sfᵉ) ,ᵉ (rfᵉ ,ᵉ Rfᵉ))
          ( (sgᵉ ,ᵉ Sgᵉ) ,ᵉ (rgᵉ ,ᵉ Rgᵉ)))) = map-coproductᵉ sfᵉ sgᵉ
    pr2ᵉ
      ( pr1ᵉ
        ( is-equiv-map-coproductᵉ {fᵉ} {gᵉ}
          ( (sfᵉ ,ᵉ Sfᵉ) ,ᵉ (rfᵉ ,ᵉ Rfᵉ))
          ( (sgᵉ ,ᵉ Sgᵉ) ,ᵉ (rgᵉ ,ᵉ Rgᵉ)))) =
      ( ( inv-htpyᵉ (preserves-comp-map-coproductᵉ sfᵉ fᵉ sgᵉ gᵉ)) ∙hᵉ
        ( htpy-map-coproductᵉ Sfᵉ Sgᵉ)) ∙hᵉ
      ( id-map-coproductᵉ A'ᵉ B'ᵉ)
    pr1ᵉ
      ( pr2ᵉ
        ( is-equiv-map-coproductᵉ
          ( (sfᵉ ,ᵉ Sfᵉ) ,ᵉ (rfᵉ ,ᵉ Rfᵉ))
          ( (sgᵉ ,ᵉ Sgᵉ) ,ᵉ (rgᵉ ,ᵉ Rgᵉ)))) = map-coproductᵉ rfᵉ rgᵉ
    pr2ᵉ
      ( pr2ᵉ
        ( is-equiv-map-coproductᵉ {fᵉ} {gᵉ}
          ( (sfᵉ ,ᵉ Sfᵉ) ,ᵉ (rfᵉ ,ᵉ Rfᵉ))
          ( (sgᵉ ,ᵉ Sgᵉ) ,ᵉ (rgᵉ ,ᵉ Rgᵉ)))) =
      ( ( inv-htpyᵉ (preserves-comp-map-coproductᵉ fᵉ rfᵉ gᵉ rgᵉ)) ∙hᵉ
        ( htpy-map-coproductᵉ Rfᵉ Rgᵉ)) ∙hᵉ
      ( id-map-coproductᵉ Aᵉ Bᵉ)

  map-equiv-coproductᵉ : Aᵉ ≃ᵉ A'ᵉ → Bᵉ ≃ᵉ B'ᵉ → Aᵉ +ᵉ Bᵉ → A'ᵉ +ᵉ B'ᵉ
  map-equiv-coproductᵉ eᵉ e'ᵉ = map-coproductᵉ (map-equivᵉ eᵉ) (map-equivᵉ e'ᵉ)

  equiv-coproductᵉ : Aᵉ ≃ᵉ A'ᵉ → Bᵉ ≃ᵉ B'ᵉ → (Aᵉ +ᵉ Bᵉ) ≃ᵉ (A'ᵉ +ᵉ B'ᵉ)
  pr1ᵉ (equiv-coproductᵉ eᵉ e'ᵉ) = map-equiv-coproductᵉ eᵉ e'ᵉ
  pr2ᵉ (equiv-coproductᵉ eᵉ e'ᵉ) =
    is-equiv-map-coproductᵉ (is-equiv-map-equivᵉ eᵉ) (is-equiv-map-equivᵉ e'ᵉ)
```

### Functoriality of coproducts preserves being surjective

```agda
module _
  {l1ᵉ l2ᵉ l1'ᵉ l2'ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ}
  where

  abstract
    is-surjective-map-coproductᵉ :
      {fᵉ : Aᵉ → A'ᵉ} {gᵉ : Bᵉ → B'ᵉ} →
      is-surjectiveᵉ fᵉ → is-surjectiveᵉ gᵉ →
      is-surjectiveᵉ (map-coproductᵉ fᵉ gᵉ)
    is-surjective-map-coproductᵉ sᵉ s'ᵉ (inlᵉ xᵉ) =
      apply-universal-property-trunc-Propᵉ (sᵉ xᵉ)
        ( trunc-Propᵉ (fiberᵉ (map-coproductᵉ _ _) (inlᵉ xᵉ)))
        ( λ (aᵉ ,ᵉ pᵉ) → unit-trunc-Propᵉ (inlᵉ aᵉ ,ᵉ apᵉ inlᵉ pᵉ))
    is-surjective-map-coproductᵉ sᵉ s'ᵉ (inrᵉ xᵉ) =
      apply-universal-property-trunc-Propᵉ (s'ᵉ xᵉ)
        ( trunc-Propᵉ (fiberᵉ (map-coproductᵉ _ _) (inrᵉ xᵉ)))
        ( λ (aᵉ ,ᵉ pᵉ) → unit-trunc-Propᵉ (inrᵉ aᵉ ,ᵉ apᵉ inrᵉ pᵉ))
```

### For any two maps `f : A → B` and `g : C → D`, there is at most one pair of maps `f' : A → B` and `g' : C → D` such that `f' + g' = f + g`

```agda
is-contr-fiber-map-coproductᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Cᵉ → Dᵉ) →
  is-contrᵉ
    ( fiberᵉ
      ( λ (fg'ᵉ : (Aᵉ → Bᵉ) ×ᵉ (Cᵉ → Dᵉ)) → map-coproductᵉ (pr1ᵉ fg'ᵉ) (pr2ᵉ fg'ᵉ))
      ( map-coproductᵉ fᵉ gᵉ))
is-contr-fiber-map-coproductᵉ {Aᵉ = Aᵉ} {Bᵉ} {Cᵉ} {Dᵉ} fᵉ gᵉ =
  is-contr-equivᵉ
    ( Σᵉ ( (Aᵉ → Bᵉ) ×ᵉ (Cᵉ → Dᵉ))
        ( λ fg'ᵉ →
          ((aᵉ : Aᵉ) → pr1ᵉ fg'ᵉ aᵉ ＝ᵉ fᵉ aᵉ) ×ᵉ ((cᵉ : Cᵉ) → pr2ᵉ fg'ᵉ cᵉ ＝ᵉ gᵉ cᵉ)))
    ( equiv-totᵉ
      ( λ fg'ᵉ →
        ( equiv-productᵉ
          ( equiv-Π-equiv-familyᵉ
            ( λ aᵉ → compute-eq-coproduct-inl-inlᵉ (pr1ᵉ fg'ᵉ aᵉ) (fᵉ aᵉ)))
          ( equiv-Π-equiv-familyᵉ
            ( λ cᵉ → compute-eq-coproduct-inr-inrᵉ (pr2ᵉ fg'ᵉ cᵉ) (gᵉ cᵉ)))) ∘eᵉ
        ( equiv-dependent-universal-property-coproductᵉ
          ( λ xᵉ → map-coproductᵉ (pr1ᵉ fg'ᵉ) (pr2ᵉ fg'ᵉ) xᵉ ＝ᵉ map-coproductᵉ fᵉ gᵉ xᵉ)) ∘eᵉ
        ( equiv-funextᵉ)))
    ( is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpy'ᵉ fᵉ)
      ( fᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-htpy'ᵉ gᵉ))
```

### For any equivalence `f : A + B ≃ A + B` and `g : B ≃ B` such that `f` and `g` coincide on `B`, we construct an `h : A ≃ A` such that `htpy-equiv (equiv-coproduct h d) f`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  equiv-coproduct-induce-equiv-disjointᵉ :
    (fᵉ : (Aᵉ +ᵉ Bᵉ) ≃ᵉ (Aᵉ +ᵉ Bᵉ)) (gᵉ : Bᵉ ≃ᵉ Bᵉ)
    (pᵉ : (bᵉ : Bᵉ) → map-equivᵉ fᵉ (inrᵉ bᵉ) ＝ᵉ inrᵉ (map-equivᵉ gᵉ bᵉ))
    (xᵉ : Aᵉ) (yᵉ : Bᵉ) → map-equivᵉ fᵉ (inlᵉ xᵉ) ≠ᵉ inrᵉ yᵉ
  equiv-coproduct-induce-equiv-disjointᵉ fᵉ gᵉ pᵉ xᵉ yᵉ qᵉ =
    neq-inr-inlᵉ
      ( is-injective-equivᵉ fᵉ
        ( ( pᵉ (map-equivᵉ (inv-equivᵉ gᵉ) yᵉ) ∙ᵉ
          ( ( apᵉ (λ zᵉ → inrᵉ (map-equivᵉ zᵉ yᵉ)) (right-inverse-law-equivᵉ gᵉ)) ∙ᵉ
            ( invᵉ qᵉ)))))

  inv-commutative-square-inrᵉ :
    (fᵉ : (Aᵉ +ᵉ Bᵉ) ≃ᵉ (Aᵉ +ᵉ Bᵉ)) (gᵉ : Bᵉ ≃ᵉ Bᵉ)
    (pᵉ : (bᵉ : Bᵉ) → map-equivᵉ fᵉ (inrᵉ bᵉ) ＝ᵉ inrᵉ (map-equivᵉ gᵉ bᵉ)) →
    (bᵉ : Bᵉ) → map-inv-equivᵉ fᵉ (inrᵉ bᵉ) ＝ᵉ inrᵉ (map-inv-equivᵉ gᵉ bᵉ)
  inv-commutative-square-inrᵉ fᵉ gᵉ pᵉ bᵉ =
    is-injective-equivᵉ fᵉ
      ( ( apᵉ (λ zᵉ → map-equivᵉ zᵉ (inrᵉ bᵉ)) (right-inverse-law-equivᵉ fᵉ)) ∙ᵉ
        ( invᵉ (apᵉ (λ zᵉ → inrᵉ (map-equivᵉ zᵉ bᵉ)) (right-inverse-law-equivᵉ gᵉ))) ∙ᵉ
        ( invᵉ (pᵉ (map-inv-equivᵉ gᵉ bᵉ))))

  cases-retraction-equiv-coproductᵉ :
    (fᵉ : (Aᵉ +ᵉ Bᵉ) ≃ᵉ (Aᵉ +ᵉ Bᵉ)) (gᵉ : Bᵉ ≃ᵉ Bᵉ)
    (pᵉ : (bᵉ : Bᵉ) → map-equivᵉ fᵉ (inrᵉ bᵉ) ＝ᵉ inrᵉ (map-equivᵉ gᵉ bᵉ))
    (xᵉ : Aᵉ) (yᵉ : Aᵉ +ᵉ Bᵉ) → map-equivᵉ fᵉ (inlᵉ xᵉ) ＝ᵉ yᵉ → Aᵉ
  cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ (inlᵉ yᵉ) qᵉ = yᵉ
  cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ (inrᵉ yᵉ) qᵉ =
    ex-falsoᵉ (equiv-coproduct-induce-equiv-disjointᵉ fᵉ gᵉ pᵉ xᵉ yᵉ qᵉ)

  inv-cases-retraction-equiv-coproductᵉ :
    (fᵉ : (Aᵉ +ᵉ Bᵉ) ≃ᵉ (Aᵉ +ᵉ Bᵉ)) (gᵉ : Bᵉ ≃ᵉ Bᵉ)
    (pᵉ : (bᵉ : Bᵉ) → map-equivᵉ fᵉ (inrᵉ bᵉ) ＝ᵉ inrᵉ (map-equivᵉ gᵉ bᵉ))
    (xᵉ : Aᵉ) (yᵉ : Aᵉ +ᵉ Bᵉ) → map-inv-equivᵉ fᵉ (inlᵉ xᵉ) ＝ᵉ yᵉ → Aᵉ
  inv-cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ =
    cases-retraction-equiv-coproductᵉ
      ( inv-equivᵉ fᵉ)
      ( inv-equivᵉ gᵉ)
      ( inv-commutative-square-inrᵉ fᵉ gᵉ pᵉ)

  retraction-cases-retraction-equiv-coproductᵉ :
    ( fᵉ : (Aᵉ +ᵉ Bᵉ) ≃ᵉ (Aᵉ +ᵉ Bᵉ)) (gᵉ : Bᵉ ≃ᵉ Bᵉ)
    ( pᵉ : (bᵉ : Bᵉ) → map-equivᵉ fᵉ (inrᵉ bᵉ) ＝ᵉ inrᵉ (map-equivᵉ gᵉ bᵉ))
    ( xᵉ : Aᵉ) (yᵉ zᵉ : Aᵉ +ᵉ Bᵉ) (qᵉ : map-equivᵉ fᵉ (inlᵉ xᵉ) ＝ᵉ yᵉ)
    ( rᵉ :
      ( map-inv-equivᵉ fᵉ (inlᵉ (cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ yᵉ qᵉ))) ＝ᵉ
      ( zᵉ)) →
    ( inv-cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ
      ( cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ yᵉ qᵉ) zᵉ rᵉ) ＝ᵉ
    ( xᵉ)
  retraction-cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ (inlᵉ yᵉ) (inlᵉ zᵉ) qᵉ rᵉ =
    is-injective-inlᵉ
      ( ( invᵉ rᵉ) ∙ᵉ
        ( ( apᵉ (map-inv-equivᵉ fᵉ) (invᵉ qᵉ)) ∙ᵉ
          ( apᵉ (λ wᵉ → map-equivᵉ wᵉ (inlᵉ xᵉ)) (left-inverse-law-equivᵉ fᵉ))))
  retraction-cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ (inlᵉ yᵉ) (inrᵉ zᵉ) qᵉ rᵉ =
    ex-falsoᵉ
      ( equiv-coproduct-induce-equiv-disjointᵉ
        ( inv-equivᵉ fᵉ)
        ( inv-equivᵉ gᵉ)
        ( inv-commutative-square-inrᵉ fᵉ gᵉ pᵉ)
        ( yᵉ)
        ( zᵉ)
        ( rᵉ))
  retraction-cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ (inrᵉ yᵉ) zᵉ qᵉ rᵉ =
    ex-falsoᵉ (equiv-coproduct-induce-equiv-disjointᵉ fᵉ gᵉ pᵉ xᵉ yᵉ qᵉ)

  section-cases-retraction-equiv-coproductᵉ :
    ( fᵉ : (Aᵉ +ᵉ Bᵉ) ≃ᵉ (Aᵉ +ᵉ Bᵉ)) (gᵉ : Bᵉ ≃ᵉ Bᵉ)
    ( pᵉ : (bᵉ : Bᵉ) → map-equivᵉ fᵉ (inrᵉ bᵉ) ＝ᵉ inrᵉ (map-equivᵉ gᵉ bᵉ))
    ( xᵉ : Aᵉ) (yᵉ zᵉ : Aᵉ +ᵉ Bᵉ) (qᵉ : map-inv-equivᵉ fᵉ (inlᵉ xᵉ) ＝ᵉ yᵉ)
    ( rᵉ :
      ( map-equivᵉ fᵉ (inlᵉ (inv-cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ yᵉ qᵉ))) ＝ᵉ
      ( zᵉ)) →
    ( cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ
      ( inv-cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ yᵉ qᵉ) zᵉ rᵉ) ＝ᵉ
    ( xᵉ)
  section-cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ (inlᵉ yᵉ) (inlᵉ zᵉ) qᵉ rᵉ =
    is-injective-inlᵉ
      ( ( invᵉ rᵉ) ∙ᵉ
        ( apᵉ (map-equivᵉ fᵉ) (invᵉ qᵉ)) ∙ᵉ
        ( apᵉ (λ wᵉ → map-equivᵉ wᵉ (inlᵉ xᵉ)) (right-inverse-law-equivᵉ fᵉ)))
  section-cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ (inlᵉ yᵉ) (inrᵉ zᵉ) qᵉ rᵉ =
    ex-falsoᵉ (equiv-coproduct-induce-equiv-disjointᵉ fᵉ gᵉ pᵉ yᵉ zᵉ rᵉ)
  section-cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ (inrᵉ yᵉ) zᵉ qᵉ rᵉ =
    ex-falsoᵉ
      ( equiv-coproduct-induce-equiv-disjointᵉ
        ( inv-equivᵉ fᵉ)
        ( inv-equivᵉ gᵉ)
        ( inv-commutative-square-inrᵉ fᵉ gᵉ pᵉ)
        ( xᵉ)
        ( yᵉ)
        ( qᵉ))

  retraction-equiv-coproductᵉ :
    (fᵉ : (Aᵉ +ᵉ Bᵉ) ≃ᵉ (Aᵉ +ᵉ Bᵉ)) (gᵉ : Bᵉ ≃ᵉ Bᵉ)
    (pᵉ : (bᵉ : Bᵉ) → map-equivᵉ fᵉ (inrᵉ bᵉ) ＝ᵉ inrᵉ (map-equivᵉ gᵉ bᵉ)) →
    Σᵉ (Aᵉ ≃ᵉ Aᵉ) (λ hᵉ → htpy-equivᵉ fᵉ (equiv-coproductᵉ hᵉ gᵉ))
  pr1ᵉ (pr1ᵉ (retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ)) xᵉ =
    cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ (map-equivᵉ fᵉ (inlᵉ xᵉ)) reflᵉ
  pr2ᵉ (pr1ᵉ (retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ)) =
    is-equiv-is-invertibleᵉ
      ( λ xᵉ →
        inv-cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ
          ( map-inv-equivᵉ fᵉ (inlᵉ xᵉ))
          ( reflᵉ))
      ( λ xᵉ →
        section-cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ
          ( map-inv-equivᵉ fᵉ (inlᵉ xᵉ))
          ( map-equivᵉ fᵉ
            ( inlᵉ
              ( inv-cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ
                ( map-inv-equivᵉ fᵉ (inlᵉ xᵉ))
                ( reflᵉ))))
          ( reflᵉ)
          ( reflᵉ))
      ( λ xᵉ →
        retraction-cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ
          ( map-equivᵉ fᵉ (inlᵉ xᵉ))
          ( map-inv-equivᵉ fᵉ
            ( inlᵉ
              ( cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ
                ( map-equivᵉ fᵉ (inlᵉ xᵉ))
                ( reflᵉ))))
          ( reflᵉ)
          ( reflᵉ))
  pr2ᵉ (retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ) (inlᵉ xᵉ) =
    commutative-square-inl-retraction-equiv-coproductᵉ
      ( xᵉ)
      ( map-equivᵉ fᵉ (inlᵉ xᵉ))
      ( reflᵉ)
    where
    commutative-square-inl-retraction-equiv-coproductᵉ :
      (xᵉ : Aᵉ) (yᵉ : Aᵉ +ᵉ Bᵉ) (qᵉ : map-equivᵉ fᵉ (inlᵉ xᵉ) ＝ᵉ yᵉ) →
      map-equivᵉ fᵉ (inlᵉ xᵉ) ＝ᵉ inlᵉ (cases-retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ xᵉ yᵉ qᵉ)
    commutative-square-inl-retraction-equiv-coproductᵉ xᵉ (inlᵉ yᵉ) qᵉ = qᵉ
    commutative-square-inl-retraction-equiv-coproductᵉ xᵉ (inrᵉ yᵉ) qᵉ =
      ex-falsoᵉ (equiv-coproduct-induce-equiv-disjointᵉ fᵉ gᵉ pᵉ xᵉ yᵉ qᵉ)
  pr2ᵉ (retraction-equiv-coproductᵉ fᵉ gᵉ pᵉ) (inrᵉ xᵉ) = pᵉ xᵉ
```

### Equivalences between mutually exclusive coproducts

Ifᵉ `Pᵉ → ¬ᵉ Q'`ᵉ andᵉ `P'ᵉ → ¬ᵉ Q`ᵉ thenᵉ `(Pᵉ +ᵉ Qᵉ ≃ᵉ P'ᵉ +ᵉ Q'ᵉ) ≃ᵉ ((Pᵉ ≃ᵉ P'ᵉ) ×ᵉ (Qᵉ ≃ᵉ Q'))`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Pᵉ : UUᵉ l1ᵉ} {Qᵉ : UUᵉ l2ᵉ} {P'ᵉ : UUᵉ l3ᵉ} {Q'ᵉ : UUᵉ l4ᵉ}
  (¬PQ'ᵉ : Pᵉ → ¬ᵉ Q'ᵉ)
  where

  left-to-leftᵉ :
    (eᵉ : (Pᵉ +ᵉ Qᵉ) ≃ᵉ (P'ᵉ +ᵉ Q'ᵉ)) →
    (uᵉ : Pᵉ +ᵉ Qᵉ) → is-leftᵉ uᵉ → is-leftᵉ (map-equivᵉ eᵉ uᵉ)
  left-to-leftᵉ eᵉ (inlᵉ pᵉ) _ =
    ind-coproductᵉ is-leftᵉ (λ _ → starᵉ) (λ q'ᵉ → ¬PQ'ᵉ pᵉ q'ᵉ) (map-equivᵉ eᵉ (inlᵉ pᵉ))
  left-to-leftᵉ eᵉ (inrᵉ qᵉ) ()

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Pᵉ : UUᵉ l1ᵉ} {Qᵉ : UUᵉ l2ᵉ} {P'ᵉ : UUᵉ l3ᵉ} {Q'ᵉ : UUᵉ l4ᵉ}
  (¬P'Qᵉ : P'ᵉ → ¬ᵉ Qᵉ)
  where

  right-to-rightᵉ :
    (eᵉ : (Pᵉ +ᵉ Qᵉ) ≃ᵉ (P'ᵉ +ᵉ Q'ᵉ)) (uᵉ : Pᵉ +ᵉ Qᵉ) →
    is-rightᵉ uᵉ → is-rightᵉ (map-equivᵉ eᵉ uᵉ)
  right-to-rightᵉ eᵉ (inlᵉ pᵉ) ()
  right-to-rightᵉ eᵉ (inrᵉ qᵉ) _ =
    ind-coproductᵉ is-rightᵉ (λ p'ᵉ → ¬P'Qᵉ p'ᵉ qᵉ) (λ _ → starᵉ) (map-equivᵉ eᵉ (inrᵉ qᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Pᵉ : UUᵉ l1ᵉ} {Qᵉ : UUᵉ l2ᵉ} {P'ᵉ : UUᵉ l3ᵉ} {Q'ᵉ : UUᵉ l4ᵉ}
  (¬PQ'ᵉ : Pᵉ → ¬ᵉ Q'ᵉ) (¬P'Qᵉ : P'ᵉ → ¬ᵉ Qᵉ)
  where

  equiv-left-to-leftᵉ :
    (eᵉ : (Pᵉ +ᵉ Qᵉ) ≃ᵉ (P'ᵉ +ᵉ Q'ᵉ)) (uᵉ : Pᵉ +ᵉ Qᵉ) → is-leftᵉ uᵉ ≃ᵉ is-leftᵉ (map-equivᵉ eᵉ uᵉ)
  pr1ᵉ (equiv-left-to-leftᵉ eᵉ uᵉ) = left-to-leftᵉ ¬PQ'ᵉ eᵉ uᵉ
  pr2ᵉ (equiv-left-to-leftᵉ eᵉ uᵉ) =
    is-equiv-is-invertibleᵉ
      ( trᵉ is-leftᵉ (is-retraction-map-inv-equivᵉ eᵉ uᵉ) ∘ᵉ
        left-to-leftᵉ ¬P'Qᵉ (inv-equivᵉ eᵉ) (map-equivᵉ eᵉ uᵉ))
      ( λ _ → eq-is-propᵉ (is-prop-is-leftᵉ (map-equivᵉ eᵉ uᵉ)))
      ( λ _ → eq-is-propᵉ (is-prop-is-leftᵉ uᵉ))

  equiv-right-to-rightᵉ :
    (eᵉ : (Pᵉ +ᵉ Qᵉ) ≃ᵉ (P'ᵉ +ᵉ Q'ᵉ)) (uᵉ : Pᵉ +ᵉ Qᵉ) →
    is-rightᵉ uᵉ ≃ᵉ is-rightᵉ (map-equivᵉ eᵉ uᵉ)
  pr1ᵉ (equiv-right-to-rightᵉ eᵉ uᵉ) = right-to-rightᵉ ¬P'Qᵉ eᵉ uᵉ
  pr2ᵉ (equiv-right-to-rightᵉ eᵉ uᵉ) =
    is-equiv-is-invertibleᵉ
      ( trᵉ is-rightᵉ (is-retraction-map-inv-equivᵉ eᵉ uᵉ) ∘ᵉ
        right-to-rightᵉ ¬PQ'ᵉ (inv-equivᵉ eᵉ) (map-equivᵉ eᵉ uᵉ))
      (λ _ → eq-is-propᵉ (is-prop-is-rightᵉ (map-equivᵉ eᵉ uᵉ)))
      (λ _ → eq-is-propᵉ (is-prop-is-rightᵉ uᵉ))

  map-mutually-exclusive-coproductᵉ : (Pᵉ +ᵉ Qᵉ) ≃ᵉ (P'ᵉ +ᵉ Q'ᵉ) → (Pᵉ ≃ᵉ P'ᵉ) ×ᵉ (Qᵉ ≃ᵉ Q'ᵉ)
  pr1ᵉ (map-mutually-exclusive-coproductᵉ eᵉ) =
    equiv-left-summandᵉ ∘eᵉ
    ( equiv-Σᵉ _ eᵉ (equiv-left-to-leftᵉ eᵉ) ∘eᵉ
      inv-equivᵉ equiv-left-summandᵉ)
  pr2ᵉ (map-mutually-exclusive-coproductᵉ eᵉ) =
    equiv-right-summandᵉ ∘eᵉ
    ( equiv-Σᵉ _ eᵉ (equiv-right-to-rightᵉ eᵉ) ∘eᵉ
      inv-equivᵉ (equiv-right-summandᵉ))

  map-inv-mutually-exclusive-coproductᵉ :
    (Pᵉ ≃ᵉ P'ᵉ) ×ᵉ (Qᵉ ≃ᵉ Q'ᵉ) → (Pᵉ +ᵉ Qᵉ) ≃ᵉ (P'ᵉ +ᵉ Q'ᵉ)
  map-inv-mutually-exclusive-coproductᵉ (e₁ᵉ ,ᵉ e₂ᵉ) = equiv-coproductᵉ e₁ᵉ e₂ᵉ

  is-retraction-map-inv-mutually-exclusive-coproductᵉ :
    map-mutually-exclusive-coproductᵉ ∘ᵉ map-inv-mutually-exclusive-coproductᵉ ~ᵉ idᵉ
  is-retraction-map-inv-mutually-exclusive-coproductᵉ (e₁ᵉ ,ᵉ e₂ᵉ) =
    eq-pairᵉ
      (eq-equiv-eq-map-equivᵉ reflᵉ)
      (eq-equiv-eq-map-equivᵉ reflᵉ)

  abstract
    is-section-map-inv-mutually-exclusive-coproductᵉ :
      map-inv-mutually-exclusive-coproductᵉ ∘ᵉ map-mutually-exclusive-coproductᵉ ~ᵉ
      idᵉ
    is-section-map-inv-mutually-exclusive-coproductᵉ eᵉ =
      eq-htpy-equivᵉ
      ( λ where
        ( inlᵉ pᵉ) →
          apᵉ
            ( pr1ᵉ)
            ( is-retraction-map-inv-equiv-left-summandᵉ
              ( map-equivᵉ eᵉ (inlᵉ pᵉ) ,ᵉ left-to-leftᵉ ¬PQ'ᵉ eᵉ (inlᵉ pᵉ) starᵉ))
        ( inrᵉ qᵉ) →
          apᵉ
            ( pr1ᵉ)
            ( is-retraction-map-inv-equiv-right-summandᵉ
              ( map-equivᵉ eᵉ (inrᵉ qᵉ) ,ᵉ right-to-rightᵉ ¬P'Qᵉ eᵉ (inrᵉ qᵉ) starᵉ)))

  equiv-mutually-exclusive-coproductᵉ :
    ((Pᵉ +ᵉ Qᵉ) ≃ᵉ (P'ᵉ +ᵉ Q'ᵉ)) ≃ᵉ ((Pᵉ ≃ᵉ P'ᵉ) ×ᵉ (Qᵉ ≃ᵉ Q'ᵉ))
  pr1ᵉ equiv-mutually-exclusive-coproductᵉ = map-mutually-exclusive-coproductᵉ
  pr2ᵉ equiv-mutually-exclusive-coproductᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-mutually-exclusive-coproductᵉ
      is-retraction-map-inv-mutually-exclusive-coproductᵉ
      is-section-map-inv-mutually-exclusive-coproductᵉ
```

### The functorial action of coproducts on arrows

Givenᵉ aᵉ pairᵉ ofᵉ [morphismsᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ)
`αᵉ : fᵉ → g`ᵉ andᵉ `βᵉ : hᵉ → i`,ᵉ thereᵉ isᵉ anᵉ inducedᵉ morphismᵉ ofᵉ arrowsᵉ
`αᵉ +ᵉ βᵉ : fᵉ +ᵉ hᵉ → gᵉ +ᵉ i`ᵉ andᵉ thisᵉ constructionᵉ isᵉ functorial.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  {Cᵉ : UUᵉ l5ᵉ} {Dᵉ : UUᵉ l6ᵉ} {Zᵉ : UUᵉ l7ᵉ} {Wᵉ : UUᵉ l8ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Cᵉ → Dᵉ) (iᵉ : Zᵉ → Wᵉ)
  (αᵉ : hom-arrowᵉ fᵉ gᵉ) (βᵉ : hom-arrowᵉ hᵉ iᵉ)
  where

  map-domain-coproduct-hom-arrowᵉ : Aᵉ +ᵉ Cᵉ → Xᵉ +ᵉ Zᵉ
  map-domain-coproduct-hom-arrowᵉ =
    map-coproductᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ) (map-domain-hom-arrowᵉ hᵉ iᵉ βᵉ)

  map-codomain-coproduct-hom-arrowᵉ : Bᵉ +ᵉ Dᵉ → Yᵉ +ᵉ Wᵉ
  map-codomain-coproduct-hom-arrowᵉ =
    map-coproductᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ) (map-codomain-hom-arrowᵉ hᵉ iᵉ βᵉ)

  coh-coproduct-hom-arrowᵉ :
    coherence-hom-arrowᵉ
      ( map-coproductᵉ fᵉ hᵉ)
      ( map-coproductᵉ gᵉ iᵉ)
      ( map-domain-coproduct-hom-arrowᵉ)
      ( map-codomain-coproduct-hom-arrowᵉ)
  coh-coproduct-hom-arrowᵉ =
    ( inv-htpyᵉ
      ( preserves-comp-map-coproductᵉ
        ( fᵉ)
        ( map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ)
        ( hᵉ)
        ( map-codomain-hom-arrowᵉ hᵉ iᵉ βᵉ))) ∙hᵉ
    ( htpy-map-coproductᵉ (coh-hom-arrowᵉ fᵉ gᵉ αᵉ) (coh-hom-arrowᵉ hᵉ iᵉ βᵉ)) ∙hᵉ
    ( preserves-comp-map-coproductᵉ
      ( map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ) gᵉ (map-domain-hom-arrowᵉ hᵉ iᵉ βᵉ) iᵉ)

  coproduct-hom-arrowᵉ : hom-arrowᵉ (map-coproductᵉ fᵉ hᵉ) (map-coproductᵉ gᵉ iᵉ)
  coproduct-hom-arrowᵉ =
    ( map-domain-coproduct-hom-arrowᵉ ,ᵉ
      map-codomain-coproduct-hom-arrowᵉ ,ᵉ
      coh-coproduct-hom-arrowᵉ)
```

## See also

-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ coproductᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-coproduct-types`](foundation.type-arithmetic-coproduct-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in coproductᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-coproduct-types`](foundation.equality-coproduct-types.md).ᵉ
-ᵉ Theᵉ universalᵉ propertyᵉ ofᵉ coproductsᵉ isᵉ treatedᵉ in
  [`foundation.universal-property-coproduct-types`](foundation.universal-property-coproduct-types.md).ᵉ
-ᵉ Functorialᵉ propertiesᵉ ofᵉ cartesianᵉ productᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).ᵉ
-ᵉ Functorialᵉ propertiesᵉ ofᵉ dependentᵉ pairᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-dependent-pair-types`](foundation.functoriality-dependent-pair-types.md).ᵉ