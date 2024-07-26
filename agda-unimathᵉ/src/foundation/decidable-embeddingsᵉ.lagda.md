# Decidable embeddings

```agda
module foundation.decidable-embeddingsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.decidable-mapsᵉ
open import foundation.decidable-subtypesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-mapsᵉ
open import foundation.structured-type-dualityᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.decidable-propositionsᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Idea

Aᵉ mapᵉ isᵉ saidᵉ to beᵉ aᵉ decidableᵉ embeddingᵉ ifᵉ itᵉ isᵉ anᵉ embeddingᵉ andᵉ itsᵉ fibersᵉ
areᵉ decidableᵉ types.ᵉ

## Definitions

### The condition on a map of being a decidable embedding

```agda
is-decidable-embᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} → (Xᵉ → Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-decidable-embᵉ {Yᵉ = Yᵉ} fᵉ = is-embᵉ fᵉ ×ᵉ is-decidable-mapᵉ fᵉ

abstract
  is-emb-is-decidable-embᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Xᵉ → Yᵉ} →
    is-decidable-embᵉ fᵉ → is-embᵉ fᵉ
  is-emb-is-decidable-embᵉ Hᵉ = pr1ᵉ Hᵉ

is-decidable-map-is-decidable-embᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Xᵉ → Yᵉ} →
  is-decidable-embᵉ fᵉ → is-decidable-mapᵉ fᵉ
is-decidable-map-is-decidable-embᵉ Hᵉ = pr2ᵉ Hᵉ
```

### Decidably propositional maps

```agda
is-decidable-prop-mapᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} → (Xᵉ → Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-decidable-prop-mapᵉ {Yᵉ = Yᵉ} fᵉ = (yᵉ : Yᵉ) → is-decidable-propᵉ (fiberᵉ fᵉ yᵉ)

abstract
  is-prop-map-is-decidable-prop-mapᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Xᵉ → Yᵉ} →
    is-decidable-prop-mapᵉ fᵉ → is-prop-mapᵉ fᵉ
  is-prop-map-is-decidable-prop-mapᵉ Hᵉ yᵉ = pr1ᵉ (Hᵉ yᵉ)

is-decidable-map-is-decidable-prop-mapᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Xᵉ → Yᵉ} →
  is-decidable-prop-mapᵉ fᵉ → is-decidable-mapᵉ fᵉ
is-decidable-map-is-decidable-prop-mapᵉ Hᵉ yᵉ = pr2ᵉ (Hᵉ yᵉ)
```

### The type of decidable embeddings

```agda
infix 5 _↪ᵈᵉ_
_↪ᵈᵉ_ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
Xᵉ ↪ᵈᵉ Yᵉ = Σᵉ (Xᵉ → Yᵉ) is-decidable-embᵉ

map-decidable-embᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} → Xᵉ ↪ᵈᵉ Yᵉ → Xᵉ → Yᵉ
map-decidable-embᵉ eᵉ = pr1ᵉ eᵉ

abstract
  is-decidable-emb-map-decidable-embᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Xᵉ ↪ᵈᵉ Yᵉ) →
    is-decidable-embᵉ (map-decidable-embᵉ eᵉ)
  is-decidable-emb-map-decidable-embᵉ eᵉ = pr2ᵉ eᵉ

abstract
  is-emb-map-decidable-embᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Xᵉ ↪ᵈᵉ Yᵉ) →
    is-embᵉ (map-decidable-embᵉ eᵉ)
  is-emb-map-decidable-embᵉ eᵉ =
    is-emb-is-decidable-embᵉ (is-decidable-emb-map-decidable-embᵉ eᵉ)

abstract
  is-decidable-map-map-decidable-embᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Xᵉ ↪ᵈᵉ Yᵉ) →
    is-decidable-mapᵉ (map-decidable-embᵉ eᵉ)
  is-decidable-map-map-decidable-embᵉ eᵉ =
    is-decidable-map-is-decidable-embᵉ (is-decidable-emb-map-decidable-embᵉ eᵉ)

emb-decidable-embᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} → Xᵉ ↪ᵈᵉ Yᵉ → Xᵉ ↪ᵉ Yᵉ
pr1ᵉ (emb-decidable-embᵉ eᵉ) = map-decidable-embᵉ eᵉ
pr2ᵉ (emb-decidable-embᵉ eᵉ) = is-emb-map-decidable-embᵉ eᵉ
```

## Properties

### Being a decidably propositional map is a proposition

```agda
abstract
  is-prop-is-decidable-prop-mapᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ) →
    is-propᵉ (is-decidable-prop-mapᵉ fᵉ)
  is-prop-is-decidable-prop-mapᵉ fᵉ =
    is-prop-Πᵉ (λ yᵉ → is-prop-is-decidable-propᵉ (fiberᵉ fᵉ yᵉ))
```

### Any map of which the fibers are decidable propositions is a decidable embedding

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Xᵉ → Yᵉ}
  where

  abstract
    is-decidable-emb-is-decidable-prop-mapᵉ :
      is-decidable-prop-mapᵉ fᵉ → is-decidable-embᵉ fᵉ
    pr1ᵉ (is-decidable-emb-is-decidable-prop-mapᵉ Hᵉ) =
      is-emb-is-prop-mapᵉ (is-prop-map-is-decidable-prop-mapᵉ Hᵉ)
    pr2ᵉ (is-decidable-emb-is-decidable-prop-mapᵉ Hᵉ) =
      is-decidable-map-is-decidable-prop-mapᵉ Hᵉ

  abstract
    is-prop-map-is-decidable-embᵉ : is-decidable-embᵉ fᵉ → is-prop-mapᵉ fᵉ
    is-prop-map-is-decidable-embᵉ Hᵉ =
      is-prop-map-is-embᵉ (is-emb-is-decidable-embᵉ Hᵉ)

  abstract
    is-decidable-prop-map-is-decidable-embᵉ :
      is-decidable-embᵉ fᵉ → is-decidable-prop-mapᵉ fᵉ
    pr1ᵉ (is-decidable-prop-map-is-decidable-embᵉ Hᵉ yᵉ) =
      is-prop-map-is-decidable-embᵉ Hᵉ yᵉ
    pr2ᵉ (is-decidable-prop-map-is-decidable-embᵉ Hᵉ yᵉ) = pr2ᵉ Hᵉ yᵉ

decidable-subtype-decidable-embᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
  (Xᵉ ↪ᵈᵉ Yᵉ) → (decidable-subtypeᵉ (l1ᵉ ⊔ l2ᵉ) Yᵉ)
pr1ᵉ (decidable-subtype-decidable-embᵉ fᵉ yᵉ) = fiberᵉ (map-decidable-embᵉ fᵉ) yᵉ
pr2ᵉ (decidable-subtype-decidable-embᵉ fᵉ yᵉ) =
  is-decidable-prop-map-is-decidable-embᵉ (pr2ᵉ fᵉ) yᵉ
```

### The type of all decidable embeddings into a type `A` is equivalent to the type of decidable subtypes of `A`

```agda
equiv-Fiber-Decidable-Propᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) →
  Σᵉ (UUᵉ (l1ᵉ ⊔ lᵉ)) (λ Xᵉ → Xᵉ ↪ᵈᵉ Aᵉ) ≃ᵉ (decidable-subtypeᵉ (l1ᵉ ⊔ lᵉ) Aᵉ)
equiv-Fiber-Decidable-Propᵉ lᵉ Aᵉ =
  ( equiv-Fiber-structureᵉ lᵉ is-decidable-propᵉ Aᵉ) ∘eᵉ
  ( equiv-totᵉ
    ( λ Xᵉ →
      equiv-totᵉ
        ( λ fᵉ →
          ( inv-distributive-Π-Σᵉ) ∘eᵉ
          ( equiv-productᵉ (equiv-is-prop-map-is-embᵉ fᵉ) id-equivᵉ))))
```

### Any equivalence is a decidable embedding

```agda
abstract
  is-decidable-emb-is-equivᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
    is-equivᵉ fᵉ → is-decidable-embᵉ fᵉ
  pr1ᵉ (is-decidable-emb-is-equivᵉ Hᵉ) = is-emb-is-equivᵉ Hᵉ
  pr2ᵉ (is-decidable-emb-is-equivᵉ Hᵉ) xᵉ = inlᵉ (centerᵉ (is-contr-map-is-equivᵉ Hᵉ xᵉ))

abstract
  is-decidable-emb-idᵉ :
    {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-decidable-embᵉ (idᵉ {Aᵉ = Aᵉ})
  pr1ᵉ (is-decidable-emb-idᵉ {l1ᵉ} {Aᵉ}) = is-emb-idᵉ
  pr2ᵉ (is-decidable-emb-idᵉ {l1ᵉ} {Aᵉ}) xᵉ = inlᵉ (pairᵉ xᵉ reflᵉ)

decidable-emb-idᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → Aᵉ ↪ᵈᵉ Aᵉ
pr1ᵉ (decidable-emb-idᵉ {l1ᵉ} {Aᵉ}) = idᵉ
pr2ᵉ (decidable-emb-idᵉ {l1ᵉ} {Aᵉ}) = is-decidable-emb-idᵉ
```

### Being a decidable embedding is a property

```agda
abstract
  is-prop-is-decidable-embᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-propᵉ (is-decidable-embᵉ fᵉ)
  is-prop-is-decidable-embᵉ fᵉ =
    is-prop-has-elementᵉ
      ( λ Hᵉ →
        is-prop-productᵉ
          ( is-property-is-embᵉ fᵉ)
          ( is-prop-Πᵉ
            ( λ yᵉ → is-prop-is-decidableᵉ (is-prop-map-is-embᵉ (pr1ᵉ Hᵉ) yᵉ))))
```

### Decidable embeddings are closed under composition

```agda
abstract
  is-decidable-emb-compᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
    {gᵉ : Bᵉ → Cᵉ} {fᵉ : Aᵉ → Bᵉ} →
    is-decidable-embᵉ fᵉ → is-decidable-embᵉ gᵉ → is-decidable-embᵉ (gᵉ ∘ᵉ fᵉ)
  pr1ᵉ (is-decidable-emb-compᵉ {gᵉ = gᵉ} {fᵉ} Hᵉ Kᵉ) =
    is-emb-compᵉ _ _ (pr1ᵉ Kᵉ) (pr1ᵉ Hᵉ)
  pr2ᵉ (is-decidable-emb-compᵉ {gᵉ = gᵉ} {fᵉ} Hᵉ Kᵉ) xᵉ =
    rec-coproductᵉ
      ( λ uᵉ →
        is-decidable-equivᵉ
          ( compute-fiber-compᵉ gᵉ fᵉ xᵉ)
          ( is-decidable-equivᵉ
            ( left-unit-law-Σ-is-contrᵉ
              ( is-proof-irrelevant-is-propᵉ
                ( is-prop-map-is-embᵉ (is-emb-is-decidable-embᵉ Kᵉ) xᵉ) ( uᵉ))
              ( uᵉ))
            ( is-decidable-map-is-decidable-embᵉ Hᵉ (pr1ᵉ uᵉ))))
      ( λ αᵉ → inrᵉ (λ tᵉ → αᵉ (fᵉ (pr1ᵉ tᵉ) ,ᵉ pr2ᵉ tᵉ)))
      ( pr2ᵉ Kᵉ xᵉ)
```

### Decidable embeddings are closed under homotopies

```agda
abstract
  is-decidable-emb-htpyᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ gᵉ : Aᵉ → Bᵉ} →
    fᵉ ~ᵉ gᵉ → is-decidable-embᵉ gᵉ → is-decidable-embᵉ fᵉ
  pr1ᵉ (is-decidable-emb-htpyᵉ {fᵉ = fᵉ} {gᵉ} Hᵉ Kᵉ) =
    is-emb-htpyᵉ Hᵉ (is-emb-is-decidable-embᵉ Kᵉ)
  pr2ᵉ (is-decidable-emb-htpyᵉ {fᵉ = fᵉ} {gᵉ} Hᵉ Kᵉ) bᵉ =
    is-decidable-equivᵉ
      ( equiv-totᵉ (λ aᵉ → equiv-concatᵉ (invᵉ (Hᵉ aᵉ)) bᵉ))
      ( is-decidable-map-is-decidable-embᵉ Kᵉ bᵉ)
```

### Characterizing equality in the type of decidable embeddings

```agda
htpy-decidable-embᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ gᵉ : Aᵉ ↪ᵈᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
htpy-decidable-embᵉ fᵉ gᵉ = map-decidable-embᵉ fᵉ ~ᵉ map-decidable-embᵉ gᵉ

refl-htpy-decidable-embᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ ↪ᵈᵉ Bᵉ) → htpy-decidable-embᵉ fᵉ fᵉ
refl-htpy-decidable-embᵉ fᵉ = refl-htpyᵉ

htpy-eq-decidable-embᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ gᵉ : Aᵉ ↪ᵈᵉ Bᵉ) →
  fᵉ ＝ᵉ gᵉ → htpy-decidable-embᵉ fᵉ gᵉ
htpy-eq-decidable-embᵉ fᵉ .fᵉ reflᵉ = refl-htpy-decidable-embᵉ fᵉ

abstract
  is-torsorial-htpy-decidable-embᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ ↪ᵈᵉ Bᵉ) →
    is-torsorialᵉ (htpy-decidable-embᵉ fᵉ)
  is-torsorial-htpy-decidable-embᵉ fᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-htpyᵉ (map-decidable-embᵉ fᵉ))
      ( is-prop-is-decidable-embᵉ)
      ( map-decidable-embᵉ fᵉ)
      ( refl-htpyᵉ)
      ( is-decidable-emb-map-decidable-embᵉ fᵉ)

abstract
  is-equiv-htpy-eq-decidable-embᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ gᵉ : Aᵉ ↪ᵈᵉ Bᵉ) →
    is-equivᵉ (htpy-eq-decidable-embᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-decidable-embᵉ fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-decidable-embᵉ fᵉ)
      ( htpy-eq-decidable-embᵉ fᵉ)

eq-htpy-decidable-embᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ gᵉ : Aᵉ ↪ᵈᵉ Bᵉ} →
  htpy-decidable-embᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
eq-htpy-decidable-embᵉ {fᵉ = fᵉ} {gᵉ} =
  map-inv-is-equivᵉ (is-equiv-htpy-eq-decidable-embᵉ fᵉ gᵉ)
```

### Precomposing decidable embeddings with equivalences

```agda
equiv-precomp-decidable-emb-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
  (Cᵉ : UUᵉ l3ᵉ) → (Bᵉ ↪ᵈᵉ Cᵉ) ≃ᵉ (Aᵉ ↪ᵈᵉ Cᵉ)
equiv-precomp-decidable-emb-equivᵉ eᵉ Cᵉ =
  equiv-Σᵉ
    ( is-decidable-embᵉ)
    ( equiv-precompᵉ eᵉ Cᵉ)
    ( λ gᵉ →
      equiv-iff-is-propᵉ
        ( is-prop-is-decidable-embᵉ gᵉ)
        ( is-prop-is-decidable-embᵉ (gᵉ ∘ᵉ map-equivᵉ eᵉ))
        ( is-decidable-emb-compᵉ (is-decidable-emb-is-equivᵉ (pr2ᵉ eᵉ)))
        ( λ dᵉ →
          is-decidable-emb-htpyᵉ
            ( λ bᵉ → apᵉ gᵉ (invᵉ (is-section-map-inv-equivᵉ eᵉ bᵉ)))
            ( is-decidable-emb-compᵉ
              ( is-decidable-emb-is-equivᵉ (is-equiv-map-inv-equivᵉ eᵉ))
              ( dᵉ))))
```

### Any map out of the empty type is a decidable embedding

```agda
abstract
  is-decidable-emb-ex-falsoᵉ :
    {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → is-decidable-embᵉ (ex-falsoᵉ {lᵉ} {Xᵉ})
  pr1ᵉ (is-decidable-emb-ex-falsoᵉ {lᵉ} {Xᵉ}) = is-emb-ex-falsoᵉ
  pr2ᵉ (is-decidable-emb-ex-falsoᵉ {lᵉ} {Xᵉ}) xᵉ = inrᵉ pr1ᵉ

decidable-emb-ex-falsoᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → emptyᵉ ↪ᵈᵉ Xᵉ
pr1ᵉ decidable-emb-ex-falsoᵉ = ex-falsoᵉ
pr2ᵉ decidable-emb-ex-falsoᵉ = is-decidable-emb-ex-falsoᵉ

decidable-emb-is-emptyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → is-emptyᵉ Aᵉ → Aᵉ ↪ᵈᵉ Bᵉ
decidable-emb-is-emptyᵉ {Aᵉ = Aᵉ} fᵉ =
  map-equivᵉ
    ( equiv-precomp-decidable-emb-equivᵉ (equiv-is-emptyᵉ fᵉ idᵉ) _)
    ( decidable-emb-ex-falsoᵉ)
```

### The map on total spaces induced by a family of decidable embeddings is a decidable embeddings

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  is-decidable-emb-totᵉ :
    {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ} →
    ((xᵉ : Aᵉ) → is-decidable-embᵉ (fᵉ xᵉ)) → is-decidable-embᵉ (totᵉ fᵉ)
  is-decidable-emb-totᵉ Hᵉ =
    ( is-emb-totᵉ (λ xᵉ → is-emb-is-decidable-embᵉ (Hᵉ xᵉ)) ,ᵉ
      is-decidable-map-totᵉ λ xᵉ → is-decidable-map-is-decidable-embᵉ (Hᵉ xᵉ))

  decidable-emb-totᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ ↪ᵈᵉ Cᵉ xᵉ) → Σᵉ Aᵉ Bᵉ ↪ᵈᵉ Σᵉ Aᵉ Cᵉ
  pr1ᵉ (decidable-emb-totᵉ fᵉ) = totᵉ (λ xᵉ → map-decidable-embᵉ (fᵉ xᵉ))
  pr2ᵉ (decidable-emb-totᵉ fᵉ) =
    is-decidable-emb-totᵉ (λ xᵉ → is-decidable-emb-map-decidable-embᵉ (fᵉ xᵉ))
```