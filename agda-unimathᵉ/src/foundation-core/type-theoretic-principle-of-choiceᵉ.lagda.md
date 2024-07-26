# The type theoretic principle of choice

```agda
module foundation-core.type-theoretic-principle-of-choiceᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Aᵉ dependentᵉ functionᵉ takingᵉ valuesᵉ in aᵉ
[dependentᵉ pairᵉ type](foundation.dependent-pair-types.mdᵉ) isᵉ
[equivalently](foundation-core.equivalences.mdᵉ) describedᵉ asᵉ aᵉ pairᵉ ofᵉ dependentᵉ
functions.ᵉ Thisᵉ equivalence,ᵉ whichᵉ givesᵉ theᵉ distributivityᵉ ofᵉ Πᵉ overᵉ Σ,ᵉ isᵉ alsoᵉ
knownᵉ asᵉ theᵉ **typeᵉ theoreticᵉ principleᵉ ofᵉ choice**.ᵉ Indeed,ᵉ itᵉ isᵉ theᵉ
Curry-Howardᵉ interpretationᵉ ofᵉ (oneᵉ formulationᵉ ofᵉ) theᵉ
[axiomᵉ ofᵉ choice](foundation.axiom-of-choice.md).ᵉ

Weᵉ establishᵉ thisᵉ equivalenceᵉ bothᵉ forᵉ explicitᵉ andᵉ implicitᵉ functionᵉ types.ᵉ

## Definitions

### Dependent products of dependent pair types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ)
  where

  Π-total-famᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  Π-total-famᵉ = (xᵉ : Aᵉ) → Σᵉ (Bᵉ xᵉ) (Cᵉ xᵉ)

  universally-structured-Πᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  universally-structured-Πᵉ = Σᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ) (λ fᵉ → (xᵉ : Aᵉ) → Cᵉ xᵉ (fᵉ xᵉ))
```

### Implicit dependent products of dependent pair types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ)
  where

  implicit-Π-total-famᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  implicit-Π-total-famᵉ = {xᵉ : Aᵉ} → Σᵉ (Bᵉ xᵉ) (Cᵉ xᵉ)

  universally-structured-implicit-Πᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  universally-structured-implicit-Πᵉ =
    Σᵉ ({xᵉ : Aᵉ} → Bᵉ xᵉ) (λ fᵉ → {xᵉ : Aᵉ} → Cᵉ xᵉ (fᵉ {xᵉ}))
```

## Theorem

### The distributivity of Π over Σ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ}
  where

  map-distributive-Π-Σᵉ : Π-total-famᵉ Cᵉ → universally-structured-Πᵉ Cᵉ
  pr1ᵉ (map-distributive-Π-Σᵉ φᵉ) xᵉ = pr1ᵉ (φᵉ xᵉ)
  pr2ᵉ (map-distributive-Π-Σᵉ φᵉ) xᵉ = pr2ᵉ (φᵉ xᵉ)

  map-inv-distributive-Π-Σᵉ : universally-structured-Πᵉ Cᵉ → Π-total-famᵉ Cᵉ
  pr1ᵉ (map-inv-distributive-Π-Σᵉ ψᵉ xᵉ) = (pr1ᵉ ψᵉ) xᵉ
  pr2ᵉ (map-inv-distributive-Π-Σᵉ ψᵉ xᵉ) = (pr2ᵉ ψᵉ) xᵉ

  is-section-map-inv-distributive-Π-Σᵉ :
    map-distributive-Π-Σᵉ ∘ᵉ map-inv-distributive-Π-Σᵉ ~ᵉ idᵉ
  is-section-map-inv-distributive-Π-Σᵉ (ψᵉ ,ᵉ ψ'ᵉ) = reflᵉ

  is-retraction-map-inv-distributive-Π-Σᵉ :
    map-inv-distributive-Π-Σᵉ ∘ᵉ map-distributive-Π-Σᵉ ~ᵉ idᵉ
  is-retraction-map-inv-distributive-Π-Σᵉ φᵉ = reflᵉ

  abstract
    is-equiv-map-distributive-Π-Σᵉ : is-equivᵉ (map-distributive-Π-Σᵉ)
    is-equiv-map-distributive-Π-Σᵉ =
      is-equiv-is-invertibleᵉ
        ( map-inv-distributive-Π-Σᵉ)
        ( is-section-map-inv-distributive-Π-Σᵉ)
        ( is-retraction-map-inv-distributive-Π-Σᵉ)

  distributive-Π-Σᵉ : Π-total-famᵉ Cᵉ ≃ᵉ universally-structured-Πᵉ Cᵉ
  pr1ᵉ distributive-Π-Σᵉ = map-distributive-Π-Σᵉ
  pr2ᵉ distributive-Π-Σᵉ = is-equiv-map-distributive-Π-Σᵉ

  abstract
    is-equiv-map-inv-distributive-Π-Σᵉ : is-equivᵉ (map-inv-distributive-Π-Σᵉ)
    is-equiv-map-inv-distributive-Π-Σᵉ =
      is-equiv-is-invertibleᵉ
        ( map-distributive-Π-Σᵉ)
        ( is-retraction-map-inv-distributive-Π-Σᵉ)
        ( is-section-map-inv-distributive-Π-Σᵉ)

  inv-distributive-Π-Σᵉ : universally-structured-Πᵉ Cᵉ ≃ᵉ Π-total-famᵉ Cᵉ
  pr1ᵉ inv-distributive-Π-Σᵉ = map-inv-distributive-Π-Σᵉ
  pr2ᵉ inv-distributive-Π-Σᵉ = is-equiv-map-inv-distributive-Π-Σᵉ
```

### The distributivity of implicit Π over Σ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ}
  where

  map-distributive-implicit-Π-Σᵉ :
    implicit-Π-total-famᵉ Cᵉ → universally-structured-implicit-Πᵉ Cᵉ
  pr1ᵉ (map-distributive-implicit-Π-Σᵉ φᵉ) {xᵉ} = pr1ᵉ (φᵉ {xᵉ})
  pr2ᵉ (map-distributive-implicit-Π-Σᵉ φᵉ) {xᵉ} = pr2ᵉ (φᵉ {xᵉ})

  map-inv-distributive-implicit-Π-Σᵉ :
    universally-structured-implicit-Πᵉ Cᵉ → implicit-Π-total-famᵉ Cᵉ
  pr1ᵉ (map-inv-distributive-implicit-Π-Σᵉ ψᵉ {xᵉ}) = pr1ᵉ ψᵉ
  pr2ᵉ (map-inv-distributive-implicit-Π-Σᵉ ψᵉ {xᵉ}) = pr2ᵉ ψᵉ

  is-section-map-inv-distributive-implicit-Π-Σᵉ :
    ( ( map-distributive-implicit-Π-Σᵉ) ∘ᵉ
      ( map-inv-distributive-implicit-Π-Σᵉ)) ~ᵉ idᵉ
  is-section-map-inv-distributive-implicit-Π-Σᵉ (ψᵉ ,ᵉ ψ'ᵉ) = reflᵉ

  is-retraction-map-inv-distributive-implicit-Π-Σᵉ :
    ( ( map-inv-distributive-implicit-Π-Σᵉ) ∘ᵉ
      ( map-distributive-implicit-Π-Σᵉ)) ~ᵉ idᵉ
  is-retraction-map-inv-distributive-implicit-Π-Σᵉ φᵉ = reflᵉ

  abstract
    is-equiv-map-distributive-implicit-Π-Σᵉ :
      is-equivᵉ (map-distributive-implicit-Π-Σᵉ)
    is-equiv-map-distributive-implicit-Π-Σᵉ =
      is-equiv-is-invertibleᵉ
        ( map-inv-distributive-implicit-Π-Σᵉ)
        ( is-section-map-inv-distributive-implicit-Π-Σᵉ)
        ( is-retraction-map-inv-distributive-implicit-Π-Σᵉ)

  distributive-implicit-Π-Σᵉ :
    implicit-Π-total-famᵉ Cᵉ ≃ᵉ universally-structured-implicit-Πᵉ Cᵉ
  pr1ᵉ distributive-implicit-Π-Σᵉ = map-distributive-implicit-Π-Σᵉ
  pr2ᵉ distributive-implicit-Π-Σᵉ = is-equiv-map-distributive-implicit-Π-Σᵉ

  abstract
    is-equiv-map-inv-distributive-implicit-Π-Σᵉ :
      is-equivᵉ (map-inv-distributive-implicit-Π-Σᵉ)
    is-equiv-map-inv-distributive-implicit-Π-Σᵉ =
      is-equiv-is-invertibleᵉ
        ( map-distributive-implicit-Π-Σᵉ)
        ( is-retraction-map-inv-distributive-implicit-Π-Σᵉ)
        ( is-section-map-inv-distributive-implicit-Π-Σᵉ)

  inv-distributive-implicit-Π-Σᵉ :
    (universally-structured-implicit-Πᵉ Cᵉ) ≃ᵉ (implicit-Π-total-famᵉ Cᵉ)
  pr1ᵉ inv-distributive-implicit-Π-Σᵉ = map-inv-distributive-implicit-Π-Σᵉ
  pr2ᵉ inv-distributive-implicit-Π-Σᵉ = is-equiv-map-inv-distributive-implicit-Π-Σᵉ
```

### Ordinary functions into a Σ-type

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Bᵉ → UUᵉ l3ᵉ}
  where

  mapping-into-Σᵉ : (Aᵉ → Σᵉ Bᵉ Cᵉ) → Σᵉ (Aᵉ → Bᵉ) (λ fᵉ → (xᵉ : Aᵉ) → Cᵉ (fᵉ xᵉ))
  mapping-into-Σᵉ = map-distributive-Π-Σᵉ {Bᵉ = λ _ → Bᵉ}

  abstract
    is-equiv-mapping-into-Σᵉ : is-equivᵉ mapping-into-Σᵉ
    is-equiv-mapping-into-Σᵉ = is-equiv-map-distributive-Π-Σᵉ

  equiv-mapping-into-Σᵉ :
    (Aᵉ → Σᵉ Bᵉ Cᵉ) ≃ᵉ Σᵉ (Aᵉ → Bᵉ) (λ fᵉ → (xᵉ : Aᵉ) → Cᵉ (fᵉ xᵉ))
  pr1ᵉ equiv-mapping-into-Σᵉ = mapping-into-Σᵉ
  pr2ᵉ equiv-mapping-into-Σᵉ = is-equiv-mapping-into-Σᵉ
```