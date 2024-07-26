# Local types

```agda
module orthogonal-factorization-systems.local-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.families-of-equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.precomposition-dependent-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.propositionsᵉ
open import foundation.retracts-of-mapsᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.sectionsᵉ
open import foundation.type-arithmetic-dependent-function-typesᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-empty-typeᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ dependentᵉ typeᵉ `A`ᵉ overᵉ `Y`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "localᵉ at"ᵉ Disambiguation="mapᵉ ofᵉ types"ᵉ}} `fᵉ : Xᵉ → Y`,ᵉ orᵉ
{{#conceptᵉ "`f`-local"ᵉ Disambiguation="mapᵉ ofᵉ types"ᵉ}} ,ᵉ ifᵉ theᵉ
[precompositionᵉ map](foundation-core.function-types.mdᵉ)

```text
  _∘ᵉ fᵉ : ((yᵉ : Yᵉ) → Aᵉ yᵉ) → ((xᵉ : Xᵉ) → Aᵉ (fᵉ xᵉ))
```

isᵉ anᵉ [equivalence](foundation-core.equivalences.md).ᵉ

Weᵉ reserveᵉ theᵉ nameᵉ `is-local`ᵉ forᵉ whenᵉ `A`ᵉ doesᵉ notᵉ varyᵉ overᵉ `Y`,ᵉ andᵉ specifyᵉ
with `is-local-dependent-type`ᵉ whenᵉ itᵉ does.ᵉ

Noteᵉ thatᵉ aᵉ localᵉ dependentᵉ typeᵉ isᵉ notᵉ theᵉ sameᵉ asᵉ aᵉ
[localᵉ family](orthogonal-factorization-systems.local-families-of-types.md).ᵉ
Whileᵉ aᵉ localᵉ familyᵉ isᵉ aᵉ typeᵉ familyᵉ `P`ᵉ onᵉ someᵉ otherᵉ indexingᵉ typeᵉ `A`,ᵉ suchᵉ
thatᵉ eachᵉ fiberᵉ isᵉ localᵉ asᵉ aᵉ nondependentᵉ typeᵉ overᵉ `Y`,ᵉ aᵉ localᵉ dependentᵉ typeᵉ
isᵉ aᵉ localᵉ typeᵉ thatᵉ additionallyᵉ mayᵉ varyᵉ overᵉ `Y`.ᵉ Concretely,ᵉ aᵉ localᵉ
dependentᵉ typeᵉ `A`ᵉ mayᵉ beᵉ understoodᵉ asᵉ aᵉ familyᵉ ofᵉ typesᵉ suchᵉ thatᵉ forᵉ everyᵉ
`yᵉ : Y`,ᵉ `Aᵉ y`ᵉ isᵉ
`fiberᵉ fᵉ y`-[null](orthogonal-factorization-systems.null-types.md).ᵉ

## Definition

### Local dependent types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ) (Aᵉ : Yᵉ → UUᵉ l3ᵉ)
  where

  is-local-dependent-typeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-local-dependent-typeᵉ = is-equivᵉ (precomp-Πᵉ fᵉ Aᵉ)

  is-property-is-local-dependent-typeᵉ : is-propᵉ is-local-dependent-typeᵉ
  is-property-is-local-dependent-typeᵉ = is-property-is-equivᵉ (precomp-Πᵉ fᵉ Aᵉ)

  is-local-dependent-type-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ is-local-dependent-type-Propᵉ = is-local-dependent-typeᵉ
  pr2ᵉ is-local-dependent-type-Propᵉ = is-property-is-local-dependent-typeᵉ
```

### Local types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ) (Aᵉ : UUᵉ l3ᵉ)
  where

  is-localᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-localᵉ = is-local-dependent-typeᵉ fᵉ (λ _ → Aᵉ)

  is-property-is-localᵉ : is-propᵉ is-localᵉ
  is-property-is-localᵉ = is-property-is-local-dependent-typeᵉ fᵉ (λ _ → Aᵉ)

  is-local-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-local-Propᵉ = is-local-dependent-type-Propᵉ fᵉ (λ _ → Aᵉ)
```

## Properties

### Locality distributes over Π-types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ)
  where

  distributive-Π-is-local-dependent-typeᵉ :
    {l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l3ᵉ} (Bᵉ : Aᵉ → Yᵉ → UUᵉ l4ᵉ) →
    ((aᵉ : Aᵉ) → is-local-dependent-typeᵉ fᵉ (Bᵉ aᵉ)) →
    is-local-dependent-typeᵉ fᵉ (λ xᵉ → (aᵉ : Aᵉ) → Bᵉ aᵉ xᵉ)
  distributive-Π-is-local-dependent-typeᵉ Bᵉ f-locᵉ =
    is-equiv-map-equivᵉ
      ( ( equiv-swap-Πᵉ) ∘eᵉ
        ( equiv-Π-equiv-familyᵉ (λ aᵉ → precomp-Πᵉ fᵉ (Bᵉ aᵉ) ,ᵉ (f-locᵉ aᵉ))) ∘eᵉ
        ( equiv-swap-Πᵉ))

  distributive-Π-is-localᵉ :
    {l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l3ᵉ} (Bᵉ : Aᵉ → UUᵉ l4ᵉ) →
    ((aᵉ : Aᵉ) → is-localᵉ fᵉ (Bᵉ aᵉ)) →
    is-localᵉ fᵉ ((aᵉ : Aᵉ) → Bᵉ aᵉ)
  distributive-Π-is-localᵉ Bᵉ =
    distributive-Π-is-local-dependent-typeᵉ (λ aᵉ _ → Bᵉ aᵉ)
```

### Local types are closed under equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Aᵉ : Yᵉ → UUᵉ l3ᵉ} {Bᵉ : Yᵉ → UUᵉ l4ᵉ}
  (fᵉ : Xᵉ → Yᵉ)
  where

  is-local-dependent-type-fam-equivᵉ :
    fam-equivᵉ Aᵉ Bᵉ → is-local-dependent-typeᵉ fᵉ Bᵉ → is-local-dependent-typeᵉ fᵉ Aᵉ
  is-local-dependent-type-fam-equivᵉ eᵉ is-local-Bᵉ =
    is-equiv-htpy-equivᵉ
      ( ( equiv-Π-equiv-familyᵉ (inv-equivᵉ ∘ᵉ eᵉ ∘ᵉ fᵉ)) ∘eᵉ
        ( precomp-Πᵉ fᵉ Bᵉ ,ᵉ is-local-Bᵉ) ∘eᵉ
        ( equiv-Π-equiv-familyᵉ eᵉ))
      ( λ gᵉ →
        eq-htpyᵉ (λ yᵉ → invᵉ (is-retraction-map-inv-equivᵉ (eᵉ (fᵉ yᵉ)) (gᵉ (fᵉ yᵉ)))))

  is-local-dependent-type-inv-fam-equivᵉ :
    fam-equivᵉ Bᵉ Aᵉ → is-local-dependent-typeᵉ fᵉ Bᵉ → is-local-dependent-typeᵉ fᵉ Aᵉ
  is-local-dependent-type-inv-fam-equivᵉ eᵉ =
    is-local-dependent-type-fam-equivᵉ (inv-equivᵉ ∘ᵉ eᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} {Bᵉ : UUᵉ l4ᵉ}
  (fᵉ : Xᵉ → Yᵉ)
  where

  is-local-equivᵉ : Aᵉ ≃ᵉ Bᵉ → is-localᵉ fᵉ Bᵉ → is-localᵉ fᵉ Aᵉ
  is-local-equivᵉ eᵉ = is-local-dependent-type-fam-equivᵉ fᵉ (λ _ → eᵉ)

  is-local-inv-equivᵉ : Bᵉ ≃ᵉ Aᵉ → is-localᵉ fᵉ Bᵉ → is-localᵉ fᵉ Aᵉ
  is-local-inv-equivᵉ eᵉ = is-local-dependent-type-inv-fam-equivᵉ fᵉ (λ _ → eᵉ)
```

### Locality is preserved by homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} {fᵉ f'ᵉ : Xᵉ → Yᵉ}
  where

  is-local-htpyᵉ : (Hᵉ : fᵉ ~ᵉ f'ᵉ) → is-localᵉ f'ᵉ Aᵉ → is-localᵉ fᵉ Aᵉ
  is-local-htpyᵉ Hᵉ = is-equiv-htpyᵉ (precompᵉ f'ᵉ Aᵉ) (htpy-precompᵉ Hᵉ Aᵉ)

  is-local-htpy'ᵉ : (Hᵉ : fᵉ ~ᵉ f'ᵉ) → is-localᵉ fᵉ Aᵉ → is-localᵉ f'ᵉ Aᵉ
  is-local-htpy'ᵉ Hᵉ = is-equiv-htpy'ᵉ (precompᵉ fᵉ Aᵉ) (htpy-precompᵉ Hᵉ Aᵉ)
```

### If `S` is `f`-local then `S` is local at every retract of `f`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (Rᵉ : fᵉ retract-of-mapᵉ gᵉ) (Sᵉ : UUᵉ l5ᵉ)
  where

  is-local-retract-map-is-localᵉ : is-localᵉ gᵉ Sᵉ → is-localᵉ fᵉ Sᵉ
  is-local-retract-map-is-localᵉ =
    is-equiv-retract-map-is-equivᵉ
      ( precompᵉ fᵉ Sᵉ)
      ( precompᵉ gᵉ Sᵉ)
      ( retract-map-precomp-retract-mapᵉ fᵉ gᵉ Rᵉ Sᵉ)
```

Inᵉ fact,ᵉ theᵉ higherᵉ coherenceᵉ ofᵉ theᵉ retractᵉ isᵉ notᵉ neededᵉ:

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (R₀ᵉ : Aᵉ retract-ofᵉ Xᵉ) (R₁ᵉ : Bᵉ retract-ofᵉ Yᵉ)
  (iᵉ : coherence-square-maps'ᵉ (inclusion-retractᵉ R₀ᵉ) fᵉ gᵉ (inclusion-retractᵉ R₁ᵉ))
  (rᵉ :
    coherence-square-maps'ᵉ
      ( map-retraction-retractᵉ R₀ᵉ)
      ( gᵉ)
      ( fᵉ)
      ( map-retraction-retractᵉ R₁ᵉ))
  (Sᵉ : UUᵉ l5ᵉ)
  where

  is-local-retract-map-is-local'ᵉ : is-localᵉ gᵉ Sᵉ → is-localᵉ fᵉ Sᵉ
  is-local-retract-map-is-local'ᵉ =
    is-equiv-retract-map-is-equiv'ᵉ
      ( precompᵉ fᵉ Sᵉ)
      ( precompᵉ gᵉ Sᵉ)
      ( retract-precompᵉ R₁ᵉ Sᵉ)
      ( retract-precompᵉ R₀ᵉ Sᵉ)
      ( precomp-coherence-square-mapsᵉ
        ( gᵉ)
        ( map-retraction-retractᵉ R₀ᵉ)
        ( map-retraction-retractᵉ R₁ᵉ)
        ( fᵉ)
        ( rᵉ)
        ( Sᵉ))
      ( precomp-coherence-square-mapsᵉ
        ( fᵉ)
        ( inclusion-retractᵉ R₀ᵉ)
        ( inclusion-retractᵉ R₁ᵉ)
        ( gᵉ)
        ( iᵉ)
        ( Sᵉ))
```

### If every type is `f`-local, then `f` is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ)
  where

  is-equiv-is-localᵉ : ({lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → is-localᵉ fᵉ Aᵉ) → is-equivᵉ fᵉ
  is-equiv-is-localᵉ = is-equiv-is-equiv-precompᵉ fᵉ
```

### If the domain and codomain of `f` is `f`-local, then `f` is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ)
  where

  section-is-local-domains'ᵉ : sectionᵉ (precompᵉ fᵉ Xᵉ) → is-localᵉ fᵉ Yᵉ → sectionᵉ fᵉ
  pr1ᵉ (section-is-local-domains'ᵉ section-precomp-Xᵉ is-local-Yᵉ) =
    pr1ᵉ section-precomp-Xᵉ idᵉ
  pr2ᵉ (section-is-local-domains'ᵉ section-precomp-Xᵉ is-local-Yᵉ) =
    htpy-eqᵉ
      ( apᵉ
        ( pr1ᵉ)
        { ( fᵉ ∘ᵉ pr1ᵉ (section-is-local-domains'ᵉ section-precomp-Xᵉ is-local-Yᵉ)) ,ᵉ
          ( apᵉ (postcompᵉ Xᵉ fᵉ) (pr2ᵉ section-precomp-Xᵉ idᵉ))}
        { idᵉ ,ᵉ reflᵉ}
        ( eq-is-contrᵉ (is-contr-map-is-equivᵉ is-local-Yᵉ fᵉ)))

  is-equiv-is-local-domains'ᵉ : sectionᵉ (precompᵉ fᵉ Xᵉ) → is-localᵉ fᵉ Yᵉ → is-equivᵉ fᵉ
  pr1ᵉ (is-equiv-is-local-domains'ᵉ section-precomp-Xᵉ is-local-Yᵉ) =
    section-is-local-domains'ᵉ section-precomp-Xᵉ is-local-Yᵉ
  pr2ᵉ (is-equiv-is-local-domains'ᵉ section-precomp-Xᵉ is-local-Yᵉ) =
    retraction-section-precomp-domainᵉ fᵉ section-precomp-Xᵉ

  is-equiv-is-local-domainsᵉ : is-localᵉ fᵉ Xᵉ → is-localᵉ fᵉ Yᵉ → is-equivᵉ fᵉ
  is-equiv-is-local-domainsᵉ is-local-Xᵉ =
    is-equiv-is-local-domains'ᵉ (pr1ᵉ is-local-Xᵉ)
```

### Propositions are `f`-local if `_∘ f` has a converse

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ)
  where

  is-local-dependent-type-is-propᵉ :
    {lᵉ : Level} (Aᵉ : Yᵉ → UUᵉ lᵉ) →
    ((yᵉ : Yᵉ) → is-propᵉ (Aᵉ yᵉ)) →
    (((xᵉ : Xᵉ) → Aᵉ (fᵉ xᵉ)) → ((yᵉ : Yᵉ) → Aᵉ yᵉ)) →
    is-local-dependent-typeᵉ fᵉ Aᵉ
  is-local-dependent-type-is-propᵉ Aᵉ is-prop-Aᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-Πᵉ is-prop-Aᵉ)
      ( is-prop-Πᵉ (is-prop-Aᵉ ∘ᵉ fᵉ))

  is-local-is-propᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
    is-propᵉ Aᵉ → ((Xᵉ → Aᵉ) → (Yᵉ → Aᵉ)) → is-localᵉ fᵉ Aᵉ
  is-local-is-propᵉ Aᵉ is-prop-Aᵉ =
    is-local-dependent-type-is-propᵉ (λ _ → Aᵉ) (λ _ → is-prop-Aᵉ)
```

### All type families are local at equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ)
  where

  is-local-dependent-type-is-equivᵉ :
    is-equivᵉ fᵉ → {lᵉ : Level} (Aᵉ : Yᵉ → UUᵉ lᵉ) → is-local-dependent-typeᵉ fᵉ Aᵉ
  is-local-dependent-type-is-equivᵉ is-equiv-fᵉ =
    is-equiv-precomp-Π-is-equivᵉ is-equiv-fᵉ

  is-local-is-equivᵉ :
    is-equivᵉ fᵉ → {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → is-localᵉ fᵉ Aᵉ
  is-local-is-equivᵉ is-equiv-fᵉ = is-equiv-precomp-is-equivᵉ fᵉ is-equiv-fᵉ
```

### Contractible types are local at any map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ)
  where

  is-local-dependent-type-is-contrᵉ :
    {lᵉ : Level} (Aᵉ : Yᵉ → UUᵉ lᵉ) →
    ((yᵉ : Yᵉ) → is-contrᵉ (Aᵉ yᵉ)) → is-local-dependent-typeᵉ fᵉ Aᵉ
  is-local-dependent-type-is-contrᵉ Aᵉ is-contr-Aᵉ =
    is-equiv-is-contrᵉ
      ( precomp-Πᵉ fᵉ Aᵉ)
      ( is-contr-Πᵉ is-contr-Aᵉ)
      ( is-contr-Πᵉ (is-contr-Aᵉ ∘ᵉ fᵉ))

  is-local-is-contrᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → is-contrᵉ Aᵉ → is-localᵉ fᵉ Aᵉ
  is-local-is-contrᵉ Aᵉ is-contr-Aᵉ =
    is-local-dependent-type-is-contrᵉ (λ _ → Aᵉ) (λ _ → is-contr-Aᵉ)
```

### A type that is local at the unique map `empty → unit` is contractible

```agda
is-contr-is-localᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → is-localᵉ (λ (ᵉ_ : emptyᵉ) → starᵉ) Aᵉ → is-contrᵉ Aᵉ
is-contr-is-localᵉ Aᵉ is-local-Aᵉ =
  is-contr-is-equivᵉ
    ( emptyᵉ → Aᵉ)
    ( λ aᵉ _ → aᵉ)
    ( is-equiv-compᵉ
      ( λ a'ᵉ _ → a'ᵉ starᵉ)
      ( λ aᵉ _ →
        map-inv-is-equivᵉ (is-equiv-map-left-unit-law-Πᵉ (λ _ → Aᵉ)) aᵉ starᵉ)
      ( is-equiv-map-inv-is-equivᵉ (is-equiv-map-left-unit-law-Πᵉ (λ _ → Aᵉ)))
      ( is-local-Aᵉ))
    ( universal-property-empty'ᵉ Aᵉ)
```

## See also

-ᵉ [Localᵉ maps](orthogonal-factorization-systems.local-maps.mdᵉ)
-ᵉ [Localizationsᵉ with respectᵉ to maps](orthogonal-factorization-systems.localizations-maps.mdᵉ)
-ᵉ [Localizationsᵉ with respectᵉ to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.mdᵉ)