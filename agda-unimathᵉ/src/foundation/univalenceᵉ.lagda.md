# The univalence axiom

```agda
module foundation.univalenceᵉ where

open import foundation-core.univalenceᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.coherently-invertible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Theᵉ univalenceᵉ axiomᵉ characterizesᵉ theᵉ
[identityᵉ types](foundation-core.identity-types.mdᵉ) ofᵉ universes.ᵉ Itᵉ assertsᵉ
thatᵉ theᵉ mapᵉ `(Aᵉ ＝ᵉ Bᵉ) → (Aᵉ ≃ᵉ B)`ᵉ isᵉ anᵉ
[equivalence](foundation-core.equivalences.md).ᵉ

Inᵉ thisᵉ fileᵉ weᵉ postulate theᵉ univalenceᵉ axiom.ᵉ Itsᵉ statementᵉ isᵉ definedᵉ in
[`foundation-core.univalence`](foundation-core.univalence.md).ᵉ

## Postulates

Ratherᵉ thanᵉ postulatingᵉ aᵉ witnessᵉ ofᵉ `univalence-axiom`ᵉ directly,ᵉ weᵉ postulate
theᵉ constituentsᵉ ofᵉ aᵉ coherentᵉ two-sidedᵉ inverseᵉ to `equiv-eq`.ᵉ Theᵉ benefitsᵉ areᵉ
thatᵉ weᵉ endᵉ upᵉ with aᵉ singleᵉ converseᵉ mapᵉ to `equiv-eq`,ᵉ ratherᵉ thanᵉ aᵉ separateᵉ
sectionᵉ andᵉ retraction,ᵉ althoughᵉ theyᵉ wouldᵉ beᵉ homotopicᵉ regardless.ᵉ Inᵉ
addition,ᵉ thisᵉ formulationᵉ helpsᵉ Agdaᵉ displayᵉ goalsᵉ involvingᵉ theᵉ univalenceᵉ
axiomᵉ in aᵉ moreᵉ readableᵉ way.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ Bᵉ : UUᵉ lᵉ}
  where

  postulate
    eq-equivᵉ : Aᵉ ≃ᵉ Bᵉ → Aᵉ ＝ᵉ Bᵉ

    is-section-eq-equivᵉ : is-sectionᵉ equiv-eqᵉ eq-equivᵉ

    is-retraction-eq-equiv'ᵉ : is-retractionᵉ equiv-eqᵉ eq-equivᵉ

    coh-eq-equiv'ᵉ :
      coherence-is-coherently-invertibleᵉ
        ( equiv-eqᵉ)
        ( eq-equivᵉ)
        ( is-section-eq-equivᵉ)
        ( is-retraction-eq-equiv'ᵉ)

univalenceᵉ : univalence-axiomᵉ
univalenceᵉ Aᵉ Bᵉ =
  is-equiv-is-invertibleᵉ eq-equivᵉ is-section-eq-equivᵉ is-retraction-eq-equiv'ᵉ
```

## Properties

```agda
module _
  {lᵉ : Level} {Aᵉ Bᵉ : UUᵉ lᵉ}
  where

  equiv-univalenceᵉ : (Aᵉ ＝ᵉ Bᵉ) ≃ᵉ (Aᵉ ≃ᵉ Bᵉ)
  pr1ᵉ equiv-univalenceᵉ = equiv-eqᵉ
  pr2ᵉ equiv-univalenceᵉ = univalenceᵉ Aᵉ Bᵉ

  abstract
    is-retraction-eq-equivᵉ : is-retractionᵉ (equiv-eqᵉ {Aᵉ = Aᵉ} {Bᵉ}) eq-equivᵉ
    is-retraction-eq-equivᵉ =
      is-retraction-map-inv-is-equivᵉ (univalenceᵉ Aᵉ Bᵉ)

module _
  {lᵉ : Level}
  where

  is-equiv-eq-equivᵉ : (Aᵉ Bᵉ : UUᵉ lᵉ) → is-equivᵉ (eq-equivᵉ {Aᵉ = Aᵉ} {Bᵉ})
  is-equiv-eq-equivᵉ Aᵉ Bᵉ =
    is-equiv-is-invertibleᵉ equiv-eqᵉ is-retraction-eq-equiv'ᵉ is-section-eq-equivᵉ

  compute-eq-equiv-id-equivᵉ : (Aᵉ : UUᵉ lᵉ) → eq-equivᵉ {Aᵉ = Aᵉ} id-equivᵉ ＝ᵉ reflᵉ
  compute-eq-equiv-id-equivᵉ Aᵉ = is-retraction-eq-equivᵉ reflᵉ

  equiv-eq-equivᵉ : (Aᵉ Bᵉ : UUᵉ lᵉ) → (Aᵉ ≃ᵉ Bᵉ) ≃ᵉ (Aᵉ ＝ᵉ Bᵉ)
  pr1ᵉ (equiv-eq-equivᵉ Aᵉ Bᵉ) = eq-equivᵉ
  pr2ᵉ (equiv-eq-equivᵉ Aᵉ Bᵉ) = is-equiv-eq-equivᵉ Aᵉ Bᵉ
```

### The total space of all equivalences out of a type or into a type is contractible

Typeᵉ familiesᵉ ofᵉ whichᵉ theᵉ [totalᵉ space](foundation.dependent-pair-types.mdᵉ) isᵉ
[contractible](foundation-core.contractible-types.mdᵉ) areᵉ alsoᵉ calledᵉ
[torsorial](foundation-core.torsorial-type-families.md).ᵉ Thisᵉ terminologyᵉ
originatesᵉ fromᵉ higherᵉ groupᵉ theory,ᵉ where aᵉ
[higherᵉ groupᵉ action](higher-group-theory.higher-group-actions.mdᵉ) isᵉ torsorialᵉ
ifᵉ itsᵉ typeᵉ ofᵉ [orbits](higher-group-theory.orbits-higher-group-actions.md),ᵉ
i.e.,ᵉ itsᵉ totalᵉ space,ᵉ isᵉ contractible.ᵉ Ourᵉ claimᵉ thatᵉ theᵉ totalᵉ spaceᵉ ofᵉ allᵉ
equivalencesᵉ outᵉ ofᵉ aᵉ typeᵉ `A`ᵉ isᵉ contractibleᵉ canᵉ thereforeᵉ beᵉ statedᵉ moreᵉ
succinctlyᵉ asᵉ theᵉ claimᵉ thatᵉ theᵉ familyᵉ ofᵉ equivalencesᵉ outᵉ ofᵉ `A`ᵉ isᵉ torsorial.ᵉ

```agda
module _
  {lᵉ : Level}
  where

  abstract
    is-torsorial-equivᵉ :
      (Aᵉ : UUᵉ lᵉ) → is-torsorialᵉ (λ (Xᵉ : UUᵉ lᵉ) → Aᵉ ≃ᵉ Xᵉ)
    is-torsorial-equivᵉ Aᵉ =
      is-torsorial-equiv-based-univalenceᵉ Aᵉ (univalenceᵉ Aᵉ)

    is-torsorial-equiv'ᵉ :
      (Aᵉ : UUᵉ lᵉ) → is-torsorialᵉ (λ (Xᵉ : UUᵉ lᵉ) → Xᵉ ≃ᵉ Aᵉ)
    is-torsorial-equiv'ᵉ Aᵉ =
      is-contr-equiv'ᵉ
        ( Σᵉ (UUᵉ lᵉ) (λ Xᵉ → Xᵉ ＝ᵉ Aᵉ))
        ( equiv-totᵉ (λ Xᵉ → equiv-univalenceᵉ))
        ( is-torsorial-Id'ᵉ Aᵉ)
```

### Univalence for type families

```agda
equiv-famᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
equiv-famᵉ {Aᵉ = Aᵉ} Bᵉ Cᵉ = (aᵉ : Aᵉ) → Bᵉ aᵉ ≃ᵉ Cᵉ aᵉ

id-equiv-famᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) → equiv-famᵉ Bᵉ Bᵉ
id-equiv-famᵉ Bᵉ aᵉ = id-equivᵉ

equiv-eq-famᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ Cᵉ : Aᵉ → UUᵉ l2ᵉ) → Bᵉ ＝ᵉ Cᵉ → equiv-famᵉ Bᵉ Cᵉ
equiv-eq-famᵉ Bᵉ .Bᵉ reflᵉ = id-equiv-famᵉ Bᵉ

abstract
  is-torsorial-equiv-famᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
    is-torsorialᵉ (λ (Cᵉ : Aᵉ → UUᵉ l2ᵉ) → equiv-famᵉ Bᵉ Cᵉ)
  is-torsorial-equiv-famᵉ Bᵉ =
    is-torsorial-Eq-Πᵉ (λ xᵉ → is-torsorial-equivᵉ (Bᵉ xᵉ))

abstract
  is-equiv-equiv-eq-famᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ Cᵉ : Aᵉ → UUᵉ l2ᵉ) → is-equivᵉ (equiv-eq-famᵉ Bᵉ Cᵉ)
  is-equiv-equiv-eq-famᵉ Bᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-equiv-famᵉ Bᵉ)
      ( equiv-eq-famᵉ Bᵉ)

extensionality-famᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ Cᵉ : Aᵉ → UUᵉ l2ᵉ) → (Bᵉ ＝ᵉ Cᵉ) ≃ᵉ equiv-famᵉ Bᵉ Cᵉ
pr1ᵉ (extensionality-famᵉ Bᵉ Cᵉ) = equiv-eq-famᵉ Bᵉ Cᵉ
pr2ᵉ (extensionality-famᵉ Bᵉ Cᵉ) = is-equiv-equiv-eq-famᵉ Bᵉ Cᵉ

eq-equiv-famᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ Cᵉ : Aᵉ → UUᵉ l2ᵉ} → equiv-famᵉ Bᵉ Cᵉ → Bᵉ ＝ᵉ Cᵉ
eq-equiv-famᵉ {Bᵉ = Bᵉ} {Cᵉ} = map-inv-is-equivᵉ (is-equiv-equiv-eq-famᵉ Bᵉ Cᵉ)
```

### Computations with univalence

```agda
compute-equiv-eq-concatᵉ :
  {lᵉ : Level} {Aᵉ Bᵉ Cᵉ : UUᵉ lᵉ} (pᵉ : Aᵉ ＝ᵉ Bᵉ) (qᵉ : Bᵉ ＝ᵉ Cᵉ) →
  equiv-eqᵉ qᵉ ∘eᵉ equiv-eqᵉ pᵉ ＝ᵉ equiv-eqᵉ (pᵉ ∙ᵉ qᵉ)
compute-equiv-eq-concatᵉ reflᵉ reflᵉ = eq-equiv-eq-map-equivᵉ reflᵉ

compute-eq-equiv-comp-equivᵉ :
  {lᵉ : Level} {Aᵉ Bᵉ Cᵉ : UUᵉ lᵉ} (fᵉ : Aᵉ ≃ᵉ Bᵉ) (gᵉ : Bᵉ ≃ᵉ Cᵉ) →
  eq-equivᵉ fᵉ ∙ᵉ eq-equivᵉ gᵉ ＝ᵉ eq-equivᵉ (gᵉ ∘eᵉ fᵉ)
compute-eq-equiv-comp-equivᵉ fᵉ gᵉ =
  is-injective-equivᵉ
    ( equiv-univalenceᵉ)
    ( ( invᵉ ( compute-equiv-eq-concatᵉ (eq-equivᵉ fᵉ) (eq-equivᵉ gᵉ))) ∙ᵉ
      ( ( apᵉ
          ( λ eᵉ → (map-equivᵉ eᵉ gᵉ) ∘eᵉ (equiv-eqᵉ (eq-equivᵉ fᵉ)))
          ( right-inverse-law-equivᵉ equiv-univalenceᵉ)) ∙ᵉ
        ( ( apᵉ
            ( λ eᵉ → gᵉ ∘eᵉ map-equivᵉ eᵉ fᵉ)
            ( right-inverse-law-equivᵉ equiv-univalenceᵉ)) ∙ᵉ
          ( apᵉ
            ( λ eᵉ → map-equivᵉ eᵉ (gᵉ ∘eᵉ fᵉ))
            ( invᵉ (right-inverse-law-equivᵉ equiv-univalenceᵉ))))))

compute-map-eq-ap-invᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
  map-eqᵉ (apᵉ Bᵉ (invᵉ pᵉ)) ∘ᵉ map-eqᵉ (apᵉ Bᵉ pᵉ) ~ᵉ idᵉ
compute-map-eq-ap-invᵉ reflᵉ = refl-htpyᵉ

commutativity-inv-equiv-eqᵉ :
  {lᵉ : Level} {Aᵉ Bᵉ : UUᵉ lᵉ} (pᵉ : Aᵉ ＝ᵉ Bᵉ) →
  inv-equivᵉ (equiv-eqᵉ pᵉ) ＝ᵉ equiv-eqᵉ (invᵉ pᵉ)
commutativity-inv-equiv-eqᵉ reflᵉ = eq-equiv-eq-map-equivᵉ reflᵉ

commutativity-inv-eq-equivᵉ :
  {lᵉ : Level} {Aᵉ Bᵉ : UUᵉ lᵉ} (fᵉ : Aᵉ ≃ᵉ Bᵉ) →
  invᵉ (eq-equivᵉ fᵉ) ＝ᵉ eq-equivᵉ (inv-equivᵉ fᵉ)
commutativity-inv-eq-equivᵉ fᵉ =
  is-injective-equivᵉ
    ( equiv-univalenceᵉ)
    ( ( invᵉ (commutativity-inv-equiv-eqᵉ (eq-equivᵉ fᵉ))) ∙ᵉ
      ( ( apᵉ
          ( λ eᵉ → (inv-equivᵉ (map-equivᵉ eᵉ fᵉ)))
          ( right-inverse-law-equivᵉ equiv-univalenceᵉ)) ∙ᵉ
        ( apᵉ
          ( λ eᵉ → map-equivᵉ eᵉ (inv-equivᵉ fᵉ))
          ( invᵉ (right-inverse-law-equivᵉ equiv-univalenceᵉ)))))
```