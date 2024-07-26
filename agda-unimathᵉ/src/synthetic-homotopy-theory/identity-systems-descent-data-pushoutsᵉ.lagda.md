# Identity systems of descent data for pushouts

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module synthetic-homotopy-theory.identity-systems-descent-data-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-systemsᵉ
open import foundation.identity-typesᵉ
open import foundation.sectionsᵉ
open import foundation.singleton-inductionᵉ
open import foundation.span-diagramsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transposition-identifications-along-equivalencesᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universal-property-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-universal-property-pushoutsᵉ
open import synthetic-homotopy-theory.descent-data-equivalence-types-over-pushoutsᵉ
open import synthetic-homotopy-theory.descent-data-identity-types-over-pushoutsᵉ
open import synthetic-homotopy-theory.descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.descent-property-pushoutsᵉ
open import synthetic-homotopy-theory.equivalences-descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.families-descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.flattening-lemma-pushoutsᵉ
open import synthetic-homotopy-theory.morphisms-descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.sections-descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Weᵉ defineᵉ aᵉ universalᵉ propertyᵉ ofᵉ
[descentᵉ data](synthetic-homotopy-theory.descent-data-pushouts.mdᵉ) forᵉ theᵉ
[identityᵉ types](foundation-core.identity-types.mdᵉ) ofᵉ
[pushouts](synthetic-homotopy-theory.pushouts.md),ᵉ whichᵉ allowsᵉ theirᵉ
alternativeᵉ characterizations.ᵉ Theᵉ propertyᵉ isᵉ analogousᵉ to beingᵉ anᵉ
[identityᵉ system](foundation.identity-systems.md);ᵉ in fact,ᵉ weᵉ showᵉ thatᵉ aᵉ typeᵉ
familyᵉ overᵉ aᵉ pushoutᵉ isᵉ anᵉ identityᵉ systemᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ correspondingᵉ
descentᵉ data satisfiesᵉ thisᵉ universalᵉ property.ᵉ

Givenᵉ descentᵉ data `(PA,ᵉ PB,ᵉ PS)`ᵉ forᵉ theᵉ pushoutᵉ

```text
        gᵉ
    Sᵉ ----->ᵉ Bᵉ
    |        |
  fᵉ |   Hᵉ    | jᵉ
    ∨ᵉ        ∨ᵉ
    Aᵉ ----->ᵉ Xᵉ
        iᵉ
```

andᵉ aᵉ pointᵉ `p₀ᵉ : PAᵉ a₀`ᵉ overᵉ aᵉ basepointᵉ `a₀ᵉ : A`,ᵉ weᵉ wouldᵉ likeᵉ to mirrorᵉ theᵉ
definitionᵉ ofᵉ identityᵉ systems.ᵉ Aᵉ naïveᵉ translationᵉ wouldᵉ leadᵉ usᵉ to defineᵉ
dependentᵉ descentᵉ data andᵉ itsᵉ sections.ᵉ Weᵉ chooseᵉ to sidestepᵉ buildingᵉ thatᵉ
technicalᵉ infrastructure.ᵉ Byᵉ theᵉ
[descentᵉ property](synthetic-homotopy-theory.descent-property-pushouts.md),ᵉ
thereᵉ isᵉ aᵉ [unique](foundation-core.contractible-types.mdᵉ) typeᵉ familyᵉ
`Pᵉ : Xᵉ → 𝒰`ᵉ
[corresponding](synthetic-homotopy-theory.families-descent-data-pushouts.mdᵉ) to
`(PA,ᵉ PB,ᵉ PS)`.ᵉ Observeᵉ thatᵉ theᵉ typeᵉ ofᵉ dependentᵉ typeᵉ familiesᵉ
`(xᵉ : Xᵉ) → (pᵉ : Pᵉ xᵉ) → 𝒰`ᵉ isᵉ [equivalent](foundation-core.equivalences.mdᵉ) to
theᵉ [uncurried](foundation.universal-property-dependent-pair-types.mdᵉ) formᵉ
`(Σᵉ Xᵉ Pᵉ) → 𝒰`.ᵉ Byᵉ theᵉ
[flatteningᵉ lemma](synthetic-homotopy-theory.flattening-lemma-pushouts.md),ᵉ theᵉ
totalᵉ spaceᵉ `Σᵉ Xᵉ P`ᵉ isᵉ theᵉ pushoutᵉ ofᵉ theᵉ
[spanᵉ diagram](foundation.span-diagrams.mdᵉ) ofᵉ totalᵉ spacesᵉ

```text
  Σᵉ Aᵉ PAᵉ <-----ᵉ Σᵉ Sᵉ (PAᵉ ∘ᵉ fᵉ) ----->ᵉ Σᵉ Bᵉ PB,ᵉ
```

so,ᵉ againᵉ byᵉ theᵉ descentᵉ property,ᵉ descentᵉ data overᵉ itᵉ correspondᵉ to typeᵉ
familiesᵉ overᵉ `Σᵉ Xᵉ P`.ᵉ Henceᵉ weᵉ canᵉ talkᵉ aboutᵉ descentᵉ data `(RΣA,ᵉ RΣB,ᵉ RΣS)`ᵉ
overᵉ theᵉ totalᵉ spanᵉ diagramᵉ insteadᵉ ofᵉ dependentᵉ descentᵉ data.ᵉ

Everyᵉ suchᵉ descentᵉ data inducesᵉ anᵉ evaluationᵉ mapᵉ `ev-refl`ᵉ onᵉ itsᵉ
[sections](synthetic-homotopy-theory.sections-descent-data-pushouts.md),ᵉ whichᵉ
takesᵉ aᵉ sectionᵉ `(tA,ᵉ tB,ᵉ tS)`ᵉ ofᵉ `(RΣA,ᵉ RΣB,ᵉ RΣS)`ᵉ to theᵉ pointᵉ
`tAᵉ (a₀,ᵉ p₀ᵉ) : RΣAᵉ (a₀,ᵉ p₀)`.ᵉ Weᵉ sayᵉ thatᵉ `(PA,ᵉ PB,ᵉ PS)`ᵉ isᵉ anᵉ
{{#conceptᵉ "identityᵉ system"ᵉ Disambiguation="descentᵉ data forᵉ pushouts"ᵉ Agda=is-identity-system-descent-data-pushoutᵉ}}
basedᵉ atᵉ `p₀`ᵉ ifᵉ `ev-refl`ᵉ hasᵉ aᵉ [section](foundation-core.sections.md),ᵉ in theᵉ
senseᵉ thatᵉ thereᵉ isᵉ aᵉ converseᵉ mapᵉ
`ind-Rᵉ : RΣAᵉ (a₀,ᵉ p₀ᵉ) → section-descent-dataᵉ (RΣA,ᵉ RΣB,ᵉ RΣS)`ᵉ suchᵉ thatᵉ
`(ind-Rᵉ r)Aᵉ (a₀,ᵉ p₀ᵉ) = r`ᵉ forᵉ allᵉ `rᵉ : RΣAᵉ (a₀,ᵉ p₀)`.ᵉ Mindᵉ theᵉ unfortunateᵉ
terminologyᵉ clashᵉ betweenᵉ "sectionsᵉ ofᵉ descentᵉ data"ᵉ andᵉ "sectionsᵉ ofᵉ aᵉ map".ᵉ

Noteᵉ thatᵉ thisᵉ developmentᵉ isᵉ biasedᵉ towardsᵉ to leftᵉ ---ᵉ weᵉ pickᵉ aᵉ basepointᵉ in
theᵉ domainᵉ `a₀ᵉ : A`,ᵉ aᵉ pointᵉ in theᵉ leftᵉ typeᵉ familyᵉ `p₀ᵉ : PAᵉ a₀`,ᵉ andᵉ theᵉ
evaluationᵉ mapᵉ evaluatesᵉ theᵉ leftᵉ mapᵉ ofᵉ theᵉ section.ᵉ Byᵉ symmetryᵉ ofᵉ pushoutsᵉ weᵉ
couldᵉ justᵉ asᵉ wellᵉ workᵉ with theᵉ pointsᵉ `b₀ᵉ : B`,ᵉ `p₀ᵉ : PBᵉ b₀`,ᵉ andᵉ theᵉ
evaluationᵉ mapᵉ evaluatingᵉ theᵉ rightᵉ mapᵉ ofᵉ theᵉ section.ᵉ

Byᵉ showingᵉ thatᵉ theᵉ canonicalᵉ
[descentᵉ data forᵉ identityᵉ types](synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.mdᵉ)
isᵉ anᵉ identityᵉ system,ᵉ weᵉ recoverᵉ theᵉ "inductionᵉ principleᵉ forᵉ pushoutᵉ equality"ᵉ
statedᵉ andᵉ provedᵉ byᵉ Krausᵉ andᵉ vonᵉ Raumerᵉ in {{#citeᵉ KvR19}}.ᵉ

Firstᵉ observeᵉ thatᵉ theᵉ typeᵉ ofᵉ sectionsᵉ ofᵉ theᵉ evaluationᵉ mapᵉ isᵉ

```text
  Σᵉ (ind-Rᵉ : (rᵉ : RΣAᵉ (a₀,ᵉ p₀ᵉ)) → sectionᵉ (RΣA,ᵉ RΣB,ᵉ RΣSᵉ))
    (is-sectᵉ : (rᵉ : RΣAᵉ (a₀,ᵉ p₀ᵉ)) → (ind-Rᵉ r)Aᵉ (a₀,ᵉ p₀ᵉ) = r),ᵉ
```

whichᵉ isᵉ equivalentᵉ to theᵉ typeᵉ

```text
  (rᵉ : RΣAᵉ (a₀,ᵉ p₀ᵉ)) →
  Σᵉ (indᵉ : sectionᵉ (RΣA,ᵉ RΣB,ᵉ RΣSᵉ))
    (preserves-ptᵉ : indAᵉ (a₀,ᵉ p₀ᵉ) = rᵉ)
```

byᵉ
[distributivityᵉ ofᵉ Πᵉ overᵉ Σ](foundation-core.type-theoretic-principle-of-choice.md).ᵉ

Thenᵉ theᵉ inductionᵉ termsᵉ fromᵉ {{#citeᵉ KvR19ᵉ}} (withᵉ namesᵉ changedᵉ to fitᵉ ourᵉ
namingᵉ schemeᵉ)

```text
  indᴬᵉ : (aᵉ : Aᵉ) (qᵉ : ia₀ᵉ = iaᵉ) → RΣAᵉ (a,ᵉ qᵉ)
  indᴮᵉ : (bᵉ : Bᵉ) (qᵉ : ia₀ᵉ = jbᵉ) → RΣBᵉ (b,ᵉ qᵉ)
```

areᵉ theᵉ firstᵉ andᵉ secondᵉ componentsᵉ ofᵉ theᵉ sectionᵉ ofᵉ `(RΣA,ᵉ RΣB,ᵉ RΣS)`ᵉ inducedᵉ
byᵉ `r`,ᵉ andᵉ theirᵉ computationᵉ rulesᵉ

```text
  indᴬᵉ a₀ᵉ reflᵉ = rᵉ
  (sᵉ : Sᵉ) (qᵉ : ia₀ᵉ = ifaᵉ) → RΣSᵉ (s,ᵉ qᵉ) (indᴬᵉ fsᵉ qᵉ) = indᴮᵉ gsᵉ (qᵉ ∙ᵉ Hᵉ sᵉ)
```

ariseᵉ asᵉ theᵉ `preserves-pt`ᵉ componentᵉ above,ᵉ andᵉ theᵉ coherenceᵉ conditionᵉ ofᵉ aᵉ
sectionᵉ ofᵉ `(RΣA,ᵉ RΣB,ᵉ RΣS)`,ᵉ respectively.ᵉ

## Definitions

### The evaluation map of a section of descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ) {a₀ᵉ : domain-span-diagramᵉ 𝒮ᵉ}
  (p₀ᵉ : left-family-descent-data-pushoutᵉ Pᵉ a₀ᵉ)
  where

  ev-refl-section-descent-data-pushoutᵉ :
    {l5ᵉ : Level}
    (Rᵉ :
      descent-data-pushoutᵉ (span-diagram-flattening-descent-data-pushoutᵉ Pᵉ) l5ᵉ)
    (tᵉ : section-descent-data-pushoutᵉ Rᵉ) →
    left-family-descent-data-pushoutᵉ Rᵉ (a₀ᵉ ,ᵉ p₀ᵉ)
  ev-refl-section-descent-data-pushoutᵉ Rᵉ tᵉ =
    left-map-section-descent-data-pushoutᵉ Rᵉ tᵉ (a₀ᵉ ,ᵉ p₀ᵉ)
```

### The predicate of being an identity system on descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ) {a₀ᵉ : domain-span-diagramᵉ 𝒮ᵉ}
  (p₀ᵉ : left-family-descent-data-pushoutᵉ Pᵉ a₀ᵉ)
  where

  is-identity-system-descent-data-pushoutᵉ : UUωᵉ
  is-identity-system-descent-data-pushoutᵉ =
    {l5ᵉ : Level}
    (Rᵉ :
      descent-data-pushoutᵉ
        ( span-diagram-flattening-descent-data-pushoutᵉ Pᵉ)
        ( l5ᵉ)) →
    sectionᵉ (ev-refl-section-descent-data-pushoutᵉ Pᵉ p₀ᵉ Rᵉ)
```

## Properties

### A type family over a pushout is an identity system if and only if the corresponding descent data is an identity system

Givenᵉ aᵉ familyᵉ with descentᵉ data `Pᵉ ≃ᵉ (PA,ᵉ PB,ᵉ PS)`ᵉ andᵉ aᵉ pointᵉ `p₀ᵉ : PAᵉ a₀`,ᵉ weᵉ
showᵉ thatᵉ `(PA,ᵉ PB,ᵉ PS)`ᵉ isᵉ anᵉ identityᵉ systemᵉ atᵉ `p₀`ᵉ ifᵉ anᵉ onlyᵉ ifᵉ `P`ᵉ isᵉ anᵉ
identityᵉ systemᵉ atᵉ `(eᴾAᵉ a)⁻¹ᵉ p₀ᵉ : Pᵉ (ia₀)`.ᵉ

**Proof:**ᵉ Considerᵉ aᵉ familyᵉ with descentᵉ data `RΣᵉ ≈ᵉ (RΣA,ᵉ RΣB,ᵉ RΣS)`.ᵉ Recallᵉ
thatᵉ thisᵉ datumᵉ consistsᵉ ofᵉ aᵉ typeᵉ familyᵉ `RΣᵉ : Σᵉ Xᵉ Pᵉ → 𝒰`,ᵉ descentᵉ data

```text
  RΣAᵉ : Σᵉ Aᵉ PAᵉ → 𝒰ᵉ
  RΣBᵉ : Σᵉ Bᵉ PBᵉ → 𝒰ᵉ
  RΣSᵉ : ((s,ᵉ pᵉ) : (Σᵉ (sᵉ : Sᵉ) (pᵉ : PAᵉ fsᵉ))) → RΣAᵉ (fs,ᵉ pᵉ) ≃ᵉ RΣBᵉ (gs,ᵉ PSᵉ sᵉ p),ᵉ
```

aᵉ pairᵉ ofᵉ equivalencesᵉ

```text
  eᴿAᵉ : ((a,ᵉ pᵉ) : Σᵉ Aᵉ PAᵉ) → RΣᵉ (ia,ᵉ (eᴾAᵉ a)⁻¹ᵉ pᵉ) ≃ᵉ RΣAᵉ (a,ᵉ pᵉ)
  eᴿBᵉ : ((b,ᵉ pᵉ) : Σᵉ Bᵉ PBᵉ) → RΣᵉ (jb,ᵉ (eᴾBᵉ b)⁻¹ᵉ pᵉ) ≃ᵉ RΣBᵉ (b,ᵉ p),ᵉ
```

andᵉ aᵉ coherenceᵉ betweenᵉ themᵉ thatᵉ isn'tᵉ relevantᵉ here.ᵉ Thenᵉ thereᵉ isᵉ aᵉ
[commutingᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ)

```text
  (xᵉ : Xᵉ) → (pᵉ : Pᵉ xᵉ) → RΣᵉ (x,ᵉ pᵉ) --->ᵉ (uᵉ : Σᵉ Xᵉ Pᵉ) → RΣᵉ uᵉ ---->ᵉ sectionᵉ (RΣA,ᵉ RΣB,ᵉ RΣSᵉ)
                |                                                           |
                | ev-reflᵉ ((eᴾAᵉ a)⁻¹ᵉ p₀ᵉ)                                    | ev-reflᵉ p₀ᵉ
                |                                                           |
                ∨ᵉ                                                           ∨ᵉ
      RΣᵉ (ia₀,ᵉ (eᴾAᵉ a)⁻¹ᵉ p₀ᵉ) --------------------------------------->ᵉ RΣAᵉ (a₀,ᵉ p₀).ᵉ
                                      eᴿAᵉ (a₀,ᵉ p₀ᵉ)
```

Sinceᵉ theᵉ topᵉ andᵉ bottomᵉ mapsᵉ areᵉ equivalences,ᵉ weᵉ getᵉ thatᵉ theᵉ leftᵉ mapᵉ hasᵉ aᵉ
sectionᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ rightᵉ mapᵉ hasᵉ aᵉ section.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} {cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ}
  (Pᵉ : family-with-descent-data-pushoutᵉ cᵉ l5ᵉ)
  {a₀ᵉ : domain-span-diagramᵉ 𝒮ᵉ}
  (p₀ᵉ : left-family-family-with-descent-data-pushoutᵉ Pᵉ a₀ᵉ)
  where

  private
    cocone-flatteningᵉ :
      cocone-span-diagramᵉ
        ( span-diagram-flattening-descent-data-pushoutᵉ
          ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ))
        ( Σᵉ Xᵉ (family-cocone-family-with-descent-data-pushoutᵉ Pᵉ))
    cocone-flatteningᵉ =
      cocone-flattening-descent-data-pushoutᵉ _ _ cᵉ
        ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
        ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ)
        ( inv-equiv-descent-data-family-with-descent-data-pushoutᵉ Pᵉ)

  square-ev-refl-section-descent-data-pushoutᵉ :
    {l5ᵉ : Level}
    (Rᵉ :
      family-with-descent-data-pushoutᵉ
        ( cocone-flattening-descent-data-pushoutᵉ _ _ cᵉ
          ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
          ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ)
          ( inv-equiv-descent-data-pushoutᵉ _ _
            ( equiv-descent-data-family-with-descent-data-pushoutᵉ Pᵉ)))
        ( l5ᵉ)) →
    coherence-square-mapsᵉ
      ( section-descent-data-section-family-cocone-span-diagramᵉ Rᵉ ∘ᵉ ind-Σᵉ)
      ( ev-refl-identity-systemᵉ
        ( inv-left-map-family-with-descent-data-pushoutᵉ Pᵉ a₀ᵉ p₀ᵉ))
      ( ev-refl-section-descent-data-pushoutᵉ
        ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
        ( p₀ᵉ)
        ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ))
      ( left-map-family-with-descent-data-pushoutᵉ Rᵉ (a₀ᵉ ,ᵉ p₀ᵉ))
  square-ev-refl-section-descent-data-pushoutᵉ Rᵉ = refl-htpyᵉ
```

Toᵉ showᵉ theᵉ forwardᵉ implication,ᵉ assumeᵉ thatᵉ `(PA,ᵉ PB,ᵉ PS)`ᵉ isᵉ anᵉ identityᵉ
systemᵉ atᵉ `p₀`.ᵉ Weᵉ needᵉ to showᵉ thatᵉ forᵉ everyᵉ `Rᵉ : (xᵉ : Xᵉ) (pᵉ : Pᵉ xᵉ) → 𝒰`,ᵉ theᵉ
evaluationᵉ mapᵉ `ev-reflᵉ ((eᴾAᵉ a)⁻¹ᵉ p₀)`ᵉ hasᵉ aᵉ section.ᵉ Byᵉ theᵉ descentᵉ property,ᵉ
thereᵉ isᵉ uniqueᵉ descentᵉ data `(RΣA,ᵉ RΣB,ᵉ RΣS)`ᵉ forᵉ theᵉ uncurriedᵉ familyᵉ
`RΣᵉ :=ᵉ λ (x,ᵉ pᵉ) → Rᵉ xᵉ p`.ᵉ Thenᵉ weᵉ getᵉ theᵉ aboveᵉ square,ᵉ andᵉ byᵉ assumptionᵉ theᵉ
rightᵉ mapᵉ hasᵉ aᵉ section,ᵉ henceᵉ theᵉ leftᵉ mapᵉ hasᵉ aᵉ section.ᵉ

```agda
  abstract
    is-identity-system-is-identity-system-descent-data-pushoutᵉ :
      universal-property-pushoutᵉ _ _ cᵉ →
      is-identity-system-descent-data-pushoutᵉ
        ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
        ( p₀ᵉ) →
      is-identity-systemᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ)
        ( horizontal-map-coconeᵉ _ _ cᵉ a₀ᵉ)
        ( inv-left-map-family-with-descent-data-pushoutᵉ Pᵉ a₀ᵉ p₀ᵉ)
    is-identity-system-is-identity-system-descent-data-pushoutᵉ
      up-cᵉ id-system-Pᵉ {lᵉ} Rᵉ =
      section-left-map-triangleᵉ _ _ _
        ( square-ev-refl-section-descent-data-pushoutᵉ fam-Rᵉ)
        ( section-is-equivᵉ
          ( is-equiv-compᵉ _ _
            ( is-equiv-ind-Σᵉ)
            ( is-equiv-section-descent-data-section-family-cocone-span-diagramᵉ
              ( fam-Rᵉ)
              ( flattening-lemma-descent-data-pushoutᵉ _ _ cᵉ
                ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
                ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ)
                ( inv-equiv-descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
                ( up-cᵉ)))))
        ( id-system-Pᵉ (descent-data-family-with-descent-data-pushoutᵉ fam-Rᵉ))
      where
        fam-Rᵉ : family-with-descent-data-pushoutᵉ cocone-flatteningᵉ lᵉ
        fam-Rᵉ =
          family-with-descent-data-pushout-family-coconeᵉ
            ( cocone-flatteningᵉ)
            ( ind-Σᵉ Rᵉ)
```

Similarly,ᵉ assumeᵉ `P`ᵉ isᵉ anᵉ identityᵉ systemᵉ atᵉ `(eᴾAᵉ a)⁻¹ᵉ p₀`,ᵉ andᵉ assumeᵉ
descentᵉ data `(RΣA,ᵉ RΣB,ᵉ RΣS)`.ᵉ Thereᵉ isᵉ aᵉ uniqueᵉ correspondingᵉ typeᵉ familyᵉ
`RΣ`.ᵉ Thenᵉ theᵉ squareᵉ aboveᵉ commutes,ᵉ andᵉ theᵉ leftᵉ mapᵉ hasᵉ aᵉ sectionᵉ byᵉ
assumption,ᵉ soᵉ theᵉ rightᵉ mapᵉ hasᵉ aᵉ section.ᵉ

```agda
  abstract
    is-identity-system-descent-data-pushout-is-identity-systemᵉ :
      universal-property-pushoutᵉ _ _ cᵉ →
      is-identity-systemᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ)
        ( horizontal-map-coconeᵉ _ _ cᵉ a₀ᵉ)
        ( inv-left-map-family-with-descent-data-pushoutᵉ Pᵉ a₀ᵉ p₀ᵉ) →
      is-identity-system-descent-data-pushoutᵉ
        ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
        ( p₀ᵉ)
    is-identity-system-descent-data-pushout-is-identity-systemᵉ
      up-cᵉ id-system-Pᵉ {lᵉ} Rᵉ =
      section-right-map-triangleᵉ _ _ _
        ( square-ev-refl-section-descent-data-pushoutᵉ fam-Rᵉ)
        ( section-compᵉ _ _
          ( id-system-Pᵉ
            ( ev-pairᵉ (family-cocone-family-with-descent-data-pushoutᵉ fam-Rᵉ)))
          ( section-map-equivᵉ
            ( left-equiv-family-with-descent-data-pushoutᵉ fam-Rᵉ (a₀ᵉ ,ᵉ p₀ᵉ))))
      where
        fam-Rᵉ : family-with-descent-data-pushoutᵉ cocone-flatteningᵉ lᵉ
        fam-Rᵉ =
          family-with-descent-data-pushout-descent-data-pushoutᵉ
            ( flattening-lemma-descent-data-pushoutᵉ _ _ cᵉ
              ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
              ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ)
              ( inv-equiv-descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
              ( up-cᵉ))
            ( Rᵉ)
```

### The canonical descent data for families of identity types is an identity system

**Proof:**ᵉ Byᵉ theᵉ aboveᵉ property,ᵉ theᵉ descentᵉ data `(IA,ᵉ IB,ᵉ IS)`ᵉ isᵉ anᵉ identityᵉ
systemᵉ atᵉ `reflᵉ : ia₀ᵉ = ia₀`ᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ correspondingᵉ typeᵉ familyᵉ
`Idᵉ (ia₀ᵉ) : Xᵉ → 𝒰`ᵉ isᵉ anᵉ identityᵉ systemᵉ atᵉ `refl`,ᵉ whichᵉ isᵉ alreadyᵉ
established.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} {cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ}
  (up-cᵉ : universal-property-pushoutᵉ _ _ cᵉ)
  (a₀ᵉ : domain-span-diagramᵉ 𝒮ᵉ)
  where

  abstract
    induction-principle-descent-data-pushout-identity-typeᵉ :
      is-identity-system-descent-data-pushoutᵉ
        ( descent-data-identity-type-pushoutᵉ cᵉ (horizontal-map-coconeᵉ _ _ cᵉ a₀ᵉ))
        ( reflᵉ)
    induction-principle-descent-data-pushout-identity-typeᵉ =
      is-identity-system-descent-data-pushout-is-identity-systemᵉ
        ( family-with-descent-data-identity-type-pushoutᵉ cᵉ
          ( horizontal-map-coconeᵉ _ _ cᵉ a₀ᵉ))
        ( reflᵉ)
        ( up-cᵉ)
        ( is-identity-system-is-torsorialᵉ
          ( horizontal-map-coconeᵉ _ _ cᵉ a₀ᵉ)
          ( reflᵉ)
          ( is-torsorial-Idᵉ _))
```

### Unique uniqueness of identity systems

Forᵉ anyᵉ identityᵉ systemᵉ `(PA,ᵉ PB,ᵉ PS)`ᵉ atᵉ `p₀`,ᵉ thereᵉ isᵉ aᵉ uniqueᵉ
[equivalenceᵉ ofᵉ descentᵉ data](synthetic-homotopy-theory.equivalences-descent-data-pushouts.mdᵉ)
`(IA,ᵉ IB,ᵉ ISᵉ) ≃ᵉ (PA,ᵉ PB,ᵉ PS)`ᵉ sendingᵉ `refl`ᵉ to `p₀`.ᵉ

**Proof:**ᵉ Considerᵉ theᵉ uniqueᵉ typeᵉ familyᵉ `Pᵉ : Xᵉ → 𝒰`ᵉ correspondingᵉ to
`(PA,ᵉ PB,ᵉ PS).`ᵉ Theᵉ typeᵉ ofᵉ pointᵉ preservingᵉ equivalencesᵉ betweenᵉ `(IA,ᵉ IB,ᵉ IS)`ᵉ
andᵉ `(PA,ᵉ PB,ᵉ PS)`ᵉ isᵉ equivalentᵉ to theᵉ typeᵉ ofᵉ
[fiberwiseᵉ equivalences](foundation-core.families-of-equivalences.mdᵉ)
`(xᵉ : Xᵉ) → (ia₀ᵉ = xᵉ) ≃ᵉ Pᵉ x`ᵉ thatᵉ sendᵉ `refl`ᵉ to `(eᴾAᵉ a₀)⁻¹ᵉ p₀`.ᵉ Toᵉ showᵉ thatᵉ
thisᵉ typeᵉ isᵉ contractible,ᵉ itᵉ sufficesᵉ to showᵉ thatᵉ `P`ᵉ isᵉ
[torsorial](foundation-core.torsorial-type-families.md).ᵉ Aᵉ typeᵉ familyᵉ isᵉ
torsorialᵉ ifᵉ itᵉ isᵉ anᵉ identityᵉ system,ᵉ andᵉ weᵉ haveᵉ shownᵉ thatᵉ `(PA,ᵉ PB,ᵉ PS)`ᵉ
beingᵉ anᵉ identityᵉ systemᵉ impliesᵉ thatᵉ `P`ᵉ isᵉ anᵉ identityᵉ system.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} {cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ}
  (up-cᵉ : universal-property-pushoutᵉ _ _ cᵉ)
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l5ᵉ) {a₀ᵉ : domain-span-diagramᵉ 𝒮ᵉ}
  (p₀ᵉ : left-family-descent-data-pushoutᵉ Pᵉ a₀ᵉ)
  (id-system-Pᵉ : is-identity-system-descent-data-pushoutᵉ Pᵉ p₀ᵉ)
  where

  abstract
    unique-uniqueness-identity-system-descent-data-pushoutᵉ :
      is-contrᵉ
        ( Σᵉ ( equiv-descent-data-pushoutᵉ
              ( descent-data-identity-type-pushoutᵉ cᵉ
                ( horizontal-map-coconeᵉ _ _ cᵉ a₀ᵉ))
              ( Pᵉ))
            ( λ eᵉ → left-map-equiv-descent-data-pushoutᵉ _ _ eᵉ a₀ᵉ reflᵉ ＝ᵉ p₀ᵉ))
    unique-uniqueness-identity-system-descent-data-pushoutᵉ =
      is-contr-is-equiv'ᵉ
        ( Σᵉ ( (xᵉ : Xᵉ) →
              (horizontal-map-coconeᵉ _ _ cᵉ a₀ᵉ ＝ᵉ xᵉ) ≃ᵉ
              family-cocone-family-with-descent-data-pushoutᵉ fam-Pᵉ xᵉ)
            ( λ eᵉ → map-equivᵉ (eᵉ (horizontal-map-coconeᵉ _ _ cᵉ a₀ᵉ)) reflᵉ ＝ᵉ p₀'ᵉ))
        ( _)
        ( is-equiv-map-Σᵉ _
          ( is-equiv-equiv-descent-data-equiv-family-cocone-span-diagramᵉ
            ( family-with-descent-data-identity-type-pushoutᵉ cᵉ
              ( horizontal-map-coconeᵉ _ _ cᵉ a₀ᵉ))
            ( fam-Pᵉ)
            ( up-cᵉ))
          ( λ eᵉ →
            is-equiv-map-inv-equivᵉ
              ( eq-transpose-equivᵉ
                ( left-equiv-family-with-descent-data-pushoutᵉ fam-Pᵉ a₀ᵉ)
                ( _)
                ( p₀ᵉ))))
        ( is-torsorial-pointed-fam-equiv-is-torsorialᵉ p₀'ᵉ
          ( is-torsorial-is-identity-systemᵉ
            ( horizontal-map-coconeᵉ _ _ cᵉ a₀ᵉ)
            ( p₀'ᵉ)
            ( is-identity-system-is-identity-system-descent-data-pushoutᵉ
              ( fam-Pᵉ)
              ( p₀ᵉ)
              ( up-cᵉ)
              ( id-system-Pᵉ))))
      where
      fam-Pᵉ : family-with-descent-data-pushoutᵉ cᵉ l5ᵉ
      fam-Pᵉ = family-with-descent-data-pushout-descent-data-pushoutᵉ up-cᵉ Pᵉ
      p₀'ᵉ :
        family-cocone-family-with-descent-data-pushoutᵉ
          ( fam-Pᵉ)
          ( horizontal-map-coconeᵉ _ _ cᵉ a₀ᵉ)
      p₀'ᵉ =
        map-compute-inv-left-family-cocone-descent-data-pushoutᵉ up-cᵉ Pᵉ a₀ᵉ p₀ᵉ
```

### Descent data with a converse to the evaluation map of sections of descent data is an identity system

Toᵉ showᵉ thatᵉ `(PA,ᵉ PB,ᵉ PS)`ᵉ isᵉ anᵉ identityᵉ systemᵉ atᵉ `p₀ᵉ : PAᵉ a₀`,ᵉ itᵉ sufficesᵉ
to provideᵉ anᵉ elementᵉ ofᵉ theᵉ typeᵉ `Hᵉ : RΣAᵉ (a₀,ᵉ p₀ᵉ) → sectionᵉ (RΣA,ᵉ RΣB,ᵉ RΣS)`ᵉ
forᵉ allᵉ `(RΣA,ᵉ RΣB,ᵉ RΣS)`.ᵉ

**Proof:**ᵉ Considerᵉ theᵉ uniqueᵉ familyᵉ `Pᵉ : Xᵉ → 𝒰`ᵉ forᵉ `(PA,ᵉ PB,ᵉ PS)`.ᵉ Itᵉ
sufficesᵉ to showᵉ thatᵉ `P`ᵉ isᵉ anᵉ identityᵉ system.ᵉ Asᵉ above,ᵉ weᵉ canᵉ do thatᵉ byᵉ
showingᵉ thatᵉ itᵉ isᵉ torsorial.ᵉ Byᵉ definition,ᵉ thatᵉ meansᵉ thatᵉ theᵉ totalᵉ spaceᵉ
`Σᵉ Xᵉ P`ᵉ isᵉ contractible.ᵉ Weᵉ canᵉ proveᵉ thatᵉ using theᵉ propertyᵉ thatᵉ aᵉ typeᵉ isᵉ
contractibleᵉ ifᵉ weᵉ provideᵉ aᵉ point,ᵉ hereᵉ `(ia₀,ᵉ (eᴾAᵉ a)⁻¹ᵉ p₀)`,ᵉ andᵉ aᵉ mapᵉ

```text
  H'ᵉ : (RΣᵉ : Σᵉ Xᵉ Pᵉ → 𝒰ᵉ) → (r₀ᵉ : RΣᵉ (ia₀,ᵉ (eᴾAᵉ a)⁻¹ᵉ p₀ᵉ)) → (uᵉ : Σᵉ Xᵉ Pᵉ) → RΣᵉ u.ᵉ
```

Assumeᵉ suchᵉ `RΣ`ᵉ andᵉ `r₀`.ᵉ Aᵉ sectionᵉ `(uᵉ : Σᵉ Xᵉ Pᵉ) → RΣᵉ u`ᵉ isᵉ givenᵉ byᵉ aᵉ sectionᵉ
ofᵉ `(RΣA,ᵉ RΣB,ᵉ RΣS)`,ᵉ andᵉ weᵉ canᵉ getᵉ oneᵉ byᵉ applyingᵉ `H`ᵉ to
`eᴿAᵉ (a₀,ᵉ p₀ᵉ) r₀ᵉ : RΣAᵉ (a₀,ᵉ p₀)`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} {cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ}
  (up-cᵉ : universal-property-pushoutᵉ _ _ cᵉ)
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l5ᵉ) {a₀ᵉ : domain-span-diagramᵉ 𝒮ᵉ}
  (p₀ᵉ : left-family-descent-data-pushoutᵉ Pᵉ a₀ᵉ)
  where

  abstract
    is-identity-system-descent-data-pushout-ind-singletonᵉ :
      (Hᵉ :
        {l6ᵉ : Level}
        (Rᵉ :
          descent-data-pushoutᵉ
            ( span-diagram-flattening-descent-data-pushoutᵉ Pᵉ)
            ( l6ᵉ))
        (r₀ᵉ : left-family-descent-data-pushoutᵉ Rᵉ (a₀ᵉ ,ᵉ p₀ᵉ)) →
        section-descent-data-pushoutᵉ Rᵉ) →
      is-identity-system-descent-data-pushoutᵉ Pᵉ p₀ᵉ
    is-identity-system-descent-data-pushout-ind-singletonᵉ Hᵉ =
      is-identity-system-descent-data-pushout-is-identity-systemᵉ
        ( family-with-descent-data-pushout-descent-data-pushoutᵉ up-cᵉ Pᵉ)
        ( p₀ᵉ)
        ( up-cᵉ)
        ( is-identity-system-is-torsorialᵉ
          ( horizontal-map-coconeᵉ _ _ cᵉ a₀ᵉ)
          ( p₀'ᵉ)
          ( is-contr-ind-singletonᵉ _
            ( horizontal-map-coconeᵉ _ _ cᵉ a₀ᵉ ,ᵉ p₀'ᵉ)
            ( λ Rᵉ r₀ᵉ →
              section-family-section-descent-data-pushoutᵉ
                ( flattening-lemma-descent-data-pushoutᵉ _ _ cᵉ Pᵉ
                  ( family-cocone-descent-data-pushoutᵉ up-cᵉ Pᵉ)
                  ( inv-equiv-family-cocone-descent-data-pushoutᵉ up-cᵉ Pᵉ)
                  ( up-cᵉ))
                ( family-with-descent-data-pushout-family-coconeᵉ _ Rᵉ)
                ( Hᵉ (descent-data-family-cocone-span-diagramᵉ _ Rᵉ) r₀ᵉ))))
      where
        p₀'ᵉ :
          family-cocone-descent-data-pushoutᵉ up-cᵉ Pᵉ
            ( horizontal-map-coconeᵉ _ _ cᵉ a₀ᵉ)
        p₀'ᵉ =
          map-compute-inv-left-family-cocone-descent-data-pushoutᵉ up-cᵉ Pᵉ a₀ᵉ p₀ᵉ
```