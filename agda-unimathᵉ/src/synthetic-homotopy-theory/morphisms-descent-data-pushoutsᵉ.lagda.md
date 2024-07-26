# Morphisms of descent data for pushouts

```agda
module synthetic-homotopy-theory.morphisms-descent-data-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-homotopiesᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.span-diagramsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.descent-data-pushoutsᵉ
```

</details>

## Idea

Givenᵉ [descentᵉ data](synthetic-homotopy-theory.descent-data-pushouts.mdᵉ) forᵉ
[pushouts](synthetic-homotopy-theory.pushouts.mdᵉ) `(PA,ᵉ PB,ᵉ PS)`ᵉ andᵉ
`(QA,ᵉ QB,ᵉ QS)`,ᵉ aᵉ
{{#conceptᵉ "morphism"ᵉ Disambiguation="descentᵉ data forᵉ pushouts"ᵉ Agda=hom-descent-data-pushoutᵉ}}
betweenᵉ themᵉ isᵉ aᵉ pairᵉ ofᵉ fiberwiseᵉ mapsᵉ

```text
  hAᵉ : (aᵉ : Aᵉ) → PAᵉ aᵉ → QAᵉ aᵉ
  hBᵉ : (bᵉ : Bᵉ) → PBᵉ bᵉ → QBᵉ bᵉ
```

equippedᵉ with aᵉ familyᵉ ofᵉ [homotopies](foundation-core.homotopies.mdᵉ) makingᵉ

```text
              hA(fsᵉ)
     PA(fsᵉ) -------->ᵉ QA(fsᵉ)
       |                |
  PSᵉ sᵉ |                | QSᵉ sᵉ
       |                |
       ∨ᵉ                ∨ᵉ
     PB(gsᵉ) -------->ᵉ QB(gsᵉ)
              hB(gsᵉ)
```

[commute](foundation-core.commuting-squares-of-maps.mdᵉ) forᵉ everyᵉ `sᵉ : S`.ᵉ

Forᵉ anyᵉ twoᵉ morphismsᵉ `(hA,ᵉ hB,ᵉ hS)`ᵉ andᵉ `(kA,ᵉ kB,ᵉ kS)`,ᵉ weᵉ canᵉ defineᵉ theᵉ typeᵉ
ofᵉ
{{#conceptᵉ "homotopies"ᵉ Disambiguation="morphismsᵉ ofᵉ descentᵉ data forᵉ pushouts"ᵉ Agda=htpy-hom-descent-data-pushoutᵉ}}
betweenᵉ themᵉ asᵉ theᵉ typeᵉ ofᵉ triplesᵉ `(HA,ᵉ HB,ᵉ HS)`,ᵉ where `HA`ᵉ andᵉ `HB`ᵉ areᵉ
fiberwiseᵉ homotopiesᵉ

```text
  HAᵉ : (aᵉ : Aᵉ) → hAᵉ aᵉ ~ᵉ kAᵉ aᵉ
  HBᵉ : (bᵉ : Bᵉ) → hBᵉ bᵉ ~ᵉ kBᵉ b,ᵉ
```

andᵉ `HS`ᵉ isᵉ aᵉ coherenceᵉ datumᵉ showingᵉ thatᵉ forᵉ allᵉ `sᵉ : S`,ᵉ theᵉ squareᵉ ofᵉ
homotopiesᵉ

```text
                 HB(gsᵉ) ·rᵉ PSᵉ sᵉ
  hB(gsᵉ) ∘ᵉ PSᵉ sᵉ --------------->ᵉ kB(gsᵉ) ∘ᵉ PSᵉ sᵉ
         |                              |
    hSᵉ sᵉ |                              | tSᵉ sᵉ
         |                              |
         ∨ᵉ                              ∨ᵉ
  QSᵉ sᵉ ∘ᵉ hA(fsᵉ) --------------->ᵉ QSᵉ sᵉ ∘ᵉ kA(fsᵉ)
                 QSᵉ sᵉ ·lᵉ HA(fsᵉ)
```

[commutes](foundation-core.commuting-squares-of-homotopies.md).ᵉ Thisᵉ coherenceᵉ
datumᵉ mayᵉ beᵉ seenᵉ asᵉ aᵉ fillerᵉ ofᵉ theᵉ diagramᵉ oneᵉ getsᵉ byᵉ gluingᵉ theᵉ squaresᵉ `hS`ᵉ
andᵉ `tS`ᵉ alongᵉ theᵉ commonᵉ verticalᵉ mapsᵉ

```text
             tA(fsᵉ)
            ________
           /ᵉ        ∨ᵉ
     PA(fsᵉ)          QA(fsᵉ)
       |   \________∧ᵉ  |
       |     hA(fsᵉ)    |
       |               |
  PSᵉ sᵉ |               | QSᵉ sᵉ
       |     tB(gsᵉ)    |
       |    ________   |
       ∨ᵉ   /ᵉ        ∨ᵉ  ∨ᵉ
     PB(gsᵉ)          QB(gs).ᵉ
           \________∧ᵉ
             hB(gsᵉ)
```

Theᵉ frontᵉ andᵉ backᵉ facesᵉ areᵉ `hSᵉ s`ᵉ andᵉ `tSᵉ s`,ᵉ andᵉ theᵉ topᵉ andᵉ bottomᵉ facesᵉ areᵉ
`HA(fs)`ᵉ andᵉ `HB(gs)`,ᵉ respectively.ᵉ `HS`ᵉ thenᵉ expressesᵉ thatᵉ goingᵉ alongᵉ theᵉ
frontᵉ faceᵉ andᵉ thenᵉ theᵉ topᵉ faceᵉ isᵉ homotopicᵉ to firstᵉ goingᵉ alongᵉ theᵉ bottomᵉ
faceᵉ andᵉ thenᵉ theᵉ backᵉ face.ᵉ

Weᵉ thenᵉ showᵉ thatᵉ homotopiesᵉ characterizeᵉ theᵉ
[identityᵉ types](foundation-core.identity-types.mdᵉ) ofᵉ morphismsᵉ ofᵉ descentᵉ
data.ᵉ

## Definitions

### Morphisms of descent data for pushouts

Noteᵉ thatᵉ theᵉ descentᵉ data argumentsᵉ cannotᵉ beᵉ inferredᵉ whenᵉ callingᵉ
`left-map-hom-descent-data-pushout`ᵉ andᵉ theᵉ like,ᵉ sinceᵉ Agdaᵉ cannotᵉ inferᵉ theᵉ
proofsᵉ ofᵉ `is-equiv`ᵉ ofᵉ theirᵉ gluingᵉ maps.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  (Qᵉ : descent-data-pushoutᵉ 𝒮ᵉ l5ᵉ)
  where

  hom-descent-data-pushoutᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  hom-descent-data-pushoutᵉ =
    Σᵉ ( (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
        left-family-descent-data-pushoutᵉ Pᵉ aᵉ →
        left-family-descent-data-pushoutᵉ Qᵉ aᵉ)
      ( λ hAᵉ →
        Σᵉ ( (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
            right-family-descent-data-pushoutᵉ Pᵉ bᵉ →
            right-family-descent-data-pushoutᵉ Qᵉ bᵉ)
          ( λ hBᵉ →
            (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
            coherence-square-mapsᵉ
              ( hAᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ))
              ( map-family-descent-data-pushoutᵉ Pᵉ sᵉ)
              ( map-family-descent-data-pushoutᵉ Qᵉ sᵉ)
              ( hBᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ))))

  module _
    (hᵉ : hom-descent-data-pushoutᵉ)
    where

    left-map-hom-descent-data-pushoutᵉ :
      (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
      left-family-descent-data-pushoutᵉ Pᵉ aᵉ →
      left-family-descent-data-pushoutᵉ Qᵉ aᵉ
    left-map-hom-descent-data-pushoutᵉ = pr1ᵉ hᵉ

    right-map-hom-descent-data-pushoutᵉ :
      (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
      right-family-descent-data-pushoutᵉ Pᵉ bᵉ →
      right-family-descent-data-pushoutᵉ Qᵉ bᵉ
    right-map-hom-descent-data-pushoutᵉ = pr1ᵉ (pr2ᵉ hᵉ)

    coherence-hom-descent-data-pushoutᵉ :
      (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
      coherence-square-mapsᵉ
        ( left-map-hom-descent-data-pushoutᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ))
        ( map-family-descent-data-pushoutᵉ Pᵉ sᵉ)
        ( map-family-descent-data-pushoutᵉ Qᵉ sᵉ)
        ( right-map-hom-descent-data-pushoutᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ))
    coherence-hom-descent-data-pushoutᵉ = pr2ᵉ (pr2ᵉ hᵉ)
```

### The identity morphism of descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  where

  id-hom-descent-data-pushoutᵉ : hom-descent-data-pushoutᵉ Pᵉ Pᵉ
  pr1ᵉ id-hom-descent-data-pushoutᵉ aᵉ = idᵉ
  pr1ᵉ (pr2ᵉ id-hom-descent-data-pushoutᵉ) bᵉ = idᵉ
  pr2ᵉ (pr2ᵉ id-hom-descent-data-pushoutᵉ) sᵉ = refl-htpyᵉ
```

### Composition of morphisms of descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  (Qᵉ : descent-data-pushoutᵉ 𝒮ᵉ l5ᵉ)
  (Rᵉ : descent-data-pushoutᵉ 𝒮ᵉ l6ᵉ)
  (gᵉ : hom-descent-data-pushoutᵉ Qᵉ Rᵉ)
  (fᵉ : hom-descent-data-pushoutᵉ Pᵉ Qᵉ)
  where

  comp-hom-descent-data-pushoutᵉ : hom-descent-data-pushoutᵉ Pᵉ Rᵉ
  pr1ᵉ comp-hom-descent-data-pushoutᵉ aᵉ =
    left-map-hom-descent-data-pushoutᵉ Qᵉ Rᵉ gᵉ aᵉ ∘ᵉ
    left-map-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ aᵉ
  pr1ᵉ (pr2ᵉ comp-hom-descent-data-pushoutᵉ) bᵉ =
    right-map-hom-descent-data-pushoutᵉ Qᵉ Rᵉ gᵉ bᵉ ∘ᵉ
    right-map-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ bᵉ
  pr2ᵉ (pr2ᵉ comp-hom-descent-data-pushoutᵉ) sᵉ =
    pasting-horizontal-coherence-square-mapsᵉ
      ( left-map-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ
        ( left-map-span-diagramᵉ 𝒮ᵉ sᵉ))
      ( left-map-hom-descent-data-pushoutᵉ Qᵉ Rᵉ gᵉ
        ( left-map-span-diagramᵉ 𝒮ᵉ sᵉ))
      ( map-family-descent-data-pushoutᵉ Pᵉ sᵉ)
      ( map-family-descent-data-pushoutᵉ Qᵉ sᵉ)
      ( map-family-descent-data-pushoutᵉ Rᵉ sᵉ)
      ( right-map-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ
        ( right-map-span-diagramᵉ 𝒮ᵉ sᵉ))
      ( right-map-hom-descent-data-pushoutᵉ Qᵉ Rᵉ gᵉ
        ( right-map-span-diagramᵉ 𝒮ᵉ sᵉ))
      ( coherence-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ sᵉ)
      ( coherence-hom-descent-data-pushoutᵉ Qᵉ Rᵉ gᵉ sᵉ)
```

### Homotopies between morphisms of descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  (Qᵉ : descent-data-pushoutᵉ 𝒮ᵉ l5ᵉ)
  (fᵉ gᵉ : hom-descent-data-pushoutᵉ Pᵉ Qᵉ)
  where

  htpy-hom-descent-data-pushoutᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  htpy-hom-descent-data-pushoutᵉ =
    Σᵉ ( (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
        left-map-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ aᵉ ~ᵉ
        left-map-hom-descent-data-pushoutᵉ Pᵉ Qᵉ gᵉ aᵉ)
      ( λ HAᵉ →
        Σᵉ ( (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
            right-map-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ bᵉ ~ᵉ
            right-map-hom-descent-data-pushoutᵉ Pᵉ Qᵉ gᵉ bᵉ)
          ( λ HBᵉ →
            (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
            coherence-square-homotopiesᵉ
              ( ( HBᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ)) ·rᵉ
                ( map-family-descent-data-pushoutᵉ Pᵉ sᵉ))
              ( coherence-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ sᵉ)
              ( coherence-hom-descent-data-pushoutᵉ Pᵉ Qᵉ gᵉ sᵉ)
              ( ( map-family-descent-data-pushoutᵉ Qᵉ sᵉ) ·lᵉ
                ( HAᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ)))))
```

### The reflexive homotopy between morphisms of descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  (Qᵉ : descent-data-pushoutᵉ 𝒮ᵉ l5ᵉ)
  (fᵉ : hom-descent-data-pushoutᵉ Pᵉ Qᵉ)
  where

  refl-htpy-hom-descent-data-pushoutᵉ : htpy-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ fᵉ
  pr1ᵉ refl-htpy-hom-descent-data-pushoutᵉ aᵉ = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ refl-htpy-hom-descent-data-pushoutᵉ) bᵉ = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ refl-htpy-hom-descent-data-pushoutᵉ) sᵉ = right-unit-htpyᵉ
```

## Properties

### Characterizing the identity type of morphisms of descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  (Qᵉ : descent-data-pushoutᵉ 𝒮ᵉ l5ᵉ)
  (fᵉ : hom-descent-data-pushoutᵉ Pᵉ Qᵉ)
  where

  htpy-eq-hom-descent-data-pushoutᵉ :
    (gᵉ : hom-descent-data-pushoutᵉ Pᵉ Qᵉ) →
    (fᵉ ＝ᵉ gᵉ) → htpy-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ gᵉ
  htpy-eq-hom-descent-data-pushoutᵉ .fᵉ reflᵉ =
    refl-htpy-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ

  abstract
    is-torsorial-htpy-hom-descent-data-pushoutᵉ :
      is-torsorialᵉ (htpy-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ)
    is-torsorial-htpy-hom-descent-data-pushoutᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-Eq-Πᵉ
          ( λ aᵉ →
            is-torsorial-htpyᵉ (left-map-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ aᵉ)))
        ( left-map-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ ,ᵉ λ aᵉ → refl-htpyᵉ)
        ( is-torsorial-Eq-structureᵉ
          ( is-torsorial-Eq-Πᵉ
            ( λ bᵉ →
              is-torsorial-htpyᵉ (right-map-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ bᵉ)))
          ( right-map-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ ,ᵉ λ bᵉ → refl-htpyᵉ)
          ( is-torsorial-Eq-Πᵉ
            ( λ sᵉ →
              is-torsorial-htpyᵉ
                ( coherence-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ sᵉ ∙hᵉ refl-htpyᵉ))))

  is-equiv-htpy-eq-hom-descent-data-pushoutᵉ :
    (gᵉ : hom-descent-data-pushoutᵉ Pᵉ Qᵉ) →
    is-equivᵉ (htpy-eq-hom-descent-data-pushoutᵉ gᵉ)
  is-equiv-htpy-eq-hom-descent-data-pushoutᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-hom-descent-data-pushoutᵉ)
      ( htpy-eq-hom-descent-data-pushoutᵉ)

  extensionality-hom-descent-data-pushoutᵉ :
    (gᵉ : hom-descent-data-pushoutᵉ Pᵉ Qᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-hom-descent-data-pushoutᵉ gᵉ) =
    htpy-eq-hom-descent-data-pushoutᵉ gᵉ
  pr2ᵉ (extensionality-hom-descent-data-pushoutᵉ gᵉ) =
    is-equiv-htpy-eq-hom-descent-data-pushoutᵉ gᵉ

  eq-htpy-hom-descent-data-pushoutᵉ :
    (gᵉ : hom-descent-data-pushoutᵉ Pᵉ Qᵉ) →
    htpy-hom-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-descent-data-pushoutᵉ gᵉ =
    map-inv-equivᵉ (extensionality-hom-descent-data-pushoutᵉ gᵉ)
```