# Equivalences of descent data for pushouts

```agda
module synthetic-homotopy-theory.equivalences-descent-data-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.span-diagramsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.morphisms-descent-data-pushoutsᵉ
```

</details>

## Idea

Givenᵉ [descentᵉ data](synthetic-homotopy-theory.descent-data-pushouts.mdᵉ) forᵉ
[pushouts](synthetic-homotopy-theory.pushouts.mdᵉ) `(PA,ᵉ PB,ᵉ PS)`ᵉ andᵉ
`(QA,ᵉ QB,ᵉ QS)`,ᵉ anᵉ
{{#conceptᵉ "equivalence"ᵉ Disambiguation="descentᵉ data forᵉ pushouts"ᵉ Agda=equiv-descent-data-pushoutᵉ}}
betweenᵉ themᵉ isᵉ aᵉ pairᵉ ofᵉ fiberwiseᵉ equivalencesᵉ

```text
  eAᵉ : (aᵉ : Aᵉ) → PAᵉ aᵉ ≃ᵉ QAᵉ aᵉ
  eBᵉ : (bᵉ : Bᵉ) → PBᵉ bᵉ ≃ᵉ QBᵉ bᵉ
```

equippedᵉ with aᵉ familyᵉ ofᵉ [homotopies](foundation-core.homotopies.mdᵉ) makingᵉ

```text
              eA(fsᵉ)
     PA(fsᵉ) -------->ᵉ QA(fsᵉ)
       |                |
  PSᵉ sᵉ |                | QSᵉ sᵉ
       |                |
       ∨ᵉ                ∨ᵉ
     PB(gsᵉ) -------->ᵉ QB(gsᵉ)
              eB(gsᵉ)
```

[commute](foundation-core.commuting-squares-of-maps.mdᵉ) forᵉ everyᵉ `sᵉ : S`.ᵉ

Weᵉ showᵉ thatᵉ equivalencesᵉ characterizeᵉ theᵉ
[identityᵉ types](foundation-core.identity-types.mdᵉ) ofᵉ descentᵉ data forᵉ
pushouts.ᵉ

Byᵉ forgettingᵉ thatᵉ theᵉ fiberwiseᵉ mapsᵉ areᵉ equivalences,ᵉ weᵉ getᵉ theᵉ underlyingᵉ
[morphismᵉ ofᵉ descentᵉ data](synthetic-homotopy-theory.morphisms-descent-data-pushouts.md).ᵉ
Weᵉ defineᵉ homotopiesᵉ ofᵉ equivalencesᵉ ofᵉ descentᵉ data to beᵉ homotopiesᵉ ofᵉ theᵉ
underlyingᵉ morphisms,ᵉ andᵉ showᵉ thatᵉ homotopiesᵉ characterizeᵉ theᵉ identityᵉ typeᵉ ofᵉ
equivalencesᵉ ofᵉ descentᵉ data.ᵉ

## Definitions

### Equivalences of descent data for pushouts

Noteᵉ thatᵉ theᵉ descentᵉ data argumentsᵉ cannotᵉ beᵉ inferredᵉ whenᵉ callingᵉ
`left-equiv-equiv-descent-data-pushout`ᵉ andᵉ theᵉ like,ᵉ sinceᵉ Agdaᵉ cannotᵉ inferᵉ
theᵉ proofsᵉ ofᵉ `is-equiv`ᵉ ofᵉ theirᵉ gluingᵉ maps.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  (Qᵉ : descent-data-pushoutᵉ 𝒮ᵉ l5ᵉ)
  where

  equiv-descent-data-pushoutᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  equiv-descent-data-pushoutᵉ =
    Σᵉ ( (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
        left-family-descent-data-pushoutᵉ Pᵉ aᵉ ≃ᵉ
        left-family-descent-data-pushoutᵉ Qᵉ aᵉ)
      ( λ eAᵉ →
        Σᵉ ( (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
            right-family-descent-data-pushoutᵉ Pᵉ bᵉ ≃ᵉ
            right-family-descent-data-pushoutᵉ Qᵉ bᵉ)
          ( λ eBᵉ →
            (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
            coherence-square-mapsᵉ
              ( map-equivᵉ (eAᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ)))
              ( map-family-descent-data-pushoutᵉ Pᵉ sᵉ)
              ( map-family-descent-data-pushoutᵉ Qᵉ sᵉ)
              ( map-equivᵉ (eBᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ)))))

  module _
    (eᵉ : equiv-descent-data-pushoutᵉ)
    where

    left-equiv-equiv-descent-data-pushoutᵉ :
      (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
      left-family-descent-data-pushoutᵉ Pᵉ aᵉ ≃ᵉ
      left-family-descent-data-pushoutᵉ Qᵉ aᵉ
    left-equiv-equiv-descent-data-pushoutᵉ = pr1ᵉ eᵉ

    left-map-equiv-descent-data-pushoutᵉ :
      (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
      left-family-descent-data-pushoutᵉ Pᵉ aᵉ →
      left-family-descent-data-pushoutᵉ Qᵉ aᵉ
    left-map-equiv-descent-data-pushoutᵉ aᵉ =
      map-equivᵉ (left-equiv-equiv-descent-data-pushoutᵉ aᵉ)

    is-equiv-left-map-equiv-descent-data-pushoutᵉ :
      (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
      is-equivᵉ (left-map-equiv-descent-data-pushoutᵉ aᵉ)
    is-equiv-left-map-equiv-descent-data-pushoutᵉ aᵉ =
      is-equiv-map-equivᵉ (left-equiv-equiv-descent-data-pushoutᵉ aᵉ)

    inv-left-map-equiv-descent-data-pushoutᵉ :
      (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
      left-family-descent-data-pushoutᵉ Qᵉ aᵉ →
      left-family-descent-data-pushoutᵉ Pᵉ aᵉ
    inv-left-map-equiv-descent-data-pushoutᵉ aᵉ =
      map-inv-equivᵉ (left-equiv-equiv-descent-data-pushoutᵉ aᵉ)

    right-equiv-equiv-descent-data-pushoutᵉ :
      (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
      right-family-descent-data-pushoutᵉ Pᵉ bᵉ ≃ᵉ
      right-family-descent-data-pushoutᵉ Qᵉ bᵉ
    right-equiv-equiv-descent-data-pushoutᵉ = pr1ᵉ (pr2ᵉ eᵉ)

    right-map-equiv-descent-data-pushoutᵉ :
      (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
      right-family-descent-data-pushoutᵉ Pᵉ bᵉ →
      right-family-descent-data-pushoutᵉ Qᵉ bᵉ
    right-map-equiv-descent-data-pushoutᵉ bᵉ =
      map-equivᵉ (right-equiv-equiv-descent-data-pushoutᵉ bᵉ)

    is-equiv-right-map-equiv-descent-data-pushoutᵉ :
      (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
      is-equivᵉ (right-map-equiv-descent-data-pushoutᵉ bᵉ)
    is-equiv-right-map-equiv-descent-data-pushoutᵉ bᵉ =
      is-equiv-map-equivᵉ (right-equiv-equiv-descent-data-pushoutᵉ bᵉ)

    inv-right-map-equiv-descent-data-pushoutᵉ :
      (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
      right-family-descent-data-pushoutᵉ Qᵉ bᵉ →
      right-family-descent-data-pushoutᵉ Pᵉ bᵉ
    inv-right-map-equiv-descent-data-pushoutᵉ bᵉ =
      map-inv-equivᵉ (right-equiv-equiv-descent-data-pushoutᵉ bᵉ)

    coherence-equiv-descent-data-pushoutᵉ :
      (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
      coherence-square-mapsᵉ
        ( left-map-equiv-descent-data-pushoutᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ))
        ( map-family-descent-data-pushoutᵉ Pᵉ sᵉ)
        ( map-family-descent-data-pushoutᵉ Qᵉ sᵉ)
        ( right-map-equiv-descent-data-pushoutᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ))
    coherence-equiv-descent-data-pushoutᵉ = pr2ᵉ (pr2ᵉ eᵉ)

    hom-equiv-descent-data-pushoutᵉ : hom-descent-data-pushoutᵉ Pᵉ Qᵉ
    pr1ᵉ hom-equiv-descent-data-pushoutᵉ =
      left-map-equiv-descent-data-pushoutᵉ
    pr1ᵉ (pr2ᵉ hom-equiv-descent-data-pushoutᵉ) =
      right-map-equiv-descent-data-pushoutᵉ
    pr2ᵉ (pr2ᵉ hom-equiv-descent-data-pushoutᵉ) =
      coherence-equiv-descent-data-pushoutᵉ
```

### The identity equivalence of descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  where

  id-equiv-descent-data-pushoutᵉ : equiv-descent-data-pushoutᵉ Pᵉ Pᵉ
  pr1ᵉ id-equiv-descent-data-pushoutᵉ aᵉ = id-equivᵉ
  pr1ᵉ (pr2ᵉ id-equiv-descent-data-pushoutᵉ) bᵉ = id-equivᵉ
  pr2ᵉ (pr2ᵉ id-equiv-descent-data-pushoutᵉ) sᵉ = refl-htpyᵉ
```

### Inverses of equivalences of descent data for pushouts

Takingᵉ anᵉ inverseᵉ ofᵉ anᵉ equivalenceᵉ `(eA,ᵉ eB,ᵉ eS)`ᵉ ofᵉ descentᵉ data amountsᵉ to
takingᵉ theᵉ inversesᵉ ofᵉ theᵉ fiberwiseᵉ mapsᵉ

```text
  aᵉ : Aᵉ ⊢ᵉ eA(a)⁻¹ᵉ : QAᵉ aᵉ ≃ᵉ PAᵉ aᵉ
  bᵉ : Bᵉ ⊢ᵉ eB(b)⁻¹ᵉ : QBᵉ bᵉ ≃ᵉ PBᵉ bᵉ
```

andᵉ mirroringᵉ theᵉ coherenceᵉ squaresᵉ verticallyᵉ to getᵉ

```text
             eA(a)⁻¹ᵉ
     QA(fsᵉ) -------->ᵉ PA(fsᵉ)
       |                |
  QSᵉ sᵉ |                | PSᵉ sᵉ
       |                |
       ∨ᵉ                ∨ᵉ
     QB(gsᵉ) -------->ᵉ PB(gs).ᵉ
             eB(a)⁻¹ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  (Qᵉ : descent-data-pushoutᵉ 𝒮ᵉ l5ᵉ)
  where

  inv-equiv-descent-data-pushoutᵉ :
    equiv-descent-data-pushoutᵉ Pᵉ Qᵉ → equiv-descent-data-pushoutᵉ Qᵉ Pᵉ
  pr1ᵉ (inv-equiv-descent-data-pushoutᵉ eᵉ) aᵉ =
    inv-equivᵉ (left-equiv-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ eᵉ aᵉ)
  pr1ᵉ (pr2ᵉ (inv-equiv-descent-data-pushoutᵉ eᵉ)) bᵉ =
    inv-equivᵉ (right-equiv-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ eᵉ bᵉ)
  pr2ᵉ (pr2ᵉ (inv-equiv-descent-data-pushoutᵉ eᵉ)) sᵉ =
    horizontal-inv-equiv-coherence-square-mapsᵉ
      ( left-equiv-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ eᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ))
      ( map-family-descent-data-pushoutᵉ Pᵉ sᵉ)
      ( map-family-descent-data-pushoutᵉ Qᵉ sᵉ)
      ( right-equiv-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ eᵉ
        ( right-map-span-diagramᵉ 𝒮ᵉ sᵉ))
      ( coherence-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ eᵉ sᵉ)
```

### Homotopies of equivalences of descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  (Qᵉ : descent-data-pushoutᵉ 𝒮ᵉ l5ᵉ)
  where

  htpy-equiv-descent-data-pushoutᵉ :
    (eᵉ fᵉ : equiv-descent-data-pushoutᵉ Pᵉ Qᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  htpy-equiv-descent-data-pushoutᵉ eᵉ fᵉ =
    htpy-hom-descent-data-pushoutᵉ Pᵉ Qᵉ
      ( hom-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ eᵉ)
      ( hom-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ)
```

## Properties

### Characterization of identity types of descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  where

  equiv-eq-descent-data-pushoutᵉ :
    (Qᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ) →
    Pᵉ ＝ᵉ Qᵉ → equiv-descent-data-pushoutᵉ Pᵉ Qᵉ
  equiv-eq-descent-data-pushoutᵉ .Pᵉ reflᵉ = id-equiv-descent-data-pushoutᵉ Pᵉ

  abstract
    is-torsorial-equiv-descent-data-pushoutᵉ :
      is-torsorialᵉ (equiv-descent-data-pushoutᵉ {l5ᵉ = l4ᵉ} Pᵉ)
    is-torsorial-equiv-descent-data-pushoutᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-Eq-Πᵉ
          ( λ aᵉ → is-torsorial-equivᵉ (left-family-descent-data-pushoutᵉ Pᵉ aᵉ)))
        ( left-family-descent-data-pushoutᵉ Pᵉ ,ᵉ λ aᵉ → id-equivᵉ)
        ( is-torsorial-Eq-structureᵉ
          ( is-torsorial-Eq-Πᵉ
            ( λ bᵉ → is-torsorial-equivᵉ (right-family-descent-data-pushoutᵉ Pᵉ bᵉ)))
          ( right-family-descent-data-pushoutᵉ Pᵉ ,ᵉ λ bᵉ → id-equivᵉ)
          ( is-torsorial-Eq-Πᵉ
            ( λ sᵉ →
              is-torsorial-htpy-equivᵉ (equiv-family-descent-data-pushoutᵉ Pᵉ sᵉ))))

    is-equiv-equiv-eq-descent-data-pushoutᵉ :
      (Qᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ) →
      is-equivᵉ (equiv-eq-descent-data-pushoutᵉ Qᵉ)
    is-equiv-equiv-eq-descent-data-pushoutᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-equiv-descent-data-pushoutᵉ)
        ( equiv-eq-descent-data-pushoutᵉ)

  extensionality-descent-data-pushoutᵉ :
    (Qᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ) →
    (Pᵉ ＝ᵉ Qᵉ) ≃ᵉ equiv-descent-data-pushoutᵉ Pᵉ Qᵉ
  pr1ᵉ (extensionality-descent-data-pushoutᵉ Qᵉ) =
    equiv-eq-descent-data-pushoutᵉ Qᵉ
  pr2ᵉ (extensionality-descent-data-pushoutᵉ Qᵉ) =
    is-equiv-equiv-eq-descent-data-pushoutᵉ Qᵉ

  eq-equiv-descent-data-pushoutᵉ :
    (Qᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ) →
    equiv-descent-data-pushoutᵉ Pᵉ Qᵉ → Pᵉ ＝ᵉ Qᵉ
  eq-equiv-descent-data-pushoutᵉ Qᵉ =
    map-inv-equivᵉ (extensionality-descent-data-pushoutᵉ Qᵉ)
```

### Characterization of identity types of equivalences of descent data of pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ}
  {Qᵉ : descent-data-pushoutᵉ 𝒮ᵉ l5ᵉ}
  (eᵉ : equiv-descent-data-pushoutᵉ Pᵉ Qᵉ)
  where

  htpy-eq-equiv-descent-data-pushoutᵉ :
    (fᵉ : equiv-descent-data-pushoutᵉ Pᵉ Qᵉ) →
    (eᵉ ＝ᵉ fᵉ) → htpy-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ eᵉ fᵉ
  htpy-eq-equiv-descent-data-pushoutᵉ .eᵉ reflᵉ =
    refl-htpy-hom-descent-data-pushoutᵉ Pᵉ Qᵉ
      ( hom-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ eᵉ)

  abstract
    is-torsorial-htpy-equiv-descent-data-pushoutᵉ :
      is-torsorialᵉ (htpy-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ eᵉ)
    is-torsorial-htpy-equiv-descent-data-pushoutᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-Eq-Πᵉ
          ( λ aᵉ →
            is-torsorial-htpy-equivᵉ
              ( left-equiv-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ eᵉ aᵉ)))
        ( left-equiv-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ eᵉ ,ᵉ λ aᵉ → refl-htpyᵉ)
        ( is-torsorial-Eq-structureᵉ
          ( is-torsorial-Eq-Πᵉ
            ( λ bᵉ →
              is-torsorial-htpy-equivᵉ
                ( right-equiv-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ eᵉ bᵉ)))
          ( right-equiv-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ eᵉ ,ᵉ λ bᵉ → refl-htpyᵉ)
          ( is-torsorial-Eq-Πᵉ
            ( λ sᵉ →
              is-torsorial-htpyᵉ
                ( coherence-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ eᵉ sᵉ ∙hᵉ refl-htpyᵉ))))

  is-equiv-htpy-eq-equiv-descent-data-pushoutᵉ :
    (fᵉ : equiv-descent-data-pushoutᵉ Pᵉ Qᵉ) →
    is-equivᵉ (htpy-eq-equiv-descent-data-pushoutᵉ fᵉ)
  is-equiv-htpy-eq-equiv-descent-data-pushoutᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-equiv-descent-data-pushoutᵉ)
      ( htpy-eq-equiv-descent-data-pushoutᵉ)

  extensionality-equiv-descent-data-pushoutᵉ :
    (fᵉ : equiv-descent-data-pushoutᵉ Pᵉ Qᵉ) →
    (eᵉ ＝ᵉ fᵉ) ≃ᵉ
    htpy-hom-descent-data-pushoutᵉ Pᵉ Qᵉ
      ( hom-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ eᵉ)
      ( hom-equiv-descent-data-pushoutᵉ Pᵉ Qᵉ fᵉ)
  pr1ᵉ (extensionality-equiv-descent-data-pushoutᵉ fᵉ) =
    htpy-eq-equiv-descent-data-pushoutᵉ fᵉ
  pr2ᵉ (extensionality-equiv-descent-data-pushoutᵉ fᵉ) =
    is-equiv-htpy-eq-equiv-descent-data-pushoutᵉ fᵉ
```