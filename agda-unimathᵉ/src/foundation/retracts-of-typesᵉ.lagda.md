# Retracts of types

```agda
module foundation.retracts-of-typesᵉ where

open import foundation-core.retracts-of-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Weᵉ sayᵉ thatᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ
{{#conceptᵉ "retract"ᵉ Disambiguation="ofᵉ types"ᵉ Agda=retractᵉ}} ofᵉ aᵉ typeᵉ `B`ᵉ ifᵉ
theᵉ typesᵉ `A`ᵉ andᵉ `B`ᵉ comeᵉ equippedᵉ with
{{#conceptᵉ "retractᵉ data"ᵉ Disambiguation="ofᵉ types"ᵉ Agda=retract}},ᵉ i.e.,ᵉ with
mapsᵉ

```text
      iᵉ        rᵉ
  Aᵉ ----->ᵉ Bᵉ ----->ᵉ Aᵉ
```

suchᵉ thatᵉ `r`ᵉ isᵉ aᵉ [retraction](foundation-core.retractions.mdᵉ) ofᵉ `i`,ᵉ i.e.,ᵉ
thereᵉ isᵉ aᵉ [homotopy](foundation-core.homotopies.mdᵉ) `rᵉ ∘ᵉ iᵉ ~ᵉ id`.ᵉ Theᵉ mapᵉ `i`ᵉ
isᵉ calledᵉ theᵉ **inclusion**ᵉ ofᵉ theᵉ retractᵉ data,ᵉ andᵉ theᵉ mapᵉ `r`ᵉ isᵉ calledᵉ theᵉ
**underlyingᵉ mapᵉ ofᵉ theᵉ retraction**.ᵉ

## Properties

### Characterizing equality of retracts

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  coherence-htpy-retractᵉ :
    (Rᵉ Sᵉ : Aᵉ retract-ofᵉ Bᵉ)
    (Iᵉ : inclusion-retractᵉ Rᵉ ~ᵉ inclusion-retractᵉ Sᵉ)
    (Hᵉ : map-retraction-retractᵉ Rᵉ ~ᵉ map-retraction-retractᵉ Sᵉ) →
    UUᵉ l1ᵉ
  coherence-htpy-retractᵉ Rᵉ Sᵉ Iᵉ Hᵉ =
    ( is-retraction-map-retraction-retractᵉ Rᵉ) ~ᵉ
    ( horizontal-concat-htpyᵉ Hᵉ Iᵉ ∙hᵉ is-retraction-map-retraction-retractᵉ Sᵉ)

  htpy-retractᵉ : (Rᵉ Sᵉ : Aᵉ retract-ofᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-retractᵉ Rᵉ Sᵉ =
    Σᵉ ( inclusion-retractᵉ Rᵉ ~ᵉ inclusion-retractᵉ Sᵉ)
      ( λ Iᵉ →
        Σᵉ ( map-retraction-retractᵉ Rᵉ ~ᵉ map-retraction-retractᵉ Sᵉ)
          ( coherence-htpy-retractᵉ Rᵉ Sᵉ Iᵉ))

  refl-htpy-retractᵉ : (Rᵉ : Aᵉ retract-ofᵉ Bᵉ) → htpy-retractᵉ Rᵉ Rᵉ
  refl-htpy-retractᵉ Rᵉ = (refl-htpyᵉ ,ᵉ refl-htpyᵉ ,ᵉ refl-htpyᵉ)

  htpy-eq-retractᵉ : (Rᵉ Sᵉ : Aᵉ retract-ofᵉ Bᵉ) → Rᵉ ＝ᵉ Sᵉ → htpy-retractᵉ Rᵉ Sᵉ
  htpy-eq-retractᵉ Rᵉ .Rᵉ reflᵉ = refl-htpy-retractᵉ Rᵉ

  is-torsorial-htpy-retractᵉ :
    (Rᵉ : Aᵉ retract-ofᵉ Bᵉ) → is-torsorialᵉ (htpy-retractᵉ Rᵉ)
  is-torsorial-htpy-retractᵉ Rᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (inclusion-retractᵉ Rᵉ))
      ( inclusion-retractᵉ Rᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ (map-retraction-retractᵉ Rᵉ))
        ( map-retraction-retractᵉ Rᵉ ,ᵉ refl-htpyᵉ)
        ( is-torsorial-htpyᵉ (is-retraction-map-retraction-retractᵉ Rᵉ)))

  is-equiv-htpy-eq-retractᵉ :
    (Rᵉ Sᵉ : Aᵉ retract-ofᵉ Bᵉ) → is-equivᵉ (htpy-eq-retractᵉ Rᵉ Sᵉ)
  is-equiv-htpy-eq-retractᵉ Rᵉ =
    fundamental-theorem-idᵉ (is-torsorial-htpy-retractᵉ Rᵉ) (htpy-eq-retractᵉ Rᵉ)

  equiv-htpy-eq-retractᵉ : (Rᵉ Sᵉ : Aᵉ retract-ofᵉ Bᵉ) → (Rᵉ ＝ᵉ Sᵉ) ≃ᵉ htpy-retractᵉ Rᵉ Sᵉ
  equiv-htpy-eq-retractᵉ Rᵉ Sᵉ =
    ( htpy-eq-retractᵉ Rᵉ Sᵉ ,ᵉ is-equiv-htpy-eq-retractᵉ Rᵉ Sᵉ)

  eq-htpy-retractᵉ : (Rᵉ Sᵉ : Aᵉ retract-ofᵉ Bᵉ) → htpy-retractᵉ Rᵉ Sᵉ → Rᵉ ＝ᵉ Sᵉ
  eq-htpy-retractᵉ Rᵉ Sᵉ = map-inv-is-equivᵉ (is-equiv-htpy-eq-retractᵉ Rᵉ Sᵉ)
```

### Characterizing equality of the total type of retracts

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  equiv-retractsᵉ :
    {l3ᵉ : Level} (Rᵉ : retractsᵉ l2ᵉ Aᵉ) (Sᵉ : retractsᵉ l3ᵉ Aᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  equiv-retractsᵉ Rᵉ Sᵉ =
    Σᵉ ( type-retractsᵉ Rᵉ ≃ᵉ type-retractsᵉ Sᵉ)
      ( λ eᵉ →
        htpy-retractᵉ
          ( retract-retractsᵉ Rᵉ)
          ( comp-retractᵉ (retract-retractsᵉ Sᵉ) (retract-equivᵉ eᵉ)))

  refl-equiv-retractsᵉ : (Rᵉ : retractsᵉ l2ᵉ Aᵉ) → equiv-retractsᵉ Rᵉ Rᵉ
  refl-equiv-retractsᵉ Rᵉ =
    ( id-equivᵉ ,ᵉ
      refl-htpyᵉ ,ᵉ
      refl-htpyᵉ ,ᵉ
      ( ( inv-htpyᵉ
          ( left-unit-law-left-whisker-compᵉ
            ( is-retraction-map-retraction-retractsᵉ Rᵉ))) ∙hᵉ
        ( inv-htpy-right-unit-htpyᵉ)))

  equiv-eq-retractsᵉ : (Rᵉ Sᵉ : retractsᵉ l2ᵉ Aᵉ) → Rᵉ ＝ᵉ Sᵉ → equiv-retractsᵉ Rᵉ Sᵉ
  equiv-eq-retractsᵉ Rᵉ .Rᵉ reflᵉ = refl-equiv-retractsᵉ Rᵉ

  is-torsorial-equiv-retractsᵉ :
    (Rᵉ : retractsᵉ l2ᵉ Aᵉ) → is-torsorialᵉ (equiv-retractsᵉ Rᵉ)
  is-torsorial-equiv-retractsᵉ Rᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ (type-retractsᵉ Rᵉ))
      ( type-retractsᵉ Rᵉ ,ᵉ id-equivᵉ)
      ( is-contr-equivᵉ
        ( Σᵉ (retractᵉ Aᵉ (type-retractsᵉ Rᵉ)) (htpy-retractᵉ (retract-retractsᵉ Rᵉ)))
        ( equiv-totᵉ
          ( λ Sᵉ →
            equiv-totᵉ
              ( λ Iᵉ →
                equiv-totᵉ
                  ( λ Jᵉ →
                    equiv-concat-htpy'ᵉ
                      ( is-retraction-map-retraction-retractsᵉ Rᵉ)
                      ( ap-concat-htpyᵉ
                        ( horizontal-concat-htpyᵉ Jᵉ Iᵉ)
                        ( right-unit-htpyᵉ ∙hᵉ
                          left-unit-law-left-whisker-compᵉ
                            ( is-retraction-map-retraction-retractᵉ Sᵉ)))))))
        ( is-torsorial-htpy-retractᵉ (retract-retractsᵉ Rᵉ)))

  is-equiv-equiv-eq-retractsᵉ :
    (Rᵉ Sᵉ : retractsᵉ l2ᵉ Aᵉ) → is-equivᵉ (equiv-eq-retractsᵉ Rᵉ Sᵉ)
  is-equiv-equiv-eq-retractsᵉ Rᵉ =
    fundamental-theorem-idᵉ (is-torsorial-equiv-retractsᵉ Rᵉ) (equiv-eq-retractsᵉ Rᵉ)

  equiv-equiv-eq-retractsᵉ : (Rᵉ Sᵉ : retractsᵉ l2ᵉ Aᵉ) → (Rᵉ ＝ᵉ Sᵉ) ≃ᵉ equiv-retractsᵉ Rᵉ Sᵉ
  equiv-equiv-eq-retractsᵉ Rᵉ Sᵉ =
    ( equiv-eq-retractsᵉ Rᵉ Sᵉ ,ᵉ is-equiv-equiv-eq-retractsᵉ Rᵉ Sᵉ)

  eq-equiv-retractsᵉ : (Rᵉ Sᵉ : retractsᵉ l2ᵉ Aᵉ) → equiv-retractsᵉ Rᵉ Sᵉ → Rᵉ ＝ᵉ Sᵉ
  eq-equiv-retractsᵉ Rᵉ Sᵉ = map-inv-is-equivᵉ (is-equiv-equiv-eq-retractsᵉ Rᵉ Sᵉ)
```

## See also

-ᵉ [Retractsᵉ ofᵉ maps](foundation.retracts-of-maps.mdᵉ)