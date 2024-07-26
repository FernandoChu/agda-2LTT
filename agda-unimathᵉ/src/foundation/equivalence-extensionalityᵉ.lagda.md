# Equivalence extensionality

```agda
module foundation.equivalence-extensionalityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-systemsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Characterizing the identity type of equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  htpy-equivᵉ : Aᵉ ≃ᵉ Bᵉ → Aᵉ ≃ᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-equivᵉ eᵉ e'ᵉ = (map-equivᵉ eᵉ) ~ᵉ (map-equivᵉ e'ᵉ)

  _~eᵉ_ = htpy-equivᵉ

  extensionality-equivᵉ : (fᵉ gᵉ : Aᵉ ≃ᵉ Bᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-equivᵉ fᵉ gᵉ
  extensionality-equivᵉ fᵉ =
    extensionality-type-subtypeᵉ
      ( is-equiv-Propᵉ)
      ( pr2ᵉ fᵉ)
      ( refl-htpy'ᵉ (pr1ᵉ fᵉ))
      ( λ gᵉ → equiv-funextᵉ)
    where
    is-equiv-Propᵉ : (fᵉ : Aᵉ → Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
    pr1ᵉ (is-equiv-Propᵉ fᵉ) = is-equivᵉ fᵉ
    pr2ᵉ (is-equiv-Propᵉ fᵉ) Hᵉ =
      is-prop-is-contrᵉ
        ( is-contr-productᵉ
          ( is-contr-equiv'ᵉ
            ( (bᵉ : Bᵉ) → fiberᵉ fᵉ bᵉ)
            ( distributive-Π-Σᵉ)
            ( is-contr-Πᵉ (is-contr-map-is-equivᵉ Hᵉ)))
          ( is-contr-is-equiv'ᵉ
            ( Σᵉ (Bᵉ → Aᵉ) (λ hᵉ → (hᵉ ∘ᵉ fᵉ) ＝ᵉ idᵉ))
            ( totᵉ (λ hᵉ → htpy-eqᵉ))
            ( is-equiv-tot-is-fiberwise-equivᵉ
              ( λ hᵉ → funextᵉ (hᵉ ∘ᵉ fᵉ) idᵉ))
            ( is-contr-map-is-equivᵉ
              ( is-equiv-precomp-Π-is-equivᵉ Hᵉ (λ yᵉ → Aᵉ))
              ( idᵉ))))
        ( Hᵉ)

  abstract
    is-torsorial-htpy-equivᵉ :
      (eᵉ : Aᵉ ≃ᵉ Bᵉ) → is-torsorialᵉ (htpy-equivᵉ eᵉ)
    is-torsorial-htpy-equivᵉ eᵉ =
      fundamental-theorem-id'ᵉ
        ( map-equivᵉ ∘ᵉ extensionality-equivᵉ eᵉ)
        ( is-equiv-map-equivᵉ ∘ᵉ extensionality-equivᵉ eᵉ)

  refl-htpy-equivᵉ : (eᵉ : Aᵉ ≃ᵉ Bᵉ) → htpy-equivᵉ eᵉ eᵉ
  refl-htpy-equivᵉ eᵉ = refl-htpyᵉ

  eq-htpy-equivᵉ : {eᵉ e'ᵉ : Aᵉ ≃ᵉ Bᵉ} → htpy-equivᵉ eᵉ e'ᵉ → eᵉ ＝ᵉ e'ᵉ
  eq-htpy-equivᵉ {eᵉ} {e'ᵉ} = map-inv-equivᵉ (extensionality-equivᵉ eᵉ e'ᵉ)

  htpy-eq-equivᵉ : {eᵉ e'ᵉ : Aᵉ ≃ᵉ Bᵉ} → eᵉ ＝ᵉ e'ᵉ → htpy-equivᵉ eᵉ e'ᵉ
  htpy-eq-equivᵉ {eᵉ} {e'ᵉ} = map-equivᵉ (extensionality-equivᵉ eᵉ e'ᵉ)

  htpy-eq-map-equivᵉ :
    {eᵉ e'ᵉ : Aᵉ ≃ᵉ Bᵉ} → (map-equivᵉ eᵉ) ＝ᵉ (map-equivᵉ e'ᵉ) → htpy-equivᵉ eᵉ e'ᵉ
  htpy-eq-map-equivᵉ = htpy-eqᵉ
```

### Homotopy induction for homotopies between equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    induction-principle-htpy-equivᵉ :
      {l3ᵉ : Level} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
      (Pᵉ : (e'ᵉ : Aᵉ ≃ᵉ Bᵉ) (Hᵉ : htpy-equivᵉ eᵉ e'ᵉ) → UUᵉ l3ᵉ) →
      sectionᵉ
        ( λ (hᵉ : (e'ᵉ : Aᵉ ≃ᵉ Bᵉ) (Hᵉ : htpy-equivᵉ eᵉ e'ᵉ) → Pᵉ e'ᵉ Hᵉ) →
          hᵉ eᵉ (refl-htpy-equivᵉ eᵉ))
    induction-principle-htpy-equivᵉ eᵉ =
      is-identity-system-is-torsorialᵉ eᵉ
        ( refl-htpy-equivᵉ eᵉ)
        ( is-torsorial-htpy-equivᵉ eᵉ)

  ind-htpy-equivᵉ :
    {l3ᵉ : Level} (eᵉ : Aᵉ ≃ᵉ Bᵉ) (Pᵉ : (e'ᵉ : Aᵉ ≃ᵉ Bᵉ) (Hᵉ : htpy-equivᵉ eᵉ e'ᵉ) → UUᵉ l3ᵉ) →
    Pᵉ eᵉ (refl-htpy-equivᵉ eᵉ) → (e'ᵉ : Aᵉ ≃ᵉ Bᵉ) (Hᵉ : htpy-equivᵉ eᵉ e'ᵉ) → Pᵉ e'ᵉ Hᵉ
  ind-htpy-equivᵉ eᵉ Pᵉ = pr1ᵉ (induction-principle-htpy-equivᵉ eᵉ Pᵉ)

  compute-ind-htpy-equivᵉ :
    {l3ᵉ : Level} (eᵉ : Aᵉ ≃ᵉ Bᵉ) (Pᵉ : (e'ᵉ : Aᵉ ≃ᵉ Bᵉ) (Hᵉ : htpy-equivᵉ eᵉ e'ᵉ) → UUᵉ l3ᵉ)
    (pᵉ : Pᵉ eᵉ (refl-htpy-equivᵉ eᵉ)) →
    ind-htpy-equivᵉ eᵉ Pᵉ pᵉ eᵉ (refl-htpy-equivᵉ eᵉ) ＝ᵉ pᵉ
  compute-ind-htpy-equivᵉ eᵉ Pᵉ = pr2ᵉ (induction-principle-htpy-equivᵉ eᵉ Pᵉ)
```