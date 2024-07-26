# Uniquely eliminating modalities

```agda
module orthogonal-factorization-systems.uniquely-eliminating-modalitiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.local-typesᵉ
open import orthogonal-factorization-systems.modal-operatorsᵉ
```

</details>

## Idea

Aᵉ **uniquelyᵉ eliminatingᵉ modality**ᵉ isᵉ aᵉ _higherᵉ modeᵉ ofᵉ logicᵉ_ definedᵉ in termsᵉ
ofᵉ aᵉ monadicᵉ
[modalᵉ operator](orthogonal-factorization-systems.modal-operators.mdᵉ) `○`ᵉ
satisfyingᵉ aᵉ certainᵉ [locality](orthogonal-factorization-systems.local-types.mdᵉ)
condition.ᵉ Namely,ᵉ thatᵉ dependentᵉ precompositionᵉ byᵉ theᵉ modalᵉ unitᵉ `unit-○`ᵉ isᵉ
anᵉ equivalenceᵉ forᵉ typeᵉ familiesᵉ overᵉ typesᵉ in theᵉ imageᵉ ofᵉ theᵉ operatorᵉ:

```text
  -ᵉ ∘ᵉ unit-○ᵉ : Πᵉ (xᵉ : ○ᵉ Xᵉ) (○ᵉ (Pᵉ xᵉ)) ≃ᵉ Πᵉ (xᵉ : Xᵉ) (○ᵉ (Pᵉ (unit-○ᵉ xᵉ)))
```

## Definition

```agda
is-uniquely-eliminating-modalityᵉ :
  {l1ᵉ l2ᵉ : Level} {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ} →
  unit-modalityᵉ ○ᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
is-uniquely-eliminating-modalityᵉ {l1ᵉ} {l2ᵉ} {○ᵉ} unit-○ᵉ =
  {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : ○ᵉ Xᵉ → UUᵉ l1ᵉ) → is-local-dependent-typeᵉ (unit-○ᵉ) (○ᵉ ∘ᵉ Pᵉ)

uniquely-eliminating-modalityᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
uniquely-eliminating-modalityᵉ l1ᵉ l2ᵉ =
  Σᵉ ( operator-modalityᵉ l1ᵉ l2ᵉ)
    ( λ ○ᵉ →
      Σᵉ ( unit-modalityᵉ ○ᵉ)
        ( is-uniquely-eliminating-modalityᵉ))
```

### Components of a uniquely eliminating modality

```agda
module _
  {l1ᵉ l2ᵉ : Level} {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ} {unit-○ᵉ : unit-modalityᵉ ○ᵉ}
  (is-uem-○ᵉ : is-uniquely-eliminating-modalityᵉ unit-○ᵉ)
  where

  ind-modality-is-uniquely-eliminating-modalityᵉ :
    {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : ○ᵉ Xᵉ → UUᵉ l1ᵉ) →
    ((xᵉ : Xᵉ) → ○ᵉ (Pᵉ (unit-○ᵉ xᵉ))) → (x'ᵉ : ○ᵉ Xᵉ) → ○ᵉ (Pᵉ x'ᵉ)
  ind-modality-is-uniquely-eliminating-modalityᵉ Pᵉ =
    map-inv-is-equivᵉ (is-uem-○ᵉ Pᵉ)

  compute-ind-modality-is-uniquely-eliminating-modalityᵉ :
    {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : ○ᵉ Xᵉ → UUᵉ l1ᵉ) (fᵉ : (xᵉ : Xᵉ) → ○ᵉ (Pᵉ (unit-○ᵉ xᵉ))) →
    (pr1ᵉ (pr1ᵉ (is-uem-○ᵉ Pᵉ)) fᵉ ∘ᵉ unit-○ᵉ) ~ᵉ fᵉ
  compute-ind-modality-is-uniquely-eliminating-modalityᵉ Pᵉ =
    htpy-eqᵉ ∘ᵉ pr2ᵉ (pr1ᵉ (is-uem-○ᵉ Pᵉ))

module _
  {l1ᵉ l2ᵉ : Level}
  ((○ᵉ ,ᵉ unit-○ᵉ ,ᵉ is-uem-○ᵉ) : uniquely-eliminating-modalityᵉ l1ᵉ l2ᵉ)
  where

  operator-modality-uniquely-eliminating-modalityᵉ : operator-modalityᵉ l1ᵉ l2ᵉ
  operator-modality-uniquely-eliminating-modalityᵉ = ○ᵉ

  unit-modality-uniquely-eliminating-modalityᵉ : unit-modalityᵉ ○ᵉ
  unit-modality-uniquely-eliminating-modalityᵉ = unit-○ᵉ

  is-uniquely-eliminating-modality-uniquely-eliminating-modalityᵉ :
    is-uniquely-eliminating-modalityᵉ unit-○ᵉ
  is-uniquely-eliminating-modality-uniquely-eliminating-modalityᵉ = is-uem-○ᵉ
```

## Properties

### Being uniquely eliminating is a property

```agda
module _
  {l1ᵉ l2ᵉ : Level} {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ} (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  is-prop-is-uniquely-eliminating-modalityᵉ :
    is-propᵉ (is-uniquely-eliminating-modalityᵉ unit-○ᵉ)
  is-prop-is-uniquely-eliminating-modalityᵉ =
    is-prop-implicit-Πᵉ
      ( λ Xᵉ →
        is-prop-Πᵉ
          ( λ Pᵉ → is-property-is-local-dependent-typeᵉ unit-○ᵉ (○ᵉ ∘ᵉ Pᵉ)))

  is-uniquely-eliminating-modality-Propᵉ : Propᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ is-uniquely-eliminating-modality-Propᵉ =
    is-uniquely-eliminating-modalityᵉ unit-○ᵉ
  pr2ᵉ is-uniquely-eliminating-modality-Propᵉ =
    is-prop-is-uniquely-eliminating-modalityᵉ
```

### `○ X` is modal

```agda
module _
  {lᵉ : Level}
  ((○ᵉ ,ᵉ unit-○ᵉ ,ᵉ is-uem-○ᵉ) : uniquely-eliminating-modalityᵉ lᵉ lᵉ)
  (Xᵉ : UUᵉ lᵉ)
  where

  map-inv-unit-uniquely-eliminating-modalityᵉ : ○ᵉ (○ᵉ Xᵉ) → ○ᵉ Xᵉ
  map-inv-unit-uniquely-eliminating-modalityᵉ =
    ind-modality-is-uniquely-eliminating-modalityᵉ is-uem-○ᵉ (λ _ → Xᵉ) idᵉ

  is-section-unit-uniquely-eliminating-modalityᵉ :
    (map-inv-unit-uniquely-eliminating-modalityᵉ ∘ᵉ unit-○ᵉ) ~ᵉ idᵉ
  is-section-unit-uniquely-eliminating-modalityᵉ =
    compute-ind-modality-is-uniquely-eliminating-modalityᵉ
      ( is-uem-○ᵉ)
      ( λ _ → Xᵉ)
      ( idᵉ)

  is-retraction-unit-uniquely-eliminating-modalityᵉ :
    (unit-○ᵉ ∘ᵉ map-inv-unit-uniquely-eliminating-modalityᵉ) ~ᵉ idᵉ
  is-retraction-unit-uniquely-eliminating-modalityᵉ =
    htpy-eqᵉ
      ( apᵉ pr1ᵉ
        ( eq-is-contr'ᵉ
          ( is-contr-map-is-equivᵉ (is-uem-○ᵉ (λ _ → ○ᵉ Xᵉ)) unit-○ᵉ)
          ( unit-○ᵉ ∘ᵉ map-inv-unit-uniquely-eliminating-modalityᵉ ,ᵉ
            eq-htpyᵉ
              ( apᵉ unit-○ᵉ ∘ᵉ (is-section-unit-uniquely-eliminating-modalityᵉ)))
          ( idᵉ ,ᵉ reflᵉ)))

  is-modal-uniquely-eliminating-modalityᵉ : is-modalᵉ unit-○ᵉ (○ᵉ Xᵉ)
  is-modal-uniquely-eliminating-modalityᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-unit-uniquely-eliminating-modalityᵉ
      is-retraction-unit-uniquely-eliminating-modalityᵉ
      is-section-unit-uniquely-eliminating-modalityᵉ
```

### Uniquely eliminating modalities are uniquely determined by their modal types

Uniquelyᵉ eliminatingᵉ modalitiesᵉ areᵉ uniquelyᵉ determinedᵉ byᵉ theirᵉ modalᵉ types.ᵉ
Equivalently,ᵉ thisᵉ canᵉ beᵉ phrazedᵉ asᵉ aᵉ characterizationᵉ ofᵉ theᵉ identityᵉ typeᵉ ofᵉ
uniquelyᵉ eliminatingᵉ modalities.ᵉ

Supposeᵉ givenᵉ twoᵉ uniquelyᵉ eliminatingᵉ modalitiesᵉ `○`ᵉ andᵉ `●`.ᵉ Theyᵉ areᵉ equalᵉ ifᵉ
andᵉ onlyᵉ ifᵉ theyᵉ haveᵉ theᵉ sameᵉ modalᵉ types.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  where

  htpy-uniquely-eliminating-modalityᵉ :
    (○ᵉ ●ᵉ : uniquely-eliminating-modalityᵉ l1ᵉ l2ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  htpy-uniquely-eliminating-modalityᵉ ○ᵉ ●ᵉ =
    equiv-famᵉ
      ( is-modalᵉ (unit-modality-uniquely-eliminating-modalityᵉ ○ᵉ))
      ( is-modalᵉ (unit-modality-uniquely-eliminating-modalityᵉ ●ᵉ))

  refl-htpy-uniquely-eliminating-modalityᵉ :
    (○ᵉ : uniquely-eliminating-modalityᵉ l1ᵉ l2ᵉ) →
    htpy-uniquely-eliminating-modalityᵉ ○ᵉ ○ᵉ
  refl-htpy-uniquely-eliminating-modalityᵉ ○ᵉ Xᵉ = id-equivᵉ

  htpy-eq-uniquely-eliminating-modalityᵉ :
    (○ᵉ ●ᵉ : uniquely-eliminating-modalityᵉ l1ᵉ l2ᵉ) →
    ○ᵉ ＝ᵉ ●ᵉ → htpy-uniquely-eliminating-modalityᵉ ○ᵉ ●ᵉ
  htpy-eq-uniquely-eliminating-modalityᵉ ○ᵉ .○ᵉ reflᵉ =
    refl-htpy-uniquely-eliminating-modalityᵉ ○ᵉ
```

Itᵉ remainsᵉ to showᵉ thatᵉ `htpy-eq-uniquely-eliminating-modality`ᵉ isᵉ anᵉ
equivalence.ᵉ

## See also

Theᵉ equivalentᵉ notionsᵉ ofᵉ

-ᵉ [Higherᵉ modalities](orthogonal-factorization-systems.higher-modalities.mdᵉ)
-ᵉ [Σ-closedᵉ reflectiveᵉ modalities](orthogonal-factorization-systems.sigma-closed-reflective-modalities.mdᵉ)
-ᵉ [Σ-closedᵉ reflectiveᵉ subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.mdᵉ)
-ᵉ [Stableᵉ orthogonalᵉ factorizationᵉ systems](orthogonal-factorization-systems.stable-orthogonal-factorization-systems.mdᵉ)

## References

{{#bibliographyᵉ}} {{#referenceᵉ RSS20ᵉ}}