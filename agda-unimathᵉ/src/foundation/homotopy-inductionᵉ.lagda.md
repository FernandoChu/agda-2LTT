# Homotopy induction

```agda
module foundation.homotopy-inductionᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-systemsᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universal-property-identity-systemsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Theᵉ principleᵉ ofᵉ **homotopyᵉ induction**ᵉ assertsᵉ thatᵉ homotopiesᵉ formᵉ anᵉ
[identityᵉ system](foundation.identity-systems.mdᵉ) onᵉ dependentᵉ functionᵉ types.ᵉ

## Statement

### Evaluation at the reflexivity homotopy

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  ev-refl-htpyᵉ :
    (Cᵉ : (gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → fᵉ ~ᵉ gᵉ → UUᵉ l3ᵉ) →
    ((gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ) → Cᵉ gᵉ Hᵉ) → Cᵉ fᵉ refl-htpyᵉ
  ev-refl-htpyᵉ Cᵉ φᵉ = φᵉ fᵉ refl-htpyᵉ

  triangle-ev-refl-htpyᵉ :
    (Cᵉ : (Σᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ) (fᵉ ~ᵉ_)) → UUᵉ l3ᵉ) →
    coherence-triangle-mapsᵉ
      ( ev-pointᵉ (fᵉ ,ᵉ refl-htpyᵉ))
      ( ev-refl-htpyᵉ (λ gᵉ Hᵉ → Cᵉ (gᵉ ,ᵉ Hᵉ)))
      ( ev-pairᵉ)
  triangle-ev-refl-htpyᵉ Cᵉ Fᵉ = reflᵉ
```

### The homotopy induction principle

```agda
induction-principle-homotopiesᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → UUωᵉ
induction-principle-homotopiesᵉ fᵉ =
  is-identity-systemᵉ (fᵉ ~ᵉ_) fᵉ (refl-htpyᵉ)
```

## Propositions

### The total space of homotopies is contractible

Typeᵉ familiesᵉ ofᵉ whichᵉ theᵉ [totalᵉ space](foundation.dependent-pair-types.mdᵉ) isᵉ
[contractible](foundation-core.contractible-types.mdᵉ) areᵉ alsoᵉ calledᵉ
[torsorial](foundation-core.torsorial-type-families.md).ᵉ Thisᵉ terminologyᵉ
originatesᵉ fromᵉ higherᵉ groupᵉ theory,ᵉ where aᵉ
[higherᵉ groupᵉ action](higher-group-theory.higher-group-actions.mdᵉ) isᵉ torsorialᵉ
ifᵉ itsᵉ typeᵉ ofᵉ [orbits](higher-group-theory.orbits-higher-group-actions.md),ᵉ
i.e.,ᵉ itsᵉ totalᵉ space,ᵉ isᵉ contractible.ᵉ Ourᵉ claimᵉ thatᵉ theᵉ totalᵉ spaceᵉ ofᵉ allᵉ
homotopiesᵉ fromᵉ aᵉ functionᵉ `f`ᵉ isᵉ contractibleᵉ canᵉ thereforeᵉ beᵉ statedᵉ moreᵉ
succinctlyᵉ asᵉ theᵉ claimᵉ thatᵉ theᵉ familyᵉ ofᵉ homotopiesᵉ fromᵉ `f`ᵉ isᵉ torsorial.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ)
  where

  abstract
    is-torsorial-htpyᵉ : is-torsorialᵉ (λ gᵉ → fᵉ ~ᵉ gᵉ)
    is-torsorial-htpyᵉ =
      is-contr-equiv'ᵉ
        ( Σᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ) (Idᵉ fᵉ))
        ( equiv-totᵉ (λ gᵉ → equiv-funextᵉ))
        ( is-torsorial-Idᵉ fᵉ)

  abstract
    is-torsorial-htpy'ᵉ : is-torsorialᵉ (λ gᵉ → gᵉ ~ᵉ fᵉ)
    is-torsorial-htpy'ᵉ =
      is-contr-equiv'ᵉ
        ( Σᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ) (λ gᵉ → gᵉ ＝ᵉ fᵉ))
        ( equiv-totᵉ (λ gᵉ → equiv-funextᵉ))
        ( is-torsorial-Id'ᵉ fᵉ)
```

### Homotopy induction is equivalent to function extensionality

```agda
abstract
  induction-principle-homotopies-based-function-extensionalityᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) →
    based-function-extensionalityᵉ fᵉ →
    induction-principle-homotopiesᵉ fᵉ
  induction-principle-homotopies-based-function-extensionalityᵉ
    {Aᵉ = Aᵉ} {Bᵉ} fᵉ funext-fᵉ =
    is-identity-system-is-torsorialᵉ fᵉ
      ( refl-htpyᵉ)
      ( is-torsorial-htpyᵉ fᵉ)

abstract
  based-function-extensionality-induction-principle-homotopiesᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) →
    induction-principle-homotopiesᵉ fᵉ →
    based-function-extensionalityᵉ fᵉ
  based-function-extensionality-induction-principle-homotopiesᵉ fᵉ ind-htpy-fᵉ =
    fundamental-theorem-id-is-identity-systemᵉ fᵉ
      ( refl-htpyᵉ)
      ( ind-htpy-fᵉ)
      ( λ _ → htpy-eqᵉ)
```

### Homotopy induction

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  abstract
    induction-principle-htpyᵉ :
      (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → induction-principle-homotopiesᵉ fᵉ
    induction-principle-htpyᵉ fᵉ =
      induction-principle-homotopies-based-function-extensionalityᵉ fᵉ (funextᵉ fᵉ)

    ind-htpyᵉ :
      {l3ᵉ : Level} (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ)
      (Cᵉ : (gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → fᵉ ~ᵉ gᵉ → UUᵉ l3ᵉ) →
      Cᵉ fᵉ refl-htpyᵉ → {gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) → Cᵉ gᵉ Hᵉ
    ind-htpyᵉ fᵉ Cᵉ tᵉ {gᵉ} = pr1ᵉ (induction-principle-htpyᵉ fᵉ Cᵉ) tᵉ gᵉ

    compute-ind-htpyᵉ :
      {l3ᵉ : Level} (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ)
      (Cᵉ : (gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → fᵉ ~ᵉ gᵉ → UUᵉ l3ᵉ) →
      (cᵉ : Cᵉ fᵉ refl-htpyᵉ) → ind-htpyᵉ fᵉ Cᵉ cᵉ refl-htpyᵉ ＝ᵉ cᵉ
    compute-ind-htpyᵉ fᵉ Cᵉ = pr2ᵉ (induction-principle-htpyᵉ fᵉ Cᵉ)
```

### The evaluation map `ev-refl-htpy` is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (Cᵉ : (gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → fᵉ ~ᵉ gᵉ → UUᵉ l3ᵉ)
  where

  is-equiv-ev-refl-htpyᵉ : is-equivᵉ (ev-refl-htpyᵉ Cᵉ)
  is-equiv-ev-refl-htpyᵉ =
    dependent-universal-property-identity-system-is-torsorialᵉ
      ( refl-htpyᵉ)
      ( is-torsorial-htpyᵉ fᵉ)
      ( Cᵉ)

  is-contr-map-ev-refl-htpyᵉ : is-contr-mapᵉ (ev-refl-htpyᵉ Cᵉ)
  is-contr-map-ev-refl-htpyᵉ = is-contr-map-is-equivᵉ is-equiv-ev-refl-htpyᵉ
```

## See also

-ᵉ [Homotopies](foundation.homotopies.md).ᵉ
-ᵉ [Functionᵉ extensionality](foundation.function-extensionality.md).ᵉ