# Equivalence induction

```agda
module foundation.equivalence-inductionᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-systemsᵉ
open import foundation.subuniversesᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-identity-systemsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.postcomposition-functionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

**Equivalenceᵉ induction**ᵉ isᵉ theᵉ principleᵉ assertingᵉ thatᵉ forᵉ anyᵉ typeᵉ familyᵉ

```text
  Pᵉ : (Bᵉ : 𝒰ᵉ) (eᵉ : Aᵉ ≃ᵉ Bᵉ) → 𝒰ᵉ
```

ofᵉ typesᵉ indexedᵉ byᵉ allᵉ [equivalences](foundation.equivalences.mdᵉ) with domainᵉ
`A`,ᵉ thereᵉ isᵉ aᵉ [section](foundation.sections.mdᵉ) ofᵉ theᵉ evaluationᵉ mapᵉ

```text
  ((Bᵉ : 𝒰ᵉ) (eᵉ : Aᵉ ≃ᵉ Bᵉ) → Pᵉ Bᵉ eᵉ) → Pᵉ Aᵉ id-equiv.ᵉ
```

Theᵉ principleᵉ ofᵉ equivalenceᵉ inductionᵉ isᵉ equivalentᵉ to theᵉ
[univalenceᵉ axiom](foundation.univalence.md).ᵉ

Byᵉ equivalenceᵉ induction,ᵉ itᵉ followsᵉ thatᵉ anyᵉ typeᵉ familyᵉ `Pᵉ : 𝒰ᵉ → 𝒱`ᵉ onᵉ theᵉ
universeᵉ hasᵉ anᵉ
[actionᵉ onᵉ equivalences](foundation.action-on-equivalences-type-families.mdᵉ)

```text
  (Aᵉ ≃ᵉ Bᵉ) → Pᵉ Aᵉ ≃ᵉ Pᵉ B.ᵉ
```

## Definitions

### Evaluation at the identity equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  ev-id-equivᵉ :
    (Pᵉ : (Bᵉ : UUᵉ l1ᵉ) → (Aᵉ ≃ᵉ Bᵉ) → UUᵉ l2ᵉ) →
    ((Bᵉ : UUᵉ l1ᵉ) (eᵉ : Aᵉ ≃ᵉ Bᵉ) → Pᵉ Bᵉ eᵉ) → Pᵉ Aᵉ id-equivᵉ
  ev-id-equivᵉ Pᵉ fᵉ = fᵉ Aᵉ id-equivᵉ

  triangle-ev-id-equivᵉ :
    (Pᵉ : (Σᵉ (UUᵉ l1ᵉ) (Aᵉ ≃ᵉ_)) → UUᵉ l2ᵉ) →
    coherence-triangle-mapsᵉ
      ( ev-pointᵉ (Aᵉ ,ᵉ id-equivᵉ))
      ( ev-id-equivᵉ (λ Xᵉ eᵉ → Pᵉ (Xᵉ ,ᵉ eᵉ)))
      ( ev-pairᵉ)
  triangle-ev-id-equivᵉ Pᵉ fᵉ = reflᵉ
```

### The equivalence induction principle

```agda
module _
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ)
  where

  induction-principle-equivalencesᵉ : UUωᵉ
  induction-principle-equivalencesᵉ =
    is-identity-systemᵉ (λ (Bᵉ : UUᵉ l1ᵉ) → Aᵉ ≃ᵉ Bᵉ) Aᵉ id-equivᵉ
```

## Properties

### Contractibility of the total space of equivalences implies equivalence induction

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  abstract
    is-identity-system-is-torsorial-equivᵉ :
      is-torsorialᵉ (λ (Bᵉ : UUᵉ l1ᵉ) → Aᵉ ≃ᵉ Bᵉ) →
      is-identity-systemᵉ (Aᵉ ≃ᵉ_) Aᵉ id-equivᵉ
    is-identity-system-is-torsorial-equivᵉ =
      is-identity-system-is-torsorialᵉ Aᵉ id-equivᵉ
```

### Equivalence induction implies contractibility of the total space of equivalences

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  abstract
    is-torsorial-equiv-induction-principle-equivalencesᵉ :
      induction-principle-equivalencesᵉ Aᵉ →
      is-torsorialᵉ (λ (Bᵉ : UUᵉ l1ᵉ) → Aᵉ ≃ᵉ Bᵉ)
    is-torsorial-equiv-induction-principle-equivalencesᵉ =
      is-torsorial-is-identity-systemᵉ Aᵉ id-equivᵉ

  abstract
    is-torsorial-is-identity-system-equivᵉ :
      is-identity-systemᵉ (Aᵉ ≃ᵉ_) Aᵉ id-equivᵉ →
      is-torsorialᵉ (λ (Bᵉ : UUᵉ l1ᵉ) → Aᵉ ≃ᵉ Bᵉ)
    is-torsorial-is-identity-system-equivᵉ =
      is-torsorial-is-identity-systemᵉ Aᵉ id-equivᵉ
```

### Equivalence induction in a universe

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  abstract
    is-identity-system-equivᵉ : induction-principle-equivalencesᵉ Aᵉ
    is-identity-system-equivᵉ =
      is-identity-system-is-torsorial-equivᵉ (is-torsorial-equivᵉ Aᵉ)

  ind-equivᵉ :
    {l2ᵉ : Level} (Pᵉ : (Bᵉ : UUᵉ l1ᵉ) → Aᵉ ≃ᵉ Bᵉ → UUᵉ l2ᵉ) →
    Pᵉ Aᵉ id-equivᵉ → {Bᵉ : UUᵉ l1ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) → Pᵉ Bᵉ eᵉ
  ind-equivᵉ Pᵉ pᵉ {Bᵉ} = pr1ᵉ (is-identity-system-equivᵉ Pᵉ) pᵉ Bᵉ

  compute-ind-equivᵉ :
    {l2ᵉ : Level} (Pᵉ : (Bᵉ : UUᵉ l1ᵉ) → Aᵉ ≃ᵉ Bᵉ → UUᵉ l2ᵉ) →
    (uᵉ : Pᵉ Aᵉ id-equivᵉ) → ind-equivᵉ Pᵉ uᵉ id-equivᵉ ＝ᵉ uᵉ
  compute-ind-equivᵉ Pᵉ = pr2ᵉ (is-identity-system-equivᵉ Pᵉ)
```

### Equivalence induction in a subuniverse

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Aᵉ : type-subuniverseᵉ Pᵉ)
  where

  ev-id-equiv-subuniverseᵉ :
    {Fᵉ : (Bᵉ : type-subuniverseᵉ Pᵉ) → equiv-subuniverseᵉ Pᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ} →
    ((Bᵉ : type-subuniverseᵉ Pᵉ) (eᵉ : equiv-subuniverseᵉ Pᵉ Aᵉ Bᵉ) → Fᵉ Bᵉ eᵉ) →
    Fᵉ Aᵉ id-equivᵉ
  ev-id-equiv-subuniverseᵉ fᵉ = fᵉ Aᵉ id-equivᵉ

  triangle-ev-id-equiv-subuniverseᵉ :
    (Fᵉ : (Bᵉ : type-subuniverseᵉ Pᵉ) → equiv-subuniverseᵉ Pᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ) →
    coherence-triangle-mapsᵉ
      ( ev-pointᵉ (Aᵉ ,ᵉ id-equivᵉ))
      ( ev-id-equiv-subuniverseᵉ {Fᵉ})
      ( ev-pairᵉ)
  triangle-ev-id-equiv-subuniverseᵉ Fᵉ Eᵉ = reflᵉ

  abstract
    is-identity-system-equiv-subuniverseᵉ :
      (Fᵉ : (Bᵉ : type-subuniverseᵉ Pᵉ) → equiv-subuniverseᵉ Pᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ) →
      sectionᵉ (ev-id-equiv-subuniverseᵉ {Fᵉ})
    is-identity-system-equiv-subuniverseᵉ =
      is-identity-system-is-torsorialᵉ Aᵉ id-equivᵉ
        ( is-torsorial-equiv-subuniverseᵉ Pᵉ Aᵉ)

  ind-equiv-subuniverseᵉ :
    (Fᵉ : (Bᵉ : type-subuniverseᵉ Pᵉ) → equiv-subuniverseᵉ Pᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ) →
    Fᵉ Aᵉ id-equivᵉ → (Bᵉ : type-subuniverseᵉ Pᵉ) (eᵉ : equiv-subuniverseᵉ Pᵉ Aᵉ Bᵉ) →
    Fᵉ Bᵉ eᵉ
  ind-equiv-subuniverseᵉ Fᵉ =
    pr1ᵉ (is-identity-system-equiv-subuniverseᵉ Fᵉ)

  compute-ind-equiv-subuniverseᵉ :
    (Fᵉ : (Bᵉ : type-subuniverseᵉ Pᵉ) → equiv-subuniverseᵉ Pᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ) →
    (uᵉ : Fᵉ Aᵉ id-equivᵉ) →
    ind-equiv-subuniverseᵉ Fᵉ uᵉ Aᵉ id-equivᵉ ＝ᵉ uᵉ
  compute-ind-equiv-subuniverseᵉ Fᵉ =
    pr2ᵉ (is-identity-system-equiv-subuniverseᵉ Fᵉ)
```

### The evaluation map `ev-id-equiv` is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : (Bᵉ : UUᵉ l1ᵉ) (eᵉ : Aᵉ ≃ᵉ Bᵉ) → UUᵉ l2ᵉ)
  where

  is-equiv-ev-id-equivᵉ : is-equivᵉ (ev-id-equivᵉ Pᵉ)
  is-equiv-ev-id-equivᵉ =
    dependent-universal-property-identity-system-is-torsorialᵉ
      ( id-equivᵉ) (is-torsorial-equivᵉ Aᵉ) Pᵉ

  is-contr-map-ev-id-equivᵉ : is-contr-mapᵉ (ev-id-equivᵉ Pᵉ)
  is-contr-map-ev-id-equivᵉ = is-contr-map-is-equivᵉ is-equiv-ev-id-equivᵉ
```

### The evaluation map `ev-id-equiv-subuniverse` is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : type-subuniverseᵉ Pᵉ)
  (Fᵉ : (Yᵉ : type-subuniverseᵉ Pᵉ) (eᵉ : equiv-subuniverseᵉ Pᵉ Xᵉ Yᵉ) → UUᵉ l3ᵉ)
  where

  is-equiv-ev-id-equiv-subuniverseᵉ :
    is-equivᵉ (ev-id-equiv-subuniverseᵉ Pᵉ Xᵉ {Fᵉ})
  is-equiv-ev-id-equiv-subuniverseᵉ =
    dependent-universal-property-identity-system-is-torsorialᵉ
    ( id-equivᵉ) (is-torsorial-equiv-subuniverseᵉ Pᵉ Xᵉ) Fᵉ

  is-contr-map-ev-id-equiv-subuniverseᵉ :
    is-contr-mapᵉ (ev-id-equiv-subuniverseᵉ Pᵉ Xᵉ {Fᵉ})
  is-contr-map-ev-id-equiv-subuniverseᵉ =
    is-contr-map-is-equivᵉ is-equiv-ev-id-equiv-subuniverseᵉ
```

### Equivalence induction implies that postcomposing by an equivalence is an equivalence

Ofᵉ courseᵉ weᵉ alreadyᵉ knowᵉ thatᵉ thisᵉ factᵉ followsᵉ fromᵉ
[functionᵉ extensionality](foundation.function-extensionality.md).ᵉ However,ᵉ weᵉ
proveᵉ itᵉ againᵉ fromᵉ equivalenceᵉ inductionᵉ soᵉ thatᵉ weᵉ canᵉ proveᵉ thatᵉ
[univalenceᵉ impliesᵉ functionᵉ extensionality](foundation.univalence-implies-function-extensionality.md).ᵉ

```agda
abstract
  is-equiv-postcomp-univalenceᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ Yᵉ : UUᵉ l1ᵉ} (Aᵉ : UUᵉ l2ᵉ) (eᵉ : Xᵉ ≃ᵉ Yᵉ) →
    is-equivᵉ (postcompᵉ Aᵉ (map-equivᵉ eᵉ))
  is-equiv-postcomp-univalenceᵉ Aᵉ =
    ind-equivᵉ (λ Yᵉ eᵉ → is-equivᵉ (postcompᵉ Aᵉ (map-equivᵉ eᵉ))) is-equiv-idᵉ
```