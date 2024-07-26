# `k`-acyclic types

```agda
module synthetic-homotopy-theory.truncated-acyclic-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.functoriality-suspensionsᵉ
open import synthetic-homotopy-theory.suspensions-of-typesᵉ
```

</details>

## Idea

Aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to beᵉ **`k`-acyclic**ᵉ ifᵉ itsᵉ
[suspension](synthetic-homotopy-theory.suspensions-of-types.mdᵉ) isᵉ
[`k`-connected](foundation.connected-types.md).ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) (Aᵉ : UUᵉ lᵉ)
  where

  is-truncated-acyclic-Propᵉ : Propᵉ lᵉ
  is-truncated-acyclic-Propᵉ = is-connected-Propᵉ kᵉ (suspensionᵉ Aᵉ)

  is-truncated-acyclicᵉ : UUᵉ lᵉ
  is-truncated-acyclicᵉ = type-Propᵉ is-truncated-acyclic-Propᵉ

  is-prop-is-truncated-acyclicᵉ : is-propᵉ is-truncated-acyclicᵉ
  is-prop-is-truncated-acyclicᵉ = is-prop-type-Propᵉ is-truncated-acyclic-Propᵉ
```

Weᵉ useᵉ theᵉ nameᵉ `is-truncated-acyclic`ᵉ insteadᵉ ofᵉ `is-truncation-acyclic`,ᵉ
becauseᵉ theᵉ latter,ᵉ in lineᵉ with
[`is-truncation-equivalence`](foundation.truncation-equivalences.md),ᵉ mightᵉ
suggestᵉ thatᵉ itᵉ isᵉ theᵉ truncationᵉ ofᵉ aᵉ typeᵉ thatᵉ isᵉ acyclicᵉ whichᵉ isᵉ notᵉ theᵉ
notionᵉ we'reᵉ interestedᵉ in.ᵉ

## Properties

### Being `k`-acyclic is invariant under equivalence

```agda
is-truncated-acyclic-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  Aᵉ ≃ᵉ Bᵉ → is-truncated-acyclicᵉ kᵉ Bᵉ → is-truncated-acyclicᵉ kᵉ Aᵉ
is-truncated-acyclic-equivᵉ {kᵉ = kᵉ} {Bᵉ = Bᵉ} eᵉ acᵉ =
  is-connected-equivᵉ (equiv-suspensionᵉ eᵉ) acᵉ

is-truncated-acyclic-equiv'ᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  Aᵉ ≃ᵉ Bᵉ → is-truncated-acyclicᵉ kᵉ Aᵉ → is-truncated-acyclicᵉ kᵉ Bᵉ
is-truncated-acyclic-equiv'ᵉ eᵉ = is-truncated-acyclic-equivᵉ (inv-equivᵉ eᵉ)
```

### `k`-acyclic types are closed under retracts

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-truncated-acyclic-retract-ofᵉ :
    Aᵉ retract-ofᵉ Bᵉ →
    is-truncated-acyclicᵉ kᵉ Bᵉ →
    is-truncated-acyclicᵉ kᵉ Aᵉ
  is-truncated-acyclic-retract-ofᵉ Rᵉ acᵉ =
    is-connected-retract-ofᵉ
      ( retract-of-suspension-retract-ofᵉ Rᵉ)
      ( acᵉ)
```

### Every `k`-connected type is `(k+1)`-acyclic

```agda
module _
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ lᵉ}
  where

  is-truncated-acyclic-succ-is-connectedᵉ :
    is-connectedᵉ kᵉ Aᵉ → is-truncated-acyclicᵉ (succ-𝕋ᵉ kᵉ) Aᵉ
  is-truncated-acyclic-succ-is-connectedᵉ =
    is-connected-succ-suspension-is-connectedᵉ
```

### Contractible types are `k`-acyclic for any `k`

```agda
is-truncated-acyclic-is-contrᵉ :
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : UUᵉ lᵉ) → is-contrᵉ Aᵉ → is-truncated-acyclicᵉ kᵉ Aᵉ
is-truncated-acyclic-is-contrᵉ {kᵉ = kᵉ} Aᵉ cᵉ =
  is-connected-is-contrᵉ kᵉ (is-contr-suspension-is-contrᵉ cᵉ)

is-truncated-acyclic-unitᵉ : {kᵉ : 𝕋ᵉ} → is-truncated-acyclicᵉ kᵉ unitᵉ
is-truncated-acyclic-unitᵉ = is-truncated-acyclic-is-contrᵉ unitᵉ is-contr-unitᵉ
```

### Every `(k+1)`-acyclic type is `k`-acyclic

```agda
module _
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ lᵉ}
  where

  is-truncated-acyclic-is-truncated-acyclic-succᵉ :
    is-truncated-acyclicᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → is-truncated-acyclicᵉ kᵉ Aᵉ
  is-truncated-acyclic-is-truncated-acyclic-succᵉ =
    is-connected-is-connected-succ-𝕋ᵉ kᵉ
```

## See also

-ᵉ [Acyclicᵉ maps](synthetic-homotopy-theory.acyclic-maps.mdᵉ)
-ᵉ [Acyclicᵉ types](synthetic-homotopy-theory.acyclic-types.mdᵉ)
-ᵉ [Dependentᵉ epimorphisms](foundation.dependent-epimorphisms.mdᵉ)
-ᵉ [Epimorphisms](foundation.epimorphisms.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to sets](foundation.epimorphisms-with-respect-to-sets.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to truncatedᵉ types](foundation.epimorphisms-with-respect-to-truncated-types.mdᵉ)