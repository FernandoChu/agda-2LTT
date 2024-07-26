# Acyclic types

```agda
module synthetic-homotopy-theory.acyclic-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.functoriality-suspensionsᵉ
open import synthetic-homotopy-theory.suspensions-of-typesᵉ
```

</details>

## Idea

Aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to beᵉ **acyclic**ᵉ ifᵉ itsᵉ
[suspension](synthetic-homotopy-theory.suspensions-of-types.mdᵉ) isᵉ
[contractible](foundation.contractible-types.md).ᵉ

## Definition

```agda
is-acyclic-Propᵉ : {lᵉ : Level} → UUᵉ lᵉ → Propᵉ lᵉ
is-acyclic-Propᵉ Aᵉ = is-contr-Propᵉ (suspensionᵉ Aᵉ)

is-acyclicᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
is-acyclicᵉ Aᵉ = type-Propᵉ (is-acyclic-Propᵉ Aᵉ)

is-prop-is-acyclicᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → is-propᵉ (is-acyclicᵉ Aᵉ)
is-prop-is-acyclicᵉ Aᵉ = is-prop-type-Propᵉ (is-acyclic-Propᵉ Aᵉ)
```

## Properties

### Being acyclic is invariant under equivalence

```agda
is-acyclic-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  Aᵉ ≃ᵉ Bᵉ → is-acyclicᵉ Bᵉ → is-acyclicᵉ Aᵉ
is-acyclic-equivᵉ {Bᵉ = Bᵉ} eᵉ acᵉ =
  is-contr-equivᵉ (suspensionᵉ Bᵉ) (equiv-suspensionᵉ eᵉ) acᵉ

is-acyclic-equiv'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  Aᵉ ≃ᵉ Bᵉ → is-acyclicᵉ Aᵉ → is-acyclicᵉ Bᵉ
is-acyclic-equiv'ᵉ eᵉ = is-acyclic-equivᵉ (inv-equivᵉ eᵉ)
```

### Acyclic types are closed under retracts

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-acyclic-retract-ofᵉ : Aᵉ retract-ofᵉ Bᵉ → is-acyclicᵉ Bᵉ → is-acyclicᵉ Aᵉ
  is-acyclic-retract-ofᵉ Rᵉ acᵉ =
    is-contr-retract-ofᵉ (suspensionᵉ Bᵉ) (retract-of-suspension-retract-ofᵉ Rᵉ) acᵉ
```

### Contractible types are acyclic

```agda
is-acyclic-is-contrᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → is-contrᵉ Aᵉ → is-acyclicᵉ Aᵉ
is-acyclic-is-contrᵉ Aᵉ = is-contr-suspension-is-contrᵉ

is-acyclic-unitᵉ : is-acyclicᵉ unitᵉ
is-acyclic-unitᵉ = is-acyclic-is-contrᵉ unitᵉ is-contr-unitᵉ
```

## See also

-ᵉ [Acyclicᵉ maps](synthetic-homotopy-theory.acyclic-maps.mdᵉ)
-ᵉ [`k`-acyclicᵉ types](synthetic-homotopy-theory.truncated-acyclic-types.mdᵉ)
-ᵉ [Dependentᵉ epimorphisms](foundation.dependent-epimorphisms.mdᵉ)
-ᵉ [Epimorphisms](foundation.epimorphisms.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to sets](foundation.epimorphisms-with-respect-to-sets.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to truncatedᵉ types](foundation.epimorphisms-with-respect-to-truncated-types.mdᵉ)

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}