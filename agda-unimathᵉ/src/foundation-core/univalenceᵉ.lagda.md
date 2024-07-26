# The univalence axiom

```agda
module foundation-core.univalenceᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "univalenceᵉ axiom"ᵉ Disambiguation="types"ᵉ Agda=univalence-axiomᵉ}}
characterizesᵉ theᵉ [identityᵉ types](foundation-core.identity-types.mdᵉ) ofᵉ
universes.ᵉ Itᵉ assertsᵉ thatᵉ theᵉ mapᵉ `(Aᵉ ＝ᵉ Bᵉ) → (Aᵉ ≃ᵉ B)`ᵉ isᵉ anᵉ equivalence.ᵉ

Inᵉ thisᵉ file,ᵉ weᵉ defineᵉ theᵉ statementᵉ ofᵉ theᵉ axiom.ᵉ Theᵉ axiomᵉ itselfᵉ isᵉ
postulatedᵉ in [`foundation.univalence`](foundation.univalence.mdᵉ) asᵉ
`univalence`.ᵉ

Univalenceᵉ isᵉ postulatedᵉ byᵉ statingᵉ thatᵉ theᵉ canonicalᵉ comparisonᵉ mapᵉ

```text
  equiv-eqᵉ : Aᵉ ＝ᵉ Bᵉ → Aᵉ ≃ᵉ Bᵉ
```

fromᵉ identificationsᵉ betweenᵉ twoᵉ typesᵉ to equivalencesᵉ betweenᵉ themᵉ isᵉ anᵉ
equivalence.ᵉ Althoughᵉ weᵉ couldᵉ defineᵉ `equiv-eq`ᵉ byᵉ pattern matching,ᵉ dueᵉ to
computationalᵉ considerations,ᵉ weᵉ defineᵉ itᵉ asᵉ

```text
  equiv-eqᵉ :=ᵉ equiv-trᵉ (id_𝒰).ᵉ
```

Itᵉ followsᵉ fromᵉ thisᵉ definitionᵉ thatᵉ `equiv-eqᵉ reflᵉ ≐ᵉ id-equiv`,ᵉ asᵉ expected.ᵉ

## Definitions

### Equalities induce equivalences

```agda
module _
  {lᵉ : Level}
  where

  equiv-eqᵉ : {Aᵉ Bᵉ : UUᵉ lᵉ} → Aᵉ ＝ᵉ Bᵉ → Aᵉ ≃ᵉ Bᵉ
  equiv-eqᵉ = equiv-trᵉ idᵉ

  map-eqᵉ : {Aᵉ Bᵉ : UUᵉ lᵉ} → Aᵉ ＝ᵉ Bᵉ → Aᵉ → Bᵉ
  map-eqᵉ = map-equivᵉ ∘ᵉ equiv-eqᵉ

  compute-equiv-eq-reflᵉ :
    {Aᵉ : UUᵉ lᵉ} → equiv-eqᵉ (reflᵉ {xᵉ = Aᵉ}) ＝ᵉ id-equivᵉ
  compute-equiv-eq-reflᵉ = reflᵉ
```

### The statement of the univalence axiom

#### An instance of univalence

```agda
instance-univalenceᵉ : {lᵉ : Level} (Aᵉ Bᵉ : UUᵉ lᵉ) → UUᵉ (lsuc lᵉ)
instance-univalenceᵉ Aᵉ Bᵉ = is-equivᵉ (equiv-eqᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ})
```

#### Based univalence

```agda
based-univalence-axiomᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → UUᵉ (lsuc lᵉ)
based-univalence-axiomᵉ {lᵉ} Aᵉ = (Bᵉ : UUᵉ lᵉ) → instance-univalenceᵉ Aᵉ Bᵉ
```

#### The univalence axiom with respect to a universe level

```agda
univalence-axiom-Levelᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
univalence-axiom-Levelᵉ lᵉ = (Aᵉ Bᵉ : UUᵉ lᵉ) → instance-univalenceᵉ Aᵉ Bᵉ
```

#### The univalence axiom

```agda
univalence-axiomᵉ : UUωᵉ
univalence-axiomᵉ = {lᵉ : Level} → univalence-axiom-Levelᵉ lᵉ
```

## Properties

### The univalence axiom implies that the total space of equivalences is contractible

```agda
abstract
  is-torsorial-equiv-based-univalenceᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
    based-univalence-axiomᵉ Aᵉ → is-torsorialᵉ (λ (Bᵉ : UUᵉ lᵉ) → Aᵉ ≃ᵉ Bᵉ)
  is-torsorial-equiv-based-univalenceᵉ Aᵉ UAᵉ =
    fundamental-theorem-id'ᵉ (λ Bᵉ → equiv-eqᵉ) UAᵉ
```

### Contractibility of the total space of equivalences implies univalence

```agda
abstract
  based-univalence-is-torsorial-equivᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
    is-torsorialᵉ (λ (Bᵉ : UUᵉ lᵉ) → Aᵉ ≃ᵉ Bᵉ) → based-univalence-axiomᵉ Aᵉ
  based-univalence-is-torsorial-equivᵉ Aᵉ cᵉ =
    fundamental-theorem-idᵉ cᵉ (λ Bᵉ → equiv-eqᵉ)
```

### The underlying map of `equiv-eq` evaluated at `ap B` is the same as transport in the family `B`

Forᵉ anyᵉ typeᵉ familyᵉ `B`ᵉ andᵉ identificationᵉ `pᵉ : xᵉ ＝ᵉ y`ᵉ in theᵉ base,ᵉ weᵉ haveᵉ aᵉ
commutingᵉ diagramᵉ

```text
                 equiv-eqᵉ
    (Bᵉ xᵉ = Bᵉ yᵉ) --------->ᵉ (Bᵉ xᵉ ≃ᵉ Bᵉ yᵉ)
         ∧ᵉ                      |
  apᵉ Bᵉ pᵉ |                      | map-equivᵉ
         |                      ∨ᵉ
      (xᵉ = yᵉ) ----------->ᵉ (Bᵉ xᵉ → Bᵉ y).ᵉ
                  trᵉ Bᵉ pᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {xᵉ yᵉ : Aᵉ}
  where

  compute-equiv-eq-apᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) → equiv-eqᵉ (apᵉ Bᵉ pᵉ) ＝ᵉ equiv-trᵉ Bᵉ pᵉ
  compute-equiv-eq-apᵉ reflᵉ = reflᵉ

  compute-map-eq-apᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) → map-eqᵉ (apᵉ Bᵉ pᵉ) ＝ᵉ trᵉ Bᵉ pᵉ
  compute-map-eq-apᵉ pᵉ = apᵉ map-equivᵉ (compute-equiv-eq-apᵉ pᵉ)
```