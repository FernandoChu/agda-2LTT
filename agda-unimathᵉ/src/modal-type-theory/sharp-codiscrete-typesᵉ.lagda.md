# Sharp codiscrete types

```agda
{-# OPTIONSᵉ --cohesionᵉ --flat-splitᵉ #-}

module modal-type-theory.sharp-codiscrete-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import modal-type-theory.sharp-modalityᵉ

open import orthogonal-factorization-systems.higher-modalitiesᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ saidᵉ to beᵉ **(sharpᵉ) codiscrete**ᵉ ifᵉ itᵉ isᵉ
[sharp](modal-type-theory.sharp-modality.mdᵉ) modal,ᵉ i.e.ᵉ ifᵉ theᵉ sharpᵉ unitᵉ isᵉ anᵉ
[equivalence](foundation-core.equivalences.mdᵉ) atᵉ thatᵉ type.ᵉ

Weᵉ postulate thatᵉ codiscreteᵉ typesᵉ areᵉ closedᵉ underᵉ

-ᵉ theᵉ formationᵉ ofᵉ identityᵉ typesᵉ
-ᵉ theᵉ formationᵉ ofᵉ dependentᵉ functionᵉ typesᵉ
-ᵉ theᵉ formationᵉ ofᵉ theᵉ subuniverseᵉ ofᵉ codiscreteᵉ types.ᵉ

Pleaseᵉ noteᵉ thatᵉ thereᵉ isᵉ someᵉ redundancyᵉ betweenᵉ theᵉ axiomsᵉ thatᵉ areᵉ assumedᵉ
hereᵉ andᵉ in theᵉ filesᵉ onᵉ
[theᵉ flat-sharpᵉ adjunction](modal-type-theory.flat-sharp-adjunction.md),ᵉ andᵉ theᵉ
fileᵉ onᵉ theᵉ [sharpᵉ modality](modal-type-theory.sharp-modality.md),ᵉ andᵉ theyᵉ mayᵉ
beᵉ subjectᵉ to changeᵉ in theᵉ future.ᵉ

## Definition

```agda
is-sharp-codiscreteᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → UUᵉ lᵉ
is-sharp-codiscreteᵉ {lᵉ} Aᵉ = is-equivᵉ (unit-sharpᵉ {lᵉ} {Aᵉ})

is-sharp-codiscrete-familyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-sharp-codiscrete-familyᵉ {Aᵉ = Aᵉ} Bᵉ = (xᵉ : Aᵉ) → is-sharp-codiscreteᵉ (Bᵉ xᵉ)

Sharp-Codiscreteᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Sharp-Codiscreteᵉ lᵉ = Σᵉ (UUᵉ lᵉ) (is-sharp-codiscreteᵉ)
```

## Postulates

### The identity types of `♯` are codiscrete

```agda
postulate
  is-sharp-codiscrete-Id-sharpᵉ :
    {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ : ♯ᵉ Aᵉ) → is-sharp-codiscreteᵉ (xᵉ ＝ᵉ yᵉ)

is-sharp-codiscrete-Idᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ : Aᵉ) →
  is-sharp-codiscreteᵉ Aᵉ → is-sharp-codiscreteᵉ (xᵉ ＝ᵉ yᵉ)
is-sharp-codiscrete-Idᵉ xᵉ yᵉ is-sharp-codiscrete-Aᵉ =
  map-tr-equivᵉ
    ( is-sharp-codiscreteᵉ)
    ( inv-equiv-ap-is-embᵉ (is-emb-is-equivᵉ is-sharp-codiscrete-Aᵉ))
    ( is-sharp-codiscrete-Id-sharpᵉ (unit-sharpᵉ xᵉ) (unit-sharpᵉ yᵉ))
```

### A `Π`-type is codiscrete if its codomain is

```agda
postulate
  is-sharp-codiscrete-Πᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    ((xᵉ : Aᵉ) → is-sharp-codiscreteᵉ (Bᵉ xᵉ)) →
    is-sharp-codiscreteᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)
```

### The universe of codiscrete types is codiscrete

```agda
postulate
  is-sharp-codiscrete-Sharp-Codiscreteᵉ :
    (lᵉ : Level) → is-sharp-codiscreteᵉ (Sharp-Codiscreteᵉ lᵉ)
```

## Properties

### Being codiscrete is a property

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  is-sharp-codiscrete-Propᵉ : Propᵉ lᵉ
  is-sharp-codiscrete-Propᵉ = is-equiv-Propᵉ (unit-sharpᵉ {lᵉ} {Aᵉ})

  is-property-is-sharp-codiscreteᵉ : is-propᵉ (is-sharp-codiscreteᵉ Aᵉ)
  is-property-is-sharp-codiscreteᵉ = is-prop-type-Propᵉ is-sharp-codiscrete-Propᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  is-sharp-codiscrete-family-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-sharp-codiscrete-family-Propᵉ = Π-Propᵉ Aᵉ (is-sharp-codiscrete-Propᵉ ∘ᵉ Bᵉ)

  is-property-is-sharp-codiscrete-familyᵉ :
    is-propᵉ (is-sharp-codiscrete-familyᵉ Bᵉ)
  is-property-is-sharp-codiscrete-familyᵉ =
    is-prop-type-Propᵉ is-sharp-codiscrete-family-Propᵉ
```

### Codiscreteness is a higher modality

```agda
module _
  (lᵉ : Level)
  where

  is-higher-modality-sharpᵉ :
    is-higher-modalityᵉ (sharp-locally-small-operator-modalityᵉ lᵉ) (unit-sharpᵉ)
  pr1ᵉ is-higher-modality-sharpᵉ = induction-principle-sharpᵉ
  pr2ᵉ is-higher-modality-sharpᵉ Xᵉ = is-sharp-codiscrete-Id-sharpᵉ

  sharp-higher-modalityᵉ : higher-modalityᵉ lᵉ lᵉ
  pr1ᵉ sharp-higher-modalityᵉ = sharp-locally-small-operator-modalityᵉ lᵉ
  pr1ᵉ (pr2ᵉ sharp-higher-modalityᵉ) = unit-sharpᵉ
  pr2ᵉ (pr2ᵉ sharp-higher-modalityᵉ) = is-higher-modality-sharpᵉ
```

### Types in the image of `♯` are codiscrete

```agda
is-sharp-codiscrete-sharpᵉ : {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-sharp-codiscreteᵉ (♯ᵉ Xᵉ)
is-sharp-codiscrete-sharpᵉ {lᵉ} =
  is-modal-operator-type-higher-modalityᵉ (sharp-higher-modalityᵉ lᵉ)
```

## See also

-ᵉ [Flatᵉ discreteᵉ types](modal-type-theory.flat-discrete-types.mdᵉ) forᵉ theᵉ dualᵉ
  notion.ᵉ