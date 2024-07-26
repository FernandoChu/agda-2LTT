# Lifts of families of elements

```agda
module orthogonal-factorization-systems.lifts-families-of-elementsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.precomposition-type-familiesᵉ
open import foundation.transport-along-homotopiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Considerᵉ aᵉ typeᵉ familyᵉ

```text
  Bᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → 𝒰ᵉ
```

andᵉ aᵉ familyᵉ ofᵉ elementsᵉ `aᵉ : (iᵉ : Iᵉ) → Aᵉ i`.ᵉ

Aᵉ
{{#conceptᵉ "dependentᵉ lift"ᵉ Disambiguation="familyᵉ ofᵉ elements"ᵉ Agda=dependent-lift-family-of-elementsᵉ}}
ofᵉ theᵉ familyᵉ ofᵉ elementsᵉ `a`ᵉ to theᵉ typeᵉ familyᵉ `B`ᵉ isᵉ aᵉ familyᵉ ofᵉ elementsᵉ

```text
  (iᵉ : Iᵉ) → Bᵉ iᵉ (aᵉ i).ᵉ
```

Anᵉ importantᵉ specialᵉ caseᵉ occursᵉ whenᵉ `aᵉ : Iᵉ → A`ᵉ isᵉ aᵉ familyᵉ ofᵉ elementsᵉ ofᵉ aᵉ
fixedᵉ typeᵉ `A`,ᵉ andᵉ `B`ᵉ isᵉ aᵉ typeᵉ familyᵉ overᵉ `A`.ᵉ Inᵉ thisᵉ case,ᵉ aᵉ
{{#conceptᵉ "lift"ᵉ Disambiguation="familyᵉ ofᵉ elements"ᵉ Agda=lift-family-of-elementsᵉ}}
ofᵉ theᵉ familyᵉ ofᵉ elementsᵉ `a`ᵉ isᵉ aᵉ familyᵉ ofᵉ elementsᵉ

```text
  (iᵉ : Iᵉ) → Bᵉ (aᵉ i).ᵉ
```

Aᵉ familyᵉ ofᵉ elementsᵉ equippedᵉ with aᵉ dependentᵉ liftᵉ isᵉ aᵉ
{{#conceptᵉ "dependentᵉ liftedᵉ familyᵉ ofᵉ elements"}},ᵉ andᵉ analogouslyᵉ aᵉ familyᵉ ofᵉ
elementsᵉ equippedᵉ with aᵉ liftᵉ isᵉ aᵉ {{#conceptᵉ "liftedᵉ familyᵉ ofᵉ elements"}}.ᵉ

Toᵉ seeᵉ howᵉ theseᵉ familiesᵉ relateᵉ to
[liftsᵉ ofᵉ maps](orthogonal-factorization-systems.lifts-of-maps.md),ᵉ considerᵉ theᵉ
liftingᵉ diagramᵉ

```text
      Σᵉ (xᵉ : Aᵉ) (Bᵉ xᵉ)
            |
            | pr1ᵉ
            |
            ∨ᵉ
  Iᵉ ------>ᵉ Aᵉ         .ᵉ
       aᵉ
```

Thenᵉ aᵉ liftᵉ ofᵉ theᵉ mapᵉ `a`ᵉ againstᵉ `pr1`ᵉ isᵉ aᵉ mapᵉ `bᵉ : Iᵉ → Σᵉ Aᵉ B`,ᵉ suchᵉ thatᵉ theᵉ
triangleᵉ commutes.ᵉ Invokingᵉ theᵉ
[typeᵉ theoreticᵉ principleᵉ ofᵉ choice](foundation.type-theoretic-principle-of-choice.md),ᵉ
weᵉ canᵉ showᵉ thatᵉ thisᵉ typeᵉ isᵉ equivalentᵉ to theᵉ typeᵉ ofᵉ familiesᵉ ofᵉ elementsᵉ
`(iᵉ : Iᵉ) → Bᵉ (aᵉ i)`ᵉ:

```text
  Σᵉ (bᵉ : Iᵉ → Σᵉ Aᵉ Bᵉ) ((iᵉ : Iᵉ) → aᵉ iᵉ ＝ᵉ pr1ᵉ (bᵉ iᵉ))
    ≃ᵉ (iᵉ : Iᵉ) → Σᵉ ((xᵉ ,ᵉ bᵉ) : Σᵉ Aᵉ Bᵉ) (aᵉ iᵉ ＝ᵉ xᵉ)
    ≃ᵉ (iᵉ : Iᵉ) → Σᵉ (xᵉ : Aᵉ) (aᵉ iᵉ ＝ᵉ xᵉ ×ᵉ Bᵉ xᵉ)
    ≃ᵉ (iᵉ : Iᵉ) → Bᵉ (aᵉ iᵉ) .ᵉ
```

Theᵉ firstᵉ equivalenceᵉ isᵉ theᵉ principleᵉ ofᵉ choice,ᵉ theᵉ secondᵉ isᵉ associativityᵉ ofᵉ
dependentᵉ pairᵉ types,ᵉ andᵉ theᵉ thirdᵉ isᵉ theᵉ leftᵉ unitᵉ lawᵉ ofᵉ dependentᵉ pairᵉ
types,ᵉ sinceᵉ `Σᵉ (xᵉ : Aᵉ) (aᵉ iᵉ ＝ᵉ x)`ᵉ isᵉ
[contractible](foundation.contractible-types.md).ᵉ

## Definitions

### Dependent lifts of families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} (Bᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → UUᵉ l3ᵉ)
  (aᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ)
  where

  dependent-lift-family-of-elementsᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  dependent-lift-family-of-elementsᵉ = (iᵉ : Iᵉ) → Bᵉ iᵉ (aᵉ iᵉ)
```

### Lifts of families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (Bᵉ : Aᵉ → UUᵉ l3ᵉ) (aᵉ : Iᵉ → Aᵉ)
  where

  lift-family-of-elementsᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  lift-family-of-elementsᵉ = dependent-lift-family-of-elementsᵉ (λ _ → Bᵉ) aᵉ
```

### Dependent lifted families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (Aᵉ : Iᵉ → UUᵉ l2ᵉ) (Bᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → UUᵉ l3ᵉ)
  where

  dependent-lifted-family-of-elementsᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  dependent-lifted-family-of-elementsᵉ =
    Σᵉ ( (iᵉ : Iᵉ) → Aᵉ iᵉ)
      ( dependent-lift-family-of-elementsᵉ Bᵉ)
```

### Lifted families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) {Aᵉ : UUᵉ l2ᵉ} (Bᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  lifted-family-of-elementsᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  lifted-family-of-elementsᵉ =
    dependent-lifted-family-of-elementsᵉ (λ (ᵉ_ : Iᵉ) → Aᵉ) (λ _ → Bᵉ)
```

### Dependent lifts of binary families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → UUᵉ l3ᵉ}
  (Cᵉ : (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) → Bᵉ iᵉ xᵉ → UUᵉ l4ᵉ) (aᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ)
  where

  dependent-lift-binary-family-of-elementsᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  dependent-lift-binary-family-of-elementsᵉ =
    dependent-lift-family-of-elementsᵉ (λ iᵉ xᵉ → (yᵉ : Bᵉ iᵉ xᵉ) → Cᵉ iᵉ xᵉ yᵉ) aᵉ
```

### Lifts of binary families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : Aᵉ → UUᵉ l3ᵉ}
  {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l4ᵉ} (aᵉ : Iᵉ → Aᵉ)
  where

  lift-binary-family-of-elementsᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  lift-binary-family-of-elementsᵉ =
    dependent-lift-binary-family-of-elementsᵉ (λ _ → Cᵉ) aᵉ
```

## Properties

### Transport in lifts of families of elements along homotopies of precompositions

Givenᵉ aᵉ mapᵉ `aᵉ : Iᵉ → A`,ᵉ andᵉ aᵉ homotopyᵉ `Hᵉ : fᵉ ~ᵉ g`,ᵉ where `f,ᵉ gᵉ : Jᵉ → I`,ᵉ weᵉ
knowᵉ thatᵉ thereᵉ isᵉ anᵉ identificationᵉ `aᵉ ∘ᵉ fᵉ ＝ᵉ aᵉ ∘ᵉ g`.ᵉ Transportingᵉ alongᵉ thisᵉ
identificationᵉ in theᵉ typeᵉ ofᵉ liftsᵉ ofᵉ familiesᵉ ofᵉ elementsᵉ intoᵉ aᵉ typeᵉ familyᵉ
`Bᵉ : Aᵉ → 𝓤`,ᵉ weᵉ getᵉ aᵉ mapᵉ

```text
  ((jᵉ : Jᵉ) → Bᵉ (aᵉ (fᵉ jᵉ))) → ((jᵉ : Jᵉ) → Bᵉ (aᵉ (gᵉ jᵉ))) .ᵉ
```

Weᵉ showᵉ thatᵉ thisᵉ mapᵉ isᵉ homotopicᵉ to transportingᵉ alongᵉ `H`ᵉ in theᵉ typeᵉ familyᵉ
`Bᵉ ∘ᵉ aᵉ : Iᵉ → 𝓤`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (Bᵉ : Aᵉ → UUᵉ l3ᵉ) (aᵉ : Iᵉ → Aᵉ)
  {Jᵉ : UUᵉ l4ᵉ} {fᵉ : Jᵉ → Iᵉ}
  where

  statement-tr-lift-family-of-elements-precompᵉ :
    {gᵉ : Jᵉ → Iᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) → UUᵉ (l3ᵉ ⊔ l4ᵉ)
  statement-tr-lift-family-of-elements-precompᵉ Hᵉ =
    trᵉ (lift-family-of-elementsᵉ Bᵉ) (htpy-precompᵉ Hᵉ Aᵉ aᵉ) ~ᵉ
    tr-htpyᵉ (λ _ → precomp-familyᵉ aᵉ Bᵉ) Hᵉ

  tr-lift-family-of-elements-precomp-refl-htpyᵉ :
    statement-tr-lift-family-of-elements-precompᵉ refl-htpyᵉ
  tr-lift-family-of-elements-precomp-refl-htpyᵉ bᵉ =
    apᵉ
      ( λ pᵉ → trᵉ (lift-family-of-elementsᵉ Bᵉ) pᵉ bᵉ)
      ( compute-htpy-precomp-refl-htpyᵉ fᵉ Aᵉ aᵉ)

  abstract
    tr-lift-family-of-elements-precompᵉ :
      {gᵉ : Jᵉ → Iᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) → statement-tr-lift-family-of-elements-precompᵉ Hᵉ
    tr-lift-family-of-elements-precompᵉ =
      ind-htpyᵉ fᵉ
        ( λ gᵉ → statement-tr-lift-family-of-elements-precompᵉ)
        ( tr-lift-family-of-elements-precomp-refl-htpyᵉ)

    compute-tr-lift-family-of-elements-precompᵉ :
      tr-lift-family-of-elements-precompᵉ refl-htpyᵉ ＝ᵉ
      tr-lift-family-of-elements-precomp-refl-htpyᵉ
    compute-tr-lift-family-of-elements-precompᵉ =
      compute-ind-htpyᵉ fᵉ
        ( λ gᵉ → statement-tr-lift-family-of-elements-precompᵉ)
        ( tr-lift-family-of-elements-precomp-refl-htpyᵉ)
```

## See also

-ᵉ [Doubleᵉ liftsᵉ ofᵉ familiesᵉ ofᵉ elements](orthogonal-factorization-systems.double-lifts-families-of-elements.mdᵉ)
-ᵉ [Liftsᵉ ofᵉ maps](orthogonal-factorization-systems.lifts-of-maps.mdᵉ)