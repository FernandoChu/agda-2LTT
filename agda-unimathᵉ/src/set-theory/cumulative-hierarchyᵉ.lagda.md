# Cumulative hierarchy

```agda
module set-theory.cumulative-hierarchyᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.booleansᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.constant-type-familiesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negationᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.truncated-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ cumulativeᵉ hierarchyᵉ isᵉ aᵉ modelᵉ ofᵉ setᵉ theory.ᵉ Insteadᵉ ofᵉ introducingᵉ itᵉ asᵉ
aᵉ HIT,ᵉ asᵉ in theᵉ HoTTᵉ Bookᵉ Sectionᵉ 10.4,ᵉ weᵉ introduceᵉ itsᵉ inductionᵉ principle,ᵉ
followingᵉ Referenceᵉ 2 below.ᵉ

## Definitions

### Smaller image

```agda
has-smaller-imageᵉ :
  { l1ᵉ l2ᵉ l3ᵉ : Level} →
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} →
  (Aᵉ → Cᵉ) → (Bᵉ → Cᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
has-smaller-imageᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Aᵉ} {Bᵉ} {Cᵉ} fᵉ gᵉ =
  (aᵉ : Aᵉ) → exists-structureᵉ Bᵉ (λ bᵉ → gᵉ bᵉ ＝ᵉ fᵉ aᵉ)

has-same-imageᵉ :
  { l1ᵉ l2ᵉ l3ᵉ : Level} →
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} →
  (Aᵉ → Cᵉ) → (Bᵉ → Cᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
has-same-imageᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Aᵉ} {Bᵉ} {Cᵉ} fᵉ gᵉ =
  has-smaller-imageᵉ fᵉ gᵉ ×ᵉ
    has-smaller-imageᵉ gᵉ fᵉ
```

### Pseudo cumulative hierarchy

Aᵉ typeᵉ isᵉ aᵉ pseudoᵉ cumulativeᵉ hierarchyᵉ ifᵉ itᵉ hasᵉ theᵉ structureᵉ ofᵉ aᵉ cumulativeᵉ
hierarchy,ᵉ butᵉ notᵉ necessarilyᵉ itsᵉ inductionᵉ principle.ᵉ

```agda
has-cumulative-hierarchy-structureᵉ :
  {lᵉ : Level} → (Vᵉ : UUᵉ (lsuc lᵉ)) → UUᵉ (lsuc lᵉ)
has-cumulative-hierarchy-structureᵉ {lᵉ} Vᵉ =
  ( is-setᵉ Vᵉ) ×ᵉ
    ( Σᵉ ({Aᵉ : UUᵉ lᵉ} → (Aᵉ → Vᵉ) → Vᵉ)
      ( λ V-setᵉ →
        ( {Aᵉ Bᵉ : UUᵉ lᵉ} (fᵉ : Aᵉ → Vᵉ) (gᵉ : Bᵉ → Vᵉ) →
          ( has-same-imageᵉ fᵉ gᵉ) → V-setᵉ fᵉ ＝ᵉ V-setᵉ gᵉ)))

pseudo-cumulative-hierarchyᵉ : (lᵉ : Level) → UUᵉ (lsuc (lsuc lᵉ))
pseudo-cumulative-hierarchyᵉ (lᵉ) =
  Σᵉ (UUᵉ (lsuc lᵉ)) has-cumulative-hierarchy-structureᵉ

module _
  {lᵉ : Level} (Vᵉ : pseudo-cumulative-hierarchyᵉ lᵉ)
  where

  type-pseudo-cumulative-hierarchyᵉ : UUᵉ (lsuc lᵉ)
  type-pseudo-cumulative-hierarchyᵉ = pr1ᵉ Vᵉ

  is-set-pseudo-cumulative-hierarchyᵉ :
    is-setᵉ type-pseudo-cumulative-hierarchyᵉ
  is-set-pseudo-cumulative-hierarchyᵉ = pr1ᵉ (pr2ᵉ Vᵉ)

  set-pseudo-cumulative-hierarchyᵉ :
    { Aᵉ : UUᵉ lᵉ} →
    ( Aᵉ → type-pseudo-cumulative-hierarchyᵉ) →
    type-pseudo-cumulative-hierarchyᵉ
  set-pseudo-cumulative-hierarchyᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Vᵉ))

  set-ext-pseudo-cumulative-hierarchyᵉ :
    { Aᵉ Bᵉ : UUᵉ lᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ)
    ( gᵉ : Bᵉ → type-pseudo-cumulative-hierarchyᵉ) →
    ( has-same-imageᵉ fᵉ gᵉ) →
    set-pseudo-cumulative-hierarchyᵉ fᵉ ＝ᵉ set-pseudo-cumulative-hierarchyᵉ gᵉ
  set-ext-pseudo-cumulative-hierarchyᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ Vᵉ))
```

### The induction principle and computation rule of the cumulative hierarchy

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Vᵉ : pseudo-cumulative-hierarchyᵉ l1ᵉ)
  where
  induction-principle-cumulative-hierarchyᵉ : UUᵉ (lsuc (l1ᵉ ⊔ l2ᵉ))
  induction-principle-cumulative-hierarchyᵉ =
    ( Pᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ → UUᵉ l2ᵉ) →
    ( (xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) → is-setᵉ (Pᵉ xᵉ)) →
    ( ρᵉ :
      { Aᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( (aᵉ : Aᵉ) → Pᵉ (fᵉ aᵉ)) → Pᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ)) →
    ( { Aᵉ Bᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( gᵉ : Bᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
      ( eᵉ : has-same-imageᵉ fᵉ gᵉ)
      ( IH₁ᵉ : (aᵉ : Aᵉ) → Pᵉ (fᵉ aᵉ))
      ( IH₂ᵉ : (bᵉ : Bᵉ) → Pᵉ (gᵉ bᵉ)) →
      ( ( aᵉ : Aᵉ) → exists-structureᵉ Bᵉ (λ bᵉ → Σᵉ (fᵉ aᵉ ＝ᵉ gᵉ bᵉ)
        ( λ pᵉ → trᵉ Pᵉ pᵉ (IH₁ᵉ aᵉ) ＝ᵉ IH₂ᵉ bᵉ))) →
      ( ( bᵉ : Bᵉ) → exists-structureᵉ Aᵉ (λ aᵉ →
        Σᵉ (gᵉ bᵉ ＝ᵉ fᵉ aᵉ) (λ pᵉ → trᵉ Pᵉ pᵉ (IH₂ᵉ bᵉ) ＝ᵉ IH₁ᵉ aᵉ))) →
      trᵉ Pᵉ (set-ext-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ gᵉ eᵉ) (ρᵉ fᵉ IH₁ᵉ) ＝ᵉ ρᵉ gᵉ IH₂ᵉ) →
    (xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) → Pᵉ xᵉ

  compute-induction-principle-cumulative-hierarchyᵉ :
    induction-principle-cumulative-hierarchyᵉ → UUᵉ (lsuc (l1ᵉ ⊔ l2ᵉ))
  compute-induction-principle-cumulative-hierarchyᵉ IPᵉ =
    ( Pᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ → UUᵉ l2ᵉ) →
    ( σᵉ : (xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) → is-setᵉ (Pᵉ xᵉ)) →
    ( ρᵉ :
      { Aᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( (aᵉ : Aᵉ) → Pᵉ (fᵉ aᵉ)) → Pᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ)) →
    ( τᵉ :
      { Aᵉ Bᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( gᵉ : Bᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
      ( eᵉ : has-same-imageᵉ fᵉ gᵉ)
      ( IH₁ᵉ : (aᵉ : Aᵉ) → Pᵉ (fᵉ aᵉ))
      ( IH₂ᵉ : (bᵉ : Bᵉ) → Pᵉ (gᵉ bᵉ)) →
      ( (aᵉ : Aᵉ) → exists-structureᵉ Bᵉ (λ bᵉ → Σᵉ (fᵉ aᵉ ＝ᵉ gᵉ bᵉ)
        ( λ pᵉ → trᵉ Pᵉ pᵉ (IH₁ᵉ aᵉ) ＝ᵉ IH₂ᵉ bᵉ))) →
      ( (bᵉ : Bᵉ) → exists-structureᵉ Aᵉ (λ aᵉ → Σᵉ (gᵉ bᵉ ＝ᵉ fᵉ aᵉ)
        (λ pᵉ → trᵉ Pᵉ pᵉ (IH₂ᵉ bᵉ) ＝ᵉ IH₁ᵉ aᵉ))) →
      trᵉ Pᵉ (set-ext-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ gᵉ eᵉ) (ρᵉ fᵉ IH₁ᵉ) ＝ᵉ ρᵉ gᵉ IH₂ᵉ) →
    { Aᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
    ( IHᵉ : (aᵉ : Aᵉ) → Pᵉ (fᵉ aᵉ)) →
    IPᵉ Pᵉ σᵉ ρᵉ τᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ) ＝ᵉ ρᵉ fᵉ IHᵉ
```

## Examples

```agda
module _
  {l1ᵉ : Level} (Vᵉ : pseudo-cumulative-hierarchyᵉ l1ᵉ)
  (induction-principle-cumulative-hierarchy-Vᵉ :
    (l2ᵉ : Level) → induction-principle-cumulative-hierarchyᵉ l2ᵉ Vᵉ)
  (compute-induction-principle-cumulative-hierarchy-Vᵉ :
    (l2ᵉ : Level) → compute-induction-principle-cumulative-hierarchyᵉ l2ᵉ Vᵉ
      (induction-principle-cumulative-hierarchy-Vᵉ l2ᵉ))
  where
```

### The empty set

```agda
  empty-set-cumulative-hierarchyᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ
  empty-set-cumulative-hierarchyᵉ =
    set-pseudo-cumulative-hierarchyᵉ Vᵉ (raise-ex-falsoᵉ l1ᵉ)
```

### The set containing only the empty set

```agda
  set-empty-set-cumulative-hierarchyᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ
  set-empty-set-cumulative-hierarchyᵉ =
    set-pseudo-cumulative-hierarchyᵉ Vᵉ {raise-unitᵉ l1ᵉ}
      ( λ _ → empty-set-cumulative-hierarchyᵉ)
```

## Properties

### Every element of the cumulative hierarchy is given by a function into the cumulative hierarchy

```agda
  underlying-function-cumulative-hierarchyᵉ :
    (vᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    exists-structureᵉ ( UUᵉ l1ᵉ)
      ( λ Aᵉ →
        Σᵉ ( Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
          ( λ fᵉ → set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ ＝ᵉ vᵉ))
  underlying-function-cumulative-hierarchyᵉ =
    induction-principle-cumulative-hierarchy-Vᵉ
      ( lsuc l1ᵉ) _
      ( λ _ → is-trunc-type-Truncated-Typeᵉ (set-trunc-Propᵉ _))
      ( λ {Aᵉ} fᵉ Hᵉ → unit-trunc-Propᵉ (pairᵉ Aᵉ (pairᵉ fᵉ reflᵉ)))
      ( λ fᵉ gᵉ eᵉ IH₁ᵉ IH₂ᵉ hIH₁ᵉ hIH₂ᵉ → eq-is-propᵉ is-prop-type-trunc-Propᵉ)
```

### The induction principle simplified for families of propositions

```agda
  prop-ind-principle-cumulative-hierarchyᵉ :
    { l2ᵉ : Level}
    ( Pᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ → UUᵉ l2ᵉ) →
    ( ( xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) → is-propᵉ (Pᵉ xᵉ)) →
    ( { Aᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( (aᵉ : Aᵉ) → Pᵉ (fᵉ aᵉ)) →
      ( Pᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ))) →
    ( xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) → Pᵉ xᵉ
  prop-ind-principle-cumulative-hierarchyᵉ {l2ᵉ} Pᵉ σᵉ ρᵉ =
    induction-principle-cumulative-hierarchy-Vᵉ l2ᵉ Pᵉ
      ( λ xᵉ → is-set-is-propᵉ (σᵉ xᵉ)) ρᵉ
      ( λ _ gᵉ _ _ _ _ _ → eq-is-propᵉ (σᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ gᵉ)))

  compute-prop-ind-principle-cumulative-hierarchyᵉ :
    { l2ᵉ : Level}
    ( Pᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ → UUᵉ l2ᵉ) →
    ( σᵉ : ( xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) → is-propᵉ (Pᵉ xᵉ)) →
    ( ρᵉ :
      { Aᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( (aᵉ : Aᵉ) → Pᵉ (fᵉ aᵉ)) →
      ( Pᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ))) →
    { Aᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
    ( IHᵉ : (aᵉ : Aᵉ) → Pᵉ (fᵉ aᵉ)) →
    prop-ind-principle-cumulative-hierarchyᵉ
      Pᵉ σᵉ ρᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ) ＝ᵉ ρᵉ fᵉ IHᵉ
  compute-prop-ind-principle-cumulative-hierarchyᵉ {l2ᵉ} Pᵉ σᵉ ρᵉ =
    compute-induction-principle-cumulative-hierarchy-Vᵉ l2ᵉ Pᵉ
      ( λ xᵉ → is-set-is-propᵉ (σᵉ xᵉ)) ρᵉ
      ( λ _ gᵉ _ _ _ _ _ → eq-is-propᵉ (σᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ gᵉ)))
```

### The recursion principle and its computation rule for the cumulative hierarchy

```agda
  recursion-principle-cumulative-hierarchyᵉ :
    { l2ᵉ : Level}
    ( Xᵉ : UUᵉ l2ᵉ) (σᵉ : is-setᵉ Xᵉ)
    ( ρᵉ : {Aᵉ : UUᵉ l1ᵉ} → (Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) → (Aᵉ → Xᵉ) → Xᵉ)
    ( τᵉ :
      { Aᵉ Bᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
      ( gᵉ : Bᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
      ( eᵉ : has-same-imageᵉ fᵉ gᵉ)
      ( IH₁ᵉ : Aᵉ → Xᵉ)
      ( IH₂ᵉ : Bᵉ → Xᵉ) →
      ( (aᵉ : Aᵉ) → exists-structureᵉ Bᵉ (λ bᵉ → (fᵉ aᵉ ＝ᵉ gᵉ bᵉ) ×ᵉ (IH₁ᵉ aᵉ ＝ᵉ IH₂ᵉ bᵉ))) →
      ( (bᵉ : Bᵉ) → exists-structureᵉ Aᵉ (λ aᵉ → (gᵉ bᵉ ＝ᵉ fᵉ aᵉ) ×ᵉ (IH₂ᵉ bᵉ ＝ᵉ IH₁ᵉ aᵉ))) →
      ρᵉ fᵉ IH₁ᵉ ＝ᵉ ρᵉ gᵉ IH₂ᵉ) →
    type-pseudo-cumulative-hierarchyᵉ Vᵉ → Xᵉ
  recursion-principle-cumulative-hierarchyᵉ {l2ᵉ} Xᵉ σᵉ ρᵉ τᵉ =
    induction-principle-cumulative-hierarchy-Vᵉ l2ᵉ (λ _ → Xᵉ) (λ _ → σᵉ) ρᵉ τ'ᵉ
    where
    τ'ᵉ :
      { Aᵉ Bᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → pr1ᵉ Vᵉ) (gᵉ : Bᵉ → pr1ᵉ Vᵉ)
      ( eᵉ : has-same-imageᵉ fᵉ gᵉ)
      ( IH₁ᵉ : (aᵉ : Aᵉ) → Xᵉ) (IH₂ᵉ : (bᵉ : Bᵉ) → Xᵉ) →
      ( (aᵉ : Aᵉ) → exists-structureᵉ Bᵉ (λ bᵉ → Σᵉ (fᵉ aᵉ ＝ᵉ gᵉ bᵉ)
        (λ pᵉ → trᵉ (λ _ → Xᵉ) pᵉ (IH₁ᵉ aᵉ) ＝ᵉ IH₂ᵉ bᵉ))) →
      ( (bᵉ : Bᵉ) → exists-structureᵉ Aᵉ (λ aᵉ → Σᵉ (gᵉ bᵉ ＝ᵉ fᵉ aᵉ)
        (λ pᵉ → trᵉ (λ _ → Xᵉ) pᵉ (IH₂ᵉ bᵉ) ＝ᵉ IH₁ᵉ aᵉ))) →
      trᵉ (λ _ → Xᵉ) (pr2ᵉ (pr2ᵉ (pr2ᵉ Vᵉ)) fᵉ gᵉ eᵉ) (ρᵉ fᵉ IH₁ᵉ) ＝ᵉ ρᵉ gᵉ IH₂ᵉ
    τ'ᵉ {Aᵉ} {Bᵉ} fᵉ gᵉ eᵉ IH₁ᵉ IH₂ᵉ hIH₁ᵉ hIH₂ᵉ =
      equational-reasoningᵉ
        trᵉ (λ _ → Xᵉ) (pr2ᵉ (pr2ᵉ (pr2ᵉ Vᵉ)) fᵉ gᵉ eᵉ) (ρᵉ fᵉ IH₁ᵉ)
        ＝ᵉ ρᵉ fᵉ IH₁ᵉ
          byᵉ tr-constant-type-familyᵉ path-f-gᵉ (ρᵉ fᵉ IH₁ᵉ)
        ＝ᵉ ρᵉ gᵉ IH₂ᵉ
          byᵉ τᵉ fᵉ gᵉ eᵉ IH₁ᵉ IH₂ᵉ hIH₁'ᵉ hIH₂'ᵉ
      where
      path-f-gᵉ :
        set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ
          ＝ᵉ set-pseudo-cumulative-hierarchyᵉ Vᵉ gᵉ
      path-f-gᵉ = set-ext-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ gᵉ eᵉ
      hIH₁'ᵉ :
        (aᵉ : Aᵉ) →
        exists-structureᵉ Bᵉ (λ bᵉ → Σᵉ (fᵉ aᵉ ＝ᵉ gᵉ bᵉ) (λ _ → IH₁ᵉ aᵉ ＝ᵉ IH₂ᵉ bᵉ))
      hIH₁'ᵉ aᵉ =
        map-trunc-Propᵉ
          ( λ (bᵉ ,ᵉ pᵉ ,ᵉ qᵉ) →
            ( bᵉ ,ᵉ pᵉ ,ᵉ (invᵉ (tr-constant-type-familyᵉ pᵉ _) ∙ᵉ qᵉ)))
          ( hIH₁ᵉ aᵉ)
      hIH₂'ᵉ :
        (bᵉ : Bᵉ) →
        exists-structureᵉ Aᵉ (λ aᵉ → Σᵉ (gᵉ bᵉ ＝ᵉ fᵉ aᵉ) (λ _ → IH₂ᵉ bᵉ ＝ᵉ IH₁ᵉ aᵉ))
      hIH₂'ᵉ bᵉ =
        map-trunc-Propᵉ
          ( λ (aᵉ ,ᵉ pᵉ ,ᵉ qᵉ) →
            ( aᵉ ,ᵉ pᵉ ,ᵉ (invᵉ (tr-constant-type-familyᵉ pᵉ _) ∙ᵉ qᵉ)))
          ( hIH₂ᵉ bᵉ)

  compute-recursion-principle-cumulative-hierarchyᵉ :
    { l2ᵉ : Level} ( Xᵉ : UUᵉ l2ᵉ) (σᵉ : is-setᵉ Xᵉ)
    ( ρᵉ : {Aᵉ : UUᵉ l1ᵉ} → (Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) → (Aᵉ → Xᵉ) → Xᵉ)
    ( τᵉ :
      { Aᵉ Bᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
      ( gᵉ : Bᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
      ( eᵉ : has-same-imageᵉ fᵉ gᵉ)
      ( IH₁ᵉ : Aᵉ → Xᵉ)
      ( IH₂ᵉ : Bᵉ → Xᵉ) →
      ( ( aᵉ : Aᵉ) → exists-structureᵉ Bᵉ (λ bᵉ → (fᵉ aᵉ ＝ᵉ gᵉ bᵉ) ×ᵉ (IH₁ᵉ aᵉ ＝ᵉ IH₂ᵉ bᵉ))) →
      ( ( bᵉ : Bᵉ) → exists-structureᵉ Aᵉ (λ aᵉ → (gᵉ bᵉ ＝ᵉ fᵉ aᵉ) ×ᵉ (IH₂ᵉ bᵉ ＝ᵉ IH₁ᵉ aᵉ))) →
      ρᵉ fᵉ IH₁ᵉ ＝ᵉ ρᵉ gᵉ IH₂ᵉ) →
    {Aᵉ : UUᵉ l1ᵉ} → (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) → (IHᵉ : Aᵉ → Xᵉ) →
    recursion-principle-cumulative-hierarchyᵉ Xᵉ σᵉ ρᵉ τᵉ
      ( set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ) ＝ᵉ ρᵉ fᵉ IHᵉ
  compute-recursion-principle-cumulative-hierarchyᵉ {l2ᵉ} Xᵉ σᵉ ρᵉ τᵉ =
    compute-induction-principle-cumulative-hierarchy-Vᵉ
      l2ᵉ (λ _ → Xᵉ) (λ _ → σᵉ) ρᵉ τ'ᵉ
    where
    τ'ᵉ :
      { Aᵉ Bᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → pr1ᵉ Vᵉ) (gᵉ : Bᵉ → pr1ᵉ Vᵉ)
      ( eᵉ : has-same-imageᵉ fᵉ gᵉ)
      ( IH₁ᵉ : (aᵉ : Aᵉ) → Xᵉ) (IH₂ᵉ : (bᵉ : Bᵉ) → Xᵉ) →
      ( ( aᵉ : Aᵉ) → exists-structureᵉ Bᵉ (λ bᵉ → Σᵉ (fᵉ aᵉ ＝ᵉ gᵉ bᵉ)
        ( λ pᵉ → trᵉ (λ _ → Xᵉ) pᵉ (IH₁ᵉ aᵉ) ＝ᵉ IH₂ᵉ bᵉ))) →
      ( ( bᵉ : Bᵉ) → exists-structureᵉ Aᵉ (λ aᵉ → Σᵉ (gᵉ bᵉ ＝ᵉ fᵉ aᵉ)
        ( λ pᵉ → trᵉ (λ _ → Xᵉ) pᵉ (IH₂ᵉ bᵉ) ＝ᵉ IH₁ᵉ aᵉ))) →
      trᵉ (λ _ → Xᵉ) (pr2ᵉ (pr2ᵉ (pr2ᵉ Vᵉ)) fᵉ gᵉ eᵉ) (ρᵉ fᵉ IH₁ᵉ) ＝ᵉ ρᵉ gᵉ IH₂ᵉ
    τ'ᵉ {Aᵉ} {Bᵉ} fᵉ gᵉ eᵉ IH₁ᵉ IH₂ᵉ hIH₁ᵉ hIH₂ᵉ =
      equational-reasoningᵉ
        trᵉ (λ _ → Xᵉ) (pr2ᵉ (pr2ᵉ (pr2ᵉ Vᵉ)) fᵉ gᵉ eᵉ) (ρᵉ fᵉ IH₁ᵉ)
        ＝ᵉ ρᵉ fᵉ IH₁ᵉ
          byᵉ tr-constant-type-familyᵉ path-f-gᵉ (ρᵉ fᵉ IH₁ᵉ)
        ＝ᵉ ρᵉ gᵉ IH₂ᵉ
          byᵉ τᵉ fᵉ gᵉ eᵉ IH₁ᵉ IH₂ᵉ hIH₁'ᵉ hIH₂'ᵉ
      where
      path-f-gᵉ :
        set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ
          ＝ᵉ set-pseudo-cumulative-hierarchyᵉ Vᵉ gᵉ
      path-f-gᵉ = set-ext-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ gᵉ eᵉ
      hIH₁'ᵉ :
        (aᵉ : Aᵉ) →
        exists-structureᵉ Bᵉ (λ bᵉ → Σᵉ (fᵉ aᵉ ＝ᵉ gᵉ bᵉ) (λ _ → IH₁ᵉ aᵉ ＝ᵉ IH₂ᵉ bᵉ))
      hIH₁'ᵉ aᵉ =
        map-trunc-Propᵉ
          ( λ (bᵉ ,ᵉ pᵉ ,ᵉ qᵉ) →
            ( bᵉ ,ᵉ pᵉ ,ᵉ (invᵉ (tr-constant-type-familyᵉ pᵉ _) ∙ᵉ qᵉ)))
          ( hIH₁ᵉ aᵉ)
      hIH₂'ᵉ :
        (bᵉ : Bᵉ) →
        exists-structureᵉ Aᵉ (λ aᵉ → Σᵉ (gᵉ bᵉ ＝ᵉ fᵉ aᵉ) (λ _ → IH₂ᵉ bᵉ ＝ᵉ IH₁ᵉ aᵉ))
      hIH₂'ᵉ bᵉ =
        map-trunc-Propᵉ
          ( λ (aᵉ ,ᵉ pᵉ ,ᵉ qᵉ) →
            ( aᵉ ,ᵉ pᵉ ,ᵉ (invᵉ (tr-constant-type-familyᵉ pᵉ _) ∙ᵉ qᵉ)))
          ( hIH₂ᵉ bᵉ)
```

Aᵉ simplificationᵉ ofᵉ theᵉ recursionᵉ principle,ᵉ whenᵉ theᵉ codomainᵉ isᵉ `Propᵉ l2`.ᵉ

```agda
  prop-recursion-principle-cumulative-hierarchyᵉ :
    {l2ᵉ : Level}
    ( ρᵉ :
      { Aᵉ : UUᵉ l1ᵉ} → (Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( Aᵉ → Propᵉ l2ᵉ) → Propᵉ l2ᵉ)
    ( τᵉ : {Aᵉ Bᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
      ( gᵉ : Bᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
      ( eᵉ : has-smaller-imageᵉ fᵉ gᵉ)
      ( IH₁ᵉ : Aᵉ → Propᵉ l2ᵉ)
      ( IH₂ᵉ : Bᵉ → Propᵉ l2ᵉ) →
      ( (aᵉ : Aᵉ) → exists-structureᵉ Bᵉ (λ bᵉ → (fᵉ aᵉ ＝ᵉ gᵉ bᵉ) ×ᵉ (IH₁ᵉ aᵉ ＝ᵉ IH₂ᵉ bᵉ))) →
      type-Propᵉ (ρᵉ fᵉ IH₁ᵉ) → type-Propᵉ (ρᵉ gᵉ IH₂ᵉ)) →
    type-pseudo-cumulative-hierarchyᵉ Vᵉ → Propᵉ l2ᵉ
  prop-recursion-principle-cumulative-hierarchyᵉ {l2ᵉ} ρᵉ τᵉ =
    recursion-principle-cumulative-hierarchyᵉ (Propᵉ l2ᵉ)
      is-set-type-Propᵉ ρᵉ τ'ᵉ
    where
    τ'ᵉ :
      { Aᵉ Bᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
      ( gᵉ : Bᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( eᵉ : has-same-imageᵉ fᵉ gᵉ)
      ( IH₁ᵉ : Aᵉ → Propᵉ l2ᵉ) (IH₂ᵉ : Bᵉ → Propᵉ l2ᵉ) →
      ( (aᵉ : Aᵉ) → exists-structureᵉ Bᵉ (λ bᵉ → (fᵉ aᵉ ＝ᵉ gᵉ bᵉ) ×ᵉ (IH₁ᵉ aᵉ ＝ᵉ IH₂ᵉ bᵉ))) →
      ( (bᵉ : Bᵉ) → exists-structureᵉ Aᵉ (λ aᵉ → (gᵉ bᵉ ＝ᵉ fᵉ aᵉ) ×ᵉ (IH₂ᵉ bᵉ ＝ᵉ IH₁ᵉ aᵉ))) →
      ρᵉ fᵉ IH₁ᵉ ＝ᵉ ρᵉ gᵉ IH₂ᵉ
    τ'ᵉ fᵉ gᵉ (e₁ᵉ ,ᵉ e₂ᵉ) IH₁ᵉ IH₂ᵉ hIH₁ᵉ hIH₂ᵉ =
      eq-iffᵉ (τᵉ fᵉ gᵉ e₁ᵉ IH₁ᵉ IH₂ᵉ hIH₁ᵉ) (τᵉ gᵉ fᵉ e₂ᵉ IH₂ᵉ IH₁ᵉ hIH₂ᵉ)

  compute-prop-recursion-principle-cumulative-hierarchyᵉ :
    {l2ᵉ : Level}
    ( ρᵉ :
      { Aᵉ : UUᵉ l1ᵉ} → (Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( Aᵉ → Propᵉ l2ᵉ) → Propᵉ l2ᵉ)
    ( τᵉ :
      { Aᵉ Bᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
      ( gᵉ : Bᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
      ( eᵉ : has-smaller-imageᵉ fᵉ gᵉ)
      ( IH₁ᵉ : Aᵉ → Propᵉ l2ᵉ)
      ( IH₂ᵉ : Bᵉ → Propᵉ l2ᵉ) →
      ( (aᵉ : Aᵉ) → exists-structureᵉ Bᵉ (λ bᵉ → (fᵉ aᵉ ＝ᵉ gᵉ bᵉ) ×ᵉ (IH₁ᵉ aᵉ ＝ᵉ IH₂ᵉ bᵉ))) →
      type-Propᵉ (ρᵉ fᵉ IH₁ᵉ) → type-Propᵉ (ρᵉ gᵉ IH₂ᵉ)) →
    { Aᵉ : UUᵉ l1ᵉ} → (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    ( IHᵉ : Aᵉ → Propᵉ l2ᵉ) →
    prop-recursion-principle-cumulative-hierarchyᵉ ρᵉ τᵉ
      ( set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ) ＝ᵉ ρᵉ fᵉ IHᵉ
  compute-prop-recursion-principle-cumulative-hierarchyᵉ {l2ᵉ} ρᵉ τᵉ =
    compute-recursion-principle-cumulative-hierarchyᵉ (Propᵉ l2ᵉ)
      is-set-type-Propᵉ ρᵉ τ'ᵉ
    where
    τ'ᵉ :
      { Aᵉ Bᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
      ( gᵉ : Bᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( eᵉ : has-same-imageᵉ fᵉ gᵉ)
      ( IH₁ᵉ : Aᵉ → Propᵉ l2ᵉ) (IH₂ᵉ : Bᵉ → Propᵉ l2ᵉ) →
      ( (aᵉ : Aᵉ) → exists-structureᵉ Bᵉ (λ bᵉ → (fᵉ aᵉ ＝ᵉ gᵉ bᵉ) ×ᵉ (IH₁ᵉ aᵉ ＝ᵉ IH₂ᵉ bᵉ))) →
      ( (bᵉ : Bᵉ) → exists-structureᵉ Aᵉ (λ aᵉ → (gᵉ bᵉ ＝ᵉ fᵉ aᵉ) ×ᵉ (IH₂ᵉ bᵉ ＝ᵉ IH₁ᵉ aᵉ))) →
      ρᵉ fᵉ IH₁ᵉ ＝ᵉ ρᵉ gᵉ IH₂ᵉ
    τ'ᵉ fᵉ gᵉ (e₁ᵉ ,ᵉ e₂ᵉ) IH₁ᵉ IH₂ᵉ hIH₁ᵉ hIH₂ᵉ =
      eq-iffᵉ (τᵉ fᵉ gᵉ e₁ᵉ IH₁ᵉ IH₂ᵉ hIH₁ᵉ) (τᵉ gᵉ fᵉ e₂ᵉ IH₂ᵉ IH₁ᵉ hIH₂ᵉ)
```

Anotherᵉ simplificationᵉ ofᵉ theᵉ recursionᵉ principle,ᵉ whenᵉ recursiveᵉ callsᵉ areᵉ notᵉ
needed.ᵉ

```agda
  simple-prop-recursion-principle-cumulative-hierarchyᵉ :
    {l2ᵉ : Level}
    ( ρᵉ : {Aᵉ : UUᵉ l1ᵉ} → (Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) → Propᵉ l2ᵉ)
    ( τᵉ :
      { Aᵉ Bᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
      ( gᵉ : Bᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( eᵉ : has-smaller-imageᵉ fᵉ gᵉ) →
      type-Propᵉ (ρᵉ fᵉ) → type-Propᵉ (ρᵉ gᵉ)) →
    type-pseudo-cumulative-hierarchyᵉ Vᵉ → Propᵉ l2ᵉ
  simple-prop-recursion-principle-cumulative-hierarchyᵉ {l2ᵉ} ρᵉ τᵉ =
    prop-recursion-principle-cumulative-hierarchyᵉ
      ( λ fᵉ _ → ρᵉ fᵉ) (λ fᵉ gᵉ eᵉ _ _ _ → τᵉ fᵉ gᵉ eᵉ)

  compute-simple-prop-recursion-principle-cumulative-hierarchyᵉ :
    {l2ᵉ : Level}
    ( ρᵉ : {Aᵉ : UUᵉ l1ᵉ} → (Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) → Propᵉ l2ᵉ)
    ( τᵉ :
      { Aᵉ Bᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
      ( gᵉ : Bᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( eᵉ : has-smaller-imageᵉ fᵉ gᵉ) →
      type-Propᵉ (ρᵉ fᵉ) → type-Propᵉ (ρᵉ gᵉ)) →
    {Aᵉ : UUᵉ l1ᵉ} → (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    simple-prop-recursion-principle-cumulative-hierarchyᵉ ρᵉ τᵉ
      ( set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ) ＝ᵉ ρᵉ fᵉ
  compute-simple-prop-recursion-principle-cumulative-hierarchyᵉ {l2ᵉ} ρᵉ τᵉ fᵉ =
    compute-prop-recursion-principle-cumulative-hierarchyᵉ
      ( λ fᵉ _ → ρᵉ fᵉ) (λ fᵉ gᵉ eᵉ _ _ _ → τᵉ fᵉ gᵉ eᵉ) fᵉ (λ _ → raise-Propᵉ l2ᵉ unit-Propᵉ)
```

### The membership relationship for the cumulative hierarchy

```agda
  ∈-cumulative-hierarchy-Propᵉ :
    ( type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    ( type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    Propᵉ (lsuc l1ᵉ)
  ∈-cumulative-hierarchy-Propᵉ xᵉ =
    simple-prop-recursion-principle-cumulative-hierarchyᵉ
      ( λ {Aᵉ} fᵉ → exists-structure-Propᵉ Aᵉ (λ aᵉ → fᵉ aᵉ ＝ᵉ xᵉ))
      ( eᵉ)
    where
    eᵉ :
      {Aᵉ Bᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
      ( gᵉ : Bᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( eᵉ : has-smaller-imageᵉ fᵉ gᵉ) →
      ( exists-structureᵉ Aᵉ (λ aᵉ → fᵉ aᵉ ＝ᵉ xᵉ) →
        exists-structureᵉ Bᵉ (λ bᵉ → gᵉ bᵉ ＝ᵉ xᵉ))
    eᵉ {Aᵉ} {Bᵉ} fᵉ gᵉ sᵉ =
      map-universal-property-trunc-Propᵉ
        ( exists-structure-Propᵉ Bᵉ (λ bᵉ → gᵉ bᵉ ＝ᵉ xᵉ))
        ( λ ( aᵉ ,ᵉ pᵉ) →
          map-trunc-Propᵉ (λ (bᵉ ,ᵉ qᵉ) → (bᵉ ,ᵉ qᵉ ∙ᵉ pᵉ)) (sᵉ aᵉ))

  ∈-cumulative-hierarchyᵉ :
    ( type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    ( type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    UUᵉ (lsuc l1ᵉ)
  ∈-cumulative-hierarchyᵉ xᵉ yᵉ =
    type-Propᵉ (∈-cumulative-hierarchy-Propᵉ xᵉ yᵉ)

  id-∈-cumulative-hierarchyᵉ :
    ( xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) {Aᵉ : UUᵉ l1ᵉ}
    ( fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    ( ∈-cumulative-hierarchyᵉ xᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ)) ＝ᵉ
      exists-structureᵉ Aᵉ (λ aᵉ → fᵉ aᵉ ＝ᵉ xᵉ)
  id-∈-cumulative-hierarchyᵉ xᵉ fᵉ =
    apᵉ pr1ᵉ (compute-simple-prop-recursion-principle-cumulative-hierarchyᵉ _ _ fᵉ)

  ∈-cumulative-hierarchy-mere-preimageᵉ :
    { xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ} →
    { Aᵉ : UUᵉ l1ᵉ}
    { fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ} →
    ( ∈-cumulative-hierarchyᵉ xᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ)) →
    exists-structureᵉ Aᵉ (λ aᵉ → fᵉ aᵉ ＝ᵉ xᵉ)
  ∈-cumulative-hierarchy-mere-preimageᵉ {xᵉ} {Aᵉ} {fᵉ} =
    trᵉ idᵉ (id-∈-cumulative-hierarchyᵉ xᵉ fᵉ)

  mere-preimage-∈-cumulative-hierarchyᵉ :
    { xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ} →
    { Aᵉ : UUᵉ l1ᵉ}
    { fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ} →
    exists-structureᵉ Aᵉ (λ aᵉ → fᵉ aᵉ ＝ᵉ xᵉ) →
    ( ∈-cumulative-hierarchyᵉ xᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ))
  mere-preimage-∈-cumulative-hierarchyᵉ {xᵉ} {Aᵉ} {fᵉ} =
    trᵉ idᵉ (invᵉ (id-∈-cumulative-hierarchyᵉ xᵉ fᵉ))

  is-prop-∈-cumulative-hierarchyᵉ :
    ( xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    ( yᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    is-propᵉ (∈-cumulative-hierarchyᵉ xᵉ yᵉ)
  is-prop-∈-cumulative-hierarchyᵉ xᵉ yᵉ =
    is-prop-type-Propᵉ (∈-cumulative-hierarchy-Propᵉ xᵉ yᵉ)
```

### The subset relationship for the cumulative hierarchy

```agda
  ⊆-cumulative-hierarchyᵉ :
    ( type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    ( type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    UUᵉ (lsuc l1ᵉ)
  ⊆-cumulative-hierarchyᵉ xᵉ yᵉ =
    ( vᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    ∈-cumulative-hierarchyᵉ vᵉ xᵉ → ∈-cumulative-hierarchyᵉ vᵉ yᵉ

  is-prop-⊆-cumulative-hierarchyᵉ :
    ( xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    ( yᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    is-propᵉ (⊆-cumulative-hierarchyᵉ xᵉ yᵉ)
  is-prop-⊆-cumulative-hierarchyᵉ xᵉ yᵉ =
    is-prop-Πᵉ ( λ vᵉ →
      ( is-prop-Πᵉ (λ _ → is-prop-∈-cumulative-hierarchyᵉ vᵉ yᵉ)))

  ⊆-cumulative-hierarchy-has-smaller-imageᵉ :
    { Aᵉ Bᵉ : UUᵉ l1ᵉ}
    ( fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
    ( gᵉ : Bᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    ⊆-cumulative-hierarchyᵉ
      ( set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ)
      ( set-pseudo-cumulative-hierarchyᵉ Vᵉ gᵉ) →
    has-smaller-imageᵉ fᵉ gᵉ
  ⊆-cumulative-hierarchy-has-smaller-imageᵉ fᵉ gᵉ sᵉ aᵉ =
    ∈-cumulative-hierarchy-mere-preimageᵉ
      ( sᵉ (fᵉ aᵉ)
        ( mere-preimage-∈-cumulative-hierarchyᵉ
          (unit-trunc-Propᵉ (aᵉ ,ᵉ reflᵉ))))

  has-smaller-image-⊆-cumulative-hierarchyᵉ :
    { Aᵉ Bᵉ : UUᵉ l1ᵉ}
    ( fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
    ( gᵉ : Bᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    has-smaller-imageᵉ fᵉ gᵉ →
    ⊆-cumulative-hierarchyᵉ
      ( set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ)
      ( set-pseudo-cumulative-hierarchyᵉ Vᵉ gᵉ)
  has-smaller-image-⊆-cumulative-hierarchyᵉ {Aᵉ} {Bᵉ} fᵉ gᵉ sᵉ xᵉ mᵉ =
    mere-preimage-∈-cumulative-hierarchyᵉ
      ( map-universal-property-trunc-Propᵉ
        ( exists-structure-Propᵉ Bᵉ (λ bᵉ → gᵉ bᵉ ＝ᵉ xᵉ))
        ( λ (aᵉ ,ᵉ pᵉ) →
          map-trunc-Propᵉ (λ (bᵉ ,ᵉ qᵉ) → (bᵉ ,ᵉ qᵉ ∙ᵉ pᵉ)) (sᵉ aᵉ))
        ( ∈-cumulative-hierarchy-mere-preimageᵉ mᵉ))
```

### Extensionality of the membership relation

```agda
  pre-extensionality-∈-cumulative-hierarchyᵉ :
    { Aᵉ : UUᵉ l1ᵉ}
    ( fᵉ : Aᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ)
    ( xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    ( ⊆-cumulative-hierarchyᵉ xᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ)) →
    ( ⊆-cumulative-hierarchyᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ) xᵉ) →
    xᵉ ＝ᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ)
  pre-extensionality-∈-cumulative-hierarchyᵉ fᵉ =
    prop-ind-principle-cumulative-hierarchyᵉ
      ( λ xᵉ →
        ⊆-cumulative-hierarchyᵉ xᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ) →
        ⊆-cumulative-hierarchyᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ) xᵉ →
        xᵉ ＝ᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ))
      ( λ vᵉ →
        is-prop-Πᵉ (λ _ →
          is-prop-Πᵉ (λ _ →
            is-set-pseudo-cumulative-hierarchyᵉ Vᵉ
              vᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ))))
      ( λ gᵉ Hᵉ H₁ᵉ H₂ᵉ →
        set-ext-pseudo-cumulative-hierarchyᵉ Vᵉ gᵉ fᵉ
          ( ⊆-cumulative-hierarchy-has-smaller-imageᵉ gᵉ fᵉ H₁ᵉ ,ᵉ
            ⊆-cumulative-hierarchy-has-smaller-imageᵉ fᵉ gᵉ H₂ᵉ))

  extensionality-∈-cumulative-hierarchyᵉ :
    ( xᵉ yᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    ( ⊆-cumulative-hierarchyᵉ xᵉ yᵉ) →
    ( ⊆-cumulative-hierarchyᵉ yᵉ xᵉ) →
    xᵉ ＝ᵉ yᵉ
  extensionality-∈-cumulative-hierarchyᵉ xᵉ =
    prop-ind-principle-cumulative-hierarchyᵉ
      ( λ yᵉ →
        ⊆-cumulative-hierarchyᵉ xᵉ yᵉ →
        ⊆-cumulative-hierarchyᵉ yᵉ xᵉ → xᵉ ＝ᵉ yᵉ)
      ( λ vᵉ →
        is-prop-Πᵉ (λ _ →
          is-prop-Πᵉ (λ _ →
            is-set-pseudo-cumulative-hierarchyᵉ Vᵉ xᵉ vᵉ)))
      ( λ fᵉ Hᵉ H₁ᵉ H₂ᵉ →
        pre-extensionality-∈-cumulative-hierarchyᵉ
          fᵉ xᵉ H₁ᵉ H₂ᵉ)
```

### Cumulative hierarchies satisfy the empty set axiom

```agda
  empty-set-axiom-cumulative-hierarchyᵉ :
    ( xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    ¬ᵉ (∈-cumulative-hierarchyᵉ xᵉ empty-set-cumulative-hierarchyᵉ)
  empty-set-axiom-cumulative-hierarchyᵉ xᵉ Hᵉ =
    map-universal-property-trunc-Propᵉ empty-Propᵉ
      ( λ (zᵉ ,ᵉ pᵉ) → raise-ex-falsoᵉ l1ᵉ zᵉ)
      ( ∈-cumulative-hierarchy-mere-preimageᵉ Hᵉ)
```

### Cumulative hierarchies satisfy the pair axiom

```agda
  pair-cumulative-hierarchyᵉ :
    ( xᵉ yᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
    type-pseudo-cumulative-hierarchyᵉ Vᵉ
  pair-cumulative-hierarchyᵉ xᵉ yᵉ =
    set-pseudo-cumulative-hierarchyᵉ Vᵉ bool-mapᵉ
    where
    bool-mapᵉ : raise-boolᵉ l1ᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ
    bool-mapᵉ (map-raiseᵉ trueᵉ) = xᵉ
    bool-mapᵉ (map-raiseᵉ falseᵉ) = yᵉ

  abstract
    pair-axiom-cumulative-hierarchyᵉ :
      ( xᵉ yᵉ vᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( ∈-cumulative-hierarchyᵉ vᵉ (pair-cumulative-hierarchyᵉ xᵉ yᵉ) ↔ᵉ
        type-trunc-Propᵉ ( (vᵉ ＝ᵉ xᵉ) +ᵉ (vᵉ ＝ᵉ yᵉ)))
    pr1ᵉ (pair-axiom-cumulative-hierarchyᵉ xᵉ yᵉ vᵉ) Hᵉ =
      map-universal-property-trunc-Propᵉ
        ( trunc-Propᵉ ((vᵉ ＝ᵉ xᵉ) +ᵉ (vᵉ ＝ᵉ yᵉ)))
        ( λ where
          ( map-raiseᵉ trueᵉ ,ᵉ pᵉ) → unit-trunc-Propᵉ (inlᵉ (invᵉ pᵉ))
          ( map-raiseᵉ falseᵉ ,ᵉ pᵉ) → unit-trunc-Propᵉ (inrᵉ (invᵉ pᵉ)))
        ( ∈-cumulative-hierarchy-mere-preimageᵉ Hᵉ)
    pr2ᵉ (pair-axiom-cumulative-hierarchyᵉ xᵉ yᵉ vᵉ) Hᵉ =
      mere-preimage-∈-cumulative-hierarchyᵉ
        ( map-trunc-Propᵉ
          ( λ where
            ( inlᵉ pᵉ) → (map-raiseᵉ trueᵉ ,ᵉ invᵉ pᵉ)
            ( inrᵉ pᵉ) → (map-raiseᵉ falseᵉ ,ᵉ invᵉ pᵉ))
          ( Hᵉ))
```

### Singleton function

```agda
  singleton-cumulative-hierarchyᵉ :
    type-pseudo-cumulative-hierarchyᵉ Vᵉ →
    type-pseudo-cumulative-hierarchyᵉ Vᵉ
  singleton-cumulative-hierarchyᵉ xᵉ =
    ( set-pseudo-cumulative-hierarchyᵉ Vᵉ {raise-unitᵉ l1ᵉ}
      ( λ _ → xᵉ))
```

### Cumulative hierarchies satisfy the infinity axiom

```agda
  infinity-cumulative-hierarchyᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ
  infinity-cumulative-hierarchyᵉ =
    set-pseudo-cumulative-hierarchyᵉ Vᵉ ℕ-mapᵉ
    where
    ℕ-mapᵉ : raiseᵉ l1ᵉ ℕᵉ → type-pseudo-cumulative-hierarchyᵉ Vᵉ
    ℕ-mapᵉ (map-raiseᵉ zero-ℕᵉ) = empty-set-cumulative-hierarchyᵉ
    ℕ-mapᵉ (map-raiseᵉ (succ-ℕᵉ xᵉ)) =
      pair-cumulative-hierarchyᵉ
        ( ℕ-mapᵉ (map-raiseᵉ xᵉ))
        ( singleton-cumulative-hierarchyᵉ (ℕ-mapᵉ (map-raiseᵉ xᵉ)))

  abstract
    infinity-axiom-cumulative-hierarchyᵉ :
      ( ∈-cumulative-hierarchyᵉ
          empty-set-cumulative-hierarchyᵉ
          infinity-cumulative-hierarchyᵉ) ×ᵉ
      ( ( xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
        ∈-cumulative-hierarchyᵉ xᵉ infinity-cumulative-hierarchyᵉ →
        ∈-cumulative-hierarchyᵉ
          ( pair-cumulative-hierarchyᵉ xᵉ
            ( singleton-cumulative-hierarchyᵉ xᵉ))
          ( infinity-cumulative-hierarchyᵉ))
    pr1ᵉ infinity-axiom-cumulative-hierarchyᵉ =
      mere-preimage-∈-cumulative-hierarchyᵉ
        ( unit-trunc-Propᵉ (map-raiseᵉ zero-ℕᵉ ,ᵉ reflᵉ))
    pr2ᵉ infinity-axiom-cumulative-hierarchyᵉ xᵉ Hᵉ =
      mere-preimage-∈-cumulative-hierarchyᵉ
        ( map-trunc-Propᵉ
          ( λ where ((map-raiseᵉ nᵉ) ,ᵉ reflᵉ) → (map-raiseᵉ (succ-ℕᵉ nᵉ) ,ᵉ reflᵉ))
          ( ∈-cumulative-hierarchy-mere-preimageᵉ Hᵉ))
```

### Cumulative hierarchies satisfy the ∈-induction axiom

```agda
  ∈-induction-cumulative-hierarchyᵉ :
    {l2ᵉ : Level}
    ( Pᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ → UUᵉ l2ᵉ) →
    ( ( xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) → is-propᵉ (Pᵉ xᵉ)) →
    ( ( xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( ( yᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
        ∈-cumulative-hierarchyᵉ yᵉ xᵉ → Pᵉ yᵉ) →
      Pᵉ xᵉ) →
    ( xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) → Pᵉ xᵉ
  ∈-induction-cumulative-hierarchyᵉ Pᵉ P-propᵉ hᵉ =
    prop-ind-principle-cumulative-hierarchyᵉ Pᵉ P-propᵉ
      ( λ fᵉ IHᵉ →
        hᵉ (set-pseudo-cumulative-hierarchyᵉ Vᵉ fᵉ)
          ( λ yᵉ mᵉ →
            map-universal-property-trunc-Propᵉ
              ( Pᵉ yᵉ ,ᵉ P-propᵉ yᵉ)
              ( λ (aᵉ ,ᵉ pᵉ) → trᵉ Pᵉ pᵉ (IHᵉ aᵉ))
              ( ∈-cumulative-hierarchy-mere-preimageᵉ mᵉ)))
```

### Cumulative hierarchies satisfy the replacement axiom

```agda
  abstract
    replacement-cumulative-hierarchyᵉ :
      ( xᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      ( rᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ →
        type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
      exists-structureᵉ
        ( type-pseudo-cumulative-hierarchyᵉ Vᵉ)
        ( λ vᵉ →
          ( yᵉ : type-pseudo-cumulative-hierarchyᵉ Vᵉ) →
          ∈-cumulative-hierarchyᵉ yᵉ vᵉ ↔ᵉ
          exists-structureᵉ
            ( type-pseudo-cumulative-hierarchyᵉ Vᵉ)
            ( λ zᵉ → (∈-cumulative-hierarchyᵉ zᵉ xᵉ) ×ᵉ (yᵉ ＝ᵉ rᵉ zᵉ)))
    replacement-cumulative-hierarchyᵉ xᵉ rᵉ =
      map-universal-property-trunc-Propᵉ
        ( exists-structure-Propᵉ (type-pseudo-cumulative-hierarchyᵉ Vᵉ) _)
        ( λ where
          ( Aᵉ ,ᵉ fᵉ ,ᵉ reflᵉ) →
            unit-trunc-Propᵉ
              ( ( set-pseudo-cumulative-hierarchyᵉ Vᵉ (rᵉ ∘ᵉ fᵉ)) ,ᵉ
                ( λ yᵉ →
                  ( pairᵉ
                    ( λ Hᵉ →
                      map-trunc-Propᵉ
                        ( λ where
                          ( aᵉ ,ᵉ reflᵉ) →
                            (fᵉ aᵉ) ,ᵉ
                            ( mere-preimage-∈-cumulative-hierarchyᵉ
                              ( unit-trunc-Propᵉ (aᵉ ,ᵉ reflᵉ))) ,ᵉ
                            ( reflᵉ))
                        ( ∈-cumulative-hierarchy-mere-preimageᵉ Hᵉ))
                    ( λ Hᵉ →
                      mere-preimage-∈-cumulative-hierarchyᵉ
                        ( map-universal-property-trunc-Propᵉ
                          ( exists-structure-Propᵉ Aᵉ _)
                          ( λ where
                            ( zᵉ ,ᵉ Kᵉ ,ᵉ reflᵉ) →
                              map-trunc-Propᵉ
                                ( λ where (aᵉ ,ᵉ reflᵉ) → (aᵉ ,ᵉ reflᵉ))
                                ( ∈-cumulative-hierarchy-mere-preimageᵉ Kᵉ))
                          ( Hᵉ)))))))
        ( underlying-function-cumulative-hierarchyᵉ xᵉ)
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ UF13ᵉ}} {{#referenceᵉ dJKFX23ᵉ}}