# The sharp modality

```agda
{-# OPTIONSᵉ --cohesionᵉ --flat-splitᵉ #-}

module modal-type-theory.sharp-modalityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.locally-small-typesᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.locally-small-modal-operatorsᵉ
open import orthogonal-factorization-systems.modal-inductionᵉ
open import orthogonal-factorization-systems.modal-subuniverse-inductionᵉ
```

</details>

## Idea

Theᵉ **sharpᵉ modalityᵉ `♯`**ᵉ isᵉ anᵉ axiomatizedᵉ
[monadicᵉ modality](orthogonal-factorization-systems.higher-modalities.mdᵉ) weᵉ
postulate asᵉ aᵉ rightᵉ adjointᵉ to theᵉ
[flatᵉ modality](modal-type-theory.flat-modality.md).ᵉ

Inᵉ thisᵉ file,ᵉ weᵉ onlyᵉ postulate thatᵉ `♯`ᵉ isᵉ aᵉ
[modalᵉ operator](orthogonal-factorization-systems.modal-operators.mdᵉ) thatᵉ hasᵉ aᵉ
[modalᵉ inductionᵉ principle](orthogonal-factorization-systems.modal-induction.md).ᵉ
Inᵉ theᵉ fileᵉ aboutᵉ
[codiscreteᵉ types](modal-type-theory.sharp-codiscrete-types.md),ᵉ weᵉ postulate
thatᵉ theᵉ [subuniverse](foundation.subuniverses.mdᵉ) ofᵉ sharpᵉ modalᵉ typesᵉ hasᵉ
appropriateᵉ closureᵉ properties.ᵉ Inᵉ
[theᵉ flat-sharpᵉ adjunction](modal-type-theory.flat-sharp-adjunction.md),ᵉ weᵉ
postulate thatᵉ itᵉ hasᵉ theᵉ appropriateᵉ relationᵉ to theᵉ flatᵉ modality,ᵉ makingᵉ itᵉ aᵉ
lexᵉ modality.ᵉ Pleaseᵉ noteᵉ thatᵉ thereᵉ isᵉ someᵉ redundancyᵉ betweenᵉ theᵉ postulatedᵉ
axioms,ᵉ andᵉ theyᵉ mayᵉ beᵉ subjectᵉ to changeᵉ in theᵉ future.ᵉ

## Postulates

```agda
postulate
  ♯ᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → UUᵉ lᵉ

  @♭ᵉ unit-sharpᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → Aᵉ → ♯ᵉ Aᵉ

  ind-sharpᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Cᵉ : ♯ᵉ Aᵉ → UUᵉ l2ᵉ) →
    ((xᵉ : Aᵉ) → ♯ᵉ (Cᵉ (unit-sharpᵉ xᵉ))) →
    ((xᵉ : ♯ᵉ Aᵉ) → ♯ᵉ (Cᵉ xᵉ))

  compute-ind-sharpᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Cᵉ : ♯ᵉ Aᵉ → UUᵉ l2ᵉ)
    (fᵉ : (xᵉ : Aᵉ) → ♯ᵉ (Cᵉ (unit-sharpᵉ xᵉ))) →
    (ind-sharpᵉ Cᵉ fᵉ ∘ᵉ unit-sharpᵉ) ~ᵉ fᵉ
```

## Definitions

### The sharp modal operator

```agda
sharp-locally-small-operator-modalityᵉ :
  (lᵉ : Level) → locally-small-operator-modalityᵉ lᵉ lᵉ lᵉ
pr1ᵉ (sharp-locally-small-operator-modalityᵉ lᵉ) = ♯ᵉ {lᵉ}
pr2ᵉ (sharp-locally-small-operator-modalityᵉ lᵉ) Aᵉ = is-locally-small'ᵉ {lᵉ} {♯ᵉ Aᵉ}
```

### The sharp induction principle

```agda
induction-principle-sharpᵉ :
  {lᵉ : Level} → induction-principle-modalityᵉ {lᵉ} unit-sharpᵉ
pr1ᵉ (induction-principle-sharpᵉ Pᵉ) = ind-sharpᵉ Pᵉ
pr2ᵉ (induction-principle-sharpᵉ Pᵉ) = compute-ind-sharpᵉ Pᵉ

strong-induction-principle-subuniverse-sharpᵉ :
  {lᵉ : Level} → strong-induction-principle-subuniverse-modalityᵉ {lᵉ} unit-sharpᵉ
strong-induction-principle-subuniverse-sharpᵉ =
  strong-induction-principle-subuniverse-induction-principle-modalityᵉ
    ( unit-sharpᵉ)
    ( induction-principle-sharpᵉ)

strong-ind-subuniverse-sharpᵉ :
  {lᵉ : Level} → strong-ind-subuniverse-modalityᵉ {lᵉ} unit-sharpᵉ
strong-ind-subuniverse-sharpᵉ =
  strong-ind-strong-induction-principle-subuniverse-modalityᵉ
    ( unit-sharpᵉ)
    ( strong-induction-principle-subuniverse-sharpᵉ)

compute-strong-ind-subuniverse-sharpᵉ :
  {lᵉ : Level} →
  compute-strong-ind-subuniverse-modalityᵉ {lᵉ}
    unit-sharpᵉ
    strong-ind-subuniverse-sharpᵉ
compute-strong-ind-subuniverse-sharpᵉ =
  compute-strong-ind-strong-induction-principle-subuniverse-modalityᵉ
    ( unit-sharpᵉ)
    ( strong-induction-principle-subuniverse-sharpᵉ)

induction-principle-subuniverse-sharpᵉ :
  {lᵉ : Level} → induction-principle-subuniverse-modalityᵉ {lᵉ} unit-sharpᵉ
induction-principle-subuniverse-sharpᵉ =
  induction-principle-subuniverse-induction-principle-modalityᵉ
    ( unit-sharpᵉ)
    ( induction-principle-sharpᵉ)

ind-subuniverse-sharpᵉ :
  {lᵉ : Level} → ind-subuniverse-modalityᵉ {lᵉ} unit-sharpᵉ
ind-subuniverse-sharpᵉ =
  ind-induction-principle-subuniverse-modalityᵉ
    ( unit-sharpᵉ)
    ( induction-principle-subuniverse-sharpᵉ)

compute-ind-subuniverse-sharpᵉ :
  {lᵉ : Level} →
  compute-ind-subuniverse-modalityᵉ {lᵉ} unit-sharpᵉ ind-subuniverse-sharpᵉ
compute-ind-subuniverse-sharpᵉ =
  compute-ind-induction-principle-subuniverse-modalityᵉ
    ( unit-sharpᵉ)
    ( induction-principle-subuniverse-sharpᵉ)
```

### Sharp recursion

```agda
rec-sharpᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (Aᵉ → ♯ᵉ Bᵉ) → (♯ᵉ Aᵉ → ♯ᵉ Bᵉ)
rec-sharpᵉ {Bᵉ = Bᵉ} = ind-sharpᵉ (λ _ → Bᵉ)

compute-rec-sharpᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → ♯ᵉ Bᵉ) →
  (rec-sharpᵉ fᵉ ∘ᵉ unit-sharpᵉ) ~ᵉ fᵉ
compute-rec-sharpᵉ {Bᵉ = Bᵉ} = compute-ind-sharpᵉ (λ _ → Bᵉ)

recursion-principle-sharpᵉ :
  {lᵉ : Level} → recursion-principle-modalityᵉ {lᵉ} unit-sharpᵉ
pr1ᵉ (recursion-principle-sharpᵉ) = rec-sharpᵉ
pr2ᵉ (recursion-principle-sharpᵉ) = compute-rec-sharpᵉ

strong-recursion-principle-subuniverse-sharpᵉ :
  {lᵉ : Level} → strong-recursion-principle-subuniverse-modalityᵉ {lᵉ} unit-sharpᵉ
strong-recursion-principle-subuniverse-sharpᵉ =
  strong-recursion-principle-subuniverse-recursion-principle-modalityᵉ
    ( unit-sharpᵉ)
    ( recursion-principle-sharpᵉ)

strong-rec-subuniverse-sharpᵉ :
  {lᵉ : Level} → strong-rec-subuniverse-modalityᵉ {lᵉ} unit-sharpᵉ
strong-rec-subuniverse-sharpᵉ =
  strong-rec-strong-recursion-principle-subuniverse-modalityᵉ
    ( unit-sharpᵉ)
    ( strong-recursion-principle-subuniverse-sharpᵉ)

compute-strong-rec-subuniverse-sharpᵉ :
  {lᵉ : Level} →
  compute-strong-rec-subuniverse-modalityᵉ {lᵉ}
    unit-sharpᵉ
    strong-rec-subuniverse-sharpᵉ
compute-strong-rec-subuniverse-sharpᵉ =
  compute-strong-rec-strong-recursion-principle-subuniverse-modalityᵉ
    ( unit-sharpᵉ)
    ( strong-recursion-principle-subuniverse-sharpᵉ)

recursion-principle-subuniverse-sharpᵉ :
  {lᵉ : Level} → recursion-principle-subuniverse-modalityᵉ {lᵉ} unit-sharpᵉ
recursion-principle-subuniverse-sharpᵉ =
  recursion-principle-subuniverse-recursion-principle-modalityᵉ
    ( unit-sharpᵉ)
    ( recursion-principle-sharpᵉ)

rec-subuniverse-sharpᵉ :
  {lᵉ : Level} → rec-subuniverse-modalityᵉ {lᵉ} unit-sharpᵉ
rec-subuniverse-sharpᵉ =
  rec-recursion-principle-subuniverse-modalityᵉ
    ( unit-sharpᵉ)
    ( recursion-principle-subuniverse-sharpᵉ)

compute-rec-subuniverse-sharpᵉ :
  {lᵉ : Level} →
  compute-rec-subuniverse-modalityᵉ {lᵉ} unit-sharpᵉ rec-subuniverse-sharpᵉ
compute-rec-subuniverse-sharpᵉ =
  compute-rec-recursion-principle-subuniverse-modalityᵉ
    ( unit-sharpᵉ)
    ( recursion-principle-subuniverse-sharpᵉ)
```

### Action on maps

```agda
ap-sharpᵉ : {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → (♯ᵉ Aᵉ → ♯ᵉ Bᵉ)
ap-sharpᵉ fᵉ = rec-sharpᵉ (unit-sharpᵉ ∘ᵉ fᵉ)
```

## See also

-ᵉ Inᵉ [codiscreteᵉ types](modal-type-theory.sharp-codiscrete-types.md),ᵉ weᵉ
  postulate thatᵉ theᵉ sharpᵉ modalityᵉ isᵉ aᵉ
  [higherᵉ modality](orthogonal-factorization-systems.higher-modalities.md).ᵉ
-ᵉ andᵉ in [theᵉ flat-sharpᵉ adjunction](modal-type-theory.flat-sharp-adjunction.mdᵉ)
  weᵉ moreoverᵉ postulate thatᵉ theᵉ sharpᵉ modalityᵉ isᵉ rightᵉ adjointᵉ to theᵉ
  [flatᵉ modality](modal-type-theory.flat-modality.md).ᵉ

## References

{{#bibliographyᵉ}} {{#referenceᵉ Shu18ᵉ}} {{#referenceᵉ Dlicata335/Cohesion-Agdaᵉ}}
{{#referenceᵉ Felixwellen/DCHoTT-Agdaᵉ}}