# The flat-sharp adjunction

```agda
{-# OPTIONSᵉ --cohesionᵉ --flat-splitᵉ #-}

module modal-type-theory.flat-sharp-adjunctionᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.locally-small-typesᵉ
open import foundation.multivariable-sectionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import modal-type-theory.crisp-identity-typesᵉ
open import modal-type-theory.flat-modalityᵉ
open import modal-type-theory.sharp-codiscrete-typesᵉ
open import modal-type-theory.sharp-modalityᵉ

open import orthogonal-factorization-systems.locally-small-modal-operatorsᵉ
open import orthogonal-factorization-systems.modal-inductionᵉ
open import orthogonal-factorization-systems.uniquely-eliminating-modalitiesᵉ
```

</details>

## Idea

Weᵉ postulate thatᵉ theᵉ [flatᵉ modality](modal-type-theory.flat-modality.mdᵉ) `♭`ᵉ isᵉ
aᵉ crispᵉ leftᵉ adjointᵉ to theᵉ
[sharpᵉ modality](modal-type-theory.sharp-modality.mdᵉ) `♯`.ᵉ

Inᵉ [Theᵉ sharpᵉ modality](modal-type-theory.sharp-modality.mdᵉ) weᵉ postulatedᵉ thatᵉ
`♯`ᵉ isᵉ aᵉ [modalᵉ operator](orthogonal-factorization-systems.modal-operators.mdᵉ)
thatᵉ hasᵉ aᵉ
[modalᵉ inductionᵉ principle](orthogonal-factorization-systems.modal-induction.md).ᵉ
Inᵉ theᵉ fileᵉ
[Sharp-Codiscreteᵉ types](modal-type-theory.sharp-codiscrete-types.md),ᵉ weᵉ
postulatedᵉ thatᵉ theᵉ [subuniverse](foundation.subuniverses.mdᵉ) ofᵉ sharpᵉ modalᵉ
typesᵉ hasᵉ appropriateᵉ closureᵉ properties.ᵉ Pleaseᵉ noteᵉ thatᵉ thereᵉ isᵉ someᵉ
redundancyᵉ betweenᵉ theᵉ postulatedᵉ axioms,ᵉ andᵉ theyᵉ mayᵉ beᵉ subjectᵉ to changeᵉ in
theᵉ future.ᵉ

## Postulates

### Crisp induction for `♯`

Sharp-Codiscreteᵉ typesᵉ areᵉ localᵉ atᵉ theᵉ flatᵉ counit.ᵉ

```agda
postulate
  crisp-ind-sharpᵉ :
    {@♭ᵉ l1ᵉ : Level} {l2ᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ l1ᵉ} (Cᵉ : Aᵉ → UUᵉ l2ᵉ) →
    ((xᵉ : Aᵉ) → is-sharp-codiscreteᵉ (Cᵉ xᵉ)) →
    ((@♭ᵉ xᵉ : Aᵉ) → Cᵉ xᵉ) → (xᵉ : Aᵉ) → Cᵉ xᵉ

  compute-crisp-ind-sharpᵉ :
    {@♭ᵉ l1ᵉ : Level} {l2ᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ l1ᵉ} (Cᵉ : Aᵉ → UUᵉ l2ᵉ)
    (is-sharp-codiscrete-Cᵉ : (xᵉ : Aᵉ) → is-sharp-codiscreteᵉ (Cᵉ xᵉ))
    (fᵉ : (@♭ᵉ xᵉ : Aᵉ) → Cᵉ xᵉ) →
    (@♭ᵉ xᵉ : Aᵉ) → crisp-ind-sharpᵉ Cᵉ is-sharp-codiscrete-Cᵉ fᵉ xᵉ ＝ᵉ fᵉ xᵉ
```

### Crisp elimination of `♯`

```agda
postulate
  crisp-elim-sharpᵉ :
    {@♭ᵉ lᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ lᵉ} → @♭ᵉ ♯ᵉ Aᵉ → Aᵉ

  compute-crisp-elim-sharpᵉ :
    {@♭ᵉ lᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ lᵉ} (@♭ᵉ xᵉ : Aᵉ) →
    crisp-elim-sharpᵉ (unit-sharpᵉ xᵉ) ＝ᵉ xᵉ

  uniqueness-crisp-elim-sharpᵉ :
    {@♭ᵉ lᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ lᵉ} (@♭ᵉ xᵉ : ♯ᵉ Aᵉ) →
    unit-sharpᵉ (crisp-elim-sharpᵉ xᵉ) ＝ᵉ xᵉ

  coherence-uniqueness-crisp-elim-sharpᵉ :
    {@♭ᵉ lᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ lᵉ} (@♭ᵉ xᵉ : Aᵉ) →
    ( uniqueness-crisp-elim-sharpᵉ (unit-sharpᵉ xᵉ)) ＝ᵉ
    ( apᵉ unit-sharpᵉ (compute-crisp-elim-sharpᵉ xᵉ))
```

## Definitions

### Crisp recursion for `♯`

```agda
crisp-rec-sharpᵉ :
  {@♭ᵉ l1ᵉ : Level} {l2ᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ l1ᵉ} (Cᵉ : UUᵉ l2ᵉ) →
  (is-sharp-codiscreteᵉ Cᵉ) →
  ((@♭ᵉ xᵉ : Aᵉ) → Cᵉ) → Aᵉ → Cᵉ
crisp-rec-sharpᵉ Cᵉ is-sharp-codiscrete-Cᵉ =
  crisp-ind-sharpᵉ (λ _ → Cᵉ) (λ _ → is-sharp-codiscrete-Cᵉ)

compute-crisp-rec-sharpᵉ :
  {@♭ᵉ l1ᵉ : Level} {l2ᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ l1ᵉ} (Cᵉ : UUᵉ l2ᵉ)
  (is-sharp-codiscrete-Cᵉ : is-sharp-codiscreteᵉ Cᵉ)
  (fᵉ : (@♭ᵉ xᵉ : Aᵉ) → Cᵉ) →
  (@♭ᵉ xᵉ : Aᵉ) → crisp-rec-sharpᵉ Cᵉ is-sharp-codiscrete-Cᵉ fᵉ xᵉ ＝ᵉ fᵉ xᵉ
compute-crisp-rec-sharpᵉ Cᵉ is-sharp-codiscrete-Cᵉ =
  compute-crisp-ind-sharpᵉ (λ _ → Cᵉ) (λ _ → is-sharp-codiscrete-Cᵉ)
```

## Properties

```agda
crisp-tr-sharpᵉ :
  {@♭ᵉ lᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ lᵉ} {Bᵉ : UUᵉ lᵉ} → (pᵉ : Aᵉ ＝ᵉ Bᵉ) →
  {@♭ᵉ xᵉ : ♯ᵉ Aᵉ} → unit-sharpᵉ (trᵉ (λ Xᵉ → Xᵉ) pᵉ (crisp-elim-sharpᵉ xᵉ)) ＝ᵉ trᵉ ♯ᵉ pᵉ xᵉ
crisp-tr-sharpᵉ reflᵉ {xᵉ} = uniqueness-crisp-elim-sharpᵉ xᵉ
```

### Crisp induction on `♯` implies typal induction

```agda
ind-crisp-ind-sharpᵉ :
  {@♭ᵉ l1ᵉ : Level} {l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Cᵉ : ♯ᵉ Aᵉ → UUᵉ l2ᵉ) →
  ((xᵉ : ♯ᵉ Aᵉ) → is-sharp-codiscreteᵉ (Cᵉ xᵉ)) →
  ((xᵉ : Aᵉ) → Cᵉ (unit-sharpᵉ xᵉ)) →
  (xᵉ : ♯ᵉ Aᵉ) → Cᵉ xᵉ
ind-crisp-ind-sharpᵉ {Aᵉ = Aᵉ} Cᵉ is-sharp-codiscrete-Cᵉ fᵉ x'ᵉ =
  crisp-ind-sharpᵉ
    ( λ Xᵉ → (xᵉ : ♯ᵉ Xᵉ) (pᵉ : Xᵉ ＝ᵉ Aᵉ) → Cᵉ (trᵉ ♯ᵉ pᵉ xᵉ))
    ( λ xᵉ →
      is-sharp-codiscrete-Πᵉ
        ( λ yᵉ → is-sharp-codiscrete-Πᵉ
          ( λ pᵉ → is-sharp-codiscrete-Cᵉ (trᵉ ♯ᵉ pᵉ yᵉ))))
    ( λ A'ᵉ →
      crisp-ind-sharpᵉ
        ( λ yᵉ → (pᵉ : A'ᵉ ＝ᵉ Aᵉ) → Cᵉ (trᵉ ♯ᵉ pᵉ yᵉ))
        ( λ yᵉ → is-sharp-codiscrete-Πᵉ (λ pᵉ → is-sharp-codiscrete-Cᵉ (trᵉ ♯ᵉ pᵉ yᵉ)))
        ( λ xᵉ pᵉ → trᵉ Cᵉ (crisp-tr-sharpᵉ pᵉ) (fᵉ (trᵉ idᵉ pᵉ (crisp-elim-sharpᵉ xᵉ)))))
    ( Aᵉ)
    ( x'ᵉ)
    ( reflᵉ)
```

Theᵉ accompanyingᵉ computationᵉ principleᵉ remainsᵉ to beᵉ fullyᵉ formalized.ᵉ

```text
compute-ind-crisp-ind-sharpᵉ :
  {@♭ᵉ l1ᵉ : Level} {l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Cᵉ : ♯ᵉ Aᵉ → UUᵉ l2ᵉ) →
  (is-sharp-codiscrete-Cᵉ : (xᵉ : ♯ᵉ Aᵉ) → is-sharp-codiscreteᵉ (Cᵉ xᵉ)) →
  (fᵉ : (xᵉ : Aᵉ) → Cᵉ (unit-sharpᵉ xᵉ)) → (xᵉ : Aᵉ) →
  ind-crisp-ind-sharpᵉ Cᵉ is-sharp-codiscrete-Cᵉ fᵉ (unit-sharpᵉ xᵉ) ＝ᵉ fᵉ xᵉ
compute-ind-crisp-ind-sharpᵉ {Aᵉ = Aᵉ} Cᵉ is-sharp-codiscrete-Cᵉ fᵉ xᵉ =
  crisp-ind-sharpᵉ
    ( λ Xᵉ → (xᵉ : Xᵉ) (pᵉ : Xᵉ ＝ᵉ Aᵉ) →
      ind-crisp-ind-sharpᵉ {!ᵉ   !ᵉ} {!ᵉ   !ᵉ} {!ᵉ   !ᵉ} {!ᵉ   !ᵉ})
    ( {!ᵉ   !ᵉ})
    {!ᵉ   !ᵉ}
    ( Aᵉ)
    ( xᵉ)
    ( reflᵉ)
```

### Flat after sharp

```agda
module _
  {@♭ᵉ lᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ lᵉ}
  where

  ap-flat-elim-sharpᵉ : ♭ᵉ (♯ᵉ Aᵉ) → ♭ᵉ Aᵉ
  ap-flat-elim-sharpᵉ = ap-crisp-flatᵉ crisp-elim-sharpᵉ

  ap-flat-unit-sharpᵉ : ♭ᵉ Aᵉ → ♭ᵉ (♯ᵉ Aᵉ)
  ap-flat-unit-sharpᵉ = ap-flatᵉ unit-sharpᵉ

  is-section-ap-flat-unit-sharpᵉ : ap-flat-elim-sharpᵉ ∘ᵉ ap-flat-unit-sharpᵉ ~ᵉ idᵉ
  is-section-ap-flat-unit-sharpᵉ (cons-flatᵉ xᵉ) =
    ap-crispᵉ cons-flatᵉ (compute-crisp-elim-sharpᵉ xᵉ)

  is-retraction-ap-flat-unit-sharpᵉ :
    ap-flat-unit-sharpᵉ ∘ᵉ ap-flat-elim-sharpᵉ ~ᵉ idᵉ
  is-retraction-ap-flat-unit-sharpᵉ (cons-flatᵉ xᵉ) =
    ap-crispᵉ cons-flatᵉ (uniqueness-crisp-elim-sharpᵉ xᵉ)

  is-equiv-ap-flat-elim-sharpᵉ : is-equivᵉ ap-flat-elim-sharpᵉ
  pr1ᵉ (pr1ᵉ is-equiv-ap-flat-elim-sharpᵉ) = ap-flat-unit-sharpᵉ
  pr2ᵉ (pr1ᵉ is-equiv-ap-flat-elim-sharpᵉ) = is-section-ap-flat-unit-sharpᵉ
  pr1ᵉ (pr2ᵉ is-equiv-ap-flat-elim-sharpᵉ) = ap-flat-unit-sharpᵉ
  pr2ᵉ (pr2ᵉ is-equiv-ap-flat-elim-sharpᵉ) = is-retraction-ap-flat-unit-sharpᵉ

  equiv-ap-flat-elim-sharpᵉ : ♭ᵉ (♯ᵉ Aᵉ) ≃ᵉ ♭ᵉ Aᵉ
  pr1ᵉ equiv-ap-flat-elim-sharpᵉ = ap-flat-elim-sharpᵉ
  pr2ᵉ equiv-ap-flat-elim-sharpᵉ = is-equiv-ap-flat-elim-sharpᵉ

  is-equiv-ap-flat-unit-sharpᵉ : is-equivᵉ ap-flat-unit-sharpᵉ
  pr1ᵉ (pr1ᵉ is-equiv-ap-flat-unit-sharpᵉ) = ap-flat-elim-sharpᵉ
  pr2ᵉ (pr1ᵉ is-equiv-ap-flat-unit-sharpᵉ) = is-retraction-ap-flat-unit-sharpᵉ
  pr1ᵉ (pr2ᵉ is-equiv-ap-flat-unit-sharpᵉ) = ap-flat-elim-sharpᵉ
  pr2ᵉ (pr2ᵉ is-equiv-ap-flat-unit-sharpᵉ) = is-section-ap-flat-unit-sharpᵉ

  equiv-ap-flat-unit-sharpᵉ : ♭ᵉ Aᵉ ≃ᵉ ♭ᵉ (♯ᵉ Aᵉ)
  pr1ᵉ equiv-ap-flat-unit-sharpᵉ = ap-flat-unit-sharpᵉ
  pr2ᵉ equiv-ap-flat-unit-sharpᵉ = is-equiv-ap-flat-unit-sharpᵉ
```

### Sharp after flat

```agda
module _
  {@♭ᵉ lᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ lᵉ}
  where

  ap-sharp-counit-flatᵉ : ♯ᵉ (♭ᵉ Aᵉ) → ♯ᵉ Aᵉ
  ap-sharp-counit-flatᵉ = rec-sharpᵉ (unit-sharpᵉ ∘ᵉ counit-flatᵉ)

  ap-sharp-cons-flatᵉ : ♯ᵉ Aᵉ → ♯ᵉ (♭ᵉ Aᵉ)
  ap-sharp-cons-flatᵉ =
    rec-sharpᵉ
      ( crisp-rec-sharpᵉ
        ( ♯ᵉ (♭ᵉ Aᵉ))
        ( is-sharp-codiscrete-sharpᵉ (♭ᵉ Aᵉ))
        ( λ xᵉ → unit-sharpᵉ (cons-flatᵉ xᵉ)))
```

Itᵉ remainsᵉ to showᵉ thatᵉ theseᵉ twoᵉ areᵉ inversesᵉ to eachᵉ other.ᵉ

```text
  is-section-cons-flatᵉ : ap-sharp-counit-flatᵉ ∘ᵉ cons-flatᵉ ~ᵉ idᵉ
  is-section-cons-flatᵉ =
    ind-subuniverse-sharpᵉ
      ( Aᵉ)
      ( λ xᵉ → ap-sharp-counit-flatᵉ (cons-flatᵉ xᵉ) ＝ᵉ xᵉ)
      ( λ xᵉ → is-sharp-codiscrete-Id-sharpᵉ (ap-sharp-counit-flatᵉ (cons-flatᵉ xᵉ)) xᵉ)
      ( λ xᵉ →
          crisp-rec-sharpᵉ
            ( ap-sharp-counit-flatᵉ (cons-flatᵉ (unit-sharpᵉ xᵉ)) ＝ᵉ unit-sharpᵉ xᵉ)
            ( is-sharp-codiscrete-Id-sharpᵉ (ap-sharp-counit-flatᵉ (cons-flatᵉ (unit-sharpᵉ xᵉ))) (unit-sharpᵉ xᵉ))
            ( λ yᵉ →
              compute-rec-subuniverse-sharpᵉ
                {!ᵉ   !ᵉ} (♯ᵉ Aᵉ) {!ᵉ  is-sharp-codiscrete-sharpᵉ ?ᵉ  !ᵉ} {!ᵉ   !ᵉ} {!ᵉ   !ᵉ})
            {!ᵉ   !ᵉ})
```

### Sharp is uniquely eliminating

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

```text
map-crisp-retraction-precomp-unit-sharpᵉ :
  {l1ᵉ : Level} {l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Pᵉ : ♯ᵉ Xᵉ → UUᵉ l2ᵉ} →
  ((xᵉ : ♯ᵉ Xᵉ) → ♯ᵉ (Pᵉ xᵉ)) → (xᵉ : Xᵉ) → ♯ᵉ (Pᵉ (unit-sharpᵉ xᵉ))
map-crisp-retraction-precomp-unit-sharpᵉ {Pᵉ = Pᵉ} fᵉ = {!ᵉ   !ᵉ}

crisp-elim-sharp'ᵉ :
    {@♭ᵉ lᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ lᵉ} → @♭ᵉ ♯ᵉ Aᵉ → Aᵉ
crisp-elim-sharp'ᵉ {Aᵉ = Aᵉ} xᵉ = crisp-ind-sharpᵉ {!ᵉ   !ᵉ} {!ᵉ   !ᵉ} {!ᵉ   !ᵉ} {!ᵉ   !ᵉ}

is-retraction-map-crisp-retraction-precomp-unit-sharpᵉ :
  {@♭ᵉ l1ᵉ : Level} {l2ᵉ : Level} {@♭ᵉ Xᵉ : UUᵉ l1ᵉ} {Pᵉ : ♯ᵉ Xᵉ → UUᵉ l2ᵉ} →
  map-crisp-retraction-precomp-unit-sharpᵉ {Xᵉ = Xᵉ} {Pᵉ} ∘ᵉ {!ᵉ precomp-Πᵉ (unit-sharpᵉ) (♯ᵉ ∘ᵉ Pᵉ)  !ᵉ} ~ᵉ idᵉ
is-retraction-map-crisp-retraction-precomp-unit-sharpᵉ = {!ᵉ   !ᵉ}

is-uniquely-eliminating-sharpᵉ :
  {lᵉ : Level} → is-uniquely-eliminating-modalityᵉ (unit-sharpᵉ {lᵉ})
is-uniquely-eliminating-sharpᵉ Xᵉ Pᵉ .pr1ᵉ =
  section-multivariable-sectionᵉ 2 (precomp-Πᵉ unit-sharpᵉ (♯ᵉ ∘ᵉ Pᵉ)) (induction-principle-sharpᵉ Xᵉ Pᵉ)
is-uniquely-eliminating-sharpᵉ {lᵉ} Xᵉ Pᵉ .pr2ᵉ .pr1ᵉ xᵉ =
is-uniquely-eliminating-sharpᵉ Xᵉ Pᵉ .pr2ᵉ .pr2ᵉ fᵉ =
  eq-htpyᵉ
  ( λ xᵉ →
    equational-reasoningᵉ
      {!ᵉ   !ᵉ}
      ＝ᵉ {!ᵉ   !ᵉ} byᵉ {!ᵉ   !ᵉ}
      ＝ᵉ {!ᵉ   !ᵉ} byᵉ compute-crisp-ind-sharpᵉ (♯ᵉ ∘ᵉ Pᵉ) {!ᵉ is-sharp-codiscrete-sharpᵉ ∘ᵉ Pᵉ  !ᵉ} crisp-elim-sharpᵉ {!ᵉ fᵉ !ᵉ}
      ＝ᵉ {!ᵉ   !ᵉ} byᵉ {!ᵉ   !ᵉ})
```

## See also

-ᵉ Inᵉ [codiscreteᵉ types](modal-type-theory.sharp-codiscrete-types.md),ᵉ weᵉ
  postulate thatᵉ theᵉ sharpᵉ modalityᵉ isᵉ aᵉ
  [higherᵉ modality](orthogonal-factorization-systems.higher-modalities.md).ᵉ

## References

{{#bibliographyᵉ}} {{#referenceᵉ Shu18ᵉ}} {{#referenceᵉ Dlicata335/Cohesion-Agdaᵉ}}