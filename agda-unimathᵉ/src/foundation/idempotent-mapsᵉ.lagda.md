# Idempotent maps

```agda
module foundation.idempotent-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.setsᵉ
```

</details>

## Idea

Anᵉ {{#conceptᵉ "idempotentᵉ map"ᵉ Disambiguation="ofᵉ types"ᵉ Agda=is-idempotentᵉ}} isᵉ
aᵉ mapᵉ `fᵉ : Aᵉ → A`ᵉ [equipped](foundation.structure.mdᵉ) with aᵉ
[homotopy](foundation-core.homotopies.mdᵉ)

```text
  fᵉ ∘ᵉ fᵉ ~ᵉ f.ᵉ
```

Whileᵉ thisᵉ definitionᵉ correspondsᵉ to theᵉ classicalᵉ conceptᵉ ofᵉ anᵉ idempotentᵉ mapᵉ
in [set](foundation-core.sets.md)-levelᵉ mathematics,ᵉ aᵉ homotopyᵉ `Iᵉ : fᵉ ∘ᵉ fᵉ ~ᵉ f`ᵉ
mayᵉ failᵉ to beᵉ coherentᵉ with itselfᵉ in Homotopyᵉ Typeᵉ Theory.ᵉ Forᵉ instance,ᵉ oneᵉ
mayᵉ askᵉ forᵉ aᵉ second-orderᵉ coherenceᵉ

```text
  Jᵉ : fᵉ ·rᵉ Iᵉ ~ᵉ Iᵉ ·lᵉ fᵉ
```

givingᵉ theᵉ definitionᵉ ofᵉ aᵉ
[quasicoherentlyᵉ idempotentᵉ map](foundation.quasicoherently-idempotent-maps.md).ᵉ

Theᵉ situationᵉ mayᵉ beᵉ comparedᵉ againstᵉ thatᵉ ofᵉ
[invertibleᵉ maps](foundation-core.invertible-maps.mdᵉ) vs.ᵉ
[coherentlyᵉ invertibleᵉ maps](foundation-core.coherently-invertible-maps.md).ᵉ
Recallᵉ thatᵉ anᵉ _invertibleᵉ mapᵉ_ isᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ equippedᵉ with aᵉ converseᵉ
mapᵉ `gᵉ : Bᵉ → A`ᵉ andᵉ homotopiesᵉ `Sᵉ : fᵉ ∘ᵉ gᵉ ~ᵉ id`ᵉ andᵉ `Rᵉ : gᵉ ∘ᵉ fᵉ ~ᵉ id`ᵉ witnessingᵉ
thatᵉ `g`ᵉ isᵉ anᵉ _inverseᵉ_ ofᵉ `f`,ᵉ whileᵉ aᵉ _coherentlyᵉ invertibleᵉ mapᵉ_ hasᵉ anᵉ
additionalᵉ coherenceᵉ `fᵉ ·rᵉ Rᵉ ~ᵉ Sᵉ ·lᵉ f`.ᵉ

Itᵉ isᵉ trueᵉ thatᵉ everyᵉ invertibleᵉ mapᵉ isᵉ coherentlyᵉ invertible,ᵉ butᵉ noᵉ suchᵉ
constructionᵉ preservesᵉ bothᵉ ofᵉ theᵉ homotopiesᵉ `S`ᵉ andᵉ `R`.ᵉ Likewise,ᵉ everyᵉ
quasicoherentlyᵉ idempotentᵉ mapᵉ isᵉ alsoᵉ coherentlyᵉ idempotent,ᵉ althoughᵉ againᵉ theᵉ
coherenceᵉ `J`ᵉ isᵉ replacedᵉ asᵉ partᵉ ofᵉ thisᵉ construction.ᵉ Onᵉ theᵉ otherᵉ hand,ᵉ in
contrastᵉ to invertibleᵉ maps,ᵉ notᵉ everyᵉ idempotentᵉ mapᵉ canᵉ beᵉ madeᵉ to beᵉ fullyᵉ
coherentᵉ orᵉ evenᵉ quasicoherent.ᵉ Forᵉ aᵉ counterexampleᵉ seeᵉ Sectionᵉ 4 ofᵉ
{{#citeᵉ Shu17}}.ᵉ

**Terminology.**ᵉ Ourᵉ definitionᵉ ofᵉ anᵉ _idempotentᵉ mapᵉ_ correspondsᵉ to theᵉ
definitionᵉ ofᵉ aᵉ _preidempotentᵉ mapᵉ_ in {{#referenceᵉ Shu17ᵉ}} andᵉ
{{#referenceᵉ Shu14SplittingIdempotents}},ᵉ whileᵉ theirᵉ definitionᵉ ofᵉ anᵉ
_idempotentᵉ mapᵉ_ correspondsᵉ in ourᵉ terminologyᵉ to aᵉ _coherentlyᵉ idempotentᵉ
map_.ᵉ

## Definitions

### The structure on a map of idempotence

```agda
is-idempotentᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → (Aᵉ → Aᵉ) → UUᵉ lᵉ
is-idempotentᵉ fᵉ = fᵉ ∘ᵉ fᵉ ~ᵉ fᵉ
```

### The type of idempotent maps on a type

```agda
idempotent-mapᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → UUᵉ lᵉ
idempotent-mapᵉ Aᵉ = Σᵉ (Aᵉ → Aᵉ) (is-idempotentᵉ)

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (fᵉ : idempotent-mapᵉ Aᵉ)
  where

  map-idempotent-mapᵉ : Aᵉ → Aᵉ
  map-idempotent-mapᵉ = pr1ᵉ fᵉ

  is-idempotent-idempotent-mapᵉ :
    is-idempotentᵉ map-idempotent-mapᵉ
  is-idempotent-idempotent-mapᵉ = pr2ᵉ fᵉ
```

## Properties

### Being an idempotent operation on a set is a property

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (is-set-Aᵉ : is-setᵉ Aᵉ) (fᵉ : Aᵉ → Aᵉ)
  where

  is-prop-is-idempotent-is-setᵉ : is-propᵉ (is-idempotentᵉ fᵉ)
  is-prop-is-idempotent-is-setᵉ =
    is-prop-Πᵉ (λ xᵉ → is-set-Aᵉ (fᵉ (fᵉ xᵉ)) (fᵉ xᵉ))

  is-idempotent-is-set-Propᵉ : Propᵉ lᵉ
  is-idempotent-is-set-Propᵉ =
    ( is-idempotentᵉ fᵉ ,ᵉ is-prop-is-idempotent-is-setᵉ)

module _
  {lᵉ : Level} (Aᵉ : Setᵉ lᵉ) (fᵉ : type-Setᵉ Aᵉ → type-Setᵉ Aᵉ)
  where

  is-prop-is-idempotent-Setᵉ : is-propᵉ (is-idempotentᵉ fᵉ)
  is-prop-is-idempotent-Setᵉ =
    is-prop-is-idempotent-is-setᵉ (is-set-type-Setᵉ Aᵉ) fᵉ

  is-idempotent-prop-Setᵉ : Propᵉ lᵉ
  is-idempotent-prop-Setᵉ =
    ( is-idempotentᵉ fᵉ ,ᵉ is-prop-is-idempotent-Setᵉ)
```

### If `i` and `r` is an inclusion-retraction pair, then `i ∘ r` is idempotent

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (iᵉ : Bᵉ → Aᵉ) (rᵉ : Aᵉ → Bᵉ) (Hᵉ : is-retractionᵉ iᵉ rᵉ)
  where

  is-idempotent-inclusion-retractionᵉ : is-idempotentᵉ (iᵉ ∘ᵉ rᵉ)
  is-idempotent-inclusion-retractionᵉ = iᵉ ·lᵉ Hᵉ ·rᵉ rᵉ
```

### Idempotence is preserved by homotopies

Ifᵉ aᵉ mapᵉ `g`ᵉ isᵉ homotopicᵉ to anᵉ idempotentᵉ mapᵉ `f`,ᵉ thenᵉ `g`ᵉ isᵉ alsoᵉ idempotent.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ gᵉ : Aᵉ → Aᵉ} (Fᵉ : is-idempotentᵉ fᵉ)
  where

  is-idempotent-htpyᵉ : gᵉ ~ᵉ fᵉ → is-idempotentᵉ gᵉ
  is-idempotent-htpyᵉ Hᵉ =
    horizontal-concat-htpyᵉ Hᵉ Hᵉ ∙hᵉ Fᵉ ∙hᵉ inv-htpyᵉ Hᵉ

  is-idempotent-inv-htpyᵉ : fᵉ ~ᵉ gᵉ → is-idempotentᵉ gᵉ
  is-idempotent-inv-htpyᵉ Hᵉ =
    horizontal-concat-htpyᵉ (inv-htpyᵉ Hᵉ) (inv-htpyᵉ Hᵉ) ∙hᵉ Fᵉ ∙hᵉ Hᵉ
```

## See also

-ᵉ [Quasicoherentlyᵉ idempotentᵉ maps](foundation.quasicoherently-idempotent-maps.mdᵉ)
-ᵉ [Splitᵉ idempotentᵉ maps](foundation.split-idempotent-maps.mdᵉ)

## References

{{#bibliographyᵉ}} {{#referenceᵉ Shu17ᵉ}} {{#referenceᵉ Shu14SplittingIdempotentsᵉ}}