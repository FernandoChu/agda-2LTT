# Rewriting rules for pushouts

```agda
{-# OPTIONSᵉ --rewritingᵉ #-}

module synthetic-homotopy-theory.rewriting-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import reflection.rewritingᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-cocones-under-spansᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
```

</details>

## Idea

Thisᵉ module endowsᵉ theᵉ eliminatorᵉ ofᵉ theᵉ
[standardᵉ pushouts](synthetic-homotopy-theory.pushouts.mdᵉ) `cogap`ᵉ with strictᵉ
computationᵉ rulesᵉ onᵉ theᵉ pointᵉ constructorsᵉ using Agda'sᵉ
[rewriting](reflection.rewriting.mdᵉ) functionality.ᵉ Thisᵉ givesᵉ theᵉ strictᵉ
equalitiesᵉ

```text
  cogapᵉ (inl-pushoutᵉ fᵉ gᵉ aᵉ) ≐ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ aᵉ
```

andᵉ

```text
  cogapᵉ (inr-pushoutᵉ fᵉ gᵉ bᵉ) ≐ᵉ vertical-map-coconeᵉ fᵉ gᵉ cᵉ b.ᵉ
```

Moreᵉ generally,ᵉ strictᵉ computationᵉ rulesᵉ forᵉ theᵉ dependentᵉ eliminatorᵉ areᵉ
enabled,ᵉ givingᵉ theᵉ strictᵉ equalitiesᵉ

```text
  dependent-cogapᵉ (inl-pushoutᵉ fᵉ gᵉ aᵉ) ≐ᵉ
  horizontal-map-dependent-coconeᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) Pᵉ cᵉ aᵉ
```

andᵉ

```text
  dependent-cogapᵉ (inr-pushoutᵉ fᵉ gᵉ bᵉ) ≐ᵉ
  vertical-map-dependent-coconeᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) Pᵉ cᵉ b.ᵉ
```

Inᵉ addition,ᵉ theᵉ pre-existingᵉ witnessesᵉ ofᵉ theseᵉ equalitiesᵉ:
`compute-inl-dependent-cogap`,ᵉ `compute-inr-dependent-cogap`,ᵉ andᵉ theirᵉ
nondependentᵉ counterparts,ᵉ reduceᵉ to `refl`.ᵉ Thisᵉ isᵉ achievedᵉ using Agda'sᵉ
[equalityᵉ erasure](reflection.erasing-equality.mdᵉ) functionality.ᵉ

Toᵉ enableᵉ theseᵉ computationᵉ rulesᵉ in yourᵉ ownᵉ formalizations,ᵉ setᵉ theᵉ
`--rewriting`ᵉ optionᵉ andᵉ import thisᵉ module.ᵉ Keepᵉ in mind,ᵉ however,ᵉ thatᵉ weᵉ
offerᵉ noᵉ wayᵉ to selectivelyᵉ disableᵉ theseᵉ rules,ᵉ soᵉ ifᵉ yourᵉ module dependsᵉ onᵉ
anyᵉ otherᵉ module thatᵉ importsᵉ thisᵉ one,ᵉ youᵉ willᵉ automaticallyᵉ alsoᵉ haveᵉ
rewritingᵉ forᵉ pushoutsᵉ enabled.ᵉ

Byᵉ default,ᵉ weᵉ abstainᵉ fromᵉ using rewriteᵉ rulesᵉ in agda-unimath.ᵉ However,ᵉ weᵉ
recognizeᵉ theirᵉ usefulnessᵉ in,ᵉ forᵉ instance,ᵉ exploratoryᵉ formalizations.ᵉ Sinceᵉ
formalizationsᵉ with andᵉ withoutᵉ rewriteᵉ rulesᵉ canᵉ coexist,ᵉ thereᵉ isᵉ noᵉ harmᵉ in
providingᵉ theseᵉ toolsᵉ forᵉ thoseᵉ thatᵉ seeᵉ aᵉ needᵉ to useᵉ them.ᵉ Weᵉ do,ᵉ however,ᵉ
emphasizeᵉ thatᵉ formalizationsᵉ withoutᵉ theᵉ useᵉ ofᵉ rewriteᵉ rulesᵉ areᵉ preferredᵉ
overᵉ thoseᵉ thatᵉ do useᵉ themᵉ in theᵉ library,ᵉ asᵉ theᵉ formerᵉ canᵉ alsoᵉ beᵉ appliedᵉ in
otherᵉ formalizationsᵉ thatᵉ do notᵉ enableᵉ rewriteᵉ rules.ᵉ

## Rewrite rules

```agda
{-# REWRITEᵉ compute-inl-dependent-cogapᵉ #-}
{-# REWRITEᵉ compute-inr-dependent-cogapᵉ #-}
```

## Properties

### Verifying the reduction behavior of the computation rules for the eliminators of standard pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Pᵉ : pushoutᵉ fᵉ gᵉ → UUᵉ l4ᵉ}
  (dᵉ : dependent-coconeᵉ fᵉ gᵉ (cocone-pushoutᵉ fᵉ gᵉ) Pᵉ)
  where

  _ : compute-inl-dependent-cogapᵉ fᵉ gᵉ dᵉ ~ᵉ refl-htpyᵉ
  _ = refl-htpyᵉ

  _ : compute-inr-dependent-cogapᵉ fᵉ gᵉ dᵉ ~ᵉ refl-htpyᵉ
  _ = refl-htpyᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  where

  _ : compute-inl-cogapᵉ fᵉ gᵉ cᵉ ~ᵉ refl-htpyᵉ
  _ = refl-htpyᵉ

  _ : compute-inr-cogapᵉ fᵉ gᵉ cᵉ ~ᵉ refl-htpyᵉ
  _ = refl-htpyᵉ
```

## See also

-ᵉ Forᵉ someᵉ discussionᵉ onᵉ strictᵉ computationᵉ rulesᵉ forᵉ higherᵉ inductive types,ᵉ
  seeᵉ theᵉ introductionᵉ to Sectionᵉ 6.2ᵉ ofᵉ {{#citeᵉ UF13}}.ᵉ

## References

{{#bibliographyᵉ}}