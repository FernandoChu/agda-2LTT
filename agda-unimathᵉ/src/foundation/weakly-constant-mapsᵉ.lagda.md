# Weakly constant maps

```agda
module foundation.weakly-constant-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.fixed-points-endofunctionsᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "weaklyᵉ constant"ᵉ Disambiguation="mapᵉ ofᵉ types"ᵉ Agda=is-weakly-constantᵉ}}
ifᵉ anyᵉ twoᵉ elementsᵉ in `A`ᵉ areᵉ mappedᵉ to
[identicalᵉ elements](foundation-core.identity-types.mdᵉ) in `B`.ᵉ

## Definitions

### The structure on a map of being weakly constant

```agda
is-weakly-constantᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-weakly-constantᵉ {Aᵉ = Aᵉ} fᵉ = (xᵉ yᵉ : Aᵉ) → fᵉ xᵉ ＝ᵉ fᵉ yᵉ
```

### The type of weakly constant maps

```agda
weakly-constant-mapᵉ : {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
weakly-constant-mapᵉ Aᵉ Bᵉ = Σᵉ (Aᵉ → Bᵉ) (is-weakly-constantᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : weakly-constant-mapᵉ Aᵉ Bᵉ)
  where

  map-weakly-constant-mapᵉ : Aᵉ → Bᵉ
  map-weakly-constant-mapᵉ = pr1ᵉ fᵉ

  is-weakly-constant-weakly-constant-mapᵉ :
    is-weakly-constantᵉ map-weakly-constant-mapᵉ
  is-weakly-constant-weakly-constant-mapᵉ = pr2ᵉ fᵉ
```

## Properties

### Being weakly constant is a property if the codomain is a set

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ)
  where

  abstract
    is-prop-is-weakly-constant-Setᵉ : is-propᵉ (is-weakly-constantᵉ fᵉ)
    is-prop-is-weakly-constant-Setᵉ =
      is-prop-iterated-Πᵉ 2 (λ xᵉ yᵉ → is-set-type-Setᵉ Bᵉ (fᵉ xᵉ) (fᵉ yᵉ))

  is-weakly-constant-prop-Setᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ is-weakly-constant-prop-Setᵉ = is-weakly-constantᵉ fᵉ
  pr2ᵉ is-weakly-constant-prop-Setᵉ = is-prop-is-weakly-constant-Setᵉ
```

### The action on identifications of a weakly constant map is weakly constant

Thisᵉ isᵉ Auxiliaryᵉ Lemmaᵉ 4.3ᵉ ofᵉ {{#citeᵉ KECA17}}.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Xᵉ → Yᵉ}
  (Wᵉ : is-weakly-constantᵉ fᵉ)
  where

  compute-ap-is-weakly-constantᵉ :
    {xᵉ yᵉ : Xᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → invᵉ (Wᵉ xᵉ xᵉ) ∙ᵉ Wᵉ xᵉ yᵉ ＝ᵉ apᵉ fᵉ pᵉ
  compute-ap-is-weakly-constantᵉ {xᵉ} reflᵉ = left-invᵉ (Wᵉ xᵉ xᵉ)

  is-weakly-constant-apᵉ : {xᵉ yᵉ : Xᵉ} → is-weakly-constantᵉ (apᵉ fᵉ {xᵉ} {yᵉ})
  is-weakly-constant-apᵉ {xᵉ} {yᵉ} pᵉ qᵉ =
    ( invᵉ (compute-ap-is-weakly-constantᵉ pᵉ)) ∙ᵉ
    ( compute-ap-is-weakly-constantᵉ qᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  (fᵉ : weakly-constant-mapᵉ Xᵉ Yᵉ)
  where

  ap-weakly-constant-mapᵉ :
    {xᵉ yᵉ : Xᵉ} →
    weakly-constant-mapᵉ
      ( xᵉ ＝ᵉ yᵉ)
      ( map-weakly-constant-mapᵉ fᵉ xᵉ ＝ᵉ map-weakly-constant-mapᵉ fᵉ yᵉ)
  ap-weakly-constant-mapᵉ {xᵉ} {yᵉ} =
    ( apᵉ (map-weakly-constant-mapᵉ fᵉ) {xᵉ} {yᵉ} ,ᵉ
      is-weakly-constant-apᵉ (is-weakly-constant-weakly-constant-mapᵉ fᵉ))
```

### The type of fixed points of a weakly constant endomap is a proposition

Thisᵉ isᵉ Lemmaᵉ 4.1ᵉ ofᵉ {{#citeᵉ KECA17}}.ᵉ Weᵉ followᵉ theᵉ secondᵉ proof,ᵉ dueᵉ to
Christianᵉ Sattler.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ : Aᵉ → Aᵉ} (Wᵉ : is-weakly-constantᵉ fᵉ)
  where

  is-proof-irrelevant-fixed-point-is-weakly-constantᵉ :
    is-proof-irrelevantᵉ (fixed-pointᵉ fᵉ)
  is-proof-irrelevant-fixed-point-is-weakly-constantᵉ (xᵉ ,ᵉ pᵉ) =
    is-contr-equivᵉ
      ( Σᵉ Aᵉ (λ zᵉ → fᵉ xᵉ ＝ᵉ zᵉ))
      ( equiv-totᵉ (λ zᵉ → equiv-concatᵉ (Wᵉ xᵉ zᵉ) zᵉ))
      ( is-torsorial-Idᵉ (fᵉ xᵉ))

  is-prop-fixed-point-is-weakly-constantᵉ : is-propᵉ (fixed-pointᵉ fᵉ)
  is-prop-fixed-point-is-weakly-constantᵉ =
    is-prop-is-proof-irrelevantᵉ
      ( is-proof-irrelevant-fixed-point-is-weakly-constantᵉ)
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ KECA17ᵉ}}