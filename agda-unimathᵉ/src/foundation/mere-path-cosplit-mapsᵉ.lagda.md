# Mere path-cosplit maps

```agda
module foundation.mere-path-cosplit-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.truncated-mapsᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.truncated-typesᵉ
```

</details>

## Idea

Inᵉ Homotopyᵉ Typeᵉ Theory,ᵉ thereᵉ areᵉ multipleᵉ nonequivalentᵉ waysᵉ to stateᵉ thatᵉ aᵉ
mapᵉ isᵉ "injective"ᵉ thatᵉ areᵉ moreᵉ orᵉ lessᵉ informedᵉ byᵉ theᵉ homotopyᵉ structuresᵉ ofᵉ
itsᵉ domainᵉ andᵉ codomain.ᵉ Aᵉ
{{#conceptᵉ "mereᵉ path-cosplitᵉ map"ᵉ Disambiguation="betweenᵉ types"ᵉ Agda=is-mere-path-cosplitᵉ}}
isᵉ oneᵉ suchᵉ notion,ᵉ lyingᵉ somewhereᵉ betweenᵉ
[embeddings](foundation-core.embeddings.mdᵉ) andᵉ
[injectiveᵉ maps](foundation-core.injective-maps.md).ᵉ Inᵉ fact,ᵉ givenᵉ anᵉ integerᵉ
`kᵉ ≥ᵉ -2`,ᵉ ifᵉ weᵉ understandᵉ `k`-injectiveᵉ mapᵉ to meanᵉ theᵉ `k+2`-dimensionalᵉ
[actionᵉ onᵉ identifications](foundation.action-on-higher-identifications-functions.mdᵉ)
hasᵉ aᵉ converseᵉ map,ᵉ thenᵉ weᵉ haveᵉ properᵉ inclusionsᵉ

```text
  k-injectiveᵉ mapsᵉ ⊃ᵉ k-path-cosplitᵉ mapsᵉ ⊃ᵉ k-truncatedᵉ maps.ᵉ
```

Whileᵉ `k`-truncatednessᵉ answersᵉ theᵉ questionᵉ:

>ᵉ Atᵉ whichᵉ dimensionᵉ isᵉ theᵉ actionᵉ onᵉ higherᵉ identificationsᵉ ofᵉ aᵉ functionᵉ
>ᵉ alwaysᵉ anᵉ [equivalence](foundation-core.equivalences.md)?ᵉ

Mereᵉ `k`-path-cosplittingᵉ insteadᵉ answersᵉ theᵉ questionᵉ:

>ᵉ Atᵉ whichᵉ dimensionᵉ isᵉ theᵉ actionᵉ merelyᵉ aᵉ
>ᵉ [retract](foundation-core.retracts-of-types.md)?ᵉ

Thusᵉ aᵉ _merelyᵉ `-2`-path-cosplitᵉ mapᵉ_ isᵉ aᵉ mapᵉ thatᵉ merelyᵉ isᵉ aᵉ retract.ᵉ Aᵉ
_merelyᵉ `k+1`-path-cosplitᵉ mapᵉ_ isᵉ aᵉ mapᵉ whoseᵉ
[actionᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ)
isᵉ merelyᵉ `k`-path-cosplit.ᵉ

Weᵉ showᵉ thatᵉ mereᵉ `k`-path-cosplittnessᵉ coincidesᵉ with `k`-truncatednessᵉ whenᵉ
theᵉ codomainᵉ isᵉ `k`-truncated,ᵉ butᵉ moreᵉ generallyᵉ mereᵉ `k`-path-cosplittingᵉ mayᵉ
onlyᵉ induceᵉ mereᵉ retractsᵉ onᵉ higherᵉ homotopyᵉ groups.ᵉ

## Definitions

```agda
is-mere-path-cosplitᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-mere-path-cosplitᵉ neg-two-𝕋ᵉ fᵉ = is-inhabitedᵉ (retractionᵉ fᵉ)
is-mere-path-cosplitᵉ (succ-𝕋ᵉ kᵉ) {Aᵉ} fᵉ =
  (xᵉ yᵉ : Aᵉ) → is-mere-path-cosplitᵉ kᵉ (apᵉ fᵉ {xᵉ} {yᵉ})
```

## Properties

### Being merely path-cosplit is a property

```agda
is-prop-is-mere-path-cosplitᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-propᵉ (is-mere-path-cosplitᵉ kᵉ fᵉ)
is-prop-is-mere-path-cosplitᵉ neg-two-𝕋ᵉ fᵉ =
  is-property-is-inhabitedᵉ (retractionᵉ fᵉ)
is-prop-is-mere-path-cosplitᵉ (succ-𝕋ᵉ kᵉ) fᵉ =
  is-prop-Πᵉ (λ xᵉ → is-prop-Πᵉ λ yᵉ → is-prop-is-mere-path-cosplitᵉ kᵉ (apᵉ fᵉ))

is-mere-path-cosplit-Propᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-mere-path-cosplit-Propᵉ kᵉ fᵉ =
  (is-mere-path-cosplitᵉ kᵉ fᵉ ,ᵉ is-prop-is-mere-path-cosplitᵉ kᵉ fᵉ)
```

### If a map is `k`-truncated then it is merely `k`-path-cosplit

```agda
is-mere-path-cosplit-is-truncᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
  is-trunc-mapᵉ kᵉ fᵉ → is-mere-path-cosplitᵉ kᵉ fᵉ
is-mere-path-cosplit-is-truncᵉ neg-two-𝕋ᵉ is-trunc-fᵉ =
  unit-trunc-Propᵉ (retraction-is-contr-mapᵉ is-trunc-fᵉ)
is-mere-path-cosplit-is-truncᵉ (succ-𝕋ᵉ kᵉ) {fᵉ = fᵉ} is-trunc-fᵉ xᵉ yᵉ =
  is-mere-path-cosplit-is-truncᵉ kᵉ
    ( is-trunc-map-ap-is-trunc-mapᵉ kᵉ fᵉ is-trunc-fᵉ xᵉ yᵉ)
```

### If a map is `k`-path-cosplit then it is merely `k+1`-path-cosplit

```agda
is-mere-path-cosplit-succ-is-mere-path-cosplitᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
  is-mere-path-cosplitᵉ kᵉ fᵉ → is-mere-path-cosplitᵉ (succ-𝕋ᵉ kᵉ) fᵉ
is-mere-path-cosplit-succ-is-mere-path-cosplitᵉ
  neg-two-𝕋ᵉ {fᵉ = fᵉ} is-cosplit-fᵉ xᵉ yᵉ =
  rec-trunc-Propᵉ
    ( is-mere-path-cosplit-Propᵉ neg-two-𝕋ᵉ (apᵉ fᵉ))
    ( λ rᵉ → unit-trunc-Propᵉ (retraction-apᵉ fᵉ rᵉ))
    ( is-cosplit-fᵉ)
is-mere-path-cosplit-succ-is-mere-path-cosplitᵉ (succ-𝕋ᵉ kᵉ) is-cosplit-fᵉ xᵉ yᵉ =
  is-mere-path-cosplit-succ-is-mere-path-cosplitᵉ kᵉ (is-cosplit-fᵉ xᵉ yᵉ)
```

### If a type maps into a `k`-truncted type via a merely `k`-path-cosplit map then it is `k`-truncated

```agda
is-trunc-domain-is-mere-path-cosplit-is-trunc-codomainᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
  is-truncᵉ kᵉ Bᵉ → is-mere-path-cosplitᵉ kᵉ fᵉ → is-truncᵉ kᵉ Aᵉ
is-trunc-domain-is-mere-path-cosplit-is-trunc-codomainᵉ neg-two-𝕋ᵉ
  {Aᵉ} {Bᵉ} {fᵉ} is-trunc-Bᵉ =
  rec-trunc-Propᵉ
    ( is-trunc-Propᵉ neg-two-𝕋ᵉ Aᵉ)
    ( λ rᵉ → is-trunc-retract-ofᵉ (fᵉ ,ᵉ rᵉ) is-trunc-Bᵉ)
is-trunc-domain-is-mere-path-cosplit-is-trunc-codomainᵉ
  (succ-𝕋ᵉ kᵉ) {Aᵉ} {Bᵉ} {fᵉ} is-trunc-Bᵉ is-cosplit-fᵉ xᵉ yᵉ =
  is-trunc-domain-is-mere-path-cosplit-is-trunc-codomainᵉ kᵉ
    ( is-trunc-Bᵉ (fᵉ xᵉ) (fᵉ yᵉ))
    ( is-cosplit-fᵉ xᵉ yᵉ)
```

Thisᵉ resultᵉ generalizesᵉ theᵉ followingᵉ statementsᵉ:

-ᵉ Aᵉ typeᵉ thatᵉ injectsᵉ intoᵉ aᵉ setᵉ isᵉ aᵉ set.ᵉ

-ᵉ Aᵉ typeᵉ thatᵉ embedsᵉ intoᵉ aᵉ `k+1`-truncatedᵉ typeᵉ isᵉ `k+1`-truncated.ᵉ

-ᵉ Aᵉ typeᵉ thatᵉ mapsᵉ intoᵉ aᵉ `k`-truncatedᵉ typeᵉ viaᵉ aᵉ `k`-truncatedᵉ mapᵉ isᵉ
  `k`-truncated.ᵉ

### If the codomain of a mere `k`-path-cosplit map is `k`-truncated then the map is `k`-truncated

```agda
is-trunc-map-is-mere-path-cosplit-is-trunc-codomainᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
  is-truncᵉ kᵉ Bᵉ → is-mere-path-cosplitᵉ kᵉ fᵉ → is-trunc-mapᵉ kᵉ fᵉ
is-trunc-map-is-mere-path-cosplit-is-trunc-codomainᵉ kᵉ is-trunc-Bᵉ is-cosplit-fᵉ =
  is-trunc-map-is-trunc-domain-codomainᵉ kᵉ
    ( is-trunc-domain-is-mere-path-cosplit-is-trunc-codomainᵉ kᵉ
      ( is-trunc-Bᵉ)
      ( is-cosplit-fᵉ))
    ( is-trunc-Bᵉ)
```

## See also

-ᵉ [Path-cosplitᵉ maps](foundation.path-cosplit-maps.mdᵉ)
-ᵉ [Path-splitᵉ maps](foundation.path-cosplit-maps.mdᵉ)
-ᵉ [Injectiveᵉ maps](foundation-core.injective-maps.mdᵉ)
-ᵉ [Truncatedᵉ maps](foundation-core.truncated-maps.mdᵉ)
-ᵉ [Embeddings](foundation-core.embeddings.mdᵉ)