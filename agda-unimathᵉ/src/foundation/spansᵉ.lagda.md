# Spans of types

```agda
module foundation.spansᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.function-typesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "binaryᵉ span"ᵉ Agda=spanᵉ}} fromᵉ `A`ᵉ to `B`ᵉ consistsᵉ ofᵉ aᵉ
{{#conceptᵉ "spanningᵉ type"ᵉ Disambiguation="binaryᵉ span"ᵉ Agda=spanning-type-spanᵉ}}
`S`ᵉ andᵉ aᵉ [pair](foundation.dependent-pair-types.mdᵉ) ofᵉ functionsᵉ `fᵉ : Sᵉ → A`ᵉ
andᵉ `gᵉ : Sᵉ → B`.ᵉ Theᵉ typesᵉ `A`ᵉ andᵉ `B`ᵉ in theᵉ specificationᵉ ofᵉ aᵉ binaryᵉ spanᵉ areᵉ
alsoᵉ referredᵉ to asᵉ theᵉ {{#conceptᵉ "domain"ᵉ Disambiguation="binaryᵉ span"ᵉ}} andᵉ
{{#conceptᵉ "codomain"ᵉ Disambiguation="binaryᵉ span"ᵉ}} ofᵉ theᵉ span,ᵉ respectively.ᵉ

Inᵉ [`foundation.binary-type-duality`](foundation.binary-type-duality.mdᵉ) weᵉ showᵉ
thatᵉ [binaryᵉ relations](foundation.binary-relations.mdᵉ) areᵉ equivalentlyᵉ
describedᵉ asᵉ spansᵉ ofᵉ types.ᵉ

Weᵉ disambiguateᵉ betweenᵉ spansᵉ andᵉ [spanᵉ diagrams](foundation.span-diagrams.md).ᵉ
Weᵉ considerᵉ spansᵉ fromᵉ `A`ᵉ to `B`ᵉ to beᵉ _morphismsᵉ_ fromᵉ `A`ᵉ to `B`ᵉ in theᵉ
categoryᵉ ofᵉ typesᵉ andᵉ spansᵉ betweenᵉ them,ᵉ whereasᵉ weᵉ considerᵉ spanᵉ diagramsᵉ to
beᵉ _objectsᵉ_ in theᵉ categoryᵉ ofᵉ diagramsᵉ ofᵉ typesᵉ ofᵉ theᵉ formᵉ
`*ᵉ <----ᵉ *ᵉ ---->ᵉ *`.ᵉ Conceptuallyᵉ thereᵉ isᵉ aᵉ subtle,ᵉ butᵉ importantᵉ distinctionᵉ
betweenᵉ spansᵉ andᵉ spanᵉ diagrams.ᵉ Asᵉ mentionedᵉ previously,ᵉ aᵉ spanᵉ fromᵉ `A`ᵉ to `B`ᵉ
isᵉ equivalentlyᵉ describedᵉ asᵉ aᵉ binaryᵉ relationᵉ fromᵉ `A`ᵉ to `B`.ᵉ Onᵉ theᵉ otherᵉ
hand,ᵉ spanᵉ diagramsᵉ areᵉ moreᵉ suitableᵉ forᵉ functorialᵉ operationsᵉ thatᵉ takeᵉ
"spans"ᵉ asᵉ input,ᵉ butᵉ forᵉ whichᵉ theᵉ functorialᵉ actionᵉ takesᵉ aᵉ naturalᵉ
transformation,ᵉ i.e.,ᵉ aᵉ morphismᵉ ofᵉ spanᵉ diagrams,ᵉ asᵉ input.ᵉ Examplesᵉ ofᵉ thisᵉ
kindᵉ includeᵉ [pushouts](synthetic-homotopy-theory.pushouts.md).ᵉ

## Definitions

### (Binary) spans

```agda
spanᵉ :
  {l1ᵉ l2ᵉ : Level} (lᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
spanᵉ lᵉ Aᵉ Bᵉ = Σᵉ (UUᵉ lᵉ) (λ Xᵉ → (Xᵉ → Aᵉ) ×ᵉ (Xᵉ → Bᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (cᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ)
  where

  spanning-type-spanᵉ : UUᵉ l3ᵉ
  spanning-type-spanᵉ = pr1ᵉ cᵉ

  left-map-spanᵉ : spanning-type-spanᵉ → Aᵉ
  left-map-spanᵉ = pr1ᵉ (pr2ᵉ cᵉ)

  right-map-spanᵉ : spanning-type-spanᵉ → Bᵉ
  right-map-spanᵉ = pr2ᵉ (pr2ᵉ cᵉ)
```

### Identity spans

```agda
module _
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ}
  where

  id-spanᵉ : spanᵉ l1ᵉ Xᵉ Xᵉ
  pr1ᵉ id-spanᵉ = Xᵉ
  pr1ᵉ (pr2ᵉ id-spanᵉ) = idᵉ
  pr2ᵉ (pr2ᵉ id-spanᵉ) = idᵉ
```

## See also

-ᵉ [Binaryᵉ typeᵉ duality](foundation.binary-type-duality.mdᵉ)
-ᵉ [Cospans](foundation.cospans.mdᵉ)
-ᵉ [Spanᵉ diagrams](foundation.span-diagrams.mdᵉ)
-ᵉ [Spansᵉ ofᵉ familiesᵉ ofᵉ types](foundation.spans-families-of-types.mdᵉ)
-ᵉ [Spansᵉ ofᵉ pointedᵉ types](structured-types.pointed-spans.mdᵉ)