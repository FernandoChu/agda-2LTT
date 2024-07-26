# Span diagrams

```agda
module foundation.span-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.spansᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "(binaryᵉ) spanᵉ diagram"ᵉ Agda=span-diagramᵉ}} isᵉ aᵉ diagramᵉ ofᵉ theᵉ
formᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ B.ᵉ
```

Inᵉ otherᵉ words,ᵉ aᵉ spanᵉ diagramᵉ consistsᵉ ofᵉ twoᵉ typesᵉ `A`ᵉ andᵉ `B`ᵉ andᵉ aᵉ
[span](foundation.spans.mdᵉ) fromᵉ `A`ᵉ to `B`.ᵉ

Weᵉ disambiguateᵉ betweenᵉ [spans](foundation.spans.mdᵉ) andᵉ spanᵉ diagrams.ᵉ Weᵉ
considerᵉ spansᵉ fromᵉ `A`ᵉ to `B`ᵉ to beᵉ _morphismsᵉ_ fromᵉ `A`ᵉ to `B`ᵉ in theᵉ categoryᵉ
ofᵉ typesᵉ andᵉ spansᵉ betweenᵉ them,ᵉ whereasᵉ weᵉ considerᵉ spanᵉ diagramsᵉ to beᵉ
_objectsᵉ_ in theᵉ categoryᵉ ofᵉ diagramsᵉ ofᵉ typesᵉ ofᵉ theᵉ formᵉ `*ᵉ <----ᵉ *ᵉ ---->ᵉ *`.ᵉ
Conceptuallyᵉ thereᵉ isᵉ aᵉ subtle,ᵉ butᵉ importantᵉ distinctionᵉ betweenᵉ spansᵉ andᵉ spanᵉ
diagrams.ᵉ Inᵉ [binaryᵉ typeᵉ duality](foundation.binary-type-duality.mdᵉ) weᵉ showᵉ aᵉ
spanᵉ fromᵉ `A`ᵉ to `B`ᵉ isᵉ [equivalently](foundation-core.equivalences.mdᵉ)
describedᵉ asᵉ aᵉ [binaryᵉ relation](foundation.binary-relations.mdᵉ) fromᵉ `A`ᵉ to
`B`.ᵉ Onᵉ theᵉ otherᵉ hand,ᵉ spanᵉ diagramsᵉ areᵉ moreᵉ suitableᵉ forᵉ functorialᵉ
operationsᵉ thatᵉ takeᵉ "spans"ᵉ asᵉ input,ᵉ butᵉ forᵉ whichᵉ theᵉ functorialᵉ actionᵉ takesᵉ
aᵉ naturalᵉ transformation,ᵉ i.e.,ᵉ aᵉ morphismᵉ ofᵉ spanᵉ diagrams,ᵉ asᵉ input.ᵉ Examplesᵉ
ofᵉ thisᵉ kindᵉ includeᵉ [pushouts](synthetic-homotopy-theory.pushouts.md).ᵉ

### (Binary) span diagrams

```agda
span-diagramᵉ : (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ =
  Σᵉ (UUᵉ l1ᵉ) (λ Aᵉ → Σᵉ (UUᵉ l2ᵉ) (λ Bᵉ → spanᵉ l3ᵉ Aᵉ Bᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  where

  make-span-diagramᵉ :
    (Sᵉ → Aᵉ) → (Sᵉ → Bᵉ) → span-diagramᵉ l2ᵉ l3ᵉ l1ᵉ
  pr1ᵉ (make-span-diagramᵉ fᵉ gᵉ) = Aᵉ
  pr1ᵉ (pr2ᵉ (make-span-diagramᵉ fᵉ gᵉ)) = Bᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (make-span-diagramᵉ fᵉ gᵉ))) = Sᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (make-span-diagramᵉ fᵉ gᵉ)))) = fᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (make-span-diagramᵉ fᵉ gᵉ)))) = gᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  domain-span-diagramᵉ : UUᵉ l1ᵉ
  domain-span-diagramᵉ = pr1ᵉ 𝒮ᵉ

  codomain-span-diagramᵉ : UUᵉ l2ᵉ
  codomain-span-diagramᵉ = pr1ᵉ (pr2ᵉ 𝒮ᵉ)

  span-span-diagramᵉ :
    spanᵉ l3ᵉ domain-span-diagramᵉ codomain-span-diagramᵉ
  span-span-diagramᵉ = pr2ᵉ (pr2ᵉ 𝒮ᵉ)

  spanning-type-span-diagramᵉ : UUᵉ l3ᵉ
  spanning-type-span-diagramᵉ =
    spanning-type-spanᵉ span-span-diagramᵉ

  left-map-span-diagramᵉ : spanning-type-span-diagramᵉ → domain-span-diagramᵉ
  left-map-span-diagramᵉ =
    left-map-spanᵉ span-span-diagramᵉ

  right-map-span-diagramᵉ : spanning-type-span-diagramᵉ → codomain-span-diagramᵉ
  right-map-span-diagramᵉ =
    right-map-spanᵉ span-span-diagramᵉ
```

### The span diagram obtained from a morphism of arrows

Givenᵉ mapsᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ `gᵉ : Xᵉ → Y`ᵉ andᵉ aᵉ morphismᵉ ofᵉ arrowsᵉ `αᵉ : fᵉ → g`,ᵉ theᵉ
spanᵉ diagramᵉ associatedᵉ to `α`ᵉ isᵉ theᵉ spanᵉ diagramᵉ

```text
       fᵉ       α₀ᵉ
  Bᵉ <-----ᵉ Aᵉ ----->ᵉ X.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  domain-span-diagram-hom-arrowᵉ : UUᵉ l2ᵉ
  domain-span-diagram-hom-arrowᵉ = Bᵉ

  codomain-span-diagram-hom-arrowᵉ : UUᵉ l3ᵉ
  codomain-span-diagram-hom-arrowᵉ = Xᵉ

  spanning-type-hom-arrowᵉ : UUᵉ l1ᵉ
  spanning-type-hom-arrowᵉ = Aᵉ

  left-map-span-diagram-hom-arrowᵉ :
    spanning-type-hom-arrowᵉ → domain-span-diagram-hom-arrowᵉ
  left-map-span-diagram-hom-arrowᵉ = fᵉ

  right-map-span-diagram-hom-arrowᵉ :
    spanning-type-hom-arrowᵉ → codomain-span-diagram-hom-arrowᵉ
  right-map-span-diagram-hom-arrowᵉ = map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ

  span-hom-arrowᵉ :
    spanᵉ l1ᵉ Bᵉ Xᵉ
  pr1ᵉ span-hom-arrowᵉ = Aᵉ
  pr1ᵉ (pr2ᵉ span-hom-arrowᵉ) = left-map-span-diagram-hom-arrowᵉ
  pr2ᵉ (pr2ᵉ span-hom-arrowᵉ) = right-map-span-diagram-hom-arrowᵉ

  span-diagram-hom-arrowᵉ : span-diagramᵉ l2ᵉ l3ᵉ l1ᵉ
  pr1ᵉ span-diagram-hom-arrowᵉ = domain-span-diagram-hom-arrowᵉ
  pr1ᵉ (pr2ᵉ span-diagram-hom-arrowᵉ) = codomain-span-diagram-hom-arrowᵉ
  pr2ᵉ (pr2ᵉ span-diagram-hom-arrowᵉ) = span-hom-arrowᵉ
```

## See also

-ᵉ [Cospanᵉ diagrams](foundation.cospan-diagrams.mdᵉ)
-ᵉ [Diagonalᵉ spanᵉ diagrams](foundation.diagonal-span-diagrams.mdᵉ)
-ᵉ [Extensionsᵉ ofᵉ spanᵉ diagrams](foundation.operations-span-diagrams.mdᵉ)
-ᵉ [Kernelᵉ spanᵉ diagramsᵉ ofᵉ maps](foundation.kernel-span-diagrams-of-maps.mdᵉ)
-ᵉ [Spansᵉ ofᵉ familiesᵉ ofᵉ types](foundation.spans-families-of-types.mdᵉ)
-ᵉ [Transpositionᵉ ofᵉ spanᵉ diagrams](foundation.transposition-span-diagrams.mdᵉ)