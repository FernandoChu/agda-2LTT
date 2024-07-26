# Commuting triangles of identifications

```agda
module foundation.commuting-triangles-of-identificationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import foundation-core.commuting-squares-of-identificationsᵉ
open import foundation-core.equivalencesᵉ
```

</details>

## Idea

Aᵉ triangleᵉ ofᵉ [identifications](foundation-core.identity-types.mdᵉ)

```text
        topᵉ
     xᵉ ---->ᵉ yᵉ
      \ᵉ     /ᵉ
  leftᵉ \ᵉ   /ᵉ rightᵉ
        ∨ᵉ ∨ᵉ
         zᵉ
```

isᵉ saidᵉ to **commute**ᵉ ifᵉ thereᵉ isᵉ anᵉ identificationᵉ `pᵉ ＝ᵉ qᵉ ∙ᵉ r`.ᵉ

## Definitions

### Commuting triangles of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ}
  where

  coherence-triangle-identificationsᵉ :
    (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ zᵉ) (topᵉ : xᵉ ＝ᵉ yᵉ) → UUᵉ lᵉ
  coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ = leftᵉ ＝ᵉ topᵉ ∙ᵉ rightᵉ

  coherence-triangle-identifications'ᵉ :
    (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ zᵉ) (topᵉ : xᵉ ＝ᵉ yᵉ) → UUᵉ lᵉ
  coherence-triangle-identifications'ᵉ leftᵉ rightᵉ topᵉ = topᵉ ∙ᵉ rightᵉ ＝ᵉ leftᵉ
```

### The horizontally constant triangle of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ}
  where

  horizontal-refl-coherence-triangle-identificationsᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) → coherence-triangle-identificationsᵉ pᵉ pᵉ reflᵉ
  horizontal-refl-coherence-triangle-identificationsᵉ pᵉ = reflᵉ
```

## Properties

### Whiskering of triangles of identifications

Givenᵉ aᵉ commutingᵉ triangleᵉ ofᵉ identificationsᵉ

```text
        topᵉ
     xᵉ ---->ᵉ yᵉ
      \ᵉ     /ᵉ
  leftᵉ \ᵉ   /ᵉ rightᵉ
        ∨ᵉ ∨ᵉ
         z,ᵉ
```

weᵉ mayᵉ considerᵉ threeᵉ waysᵉ ofᵉ attachingᵉ newᵉ identificationsᵉ to itᵉ:

1.ᵉ Prependingᵉ `pᵉ : uᵉ ＝ᵉ x`ᵉ to theᵉ leftᵉ givesᵉ usᵉ aᵉ commutingᵉ triangleᵉ

   ```text
             pᵉ ∙ᵉ topᵉ
            uᵉ ---->ᵉ yᵉ
             \ᵉ     /ᵉ
     pᵉ ∙ᵉ leftᵉ \ᵉ   /ᵉ rightᵉ
               ∨ᵉ ∨ᵉ
                z.ᵉ
   ```

   Inᵉ otherᵉ words,ᵉ weᵉ haveᵉ aᵉ mapᵉ

   ```text
     (leftᵉ ＝ᵉ topᵉ ∙ᵉ rightᵉ) → (pᵉ ∙ᵉ leftᵉ ＝ᵉ (pᵉ ∙ᵉ topᵉ) ∙ᵉ right).ᵉ
   ```

2.ᵉ Appendingᵉ anᵉ identificationᵉ `pᵉ : zᵉ ＝ᵉ u`ᵉ to theᵉ rightᵉ givesᵉ aᵉ commutingᵉ
   triangleᵉ ofᵉ identificationsᵉ

   ```text
               topᵉ
            xᵉ ---->ᵉ yᵉ
             \ᵉ     /ᵉ
     leftᵉ ∙ᵉ pᵉ \ᵉ   /ᵉ rightᵉ ∙ᵉ pᵉ
               ∨ᵉ ∨ᵉ
                u.ᵉ
   ```

   Inᵉ otherᵉ words,ᵉ weᵉ haveᵉ aᵉ mapᵉ

   ```text
     (leftᵉ ＝ᵉ topᵉ ∙ᵉ rightᵉ) → (leftᵉ ∙ᵉ pᵉ ＝ᵉ topᵉ ∙ᵉ (rightᵉ ∙ᵉ p)).ᵉ

   ```

3.ᵉ Splicingᵉ anᵉ identificationᵉ `pᵉ : yᵉ ＝ᵉ u`ᵉ andᵉ itsᵉ inverseᵉ intoᵉ theᵉ middleᵉ givesᵉ
   aᵉ commutingᵉ triangleᵉ ofᵉ identificationsᵉ

   ```text
         topᵉ ∙ᵉ pᵉ
        xᵉ ---->ᵉ uᵉ
         \ᵉ     /ᵉ
     leftᵉ \ᵉ   /ᵉ p⁻¹ᵉ ∙ᵉ rightᵉ
           ∨ᵉ ∨ᵉ
            z.ᵉ
   ```

   Inᵉ otherᵉ words,ᵉ weᵉ haveᵉ aᵉ mapᵉ

   ```text
     (leftᵉ ＝ᵉ topᵉ ∙ᵉ rightᵉ) → leftᵉ ＝ᵉ (topᵉ ∙ᵉ pᵉ) ∙ᵉ (p⁻¹ᵉ ∙ᵉ right).ᵉ
   ```

   Similarly,ᵉ weᵉ haveᵉ aᵉ mapᵉ

   ```text
     (leftᵉ ＝ᵉ topᵉ ∙ᵉ rightᵉ) → leftᵉ ＝ᵉ (topᵉ ∙ᵉ p⁻¹ᵉ) ∙ᵉ (pᵉ ∙ᵉ right).ᵉ
   ```

Becauseᵉ concatenationᵉ ofᵉ identificationsᵉ isᵉ anᵉ
[equivalence](foundation-core.equivalences.md),ᵉ itᵉ followsᵉ thatᵉ allᵉ ofᵉ theseᵉ
transformationsᵉ areᵉ equivalences.ᵉ

Theseᵉ operationsᵉ areᵉ usefulᵉ in proofsᵉ involvingᵉ
[pathᵉ algebra](foundation.path-algebra.md),ᵉ becauseᵉ takingᵉ
`equiv-right-whisker-triangle-identifications`ᵉ asᵉ anᵉ example,ᵉ itᵉ providesᵉ usᵉ
with twoᵉ mapsᵉ: theᵉ forwardᵉ directionᵉ statesᵉ
`(pᵉ ＝ᵉ qᵉ ∙ᵉ rᵉ) → (pᵉ ∙ᵉ sᵉ ＝ᵉ qᵉ ∙ᵉ (rᵉ ∙ᵉ s))`,ᵉ whichᵉ allowsᵉ oneᵉ to appendᵉ anᵉ
identificationᵉ withoutᵉ needingᵉ to reassociateᵉ onᵉ theᵉ right,ᵉ andᵉ theᵉ backwardsᵉ
directionᵉ converselyᵉ allowsᵉ oneᵉ to cancelᵉ outᵉ anᵉ identificationᵉ in parentheses.ᵉ

#### Left whiskering commuting squares of identifications

Thereᵉ isᵉ anᵉ equivalenceᵉ ofᵉ commutingᵉ squaresᵉ

```text
        topᵉ                        pᵉ ∙ᵉ topᵉ
     xᵉ ---->ᵉ yᵉ                    uᵉ ---->ᵉ yᵉ
      \ᵉ     /ᵉ                      \ᵉ     /ᵉ
  leftᵉ \ᵉ   /ᵉ rightᵉ    ≃ᵉ    pᵉ ∙ᵉ leftᵉ \ᵉ   /ᵉ rightᵉ
        ∨ᵉ ∨ᵉ                          ∨ᵉ ∨ᵉ
         zᵉ                            zᵉ
```

forᵉ anyᵉ identificationᵉ `pᵉ : uᵉ ＝ᵉ x`.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ uᵉ : Aᵉ}
  (pᵉ : uᵉ ＝ᵉ xᵉ) (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ zᵉ) (topᵉ : xᵉ ＝ᵉ yᵉ)
  where

  equiv-left-whisker-concat-coherence-triangle-identificationsᵉ :
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ ≃ᵉ
    coherence-triangle-identificationsᵉ (pᵉ ∙ᵉ leftᵉ) rightᵉ (pᵉ ∙ᵉ topᵉ)
  equiv-left-whisker-concat-coherence-triangle-identificationsᵉ =
    ( equiv-inv-concat'ᵉ _ (assocᵉ pᵉ topᵉ rightᵉ)) ∘eᵉ
    ( equiv-left-whisker-concatᵉ pᵉ)

  left-whisker-concat-coherence-triangle-identificationsᵉ :
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ →
    coherence-triangle-identificationsᵉ (pᵉ ∙ᵉ leftᵉ) rightᵉ (pᵉ ∙ᵉ topᵉ)
  left-whisker-concat-coherence-triangle-identificationsᵉ =
    map-equivᵉ equiv-left-whisker-concat-coherence-triangle-identificationsᵉ

  left-unwhisker-concat-coherence-triangle-identificationsᵉ :
    coherence-triangle-identificationsᵉ (pᵉ ∙ᵉ leftᵉ) rightᵉ (pᵉ ∙ᵉ topᵉ) →
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ
  left-unwhisker-concat-coherence-triangle-identificationsᵉ =
    map-inv-equivᵉ equiv-left-whisker-concat-coherence-triangle-identificationsᵉ

  is-equiv-left-whisker-concat-coherence-triangle-identificationsᵉ :
    is-equivᵉ
      ( left-whisker-concat-coherence-triangle-identificationsᵉ)
  is-equiv-left-whisker-concat-coherence-triangle-identificationsᵉ =
    is-equiv-map-equivᵉ
      equiv-left-whisker-concat-coherence-triangle-identificationsᵉ

  equiv-left-whisker-concat-coherence-triangle-identifications'ᵉ :
    coherence-triangle-identifications'ᵉ leftᵉ rightᵉ topᵉ ≃ᵉ
    coherence-triangle-identifications'ᵉ (pᵉ ∙ᵉ leftᵉ) rightᵉ (pᵉ ∙ᵉ topᵉ)
  equiv-left-whisker-concat-coherence-triangle-identifications'ᵉ =
    ( equiv-concatᵉ (assocᵉ pᵉ topᵉ rightᵉ) _) ∘eᵉ
    ( equiv-left-whisker-concatᵉ pᵉ)

  left-whisker-concat-coherence-triangle-identifications'ᵉ :
    coherence-triangle-identifications'ᵉ leftᵉ rightᵉ topᵉ →
    coherence-triangle-identifications'ᵉ (pᵉ ∙ᵉ leftᵉ) rightᵉ (pᵉ ∙ᵉ topᵉ)
  left-whisker-concat-coherence-triangle-identifications'ᵉ =
    map-equivᵉ equiv-left-whisker-concat-coherence-triangle-identifications'ᵉ

  left-unwhisker-concat-coherence-triangle-identifications'ᵉ :
    coherence-triangle-identifications'ᵉ (pᵉ ∙ᵉ leftᵉ) rightᵉ (pᵉ ∙ᵉ topᵉ) →
    coherence-triangle-identifications'ᵉ leftᵉ rightᵉ topᵉ
  left-unwhisker-concat-coherence-triangle-identifications'ᵉ =
    map-inv-equivᵉ equiv-left-whisker-concat-coherence-triangle-identifications'ᵉ

  is-equiv-left-whisker-concat-coherence-triangle-identifications'ᵉ :
    is-equivᵉ left-whisker-concat-coherence-triangle-identifications'ᵉ
  is-equiv-left-whisker-concat-coherence-triangle-identifications'ᵉ =
    is-equiv-map-equivᵉ
      equiv-left-whisker-concat-coherence-triangle-identifications'ᵉ
```

#### Right whiskering commuting squares of identifications

Thereᵉ isᵉ anᵉ equivalenceᵉ ofᵉ commutingᵉ trianglesᵉ ofᵉ identificationsᵉ

```text
        topᵉ                            topᵉ
     xᵉ ---->ᵉ yᵉ                      xᵉ ---->ᵉ yᵉ
      \ᵉ     /ᵉ                        \ᵉ     /ᵉ
  leftᵉ \ᵉ   /ᵉ rightᵉ     ≃ᵉ     leftᵉ ∙ᵉ pᵉ \ᵉ   /ᵉ rightᵉ ∙ᵉ pᵉ
        ∨ᵉ ∨ᵉ                            ∨ᵉ ∨ᵉ
         zᵉ                              uᵉ
```

forᵉ anyᵉ identificationᵉ `pᵉ : zᵉ ＝ᵉ u`.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ uᵉ : Aᵉ}
  (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ zᵉ) (topᵉ : xᵉ ＝ᵉ yᵉ) (pᵉ : zᵉ ＝ᵉ uᵉ)
  where

  equiv-right-whisker-concat-coherence-triangle-identificationsᵉ :
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ ≃ᵉ
    coherence-triangle-identificationsᵉ (leftᵉ ∙ᵉ pᵉ) (rightᵉ ∙ᵉ pᵉ) topᵉ
  equiv-right-whisker-concat-coherence-triangle-identificationsᵉ =
    ( equiv-concat-assoc'ᵉ (leftᵉ ∙ᵉ pᵉ) topᵉ rightᵉ pᵉ) ∘eᵉ
    ( equiv-right-whisker-concatᵉ pᵉ)

  right-whisker-concat-coherence-triangle-identificationsᵉ :
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ →
    coherence-triangle-identificationsᵉ (leftᵉ ∙ᵉ pᵉ) (rightᵉ ∙ᵉ pᵉ) topᵉ
  right-whisker-concat-coherence-triangle-identificationsᵉ =
    map-equivᵉ equiv-right-whisker-concat-coherence-triangle-identificationsᵉ

  right-unwhisker-concat-coherence-triangle-identificationsᵉ :
    coherence-triangle-identificationsᵉ (leftᵉ ∙ᵉ pᵉ) (rightᵉ ∙ᵉ pᵉ) topᵉ →
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ
  right-unwhisker-concat-coherence-triangle-identificationsᵉ =
    map-inv-equivᵉ equiv-right-whisker-concat-coherence-triangle-identificationsᵉ

  is-equiv-right-whisker-concat-coherence-triangle-identificationsᵉ :
    is-equivᵉ right-whisker-concat-coherence-triangle-identificationsᵉ
  is-equiv-right-whisker-concat-coherence-triangle-identificationsᵉ =
    is-equiv-map-equivᵉ
      equiv-right-whisker-concat-coherence-triangle-identificationsᵉ

  equiv-right-whisker-concat-coherence-triangle-identifications'ᵉ :
    coherence-triangle-identifications'ᵉ leftᵉ rightᵉ topᵉ ≃ᵉ
    coherence-triangle-identifications'ᵉ (leftᵉ ∙ᵉ pᵉ) (rightᵉ ∙ᵉ pᵉ) topᵉ
  equiv-right-whisker-concat-coherence-triangle-identifications'ᵉ =
    ( equiv-concat-assocᵉ topᵉ rightᵉ pᵉ (leftᵉ ∙ᵉ pᵉ)) ∘eᵉ
    ( equiv-right-whisker-concatᵉ pᵉ)

  right-whisker-concat-coherence-triangle-identifications'ᵉ :
    coherence-triangle-identifications'ᵉ leftᵉ rightᵉ topᵉ →
    coherence-triangle-identifications'ᵉ (leftᵉ ∙ᵉ pᵉ) (rightᵉ ∙ᵉ pᵉ) topᵉ
  right-whisker-concat-coherence-triangle-identifications'ᵉ =
    map-equivᵉ equiv-right-whisker-concat-coherence-triangle-identifications'ᵉ

  right-unwhisker-concat-coherence-triangle-identifications'ᵉ :
    coherence-triangle-identifications'ᵉ (leftᵉ ∙ᵉ pᵉ) (rightᵉ ∙ᵉ pᵉ) topᵉ →
    coherence-triangle-identifications'ᵉ leftᵉ rightᵉ topᵉ
  right-unwhisker-concat-coherence-triangle-identifications'ᵉ =
    map-inv-equivᵉ equiv-right-whisker-concat-coherence-triangle-identifications'ᵉ

  is-equiv-right-whisker-concat-coherence-triangle-identifications'ᵉ :
    is-equivᵉ right-whisker-concat-coherence-triangle-identifications'ᵉ
  is-equiv-right-whisker-concat-coherence-triangle-identifications'ᵉ =
    is-equiv-map-equivᵉ
      equiv-right-whisker-concat-coherence-triangle-identifications'ᵉ
```

#### Splicing a pair of mutual inverse identifications in a commuting triangle of identifications

Considerᵉ twoᵉ identificationsᵉ `pᵉ : yᵉ ＝ᵉ u`ᵉ andᵉ `qᵉ : uᵉ ＝ᵉ y`ᵉ equippedᵉ with anᵉ
identificationᵉ `αᵉ : invᵉ pᵉ ＝ᵉ q`.ᵉ Thenᵉ weᵉ haveᵉ anᵉ equivalenceᵉ ofᵉ commutingᵉ
trianglesᵉ ofᵉ identificationsᵉ

```text
        topᵉ                       topᵉ ∙ᵉ pᵉ
     xᵉ ---->ᵉ yᵉ                   xᵉ ---->ᵉ uᵉ
      \ᵉ     /ᵉ                     \ᵉ     /ᵉ
  leftᵉ \ᵉ   /ᵉ rightᵉ     ≃ᵉ     leftᵉ  \ᵉ   /ᵉ qᵉ ∙ᵉ rightᵉ
        ∨ᵉ ∨ᵉ                         ∨ᵉ ∨ᵉ
         zᵉ                           z.ᵉ
```

Noteᵉ thatᵉ weᵉ haveᵉ formulatedᵉ theᵉ equivalenceᵉ in suchᵉ aᵉ wayᵉ thatᵉ itᵉ givesᵉ usᵉ bothᵉ
equivalencesᵉ

```text
  (leftᵉ ＝ᵉ topᵉ ∙ᵉ rightᵉ) ≃ᵉ (leftᵉ ＝ᵉ (topᵉ ∙ᵉ pᵉ) ∙ᵉ (p⁻¹ᵉ ∙ᵉ right)),ᵉ
```

andᵉ

```text
  (leftᵉ ＝ᵉ topᵉ ∙ᵉ rightᵉ) ≃ᵉ (leftᵉ ＝ᵉ (topᵉ ∙ᵉ p⁻¹ᵉ) ∙ᵉ (pᵉ ∙ᵉ rightᵉ))
```

withoutᵉ furtherᵉ ado.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ uᵉ : Aᵉ}
  where

  equiv-splice-coherence-triangle-identificationsᵉ :
    (pᵉ : yᵉ ＝ᵉ uᵉ) (qᵉ : uᵉ ＝ᵉ yᵉ) (αᵉ : invᵉ pᵉ ＝ᵉ qᵉ) →
    (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ zᵉ) (topᵉ : xᵉ ＝ᵉ yᵉ) →
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ ≃ᵉ
    coherence-triangle-identificationsᵉ leftᵉ (qᵉ ∙ᵉ rightᵉ) (topᵉ ∙ᵉ pᵉ)
  equiv-splice-coherence-triangle-identificationsᵉ reflᵉ .reflᵉ reflᵉ
    leftᵉ rightᵉ topᵉ =
    equiv-concat'ᵉ leftᵉ (right-whisker-concatᵉ (invᵉ right-unitᵉ) rightᵉ)

  splice-coherence-triangle-identificationsᵉ :
    (pᵉ : yᵉ ＝ᵉ uᵉ) (qᵉ : uᵉ ＝ᵉ yᵉ) (αᵉ : invᵉ pᵉ ＝ᵉ qᵉ) →
    (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ zᵉ) (topᵉ : xᵉ ＝ᵉ yᵉ) →
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ →
    coherence-triangle-identificationsᵉ leftᵉ (qᵉ ∙ᵉ rightᵉ) (topᵉ ∙ᵉ pᵉ)
  splice-coherence-triangle-identificationsᵉ reflᵉ .reflᵉ reflᵉ
    leftᵉ rightᵉ topᵉ tᵉ =
    tᵉ ∙ᵉ invᵉ (right-whisker-concatᵉ right-unitᵉ rightᵉ)

  unsplice-coherence-triangle-identificationsᵉ :
    (pᵉ : yᵉ ＝ᵉ uᵉ) (qᵉ : uᵉ ＝ᵉ yᵉ) (αᵉ : invᵉ pᵉ ＝ᵉ qᵉ) →
    (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ zᵉ) (topᵉ : xᵉ ＝ᵉ yᵉ) →
    coherence-triangle-identificationsᵉ leftᵉ (qᵉ ∙ᵉ rightᵉ) (topᵉ ∙ᵉ pᵉ) →
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ
  unsplice-coherence-triangle-identificationsᵉ reflᵉ .reflᵉ reflᵉ
    leftᵉ rightᵉ topᵉ tᵉ =
    tᵉ ∙ᵉ right-whisker-concatᵉ right-unitᵉ rightᵉ

  equiv-splice-coherence-triangle-identifications'ᵉ :
    (pᵉ : yᵉ ＝ᵉ uᵉ) (qᵉ : uᵉ ＝ᵉ yᵉ) (αᵉ : invᵉ pᵉ ＝ᵉ qᵉ) →
    (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ zᵉ) (topᵉ : xᵉ ＝ᵉ yᵉ) →
    coherence-triangle-identifications'ᵉ leftᵉ rightᵉ topᵉ ≃ᵉ
    coherence-triangle-identifications'ᵉ leftᵉ (qᵉ ∙ᵉ rightᵉ) (topᵉ ∙ᵉ pᵉ)
  equiv-splice-coherence-triangle-identifications'ᵉ reflᵉ .reflᵉ reflᵉ
    leftᵉ rightᵉ topᵉ =
    equiv-concatᵉ (right-whisker-concatᵉ right-unitᵉ rightᵉ) leftᵉ

  splice-coherence-triangle-identifications'ᵉ :
    (pᵉ : yᵉ ＝ᵉ uᵉ) (qᵉ : uᵉ ＝ᵉ yᵉ) (αᵉ : invᵉ pᵉ ＝ᵉ qᵉ) →
    (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ zᵉ) (topᵉ : xᵉ ＝ᵉ yᵉ) →
    coherence-triangle-identifications'ᵉ leftᵉ rightᵉ topᵉ →
    coherence-triangle-identifications'ᵉ leftᵉ (qᵉ ∙ᵉ rightᵉ) (topᵉ ∙ᵉ pᵉ)
  splice-coherence-triangle-identifications'ᵉ reflᵉ .reflᵉ reflᵉ
    leftᵉ rightᵉ topᵉ tᵉ =
    right-whisker-concatᵉ right-unitᵉ rightᵉ ∙ᵉ tᵉ

  unsplice-coherence-triangle-identifications'ᵉ :
    (pᵉ : yᵉ ＝ᵉ uᵉ) (qᵉ : uᵉ ＝ᵉ yᵉ) (αᵉ : invᵉ pᵉ ＝ᵉ qᵉ) →
    (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ zᵉ) (topᵉ : xᵉ ＝ᵉ yᵉ) →
    coherence-triangle-identifications'ᵉ leftᵉ (qᵉ ∙ᵉ rightᵉ) (topᵉ ∙ᵉ pᵉ) →
    coherence-triangle-identifications'ᵉ leftᵉ rightᵉ topᵉ
  unsplice-coherence-triangle-identifications'ᵉ reflᵉ .reflᵉ reflᵉ
    leftᵉ rightᵉ topᵉ tᵉ =
    invᵉ (right-whisker-concatᵉ right-unitᵉ rightᵉ) ∙ᵉ tᵉ
```

### The action of functions on commuting triangles of identifications

Considerᵉ aᵉ commutingᵉ triangleᵉ ofᵉ identificationsᵉ

```text
        topᵉ
     xᵉ ---->ᵉ yᵉ
      \ᵉ     /ᵉ
  leftᵉ \ᵉ   /ᵉ rightᵉ
        ∨ᵉ ∨ᵉ
         zᵉ
```

in aᵉ typeᵉ `A`ᵉ andᵉ considerᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`.ᵉ Thenᵉ weᵉ obtainᵉ aᵉ commutingᵉ
triangleᵉ ofᵉ identificationsᵉ

```text
          apᵉ fᵉ topᵉ
        fᵉ xᵉ ---->ᵉ fᵉ yᵉ
           \ᵉ     /ᵉ
  apᵉ fᵉ leftᵉ \ᵉ   /ᵉ apᵉ fᵉ rightᵉ
             ∨ᵉ ∨ᵉ
             fᵉ zᵉ
```

Furthermore,ᵉ in theᵉ caseᵉ where theᵉ identificationᵉ `right`ᵉ isᵉ `refl`ᵉ weᵉ obtainᵉ anᵉ
identificationᵉ

```text
  invᵉ right-unitᵉ ＝ᵉ
  map-coherence-triangle-identificationsᵉ pᵉ reflᵉ pᵉ (invᵉ right-unitᵉ)
```

andᵉ in theᵉ caseᵉ where theᵉ identificationᵉ `top`ᵉ isᵉ `refl`ᵉ weᵉ obtainᵉ

```text
  reflᵉ ＝ᵉ map-coherence-triangle-identificationsᵉ pᵉ pᵉ reflᵉ refl.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  map-coherence-triangle-identificationsᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ zᵉ) (topᵉ : xᵉ ＝ᵉ yᵉ) →
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ →
    coherence-triangle-identificationsᵉ (apᵉ fᵉ leftᵉ) (apᵉ fᵉ rightᵉ) (apᵉ fᵉ topᵉ)
  map-coherence-triangle-identificationsᵉ .(topᵉ ∙ᵉ rightᵉ) rightᵉ topᵉ reflᵉ =
    ap-concatᵉ fᵉ topᵉ rightᵉ

  compute-refl-right-map-coherence-triangle-identificationsᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
    invᵉ right-unitᵉ ＝ᵉ
    map-coherence-triangle-identificationsᵉ pᵉ reflᵉ pᵉ (invᵉ right-unitᵉ)
  compute-refl-right-map-coherence-triangle-identificationsᵉ reflᵉ = reflᵉ

  compute-refl-top-map-coherence-triangle-identificationsᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
    reflᵉ ＝ᵉ map-coherence-triangle-identificationsᵉ pᵉ pᵉ reflᵉ reflᵉ
  compute-refl-top-map-coherence-triangle-identificationsᵉ pᵉ = reflᵉ
```

### Inverting one side of a commuting triangle of identifications

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  transpose-top-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ cᵉ) (topᵉ : bᵉ ＝ᵉ aᵉ)
    {top'ᵉ : aᵉ ＝ᵉ bᵉ} (αᵉ : invᵉ topᵉ ＝ᵉ top'ᵉ) →
    coherence-triangle-identificationsᵉ rightᵉ leftᵉ topᵉ →
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ top'ᵉ
  transpose-top-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ reflᵉ tᵉ =
    left-transpose-eq-concatᵉ _ _ _ (invᵉ tᵉ)

  equiv-transpose-top-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ cᵉ) (topᵉ : bᵉ ＝ᵉ aᵉ) →
    coherence-triangle-identificationsᵉ rightᵉ leftᵉ topᵉ ≃ᵉ
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ (invᵉ topᵉ)
  equiv-transpose-top-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ =
    equiv-left-transpose-eq-concatᵉ _ _ _ ∘eᵉ equiv-invᵉ _ _

  equiv-higher-transpose-top-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ cᵉ) (topᵉ : bᵉ ＝ᵉ aᵉ)
    {left'ᵉ : aᵉ ＝ᵉ cᵉ} (pᵉ : leftᵉ ＝ᵉ left'ᵉ)
    {top'ᵉ : aᵉ ＝ᵉ bᵉ} (αᵉ : invᵉ topᵉ ＝ᵉ top'ᵉ) →
    (sᵉ : coherence-triangle-identificationsᵉ rightᵉ leftᵉ topᵉ) →
    (tᵉ : coherence-triangle-identificationsᵉ rightᵉ left'ᵉ topᵉ) →
    coherence-triangle-identificationsᵉ tᵉ (left-whisker-concatᵉ topᵉ pᵉ) sᵉ ≃ᵉ
    coherence-triangle-identificationsᵉ
      ( transpose-top-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ αᵉ sᵉ)
      ( transpose-top-coherence-triangle-identificationsᵉ left'ᵉ rightᵉ topᵉ αᵉ tᵉ)
      ( pᵉ)
  equiv-higher-transpose-top-coherence-triangle-identificationsᵉ
    leftᵉ rightᵉ topᵉ reflᵉ reflᵉ sᵉ tᵉ =
    ( equiv-apᵉ
      ( equiv-transpose-top-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ)
      ( _)
      ( _)) ∘eᵉ
    ( equiv-invᵉ _ _) ∘eᵉ
    ( equiv-concat'ᵉ _ right-unitᵉ)

  higher-transpose-top-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ cᵉ) (topᵉ : bᵉ ＝ᵉ aᵉ) →
    {left'ᵉ : aᵉ ＝ᵉ cᵉ} (pᵉ : leftᵉ ＝ᵉ left'ᵉ)
    {top'ᵉ : aᵉ ＝ᵉ bᵉ} (qᵉ : invᵉ topᵉ ＝ᵉ top'ᵉ) →
    (sᵉ : coherence-triangle-identificationsᵉ rightᵉ leftᵉ topᵉ) →
    (tᵉ : coherence-triangle-identificationsᵉ rightᵉ left'ᵉ topᵉ) →
    coherence-triangle-identificationsᵉ tᵉ (left-whisker-concatᵉ topᵉ pᵉ) sᵉ →
    coherence-triangle-identificationsᵉ
      ( transpose-top-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ qᵉ sᵉ)
      ( transpose-top-coherence-triangle-identificationsᵉ left'ᵉ rightᵉ topᵉ qᵉ tᵉ)
      ( pᵉ)
  higher-transpose-top-coherence-triangle-identificationsᵉ
    leftᵉ rightᵉ topᵉ pᵉ qᵉ sᵉ tᵉ =
    map-equivᵉ
      ( equiv-higher-transpose-top-coherence-triangle-identificationsᵉ
        leftᵉ rightᵉ topᵉ pᵉ qᵉ sᵉ tᵉ)

  transpose-right-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : cᵉ ＝ᵉ bᵉ) (topᵉ : aᵉ ＝ᵉ bᵉ)
    {right'ᵉ : bᵉ ＝ᵉ cᵉ} (pᵉ : invᵉ rightᵉ ＝ᵉ right'ᵉ) →
    coherence-triangle-identificationsᵉ topᵉ rightᵉ leftᵉ →
    coherence-triangle-identificationsᵉ leftᵉ right'ᵉ topᵉ
  transpose-right-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ reflᵉ tᵉ =
    right-transpose-eq-concatᵉ _ _ _ (invᵉ tᵉ)

  equiv-transpose-right-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : cᵉ ＝ᵉ bᵉ) (topᵉ : aᵉ ＝ᵉ bᵉ) →
    coherence-triangle-identificationsᵉ topᵉ rightᵉ leftᵉ ≃ᵉ
    coherence-triangle-identificationsᵉ leftᵉ (invᵉ rightᵉ) topᵉ
  equiv-transpose-right-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ =
    equiv-right-transpose-eq-concatᵉ _ _ _ ∘eᵉ equiv-invᵉ _ _

  equiv-higher-transpose-right-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : cᵉ ＝ᵉ bᵉ) (topᵉ : aᵉ ＝ᵉ bᵉ) →
    {left'ᵉ : aᵉ ＝ᵉ cᵉ} (pᵉ : leftᵉ ＝ᵉ left'ᵉ)
    {right'ᵉ : bᵉ ＝ᵉ cᵉ} (qᵉ : invᵉ rightᵉ ＝ᵉ right'ᵉ) →
    (sᵉ : coherence-triangle-identificationsᵉ topᵉ rightᵉ leftᵉ) →
    (tᵉ : coherence-triangle-identificationsᵉ topᵉ rightᵉ left'ᵉ) →
    coherence-triangle-identificationsᵉ tᵉ (right-whisker-concatᵉ pᵉ rightᵉ) sᵉ ≃ᵉ
    coherence-triangle-identificationsᵉ
      ( transpose-right-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ qᵉ sᵉ)
      ( transpose-right-coherence-triangle-identificationsᵉ left'ᵉ rightᵉ topᵉ qᵉ tᵉ)
      ( pᵉ)
  equiv-higher-transpose-right-coherence-triangle-identificationsᵉ
    leftᵉ rightᵉ topᵉ reflᵉ reflᵉ sᵉ tᵉ =
    ( equiv-apᵉ
      ( equiv-transpose-right-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ)
      ( _)
      ( _)) ∘eᵉ
    ( equiv-invᵉ _ _) ∘eᵉ
    ( equiv-concat'ᵉ tᵉ right-unitᵉ)

  higher-transpose-right-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : cᵉ ＝ᵉ bᵉ) (topᵉ : aᵉ ＝ᵉ bᵉ) →
    {left'ᵉ : aᵉ ＝ᵉ cᵉ} (pᵉ : leftᵉ ＝ᵉ left'ᵉ)
    {right'ᵉ : bᵉ ＝ᵉ cᵉ} (qᵉ : invᵉ rightᵉ ＝ᵉ right'ᵉ) →
    (sᵉ : coherence-triangle-identificationsᵉ topᵉ rightᵉ leftᵉ) →
    (tᵉ : coherence-triangle-identificationsᵉ topᵉ rightᵉ left'ᵉ) →
    coherence-triangle-identificationsᵉ tᵉ (right-whisker-concatᵉ pᵉ rightᵉ) sᵉ →
    coherence-triangle-identificationsᵉ
      ( transpose-right-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ qᵉ sᵉ)
      ( transpose-right-coherence-triangle-identificationsᵉ left'ᵉ rightᵉ topᵉ qᵉ tᵉ)
      ( pᵉ)
  higher-transpose-right-coherence-triangle-identificationsᵉ
    leftᵉ rightᵉ topᵉ pᵉ qᵉ sᵉ tᵉ =
    map-equivᵉ
      ( equiv-higher-transpose-right-coherence-triangle-identificationsᵉ
        ( leftᵉ)
        ( rightᵉ)
        ( topᵉ)
        ( pᵉ)
        ( qᵉ)
        ( sᵉ)
        ( tᵉ))
```

### Inverting all sides of a commuting triangle of identifications

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ zᵉ : Aᵉ}
  where

  inv-coherence-triangle-identificationsᵉ :
    (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ zᵉ) (topᵉ : xᵉ ＝ᵉ yᵉ) →
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ →
    coherence-triangle-identificationsᵉ (invᵉ leftᵉ) (invᵉ topᵉ) (invᵉ rightᵉ)
  inv-coherence-triangle-identificationsᵉ .(topᵉ ∙ᵉ rightᵉ) rightᵉ topᵉ reflᵉ =
    distributive-inv-concatᵉ topᵉ rightᵉ
```

### Concatenating identifications on edges with coherences of commuting triangles of identifications

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  equiv-concat-top-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ cᵉ) (topᵉ : aᵉ ＝ᵉ bᵉ)
    {top'ᵉ : aᵉ ＝ᵉ bᵉ} (pᵉ : top'ᵉ ＝ᵉ topᵉ) →
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ top'ᵉ ≃ᵉ
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ
  equiv-concat-top-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ pᵉ =
    equiv-concat'ᵉ leftᵉ (right-whisker-concatᵉ pᵉ rightᵉ)

  concat-top-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ cᵉ) (topᵉ : aᵉ ＝ᵉ bᵉ)
    {top'ᵉ : aᵉ ＝ᵉ bᵉ} (pᵉ : top'ᵉ ＝ᵉ topᵉ) →
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ top'ᵉ →
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ
  concat-top-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ pᵉ =
    map-equivᵉ
      ( equiv-concat-top-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ pᵉ)

  equiv-concat-right-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ cᵉ) (topᵉ : aᵉ ＝ᵉ bᵉ)
    {right'ᵉ : bᵉ ＝ᵉ cᵉ} (pᵉ : right'ᵉ ＝ᵉ rightᵉ) →
    coherence-triangle-identificationsᵉ leftᵉ right'ᵉ topᵉ ≃ᵉ
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ
  equiv-concat-right-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ pᵉ =
    equiv-concat'ᵉ leftᵉ (left-whisker-concatᵉ topᵉ pᵉ)

  concat-right-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ cᵉ) (topᵉ : aᵉ ＝ᵉ bᵉ)
    {right'ᵉ : bᵉ ＝ᵉ cᵉ} (pᵉ : right'ᵉ ＝ᵉ rightᵉ) →
    coherence-triangle-identificationsᵉ leftᵉ right'ᵉ topᵉ →
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ
  concat-right-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ pᵉ =
    map-equivᵉ
      ( equiv-concat-right-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ pᵉ)

  equiv-concat-left-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ cᵉ) (topᵉ : aᵉ ＝ᵉ bᵉ)
    {left'ᵉ : aᵉ ＝ᵉ cᵉ} (pᵉ : leftᵉ ＝ᵉ left'ᵉ) →
    coherence-triangle-identificationsᵉ left'ᵉ rightᵉ topᵉ ≃ᵉ
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ
  equiv-concat-left-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ pᵉ =
    equiv-concatᵉ pᵉ (topᵉ ∙ᵉ rightᵉ)

  concat-left-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ cᵉ) (topᵉ : aᵉ ＝ᵉ bᵉ)
    {left'ᵉ : aᵉ ＝ᵉ cᵉ} (pᵉ : leftᵉ ＝ᵉ left'ᵉ) →
    coherence-triangle-identificationsᵉ left'ᵉ rightᵉ topᵉ →
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ
  concat-left-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ pᵉ =
    map-equivᵉ
      ( equiv-concat-left-coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ pᵉ)
```

### Horizontal pasting of commuting triangles of identifications

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ identificationsᵉ ofᵉ theᵉ formᵉ

```text
  top-leftᵉ   top-rightᵉ
    aᵉ --->ᵉ bᵉ --->ᵉ cᵉ
      \ᵉ    |    /ᵉ
  leftᵉ \ᵉ   |mᵉ  /ᵉ rightᵉ
        \ᵉ  |  /ᵉ
         ∨ᵉ ∨ᵉ ∨ᵉ
           dᵉ
```

Thenᵉ theᵉ outerᵉ triangleᵉ commutesᵉ too.ᵉ Indeed,ᵉ anᵉ identificationᵉ
`leftᵉ ＝ᵉ top-leftᵉ ∙ᵉ middle`ᵉ isᵉ given.ᵉ Then,ᵉ anᵉ identificationᵉ

```text
  top-leftᵉ ∙ᵉ middleᵉ ＝ᵉ (top-leftᵉ ∙ᵉ top-rightᵉ) ∙ᵉ rightᵉ
```

isᵉ obtainedᵉ immediatelyᵉ byᵉ leftᵉ whiskeringᵉ theᵉ rightᵉ triangleᵉ with theᵉ
identificationᵉ `top-left`.ᵉ Noteᵉ thatᵉ thisᵉ directᵉ constructionᵉ ofᵉ theᵉ coherenceᵉ
ofᵉ theᵉ outerᵉ commutingᵉ triangleᵉ ofᵉ identificationsᵉ avoidsᵉ anyᵉ useᵉ ofᵉ
associativity.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  {aᵉ bᵉ cᵉ dᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ dᵉ) (middleᵉ : bᵉ ＝ᵉ dᵉ) (rightᵉ : cᵉ ＝ᵉ dᵉ)
  (top-leftᵉ : aᵉ ＝ᵉ bᵉ) (top-rightᵉ : bᵉ ＝ᵉ cᵉ)
  where

  horizontal-pasting-coherence-triangle-identificationsᵉ :
    coherence-triangle-identificationsᵉ leftᵉ middleᵉ top-leftᵉ →
    coherence-triangle-identificationsᵉ middleᵉ rightᵉ top-rightᵉ →
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ (top-leftᵉ ∙ᵉ top-rightᵉ)
  horizontal-pasting-coherence-triangle-identificationsᵉ sᵉ tᵉ =
    ( sᵉ) ∙ᵉ
    ( left-whisker-concat-coherence-triangle-identificationsᵉ
      ( top-leftᵉ)
      ( middleᵉ)
      ( rightᵉ)
      ( top-rightᵉ)
      ( tᵉ))
```

### Horizontal pasting of commuting triangles of identifications is a binary equivalence

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  {aᵉ bᵉ cᵉ dᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ dᵉ) (middleᵉ : bᵉ ＝ᵉ dᵉ) (rightᵉ : cᵉ ＝ᵉ dᵉ)
  (top-leftᵉ : aᵉ ＝ᵉ bᵉ) (top-rightᵉ : bᵉ ＝ᵉ cᵉ)
  where

  abstract
    is-equiv-horizontal-pasting-coherence-triangle-identificationsᵉ :
      (sᵉ : coherence-triangle-identificationsᵉ leftᵉ middleᵉ top-leftᵉ) →
      is-equivᵉ
        ( horizontal-pasting-coherence-triangle-identificationsᵉ
          ( leftᵉ)
          ( middleᵉ)
          ( rightᵉ)
          ( top-leftᵉ)
          ( top-rightᵉ)
          ( sᵉ))
    is-equiv-horizontal-pasting-coherence-triangle-identificationsᵉ sᵉ =
      is-equiv-compᵉ _ _
        ( is-equiv-left-whisker-concat-coherence-triangle-identificationsᵉ
          ( top-leftᵉ)
          ( middleᵉ)
          ( rightᵉ)
          ( top-rightᵉ))
        ( is-equiv-concatᵉ sᵉ _)

  equiv-horizontal-pasting-coherence-triangle-identificationsᵉ :
    (sᵉ : coherence-triangle-identificationsᵉ leftᵉ middleᵉ top-leftᵉ) →
    coherence-triangle-identificationsᵉ middleᵉ rightᵉ top-rightᵉ ≃ᵉ
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ (top-leftᵉ ∙ᵉ top-rightᵉ)
  pr1ᵉ (equiv-horizontal-pasting-coherence-triangle-identificationsᵉ sᵉ) =
    horizontal-pasting-coherence-triangle-identificationsᵉ _ _ _ _ _ sᵉ
  pr2ᵉ (equiv-horizontal-pasting-coherence-triangle-identificationsᵉ sᵉ) =
    is-equiv-horizontal-pasting-coherence-triangle-identificationsᵉ sᵉ

  abstract
    is-equiv-horizontal-pasting-coherence-triangle-identifications'ᵉ :
      (tᵉ : coherence-triangle-identificationsᵉ middleᵉ rightᵉ top-rightᵉ) →
      is-equivᵉ
        ( λ sᵉ →
          horizontal-pasting-coherence-triangle-identificationsᵉ
            ( leftᵉ)
            ( middleᵉ)
            ( rightᵉ)
            ( top-leftᵉ)
            ( top-rightᵉ)
            ( sᵉ)
            ( tᵉ))
    is-equiv-horizontal-pasting-coherence-triangle-identifications'ᵉ tᵉ =
      is-equiv-concat'ᵉ _
        ( left-whisker-concat-coherence-triangle-identificationsᵉ
          ( top-leftᵉ)
          ( middleᵉ)
          ( rightᵉ)
          ( top-rightᵉ)
          ( tᵉ))

  equiv-horizontal-pasting-coherence-triangle-identifications'ᵉ :
    (tᵉ : coherence-triangle-identificationsᵉ middleᵉ rightᵉ top-rightᵉ) →
    coherence-triangle-identificationsᵉ leftᵉ middleᵉ top-leftᵉ ≃ᵉ
    coherence-triangle-identificationsᵉ leftᵉ rightᵉ (top-leftᵉ ∙ᵉ top-rightᵉ)
  pr1ᵉ (equiv-horizontal-pasting-coherence-triangle-identifications'ᵉ tᵉ) sᵉ =
    horizontal-pasting-coherence-triangle-identificationsᵉ
      ( leftᵉ)
      ( middleᵉ)
      ( rightᵉ)
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( sᵉ)
      ( tᵉ)
  pr2ᵉ (equiv-horizontal-pasting-coherence-triangle-identifications'ᵉ tᵉ) =
    is-equiv-horizontal-pasting-coherence-triangle-identifications'ᵉ tᵉ

  is-binary-equiv-horizontal-pasting-coherence-triangle-identificationsᵉ :
    is-binary-equivᵉ
      ( horizontal-pasting-coherence-triangle-identificationsᵉ
        ( leftᵉ)
        ( middleᵉ)
        ( rightᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ))
  pr1ᵉ is-binary-equiv-horizontal-pasting-coherence-triangle-identificationsᵉ =
    is-equiv-horizontal-pasting-coherence-triangle-identifications'ᵉ
  pr2ᵉ is-binary-equiv-horizontal-pasting-coherence-triangle-identificationsᵉ =
    is-equiv-horizontal-pasting-coherence-triangle-identificationsᵉ
```

### The left unit law for horizontal pastinf of commuting triangles of identifications

Considerᵉ aᵉ commutingᵉ triangleᵉ ofᵉ identificationsᵉ

```text
         topᵉ
     aᵉ ------>ᵉ bᵉ
      \ᵉ       /ᵉ
  leftᵉ \ᵉ     /ᵉ rightᵉ
        \ᵉ   /ᵉ
         ∨ᵉ ∨ᵉ
          cᵉ
```

with `tᵉ : leftᵉ ＝ᵉ topᵉ ∙ᵉ right`.ᵉ Thenᵉ weᵉ haveᵉ anᵉ identificationᵉ

```text
  horizontal-pastingᵉ leftᵉ leftᵉ rightᵉ reflᵉ topᵉ reflᵉ tᵉ ＝ᵉ tᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ : Aᵉ}
  where

  left-unit-law-horizontal-pasting-coherence-triangle-identificationsᵉ :
    (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ cᵉ) (topᵉ : aᵉ ＝ᵉ bᵉ) →
    (tᵉ : coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ) →
    horizontal-pasting-coherence-triangle-identificationsᵉ
      ( leftᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( reflᵉ)
      ( topᵉ)
      ( reflᵉ)
      ( tᵉ) ＝ᵉ
    tᵉ
  left-unit-law-horizontal-pasting-coherence-triangle-identificationsᵉ
    ._ rightᵉ topᵉ reflᵉ =
    reflᵉ
```

### The left unit law for horizontal pastinf of commuting triangles of identifications

Considerᵉ aᵉ commutingᵉ triangleᵉ ofᵉ identificationsᵉ

```text
         topᵉ
     aᵉ ------>ᵉ bᵉ
      \ᵉ       /ᵉ
  leftᵉ \ᵉ     /ᵉ rightᵉ
        \ᵉ   /ᵉ
         ∨ᵉ ∨ᵉ
          cᵉ
```

with `tᵉ : leftᵉ ＝ᵉ topᵉ ∙ᵉ right`.ᵉ Thenᵉ weᵉ haveᵉ aᵉ commutingᵉ triangleᵉ ofᵉ
identificationsᵉ

```text
      horizontal-pastingᵉ tᵉ reflᵉ
  leftᵉ ---------------------->ᵉ (topᵉ ∙ᵉ reflᵉ) ∙ᵉ rightᵉ
       \ᵉ                     /ᵉ
        \ᵉ                   /ᵉ
       tᵉ \ᵉ                 /ᵉ right-whiskerᵉ right-unitᵉ rightᵉ
          \ᵉ               /ᵉ
           \ᵉ             /ᵉ
            ∨ᵉ           ∨ᵉ
             topᵉ ∙ᵉ rightᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ : Aᵉ}
  where

  right-unit-law-horizontal-pasting-coherence-triangle-identificationsᵉ :
    (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ cᵉ) (topᵉ : aᵉ ＝ᵉ bᵉ) →
    (tᵉ : coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ) →
    coherence-triangle-identificationsᵉ
      ( tᵉ)
      ( right-whisker-concatᵉ right-unitᵉ rightᵉ)
      ( horizontal-pasting-coherence-triangle-identificationsᵉ
        ( leftᵉ)
        ( rightᵉ)
        ( rightᵉ)
        ( topᵉ)
        ( reflᵉ)
        ( tᵉ)
        ( reflᵉ))
  right-unit-law-horizontal-pasting-coherence-triangle-identificationsᵉ
    ._ rightᵉ reflᵉ reflᵉ = reflᵉ
```

### Associativity of horizontal pasting of coherences of commuting triangles of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ dᵉ eᵉ : Aᵉ}
  where

  associative-horizontal-pasting-coherence-triangle-identificationsᵉ :
    (leftᵉ : aᵉ ＝ᵉ eᵉ) (mid-leftᵉ : bᵉ ＝ᵉ eᵉ) (mid-rightᵉ : cᵉ ＝ᵉ eᵉ) (rightᵉ : dᵉ ＝ᵉ eᵉ)
    (top-leftᵉ : aᵉ ＝ᵉ bᵉ) (top-middleᵉ : bᵉ ＝ᵉ cᵉ) (top-rightᵉ : cᵉ ＝ᵉ dᵉ)
    (rᵉ : coherence-triangle-identificationsᵉ leftᵉ mid-leftᵉ top-leftᵉ) →
    (sᵉ : coherence-triangle-identificationsᵉ mid-leftᵉ mid-rightᵉ top-middleᵉ) →
    (tᵉ : coherence-triangle-identificationsᵉ mid-rightᵉ rightᵉ top-rightᵉ) →
    coherence-triangle-identificationsᵉ
      ( horizontal-pasting-coherence-triangle-identificationsᵉ
        ( leftᵉ)
        ( mid-leftᵉ)
        ( rightᵉ)
        ( top-leftᵉ)
        ( top-middleᵉ ∙ᵉ top-rightᵉ)
        ( rᵉ)
        ( horizontal-pasting-coherence-triangle-identificationsᵉ
          ( mid-leftᵉ)
          ( mid-rightᵉ)
          ( rightᵉ)
          ( top-middleᵉ)
          ( top-rightᵉ)
          ( sᵉ)
          ( tᵉ)))
      ( right-whisker-concatᵉ (assocᵉ top-leftᵉ top-middleᵉ top-rightᵉ) rightᵉ)
      ( horizontal-pasting-coherence-triangle-identificationsᵉ
        ( leftᵉ)
        ( mid-rightᵉ)
        ( rightᵉ)
        ( top-leftᵉ ∙ᵉ top-middleᵉ)
        ( top-rightᵉ)
        ( horizontal-pasting-coherence-triangle-identificationsᵉ
          ( leftᵉ)
          ( mid-leftᵉ)
          ( mid-rightᵉ)
          ( top-leftᵉ)
          ( top-middleᵉ)
          ( rᵉ)
          ( sᵉ))
        ( tᵉ))
  associative-horizontal-pasting-coherence-triangle-identificationsᵉ
    reflᵉ .reflᵉ .reflᵉ .reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ =
    reflᵉ
```

### Left whiskering of horizontal pasting of commuting triangles of identifications

Considerᵉ twoᵉ commutingᵉ trianglesᵉ ofᵉ identificationsᵉ asᵉ in theᵉ diagramᵉ

```text
      sᵉ       tᵉ
  aᵉ ---->ᵉ bᵉ ---->ᵉ cᵉ
    \ᵉ     |     /ᵉ
     \ᵉ  Lᵉ |  Rᵉ /ᵉ
    lᵉ \ᵉ   |mᵉ  /ᵉ rᵉ
       \ᵉ  |  /ᵉ
        ∨ᵉ ∨ᵉ ∨ᵉ
          d,ᵉ
```

andᵉ considerᵉ furthermoreᵉ aᵉ commutingᵉ triangleᵉ ofᵉ identificationsᵉ

```text
             t'ᵉ
         bᵉ ---->ᵉ cᵉ
         |     /ᵉ
         | R'ᵉ /ᵉ
       mᵉ |   /ᵉ rᵉ
         |  /ᵉ
         ∨ᵉ ∨ᵉ
         dᵉ
```

where theᵉ identificationsᵉ `mᵉ : bᵉ ＝ᵉ d`ᵉ andᵉ `rᵉ : cᵉ ＝ᵉ d`ᵉ areᵉ theᵉ sameᵉ asᵉ in theᵉ
previousᵉ diagram.ᵉ Finally,ᵉ considerᵉ anᵉ identificationᵉ `pᵉ : tᵉ ＝ᵉ t'`ᵉ andᵉ anᵉ
identificationᵉ `q`ᵉ witnessingᵉ thatᵉ theᵉ triangleᵉ

```text
        Rᵉ
   mᵉ ------>ᵉ tᵉ ∙ᵉ rᵉ
    \ᵉ       /ᵉ
  R'ᵉ \ᵉ     /ᵉ right-whiskerᵉ pᵉ rᵉ
      \ᵉ   /ᵉ
       ∨ᵉ ∨ᵉ
     t'ᵉ ∙ᵉ rᵉ
```

commutes.ᵉ Thenᵉ theᵉ triangleᵉ

```text
                      horizontal-pastingᵉ Lᵉ Rᵉ
                      lᵉ ---------------->ᵉ (sᵉ ∙ᵉ tᵉ) ∙ᵉ rᵉ
                        \ᵉ               /ᵉ
                         \ᵉ             /ᵉ
  horizontal-pastingᵉ Lᵉ R'ᵉ \ᵉ           /ᵉ right-whiskerᵉ (left-whiskerᵉ sᵉ pᵉ) rᵉ
                           \ᵉ         /ᵉ
                            ∨ᵉ       ∨ᵉ
                          (sᵉ ∙ᵉ t'ᵉ) ∙ᵉ rᵉ
```

commutes.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ dᵉ : Aᵉ}
  where

  left-whisker-horizontal-pasting-coherence-triangle-identificationsᵉ :
    (leftᵉ : aᵉ ＝ᵉ dᵉ) (middleᵉ : bᵉ ＝ᵉ dᵉ) (rightᵉ : cᵉ ＝ᵉ dᵉ)
    (top-leftᵉ : aᵉ ＝ᵉ bᵉ) (top-rightᵉ top-right'ᵉ : bᵉ ＝ᵉ cᵉ) →
    (Lᵉ : coherence-triangle-identificationsᵉ leftᵉ middleᵉ top-leftᵉ)
    (Rᵉ : coherence-triangle-identificationsᵉ middleᵉ rightᵉ top-rightᵉ)
    (R'ᵉ : coherence-triangle-identificationsᵉ middleᵉ rightᵉ top-right'ᵉ)
    (pᵉ : top-rightᵉ ＝ᵉ top-right'ᵉ) →
    coherence-triangle-identificationsᵉ R'ᵉ (right-whisker-concatᵉ pᵉ rightᵉ) Rᵉ →
    coherence-triangle-identificationsᵉ
      ( horizontal-pasting-coherence-triangle-identificationsᵉ
        ( leftᵉ)
        ( middleᵉ)
        ( rightᵉ)
        ( top-leftᵉ)
        ( top-right'ᵉ)
        ( Lᵉ)
        ( R'ᵉ))
      ( right-whisker-concatᵉ (left-whisker-concatᵉ top-leftᵉ pᵉ) rightᵉ)
      ( horizontal-pasting-coherence-triangle-identificationsᵉ
        ( leftᵉ)
        ( middleᵉ)
        ( rightᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( Lᵉ)
        ( Rᵉ))
  left-whisker-horizontal-pasting-coherence-triangle-identificationsᵉ
    ._ ._ reflᵉ reflᵉ reflᵉ .reflᵉ reflᵉ reflᵉ ._ reflᵉ reflᵉ =
    reflᵉ
```

### Right whiskering of horizontal pasting of commuting triangles of identifications

Considerᵉ twoᵉ commutingᵉ trianglesᵉ ofᵉ identificationsᵉ asᵉ in theᵉ diagramᵉ

```text
     sᵉ      tᵉ
  aᵉ ---->ᵉ bᵉ ---->ᵉ cᵉ
    \ᵉ     |     /ᵉ
     \ᵉ  Lᵉ |  Rᵉ /ᵉ
    lᵉ \ᵉ   |mᵉ  /ᵉ rᵉ
       \ᵉ  |  /ᵉ
        ∨ᵉ ∨ᵉ ∨ᵉ
          d,ᵉ
```

andᵉ considerᵉ furthermoreᵉ aᵉ commutingᵉ triangleᵉ ofᵉ identificationsᵉ

```text
      s'ᵉ
  aᵉ ---->ᵉ bᵉ
    \ᵉ     |
     \ᵉ L'ᵉ |
    lᵉ \ᵉ   |mᵉ
       \ᵉ  |
        ∨ᵉ ∨ᵉ
          d,ᵉ
```

where theᵉ identificationsᵉ `mᵉ : bᵉ ＝ᵉ d`ᵉ andᵉ `lᵉ : aᵉ ＝ᵉ d`ᵉ areᵉ theᵉ sameᵉ asᵉ in theᵉ
previousᵉ diagram.ᵉ Finally,ᵉ considerᵉ anᵉ identificationᵉ `pᵉ : sᵉ ＝ᵉ s'`ᵉ andᵉ anᵉ
identificationᵉ `q`ᵉ witnessingᵉ thatᵉ theᵉ triangleᵉ

```text
        Lᵉ
   lᵉ ------>ᵉ sᵉ ∙ᵉ mᵉ
    \ᵉ       /ᵉ
  L'ᵉ \ᵉ     /ᵉ right-whiskerᵉ pᵉ mᵉ
      \ᵉ   /ᵉ
       ∨ᵉ ∨ᵉ
     s'ᵉ ∙ᵉ rᵉ
```

commutes.ᵉ Thenᵉ theᵉ triangleᵉ

```text
                      horizontal-pastingᵉ Lᵉ Rᵉ
                      lᵉ ---------------->ᵉ (sᵉ ∙ᵉ tᵉ) ∙ᵉ rᵉ
                        \ᵉ               /ᵉ
                         \ᵉ             /ᵉ
  horizontal-pastingᵉ Lᵉ R'ᵉ \ᵉ           /ᵉ right-whiskerᵉ (right-whiskerᵉ pᵉ tᵉ) rᵉ
                           \ᵉ         /ᵉ
                            ∨ᵉ       ∨ᵉ
                          (s'ᵉ ∙ᵉ tᵉ) ∙ᵉ rᵉ
```

commutes.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ dᵉ : Aᵉ}
  where

  right-whisker-horizontal-pasting-coherence-triangle-identificationsᵉ :
    (leftᵉ : aᵉ ＝ᵉ dᵉ) (middleᵉ : bᵉ ＝ᵉ dᵉ) (rightᵉ : cᵉ ＝ᵉ dᵉ)
    (top-leftᵉ top-left'ᵉ : aᵉ ＝ᵉ bᵉ) (top-rightᵉ : bᵉ ＝ᵉ cᵉ) →
    (Lᵉ : coherence-triangle-identificationsᵉ leftᵉ middleᵉ top-leftᵉ)
    (L'ᵉ : coherence-triangle-identificationsᵉ leftᵉ middleᵉ top-left'ᵉ)
    (Rᵉ : coherence-triangle-identificationsᵉ middleᵉ rightᵉ top-rightᵉ)
    (pᵉ : top-leftᵉ ＝ᵉ top-left'ᵉ) →
    coherence-triangle-identificationsᵉ L'ᵉ (right-whisker-concatᵉ pᵉ middleᵉ) Lᵉ →
    coherence-triangle-identificationsᵉ
      ( horizontal-pasting-coherence-triangle-identificationsᵉ
        ( leftᵉ)
        ( middleᵉ)
        ( rightᵉ)
        ( top-left'ᵉ)
        ( top-rightᵉ)
        ( L'ᵉ)
        ( Rᵉ))
      ( right-whisker-concatᵉ (right-whisker-concatᵉ pᵉ top-rightᵉ) rightᵉ)
      ( horizontal-pasting-coherence-triangle-identificationsᵉ
        ( leftᵉ)
        ( middleᵉ)
        ( rightᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( Lᵉ)
        ( Rᵉ))
  right-whisker-horizontal-pasting-coherence-triangle-identificationsᵉ
    reflᵉ .reflᵉ .reflᵉ reflᵉ .reflᵉ reflᵉ reflᵉ ._ reflᵉ reflᵉ reflᵉ =
    reflᵉ
```

### Right pasting of commuting triangles of identifications

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ identificationsᵉ ofᵉ theᵉ formᵉ

```text
          topᵉ
   aᵉ ------------>ᵉ bᵉ
    \ᵉ ⎻⎽ᵉ          /ᵉ
     \ᵉ  ⎺⎽ᵉ midᵉ   /ᵉ top-rightᵉ
      \ᵉ   ⎺⎽ᵉ    ∨ᵉ
  leftᵉ \ᵉ    ⎺>ᵉ cᵉ
        \ᵉ     /ᵉ
         \ᵉ   /ᵉ bottom-rightᵉ
          ∨ᵉ ∨ᵉ
           dᵉ
```

Thenᵉ theᵉ outerᵉ triangleᵉ commutesᵉ too.ᵉ Indeed,ᵉ anᵉ identificationᵉ
`leftᵉ ＝ᵉ midᵉ ∙ᵉ bottom-right`ᵉ isᵉ given.ᵉ Then,ᵉ anᵉ identificationᵉ

```text
  midᵉ ∙ᵉ bottom-rightᵉ ＝ᵉ topᵉ ∙ᵉ (top-rightᵉ ∙ᵉ bottom-rightᵉ)
```

isᵉ obtainedᵉ immediatelyᵉ byᵉ rightᵉ whiskeringᵉ theᵉ upperᵉ triangleᵉ with theᵉ
identificationᵉ `bottom-right`.ᵉ Noteᵉ thatᵉ thisᵉ directᵉ constructionᵉ ofᵉ theᵉ
coherenceᵉ ofᵉ theᵉ outerᵉ commutingᵉ triangleᵉ ofᵉ identificationsᵉ avoidsᵉ anyᵉ useᵉ ofᵉ
associativity.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ dᵉ : Aᵉ}
  (leftᵉ : aᵉ ＝ᵉ dᵉ) (top-rightᵉ : bᵉ ＝ᵉ cᵉ) (bottom-rightᵉ : cᵉ ＝ᵉ dᵉ)
  (middleᵉ : aᵉ ＝ᵉ cᵉ) (topᵉ : aᵉ ＝ᵉ bᵉ)
  where

  right-pasting-coherence-triangle-identificationsᵉ :
    (sᵉ : coherence-triangle-identificationsᵉ leftᵉ bottom-rightᵉ middleᵉ) →
    (tᵉ : coherence-triangle-identificationsᵉ middleᵉ top-rightᵉ topᵉ) →
    coherence-triangle-identificationsᵉ leftᵉ (top-rightᵉ ∙ᵉ bottom-rightᵉ) topᵉ
  right-pasting-coherence-triangle-identificationsᵉ sᵉ tᵉ =
    ( sᵉ) ∙ᵉ
    ( right-whisker-concat-coherence-triangle-identificationsᵉ
      ( middleᵉ)
      ( top-rightᵉ)
      ( topᵉ)
      ( bottom-rightᵉ)
      ( tᵉ))
```

### Right pasting commuting triangles of identifications is a binary equivalence

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ dᵉ : Aᵉ}
  (leftᵉ : aᵉ ＝ᵉ dᵉ) (top-rightᵉ : bᵉ ＝ᵉ cᵉ) (bottom-rightᵉ : cᵉ ＝ᵉ dᵉ)
  (middleᵉ : aᵉ ＝ᵉ cᵉ) (topᵉ : aᵉ ＝ᵉ bᵉ)
  where

  abstract
    is-equiv-right-pasting-coherence-triangle-identificationsᵉ :
      (sᵉ : coherence-triangle-identificationsᵉ leftᵉ bottom-rightᵉ middleᵉ) →
      is-equivᵉ
        ( right-pasting-coherence-triangle-identificationsᵉ
          ( leftᵉ)
          ( top-rightᵉ)
          ( bottom-rightᵉ)
          ( middleᵉ)
          ( topᵉ)
          ( sᵉ))
    is-equiv-right-pasting-coherence-triangle-identificationsᵉ sᵉ =
      is-equiv-compᵉ _ _
        ( is-equiv-right-whisker-concat-coherence-triangle-identificationsᵉ
          ( middleᵉ)
          ( top-rightᵉ)
          ( topᵉ)
          ( bottom-rightᵉ))
        ( is-equiv-concatᵉ sᵉ _)

  equiv-right-pasting-coherence-triangle-identificationsᵉ :
    (sᵉ : coherence-triangle-identificationsᵉ leftᵉ bottom-rightᵉ middleᵉ) →
    coherence-triangle-identificationsᵉ middleᵉ top-rightᵉ topᵉ ≃ᵉ
    coherence-triangle-identificationsᵉ leftᵉ (top-rightᵉ ∙ᵉ bottom-rightᵉ) topᵉ
  pr1ᵉ (equiv-right-pasting-coherence-triangle-identificationsᵉ sᵉ) =
    right-pasting-coherence-triangle-identificationsᵉ
      ( leftᵉ)
      ( top-rightᵉ)
      ( bottom-rightᵉ)
      ( middleᵉ)
      ( topᵉ)
      ( sᵉ)
  pr2ᵉ (equiv-right-pasting-coherence-triangle-identificationsᵉ sᵉ) =
    is-equiv-right-pasting-coherence-triangle-identificationsᵉ sᵉ

  abstract
    is-equiv-right-pasting-coherence-triangle-identifications'ᵉ :
      (tᵉ : coherence-triangle-identificationsᵉ middleᵉ top-rightᵉ topᵉ) →
      is-equivᵉ
        ( λ (sᵉ : coherence-triangle-identificationsᵉ leftᵉ bottom-rightᵉ middleᵉ) →
          right-pasting-coherence-triangle-identificationsᵉ
            ( leftᵉ)
            ( top-rightᵉ)
            ( bottom-rightᵉ)
            ( middleᵉ)
            ( topᵉ)
            ( sᵉ)
            ( tᵉ))
    is-equiv-right-pasting-coherence-triangle-identifications'ᵉ tᵉ =
      is-equiv-concat'ᵉ _
        ( right-whisker-concat-coherence-triangle-identificationsᵉ
          ( middleᵉ)
          ( top-rightᵉ)
          ( topᵉ)
          ( bottom-rightᵉ)
          ( tᵉ))

  equiv-right-pasting-coherence-triangle-identifications'ᵉ :
    (tᵉ : coherence-triangle-identificationsᵉ middleᵉ top-rightᵉ topᵉ) →
    coherence-triangle-identificationsᵉ leftᵉ bottom-rightᵉ middleᵉ ≃ᵉ
    coherence-triangle-identificationsᵉ leftᵉ (top-rightᵉ ∙ᵉ bottom-rightᵉ) topᵉ
  pr1ᵉ (equiv-right-pasting-coherence-triangle-identifications'ᵉ tᵉ) sᵉ =
    right-pasting-coherence-triangle-identificationsᵉ
      ( leftᵉ)
      ( top-rightᵉ)
      ( bottom-rightᵉ)
      ( middleᵉ)
      ( topᵉ)
      ( sᵉ)
      ( tᵉ)
  pr2ᵉ (equiv-right-pasting-coherence-triangle-identifications'ᵉ tᵉ) =
    is-equiv-right-pasting-coherence-triangle-identifications'ᵉ tᵉ

  is-binary-equiv-right-pasting-coherence-triangle-identificationsᵉ :
    is-binary-equivᵉ
      ( right-pasting-coherence-triangle-identificationsᵉ
        ( leftᵉ)
        ( top-rightᵉ)
        ( bottom-rightᵉ)
        ( middleᵉ)
        ( topᵉ))
  pr1ᵉ is-binary-equiv-right-pasting-coherence-triangle-identificationsᵉ =
    is-equiv-right-pasting-coherence-triangle-identifications'ᵉ
  pr2ᵉ is-binary-equiv-right-pasting-coherence-triangle-identificationsᵉ =
    is-equiv-right-pasting-coherence-triangle-identificationsᵉ
```

### Left pasting of commuting triangles of identifications

**Note.**ᵉ Forᵉ leftᵉ pastingᵉ thereᵉ areᵉ twoᵉ potentialᵉ constructions.ᵉ Oneᵉ takesᵉ aᵉ
commutingᵉ diagramᵉ ofᵉ identificationsᵉ ofᵉ theᵉ formᵉ

```text
                topᵉ
         aᵉ ------------>ᵉ bᵉ
          \ᵉ          ⎽⎻ᵉ /ᵉ
  top-leftᵉ \ᵉ     mᵉ ⎽⎺ᵉ  /ᵉ
            ∨ᵉ    ⎽⎺ᵉ   /ᵉ
             cᵉ <⎺ᵉ    /ᵉ rightᵉ
              \ᵉ     /ᵉ
   bottom-leftᵉ \ᵉ   /ᵉ
                ∨ᵉ ∨ᵉ
                 dᵉ
```

andᵉ returnsᵉ anᵉ identificationᵉ witnessingᵉ thatᵉ theᵉ outerᵉ triangleᵉ commutes.ᵉ Inᵉ
thisᵉ caseᵉ theᵉ topᵉ triangleᵉ isᵉ anᵉ ordinaryᵉ commutingᵉ triangleᵉ ofᵉ identifications,ᵉ
andᵉ theᵉ bottomᵉ triangleᵉ isᵉ invertedᵉ alongᵉ theᵉ topᵉ edgeᵉ `m`.ᵉ

Theᵉ otherᵉ leftᵉ pastingᵉ ofᵉ commutingᵉ trianglesᵉ ofᵉ identificationsᵉ takesᵉ aᵉ
commutingᵉ diagramᵉ ofᵉ identificationsᵉ ofᵉ theᵉ formᵉ

```text
                topᵉ
         aᵉ ------------>ᵉ bᵉ
          \ᵉ         ⎽->ᵉ /ᵉ
  top-leftᵉ \ᵉ    mᵉ ⎽⎺ᵉ   /ᵉ
            ∨ᵉ   ⎽⎺ᵉ    /ᵉ
             cᵉ ⎺ᵉ     /ᵉ rightᵉ
              \ᵉ     /ᵉ
   bottom-leftᵉ \ᵉ   /ᵉ
                ∨ᵉ ∨ᵉ
                 dᵉ
```

andᵉ returnsᵉ anᵉ identificationᵉ witnessingᵉ thatᵉ theᵉ outerᵉ rectangleᵉ commutes.ᵉ Inᵉ
thisᵉ caseᵉ theᵉ bottomᵉ triangleᵉ ofᵉ identificationsᵉ isᵉ anᵉ ordinaryᵉ commutingᵉ
triangleᵉ ofᵉ identifications,ᵉ andᵉ theᵉ topᵉ triangleᵉ isᵉ invertedᵉ alongᵉ theᵉ rightᵉ
edgeᵉ `m`.ᵉ

Bothᵉ constructionsᵉ haveᵉ yetᵉ to beᵉ formalized.ᵉ

### Vertically pasting commuting squares and commuting triangles of identifications

Considerᵉ aᵉ diagramᵉ ofᵉ theᵉ formᵉ

```text
                topᵉ
         aᵉ ------------>ᵉ bᵉ
          \ᵉ             /ᵉ
  top-leftᵉ \ᵉ           /ᵉ top-rightᵉ
            ∨ᵉ   midᵉ   ∨ᵉ
             cᵉ ---->ᵉ dᵉ
              \ᵉ     /ᵉ
   bottom-leftᵉ \ᵉ   /ᵉ bottom-rightᵉ
                ∨ᵉ ∨ᵉ
                 eᵉ
```

with `sᵉ : top-leftᵉ ∙ᵉ midᵉ ＝ᵉ topᵉ ∙ᵉ top-right`ᵉ witnessingᵉ thatᵉ theᵉ squareᵉ
commutes,ᵉ andᵉ with `tᵉ : bottom-leftᵉ ＝ᵉ midᵉ ∙ᵉ bottom-right`ᵉ witnessingᵉ thatᵉ theᵉ
triangleᵉ commutes.ᵉ Thenᵉ theᵉ outerᵉ triangleᵉ commutes.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  vertical-pasting-coherence-square-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ dᵉ eᵉ : Aᵉ}
    (topᵉ : aᵉ ＝ᵉ bᵉ) (top-leftᵉ : aᵉ ＝ᵉ cᵉ) (top-rightᵉ : bᵉ ＝ᵉ dᵉ) (midᵉ : cᵉ ＝ᵉ dᵉ)
    (bottom-leftᵉ : cᵉ ＝ᵉ eᵉ) (bottom-rightᵉ : dᵉ ＝ᵉ eᵉ) →
    coherence-square-identificationsᵉ topᵉ top-leftᵉ top-rightᵉ midᵉ →
    coherence-triangle-identificationsᵉ bottom-leftᵉ bottom-rightᵉ midᵉ →
    coherence-triangle-identificationsᵉ
      ( top-leftᵉ ∙ᵉ bottom-leftᵉ)
      ( top-rightᵉ ∙ᵉ bottom-rightᵉ)
      ( topᵉ)
  vertical-pasting-coherence-square-coherence-triangle-identificationsᵉ
    topᵉ top-leftᵉ top-rightᵉ midᵉ bottom-leftᵉ bottom-rightᵉ sᵉ tᵉ =
    ( left-whisker-concatᵉ top-leftᵉ tᵉ) ∙ᵉ
    ( right-whisker-concat-coherence-square-identificationsᵉ
      ( topᵉ)
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( midᵉ)
      ( sᵉ)
      ( bottom-rightᵉ))
```

### Vertical pasting of horizontally constant commuting squares of identifications and commuting triangles of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  vertical-pasting-coherence-horizontally-constant-square-coherence-triangle-identificationsᵉ :
    {aᵉ cᵉ eᵉ : Aᵉ} (pᵉ : aᵉ ＝ᵉ cᵉ)
    (bottom-leftᵉ : cᵉ ＝ᵉ eᵉ) (bottom-rightᵉ : cᵉ ＝ᵉ eᵉ) →
    (tᵉ : coherence-triangle-identificationsᵉ bottom-leftᵉ bottom-rightᵉ reflᵉ) →
    ( vertical-pasting-coherence-square-coherence-triangle-identificationsᵉ
      ( reflᵉ)
      ( pᵉ)
      ( pᵉ)
      ( reflᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ)
      ( horizontal-refl-coherence-square-identificationsᵉ pᵉ)
      ( tᵉ)) ＝ᵉ
    ( left-whisker-concatᵉ pᵉ tᵉ)
  vertical-pasting-coherence-horizontally-constant-square-coherence-triangle-identificationsᵉ
    reflᵉ reflᵉ .reflᵉ reflᵉ =
    reflᵉ
```

### Vertical pasting of verticaly constant commuting squares of identifications and commuting triangles of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  vertical-pasting-coherence-vertically-constant-square-coherence-triangle-identificationsᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ cᵉ) (topᵉ : aᵉ ＝ᵉ bᵉ) →
    (tᵉ : coherence-triangle-identificationsᵉ leftᵉ rightᵉ topᵉ) →
    ( vertical-pasting-coherence-square-coherence-triangle-identificationsᵉ
      ( topᵉ)
      ( reflᵉ)
      ( reflᵉ)
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( vertical-refl-coherence-square-identificationsᵉ topᵉ)
      ( tᵉ)) ＝ᵉ
    tᵉ
  vertical-pasting-coherence-vertically-constant-square-coherence-triangle-identificationsᵉ
    ._ reflᵉ reflᵉ reflᵉ = reflᵉ
```