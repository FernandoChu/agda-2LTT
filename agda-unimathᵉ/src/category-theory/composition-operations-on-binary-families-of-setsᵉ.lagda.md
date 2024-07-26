# Composition operations on binary families of sets

```agda
module category-theory.composition-operations-on-binary-families-of-setsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ typeᵉ `A`,ᵉ aᵉ
{{#conceptᵉ "compositionᵉ operation"ᵉ Disambiguation="onᵉ binaryᵉ familiesᵉ ofᵉ sets"ᵉ Agda=composition-operation-binary-family-Setᵉ}}
onᵉ aᵉ binaryᵉ familyᵉ ofᵉ [sets](foundation-core.sets.mdᵉ) `homᵉ : Aᵉ → Aᵉ → Set`ᵉ isᵉ aᵉ
mapᵉ

```text
  _∘ᵉ_ : homᵉ yᵉ zᵉ → homᵉ xᵉ yᵉ → homᵉ xᵉ zᵉ
```

forᵉ everyᵉ tripleᵉ ofᵉ elementsᵉ `xᵉ yᵉ zᵉ : A`.ᵉ

Forᵉ suchᵉ operations,ᵉ weᵉ canᵉ considerᵉ
[properties](foundation-core.propositions.mdᵉ) suchᵉ asᵉ _associativityᵉ_ andᵉ
_unitality_.ᵉ

## Definitions

### Composition operations on binary families of sets

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (hom-setᵉ : Aᵉ → Aᵉ → Setᵉ l2ᵉ)
  where

  composition-operation-binary-family-Setᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  composition-operation-binary-family-Setᵉ =
    {xᵉ yᵉ zᵉ : Aᵉ} →
    type-Setᵉ (hom-setᵉ yᵉ zᵉ) → type-Setᵉ (hom-setᵉ xᵉ yᵉ) → type-Setᵉ (hom-setᵉ xᵉ zᵉ)
```

### Associative composition operations on binary families of sets

Aᵉ compositionᵉ operationᵉ

```text
  _∘ᵉ_ : homᵉ yᵉ zᵉ → homᵉ xᵉ yᵉ → homᵉ xᵉ zᵉ
```

onᵉ aᵉ binaryᵉ familyᵉ ofᵉ setsᵉ ofᵉ morphismsᵉ isᵉ calledᵉ
{{#conceptᵉ "associative"ᵉ Disambiguation="compositionᵉ operationᵉ onᵉ aᵉ binaryᵉ familyᵉ ofᵉ sets"ᵉ Agda=is-associative-composition-operation-binary-family-Setᵉ}}
if,ᵉ forᵉ everyᵉ tripleᵉ ofᵉ composableᵉ morphismsᵉ weᵉ haveᵉ

```text
  (hᵉ ∘ᵉ gᵉ) ∘ᵉ fᵉ ＝ᵉ hᵉ ∘ᵉ (gᵉ ∘ᵉ f).ᵉ
```

Weᵉ giveᵉ aᵉ slightlyᵉ nonstandardᵉ definitionᵉ ofᵉ associativityᵉ using theᵉ
[strictlyᵉ involutiveᵉ identityᵉ types](foundation.strictly-involutive-identity-types.mdᵉ)
ratherᵉ thanᵉ theᵉ standardᵉ [identityᵉ types](foundation-core.identity-types.md).ᵉ
Thisᵉ isᵉ because,ᵉ whileᵉ theᵉ strictlyᵉ involutiveᵉ identityᵉ typesᵉ areᵉ alwaysᵉ
[equivalent](foundation-core.equivalences.mdᵉ) to theᵉ standardᵉ ones,ᵉ theyᵉ satisfyᵉ
theᵉ strictᵉ computationᵉ ruleᵉ `invᵉ (invᵉ pᵉ) ≐ᵉ p`ᵉ whichᵉ isᵉ practicalᵉ in definingᵉ theᵉ
[oppositeᵉ category](category-theory.opposite-categories.md),ᵉ asᵉ thisᵉ alsoᵉ makesᵉ
theᵉ oppositeᵉ constructionᵉ strictlyᵉ involutiveᵉ: `(𝒞ᵒᵖ)ᵒᵖᵉ ≐ᵉ 𝒞`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (hom-setᵉ : Aᵉ → Aᵉ → Setᵉ l2ᵉ)
  where

  is-associative-composition-operation-binary-family-Setᵉ :
    composition-operation-binary-family-Setᵉ hom-setᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-associative-composition-operation-binary-family-Setᵉ comp-homᵉ =
    {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
    (hᵉ : type-Setᵉ (hom-setᵉ zᵉ wᵉ))
    (gᵉ : type-Setᵉ (hom-setᵉ yᵉ zᵉ))
    (fᵉ : type-Setᵉ (hom-setᵉ xᵉ yᵉ)) →
    ( comp-homᵉ (comp-homᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ comp-homᵉ hᵉ (comp-homᵉ gᵉ fᵉ))

  associative-composition-operation-binary-family-Setᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  associative-composition-operation-binary-family-Setᵉ =
    Σᵉ ( composition-operation-binary-family-Setᵉ hom-setᵉ)
      ( is-associative-composition-operation-binary-family-Setᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (hom-setᵉ : Aᵉ → Aᵉ → Setᵉ l2ᵉ)
  (Hᵉ : associative-composition-operation-binary-family-Setᵉ hom-setᵉ)
  where

  comp-hom-associative-composition-operation-binary-family-Setᵉ :
    composition-operation-binary-family-Setᵉ hom-setᵉ
  comp-hom-associative-composition-operation-binary-family-Setᵉ = pr1ᵉ Hᵉ

  involutive-eq-associative-composition-operation-binary-family-Setᵉ :
    {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
    (hᵉ : type-Setᵉ (hom-setᵉ zᵉ wᵉ))
    (gᵉ : type-Setᵉ (hom-setᵉ yᵉ zᵉ))
    (fᵉ : type-Setᵉ (hom-setᵉ xᵉ yᵉ)) →
    ( comp-hom-associative-composition-operation-binary-family-Setᵉ
      ( comp-hom-associative-composition-operation-binary-family-Setᵉ hᵉ gᵉ)
      ( fᵉ)) ＝ⁱᵉ
    ( comp-hom-associative-composition-operation-binary-family-Setᵉ
      ( hᵉ)
      ( comp-hom-associative-composition-operation-binary-family-Setᵉ gᵉ fᵉ))
  involutive-eq-associative-composition-operation-binary-family-Setᵉ = pr2ᵉ Hᵉ

  witness-associative-composition-operation-binary-family-Setᵉ :
    {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
    (hᵉ : type-Setᵉ (hom-setᵉ zᵉ wᵉ))
    (gᵉ : type-Setᵉ (hom-setᵉ yᵉ zᵉ))
    (fᵉ : type-Setᵉ (hom-setᵉ xᵉ yᵉ)) →
    ( comp-hom-associative-composition-operation-binary-family-Setᵉ
      ( comp-hom-associative-composition-operation-binary-family-Setᵉ hᵉ gᵉ) (fᵉ)) ＝ᵉ
    ( comp-hom-associative-composition-operation-binary-family-Setᵉ
      ( hᵉ) (comp-hom-associative-composition-operation-binary-family-Setᵉ gᵉ fᵉ))
  witness-associative-composition-operation-binary-family-Setᵉ hᵉ gᵉ fᵉ =
    eq-involutive-eqᵉ
      ( involutive-eq-associative-composition-operation-binary-family-Setᵉ hᵉ gᵉ fᵉ)

  inv-witness-associative-composition-operation-binary-family-Setᵉ :
    {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
    (hᵉ : type-Setᵉ (hom-setᵉ zᵉ wᵉ))
    (gᵉ : type-Setᵉ (hom-setᵉ yᵉ zᵉ))
    (fᵉ : type-Setᵉ (hom-setᵉ xᵉ yᵉ)) →
    ( comp-hom-associative-composition-operation-binary-family-Setᵉ
      ( hᵉ) (comp-hom-associative-composition-operation-binary-family-Setᵉ gᵉ fᵉ)) ＝ᵉ
    ( comp-hom-associative-composition-operation-binary-family-Setᵉ
      ( comp-hom-associative-composition-operation-binary-family-Setᵉ hᵉ gᵉ) (fᵉ))
  inv-witness-associative-composition-operation-binary-family-Setᵉ hᵉ gᵉ fᵉ =
    eq-involutive-eqᵉ
      ( invⁱᵉ
        ( involutive-eq-associative-composition-operation-binary-family-Setᵉ
          ( hᵉ)
          ( gᵉ)
          ( fᵉ)))
```

### Unital composition operations on binary families of sets

Aᵉ compositionᵉ operationᵉ

```text
  _∘ᵉ_ : homᵉ yᵉ zᵉ → homᵉ xᵉ yᵉ → homᵉ xᵉ zᵉ
```

onᵉ aᵉ binaryᵉ familyᵉ ofᵉ setsᵉ ofᵉ morphismsᵉ isᵉ calledᵉ
{{#conceptᵉ "unital"ᵉ Disambiguation="compositionᵉ operationᵉ onᵉ aᵉ binaryᵉ familyᵉ ofᵉ sets"ᵉ Agda=is-unital-composition-operation-binary-family-Setᵉ}}
ifᵉ thereᵉ isᵉ aᵉ morphismᵉ `id_xᵉ : homᵉ xᵉ x`ᵉ forᵉ everyᵉ elementᵉ `xᵉ : A`ᵉ suchᵉ thatᵉ

```text
  id_yᵉ ∘ᵉ fᵉ ＝ᵉ fᵉ   andᵉ fᵉ ∘ᵉ id_xᵉ = f.ᵉ
```

Asᵉ willᵉ beᵉ demonstratedᵉ momentarily,ᵉ everyᵉ compositionᵉ operationᵉ onᵉ aᵉ binaryᵉ
familyᵉ ofᵉ setsᵉ isᵉ unitalᵉ in [atᵉ mostᵉ one](foundation.subterminal-types.mdᵉ) way.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (hom-setᵉ : Aᵉ → Aᵉ → Setᵉ l2ᵉ)
  where

  is-unital-composition-operation-binary-family-Setᵉ :
    composition-operation-binary-family-Setᵉ hom-setᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-unital-composition-operation-binary-family-Setᵉ comp-homᵉ =
    Σᵉ ( (xᵉ : Aᵉ) → type-Setᵉ (hom-setᵉ xᵉ xᵉ))
      ( λ eᵉ →
        ( {xᵉ yᵉ : Aᵉ} (fᵉ : type-Setᵉ (hom-setᵉ xᵉ yᵉ)) → comp-homᵉ (eᵉ yᵉ) fᵉ ＝ᵉ fᵉ) ×ᵉ
        ( {xᵉ yᵉ : Aᵉ} (fᵉ : type-Setᵉ (hom-setᵉ xᵉ yᵉ)) → comp-homᵉ fᵉ (eᵉ xᵉ) ＝ᵉ fᵉ))
```

## Properties

### Being associative is a property of composition operations on binary families of sets

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (hom-setᵉ : Aᵉ → Aᵉ → Setᵉ l2ᵉ)
  (comp-homᵉ : composition-operation-binary-family-Setᵉ hom-setᵉ)
  where
  is-prop-is-associative-composition-operation-binary-family-Setᵉ :
    is-propᵉ
      ( is-associative-composition-operation-binary-family-Setᵉ hom-setᵉ comp-homᵉ)
  is-prop-is-associative-composition-operation-binary-family-Setᵉ =
    is-prop-iterated-implicit-Πᵉ 4
      ( λ xᵉ yᵉ zᵉ wᵉ →
        is-prop-iterated-Πᵉ 3
          ( λ hᵉ gᵉ fᵉ →
            is-prop-equivᵉ
              ( equiv-eq-involutive-eqᵉ)
              ( is-set-type-Setᵉ
                ( hom-setᵉ xᵉ wᵉ)
                ( comp-homᵉ (comp-homᵉ hᵉ gᵉ) fᵉ)
                ( comp-homᵉ hᵉ (comp-homᵉ gᵉ fᵉ)))))

  is-associative-prop-composition-operation-binary-family-Setᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ is-associative-prop-composition-operation-binary-family-Setᵉ =
    is-associative-composition-operation-binary-family-Setᵉ hom-setᵉ comp-homᵉ
  pr2ᵉ is-associative-prop-composition-operation-binary-family-Setᵉ =
    is-prop-is-associative-composition-operation-binary-family-Setᵉ
```

### Being unital is a property of composition operations on binary families of sets

**Proof:**ᵉ Supposeᵉ `eᵉ e'ᵉ : (xᵉ : Aᵉ) → hom-setᵉ xᵉ x`ᵉ areᵉ bothᵉ rightᵉ andᵉ leftᵉ unitsᵉ
with regardᵉ to composition.ᵉ Itᵉ isᵉ enoughᵉ to showᵉ thatᵉ `eᵉ ＝ᵉ e'`ᵉ sinceᵉ theᵉ rightᵉ
andᵉ leftᵉ unitᵉ lawsᵉ areᵉ propositionsᵉ (becauseᵉ allᵉ hom-typesᵉ areᵉ sets).ᵉ Byᵉ
functionᵉ extensionality,ᵉ itᵉ isᵉ enoughᵉ to showᵉ thatᵉ `eᵉ xᵉ ＝ᵉ e'ᵉ x`ᵉ forᵉ allᵉ
`xᵉ : A`.ᵉ Butᵉ byᵉ theᵉ unitᵉ lawsᵉ weᵉ haveᵉ theᵉ followingᵉ chainᵉ ofᵉ equalitiesᵉ:
`eᵉ xᵉ ＝ᵉ (e'ᵉ xᵉ) ∘ᵉ (eᵉ xᵉ) ＝ᵉ e'ᵉ x.`ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (hom-setᵉ : Aᵉ → Aᵉ → Setᵉ l2ᵉ)
  (comp-homᵉ : composition-operation-binary-family-Setᵉ hom-setᵉ)
  where

  abstract
    all-elements-equal-is-unital-composition-operation-binary-family-Setᵉ :
      all-elements-equalᵉ
        ( is-unital-composition-operation-binary-family-Setᵉ hom-setᵉ comp-homᵉ)
    all-elements-equal-is-unital-composition-operation-binary-family-Setᵉ
      ( eᵉ ,ᵉ left-unit-law-eᵉ ,ᵉ right-unit-law-eᵉ)
      ( e'ᵉ ,ᵉ left-unit-law-e'ᵉ ,ᵉ right-unit-law-e'ᵉ) =
      eq-type-subtypeᵉ
        ( λ xᵉ →
          product-Propᵉ
            ( implicit-Π-Propᵉ Aᵉ
              ( λ aᵉ →
                implicit-Π-Propᵉ Aᵉ
                ( λ bᵉ →
                  Π-Propᵉ
                    ( type-Setᵉ (hom-setᵉ aᵉ bᵉ))
                    ( λ f'ᵉ → Id-Propᵉ (hom-setᵉ aᵉ bᵉ) (comp-homᵉ (xᵉ bᵉ) f'ᵉ) f'ᵉ))))
            ( implicit-Π-Propᵉ Aᵉ
              ( λ aᵉ →
                implicit-Π-Propᵉ Aᵉ
                ( λ bᵉ →
                  Π-Propᵉ
                    ( type-Setᵉ (hom-setᵉ aᵉ bᵉ))
                    ( λ f'ᵉ → Id-Propᵉ (hom-setᵉ aᵉ bᵉ) (comp-homᵉ f'ᵉ (xᵉ aᵉ)) f'ᵉ)))))
        ( eq-htpyᵉ
          ( λ xᵉ → invᵉ (left-unit-law-e'ᵉ (eᵉ xᵉ)) ∙ᵉ right-unit-law-eᵉ (e'ᵉ xᵉ)))

  abstract
    is-prop-is-unital-composition-operation-binary-family-Setᵉ :
      is-propᵉ
        ( is-unital-composition-operation-binary-family-Setᵉ hom-setᵉ comp-homᵉ)
    is-prop-is-unital-composition-operation-binary-family-Setᵉ =
      is-prop-all-elements-equalᵉ
        all-elements-equal-is-unital-composition-operation-binary-family-Setᵉ

  is-unital-prop-composition-operation-binary-family-Setᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ is-unital-prop-composition-operation-binary-family-Setᵉ =
    is-unital-composition-operation-binary-family-Setᵉ hom-setᵉ comp-homᵉ
  pr2ᵉ is-unital-prop-composition-operation-binary-family-Setᵉ =
    is-prop-is-unital-composition-operation-binary-family-Setᵉ
```

## See also

-ᵉ [Set-magmoids](category-theory.set-magmoids.mdᵉ) captureᵉ theᵉ structureᵉ ofᵉ
  compositionᵉ operationsᵉ onᵉ binaryᵉ familiesᵉ ofᵉ sets.ᵉ
-ᵉ [Precategories](category-theory.precategories.mdᵉ) areᵉ theᵉ structureᵉ ofᵉ anᵉ
  associativeᵉ andᵉ unitalᵉ compositionᵉ operationᵉ onᵉ aᵉ binaryᵉ familiesᵉ ofᵉ sets.ᵉ
-ᵉ [Nonunitalᵉ precategories](category-theory.nonunital-precategories.mdᵉ) areᵉ theᵉ
  structureᵉ ofᵉ anᵉ associativeᵉ compositionᵉ operationᵉ onᵉ aᵉ binaryᵉ familiesᵉ ofᵉ
  sets.ᵉ