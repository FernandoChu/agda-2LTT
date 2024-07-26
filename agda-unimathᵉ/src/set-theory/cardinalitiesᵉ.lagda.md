# Cardinalities of sets

```agda
module set-theory.cardinalitiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.law-of-excluded-middleᵉ
open import foundation.mere-embeddingsᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.propositionsᵉ
open import foundation.set-truncationsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **cardinality**ᵉ ofᵉ aᵉ [set](foundation-core.sets.mdᵉ) isᵉ itsᵉ
[isomorphism](category-theory.isomorphisms-in-categories.mdᵉ) class.ᵉ Weᵉ takeᵉ
isomorphismᵉ classesᵉ ofᵉ setsᵉ byᵉ [setᵉ truncating](foundation.set-truncations.mdᵉ)
theᵉ universeᵉ ofᵉ setsᵉ ofᵉ anyᵉ givenᵉ
[universeᵉ level](foundation.universe-levels.md).ᵉ Noteᵉ thatᵉ thisᵉ definitionᵉ takesᵉ
advantageᵉ ofᵉ theᵉ [univalenceᵉ axiom](foundation.univalence.mdᵉ): Byᵉ theᵉ univalenceᵉ
axiomᵉ [isomorphicᵉ sets](foundation.isomorphisms-of-sets.mdᵉ) areᵉ
[equal](foundation-core.identity-types.md),ᵉ andᵉ willᵉ beᵉ mappedᵉ to theᵉ sameᵉ
elementᵉ in theᵉ setᵉ truncationᵉ ofᵉ theᵉ universeᵉ ofᵉ allᵉ sets.ᵉ

## Definition

### Cardinalities

```agda
cardinal-Setᵉ : (lᵉ : Level) → Setᵉ (lsuc lᵉ)
cardinal-Setᵉ lᵉ = trunc-Setᵉ (Setᵉ lᵉ)

cardinalᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
cardinalᵉ lᵉ = type-Setᵉ (cardinal-Setᵉ lᵉ)

cardinalityᵉ : {lᵉ : Level} → Setᵉ lᵉ → cardinalᵉ lᵉ
cardinalityᵉ Aᵉ = unit-trunc-Setᵉ Aᵉ
```

### Inequality of cardinalities

```agda
leq-cardinality-Prop'ᵉ :
  {l1ᵉ l2ᵉ : Level} → Setᵉ l1ᵉ → cardinalᵉ l2ᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
leq-cardinality-Prop'ᵉ {l1ᵉ} {l2ᵉ} Xᵉ =
  map-universal-property-trunc-Setᵉ
    ( Prop-Setᵉ (l1ᵉ ⊔ l2ᵉ))
    ( λ Y'ᵉ → mere-emb-Propᵉ (type-Setᵉ Xᵉ) (type-Setᵉ Y'ᵉ))

compute-leq-cardinality-Prop'ᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Setᵉ l1ᵉ) (Yᵉ : Setᵉ l2ᵉ) →
  ( leq-cardinality-Prop'ᵉ Xᵉ (cardinalityᵉ Yᵉ)) ＝ᵉ
  ( mere-emb-Propᵉ (type-Setᵉ Xᵉ) (type-Setᵉ Yᵉ))
compute-leq-cardinality-Prop'ᵉ {l1ᵉ} {l2ᵉ} Xᵉ =
  triangle-universal-property-trunc-Setᵉ
    ( Prop-Setᵉ (l1ᵉ ⊔ l2ᵉ))
    ( λ Y'ᵉ → mere-emb-Propᵉ (type-Setᵉ Xᵉ) (type-Setᵉ Y'ᵉ))

leq-cardinality-Propᵉ :
  {l1ᵉ l2ᵉ : Level} → cardinalᵉ l1ᵉ → cardinalᵉ l2ᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
leq-cardinality-Propᵉ {l1ᵉ} {l2ᵉ} =
  map-universal-property-trunc-Setᵉ
    ( hom-set-Setᵉ (cardinal-Setᵉ l2ᵉ) (Prop-Setᵉ (l1ᵉ ⊔ l2ᵉ)))
    ( leq-cardinality-Prop'ᵉ)

leq-cardinalityᵉ :
  {l1ᵉ l2ᵉ : Level} → cardinalᵉ l1ᵉ → cardinalᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
leq-cardinalityᵉ Xᵉ Yᵉ = type-Propᵉ (leq-cardinality-Propᵉ Xᵉ Yᵉ)

is-prop-leq-cardinalityᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : cardinalᵉ l1ᵉ} {Yᵉ : cardinalᵉ l2ᵉ} →
  is-propᵉ (leq-cardinalityᵉ Xᵉ Yᵉ)
is-prop-leq-cardinalityᵉ {Xᵉ = Xᵉ} {Yᵉ = Yᵉ} =
  is-prop-type-Propᵉ (leq-cardinality-Propᵉ Xᵉ Yᵉ)

compute-leq-cardinalityᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Setᵉ l1ᵉ) (Yᵉ : Setᵉ l2ᵉ) →
  ( leq-cardinalityᵉ (cardinalityᵉ Xᵉ) (cardinalityᵉ Yᵉ)) ≃ᵉ
  ( mere-embᵉ (type-Setᵉ Xᵉ) (type-Setᵉ Yᵉ))
compute-leq-cardinalityᵉ {l1ᵉ} {l2ᵉ} Xᵉ Yᵉ =
  equiv-eq-Propᵉ
    ( ( htpy-eqᵉ
        ( triangle-universal-property-trunc-Setᵉ
          ( hom-set-Setᵉ (cardinal-Setᵉ l2ᵉ) (Prop-Setᵉ (l1ᵉ ⊔ l2ᵉ)))
          ( leq-cardinality-Prop'ᵉ) Xᵉ) (cardinalityᵉ Yᵉ)) ∙ᵉ
      ( compute-leq-cardinality-Prop'ᵉ Xᵉ Yᵉ))

unit-leq-cardinalityᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Setᵉ l1ᵉ) (Yᵉ : Setᵉ l2ᵉ) →
  mere-embᵉ (type-Setᵉ Xᵉ) (type-Setᵉ Yᵉ) →
  leq-cardinalityᵉ (cardinalityᵉ Xᵉ) (cardinalityᵉ Yᵉ)
unit-leq-cardinalityᵉ Xᵉ Yᵉ = map-inv-equivᵉ (compute-leq-cardinalityᵉ Xᵉ Yᵉ)

inv-unit-leq-cardinalityᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Setᵉ l1ᵉ) (Yᵉ : Setᵉ l2ᵉ) →
  leq-cardinalityᵉ (cardinalityᵉ Xᵉ) (cardinalityᵉ Yᵉ) →
  mere-embᵉ (type-Setᵉ Xᵉ) (type-Setᵉ Yᵉ)
inv-unit-leq-cardinalityᵉ Xᵉ Yᵉ = pr1ᵉ (compute-leq-cardinalityᵉ Xᵉ Yᵉ)

refl-leq-cardinalityᵉ : is-reflexive-Large-Relationᵉ cardinalᵉ leq-cardinalityᵉ
refl-leq-cardinalityᵉ {lᵉ} =
  apply-dependent-universal-property-trunc-Set'ᵉ
    ( λ Xᵉ → set-Propᵉ (leq-cardinality-Propᵉ Xᵉ Xᵉ))
    ( λ Aᵉ → unit-leq-cardinalityᵉ Aᵉ Aᵉ (refl-mere-embᵉ (type-Setᵉ Aᵉ)))

transitive-leq-cardinalityᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Xᵉ : cardinalᵉ l1ᵉ)
  (Yᵉ : cardinalᵉ l2ᵉ)
  (Zᵉ : cardinalᵉ l3ᵉ) →
  leq-cardinalityᵉ Xᵉ Yᵉ →
  leq-cardinalityᵉ Yᵉ Zᵉ →
  leq-cardinalityᵉ Xᵉ Zᵉ
transitive-leq-cardinalityᵉ Xᵉ Yᵉ Zᵉ =
  apply-dependent-universal-property-trunc-Set'ᵉ
  ( λ uᵉ →
    set-Propᵉ
      ( function-Propᵉ
        ( leq-cardinalityᵉ uᵉ Yᵉ)
        ( function-Propᵉ (leq-cardinalityᵉ Yᵉ Zᵉ)
          ( leq-cardinality-Propᵉ uᵉ Zᵉ))))
  ( λ aᵉ →
    apply-dependent-universal-property-trunc-Set'ᵉ
    ( λ vᵉ →
      set-Propᵉ
        (function-Propᵉ
          (leq-cardinalityᵉ (cardinalityᵉ aᵉ) vᵉ)
          (function-Propᵉ (leq-cardinalityᵉ vᵉ Zᵉ)
            (leq-cardinality-Propᵉ (cardinalityᵉ aᵉ) Zᵉ))))
    ( λ bᵉ →
      apply-dependent-universal-property-trunc-Set'ᵉ
      ( λ wᵉ →
        set-Propᵉ
          (function-Propᵉ
            (leq-cardinalityᵉ (cardinalityᵉ aᵉ) (cardinalityᵉ bᵉ))
            (function-Propᵉ (leq-cardinalityᵉ (cardinalityᵉ bᵉ) wᵉ)
              (leq-cardinality-Propᵉ (cardinalityᵉ aᵉ) wᵉ))))
      ( λ cᵉ a<bᵉ b<cᵉ →
        unit-leq-cardinalityᵉ
          ( aᵉ)
          ( cᵉ)
          ( transitive-mere-embᵉ
            ( inv-unit-leq-cardinalityᵉ bᵉ cᵉ b<cᵉ)
            ( inv-unit-leq-cardinalityᵉ aᵉ bᵉ a<bᵉ)))
      ( Zᵉ))
    ( Yᵉ))
  ( Xᵉ)
```

## Properties

### For sets, the type `# X ＝ # Y` is equivalent to the type of mere equivalences from `X` to `Y`

```agda
is-effective-cardinalityᵉ :
  {lᵉ : Level} (Xᵉ Yᵉ : Setᵉ lᵉ) →
  (cardinalityᵉ Xᵉ ＝ᵉ cardinalityᵉ Yᵉ) ≃ᵉ mere-equivᵉ (type-Setᵉ Xᵉ) (type-Setᵉ Yᵉ)
is-effective-cardinalityᵉ Xᵉ Yᵉ =
  ( equiv-trunc-Propᵉ (extensionality-Setᵉ Xᵉ Yᵉ)) ∘eᵉ
  ( is-effective-unit-trunc-Setᵉ (Setᵉ _) Xᵉ Yᵉ)
```

### Assuming excluded middle we can show that `leq-cardinality` is a partial order

Usingᵉ theᵉ previousᵉ resultᵉ andᵉ assumingᵉ excludedᵉ middle,ᵉ weᵉ canᵉ concludeᵉ
`leq-cardinality`ᵉ isᵉ aᵉ partialᵉ orderᵉ byᵉ showingᵉ thatᵉ itᵉ isᵉ antisymmetric.ᵉ

```agda
antisymmetric-leq-cardinalityᵉ :
  {l1ᵉ : Level} (Xᵉ Yᵉ : cardinalᵉ l1ᵉ) → (LEMᵉ l1ᵉ) →
  leq-cardinalityᵉ Xᵉ Yᵉ → leq-cardinalityᵉ Yᵉ Xᵉ → Xᵉ ＝ᵉ Yᵉ
antisymmetric-leq-cardinalityᵉ {l1ᵉ} Xᵉ Yᵉ lemᵉ =
  apply-dependent-universal-property-trunc-Set'ᵉ
  ( λ uᵉ →
    set-Propᵉ
      ( function-Propᵉ
        ( leq-cardinalityᵉ uᵉ Yᵉ)
        ( function-Propᵉ
          ( leq-cardinalityᵉ Yᵉ uᵉ)
          ( Id-Propᵉ (cardinal-Setᵉ l1ᵉ) uᵉ Yᵉ))))
  ( λ aᵉ →
    apply-dependent-universal-property-trunc-Set'ᵉ
    ( λ vᵉ →
      set-Propᵉ
        ( function-Propᵉ
          ( leq-cardinalityᵉ (cardinalityᵉ aᵉ) vᵉ)
          ( function-Propᵉ
            ( leq-cardinalityᵉ vᵉ (cardinalityᵉ aᵉ))
            ( Id-Propᵉ (cardinal-Setᵉ l1ᵉ) (cardinalityᵉ aᵉ) vᵉ))))
    ( λ bᵉ a<bᵉ b<aᵉ →
      map-inv-equivᵉ (is-effective-cardinalityᵉ aᵉ bᵉ)
        (antisymmetric-mere-embᵉ lemᵉ
        (inv-unit-leq-cardinalityᵉ _ _ a<bᵉ)
        (inv-unit-leq-cardinalityᵉ _ _ b<aᵉ)))
    ( Yᵉ))
  ( Xᵉ)
```