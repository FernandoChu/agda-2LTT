# Nontrivial groups

```agda
module group-theory.nontrivial-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.disjunctionᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.trivial-groupsᵉ
```

</details>

## Idea

Aᵉ [group](group-theory.groups.mdᵉ) isᵉ saidᵉ to beᵉ **nontrivial**ᵉ ifᵉ thereᵉ
[exists](foundation.existential-quantification.mdᵉ) aᵉ nonidentityᵉ element.ᵉ

## Definitions

### The predicate of being a nontrivial group

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-nontrivial-prop-Groupᵉ : Propᵉ l1ᵉ
  is-nontrivial-prop-Groupᵉ =
    exists-structure-Propᵉ (type-Groupᵉ Gᵉ) (λ gᵉ → unit-Groupᵉ Gᵉ ≠ᵉ gᵉ)

  is-nontrivial-Groupᵉ : UUᵉ l1ᵉ
  is-nontrivial-Groupᵉ =
    type-Propᵉ is-nontrivial-prop-Groupᵉ

  is-prop-is-nontrivial-Groupᵉ :
    is-propᵉ is-nontrivial-Groupᵉ
  is-prop-is-nontrivial-Groupᵉ =
    is-prop-type-Propᵉ is-nontrivial-prop-Groupᵉ
```

### The predicate of not being the trivial group

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-not-trivial-prop-Groupᵉ : Propᵉ l1ᵉ
  is-not-trivial-prop-Groupᵉ =
    neg-type-Propᵉ ((xᵉ : type-Groupᵉ Gᵉ) → unit-Groupᵉ Gᵉ ＝ᵉ xᵉ)

  is-not-trivial-Groupᵉ : UUᵉ l1ᵉ
  is-not-trivial-Groupᵉ =
    type-Propᵉ is-not-trivial-prop-Groupᵉ

  is-prop-is-not-trivial-Groupᵉ :
    is-propᵉ is-not-trivial-Groupᵉ
  is-prop-is-not-trivial-Groupᵉ =
    is-prop-type-Propᵉ is-not-trivial-prop-Groupᵉ
```

## Properties

### A group is not a trivial group if and only if it satisfies the predicate of not being trivial

**Proof:**ᵉ Theᵉ propositionᵉ `¬ᵉ (is-trivial-Groupᵉ G)`ᵉ holdsᵉ ifᵉ andᵉ onlyᵉ ifᵉ `G`ᵉ isᵉ
notᵉ contractible,ᵉ whichᵉ holdsᵉ ifᵉ andᵉ onlyᵉ ifᵉ `¬ᵉ ((xᵉ : Gᵉ) → 1 ＝ᵉ x)`.ᵉ

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  neg-is-trivial-is-not-trivial-Groupᵉ :
    is-not-trivial-Groupᵉ Gᵉ → ¬ᵉ (is-trivial-Groupᵉ Gᵉ)
  neg-is-trivial-is-not-trivial-Groupᵉ Hᵉ pᵉ = Hᵉ (λ xᵉ → eq-is-contrᵉ pᵉ)

  is-not-trivial-neg-is-trivial-Groupᵉ :
    ¬ᵉ (is-trivial-Groupᵉ Gᵉ) → is-not-trivial-Groupᵉ Gᵉ
  is-not-trivial-neg-is-trivial-Groupᵉ Hᵉ pᵉ = Hᵉ (unit-Groupᵉ Gᵉ ,ᵉ pᵉ)
```

### The map `subgroup-Prop G : Prop → Subgroup G` is an embedding for any nontrivial group

Recallᵉ thatᵉ theᵉ subgroupᵉ `subgroup-Propᵉ Gᵉ P`ᵉ associatedᵉ to aᵉ propositionᵉ `P`ᵉ wasᵉ
definedᵉ in [`group-theory.subgroups`](group-theory.subgroups.md).ᵉ

**Proof:**ᵉ Supposeᵉ thatᵉ `G`ᵉ isᵉ aᵉ nontrivialᵉ groupᵉ andᵉ `x`ᵉ isᵉ aᵉ groupᵉ elementᵉ
suchᵉ thatᵉ `1ᵉ ≠ᵉ x`.ᵉ Thenᵉ `subgroup-Propᵉ Gᵉ Pᵉ ＝ᵉ subgroup-Propᵉ Gᵉ Q`ᵉ ifᵉ andᵉ onlyᵉ ifᵉ
`xᵉ ∈ᵉ subgroup-Propᵉ Gᵉ Pᵉ ⇔ᵉ xᵉ ∈ᵉ subgroup-Propᵉ Gᵉ Q`,ᵉ whichᵉ holdsᵉ ifᵉ andᵉ onlyᵉ ifᵉ
`Pᵉ ⇔ᵉ Q`ᵉ sinceᵉ `x`ᵉ isᵉ assumedᵉ to beᵉ aᵉ nonidentityᵉ element.ᵉ Thisᵉ showsᵉ thatᵉ
`subgroup-Propᵉ Gᵉ : Propᵉ → Subgroupᵉ G`ᵉ isᵉ anᵉ injectiveᵉ map.ᵉ Sinceᵉ itᵉ isᵉ anᵉ
injectiveᵉ mapsᵉ betweenᵉ sets,ᵉ itᵉ followsᵉ thatᵉ `subgroup-Propᵉ G`ᵉ isᵉ anᵉ embedding.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  abstract
    is-emb-subgroup-prop-is-nontrivial-Groupᵉ :
      is-nontrivial-Groupᵉ Gᵉ → is-embᵉ (subgroup-Propᵉ {l2ᵉ = l2ᵉ} Gᵉ)
    is-emb-subgroup-prop-is-nontrivial-Groupᵉ Hᵉ =
      apply-universal-property-trunc-Propᵉ Hᵉ
        ( is-emb-Propᵉ _)
        ( λ (xᵉ ,ᵉ fᵉ) →
          is-emb-is-injectiveᵉ
            ( is-set-Subgroupᵉ Gᵉ)
            ( λ {Pᵉ} {Qᵉ} αᵉ →
              eq-iffᵉ
                ( λ pᵉ →
                  map-left-unit-law-disjunction-is-empty-Propᵉ
                    ( Id-Propᵉ (set-Groupᵉ Gᵉ) _ _)
                    ( Qᵉ)
                    ( fᵉ)
                    ( forward-implicationᵉ
                      ( iff-eqᵉ (apᵉ (λ Tᵉ → subset-Subgroupᵉ Gᵉ Tᵉ xᵉ) αᵉ))
                      ( inr-disjunctionᵉ pᵉ)))
                ( λ qᵉ →
                  map-left-unit-law-disjunction-is-empty-Propᵉ
                    ( Id-Propᵉ (set-Groupᵉ Gᵉ) _ _)
                    ( Pᵉ)
                    ( fᵉ)
                    ( backward-implicationᵉ
                      ( iff-eqᵉ (apᵉ (λ Tᵉ → subset-Subgroupᵉ Gᵉ Tᵉ xᵉ) αᵉ))
                      ( inr-disjunctionᵉ qᵉ)))))
```

### If the map `subgroup-Prop G : Prop lzero → Subgroup l1 G` is an embedding, then `G` is not a trivial group

**Proof:**ᵉ Supposeᵉ thatᵉ `subgroup-Propᵉ Gᵉ : Propᵉ lzero → Subgroupᵉ l1ᵉ G`ᵉ isᵉ anᵉ
embedding,ᵉ andᵉ byᵉ wayᵉ ofᵉ contradictionᵉ supposeᵉ thatᵉ `G`ᵉ isᵉ trivial.ᵉ Thenᵉ itᵉ
followsᵉ thatᵉ `Subgroupᵉ l1ᵉ G`ᵉ isᵉ contractible.ᵉ Sinceᵉ `subgroup-Propᵉ G`ᵉ isᵉ assumedᵉ
to beᵉ anᵉ embedding,ᵉ itᵉ followsᵉ thatᵉ `Propᵉ lzero`ᵉ isᵉ contractible.ᵉ Thisᵉ
contradictsᵉ theᵉ factᵉ thatᵉ `Propᵉ lzero`ᵉ containsᵉ theᵉ distinctᵉ propositionsᵉ
`empty-Prop`ᵉ andᵉ `unit-Prop`.ᵉ

Noteᵉ: Ourᵉ handlingᵉ ofᵉ universeᵉ levelsᵉ mightᵉ beᵉ tooᵉ restrictiveᵉ here.ᵉ

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-not-trivial-is-emb-subgroup-Propᵉ :
    is-embᵉ (subgroup-Propᵉ {l2ᵉ = lzeroᵉ} Gᵉ) → is-not-trivial-Groupᵉ Gᵉ
  is-not-trivial-is-emb-subgroup-Propᵉ Hᵉ Kᵉ =
    backward-implicationᵉ
      ( iff-eqᵉ
        ( is-injective-is-embᵉ Hᵉ
          { xᵉ = empty-Propᵉ}
          { yᵉ = unit-Propᵉ}
          ( eq-is-contrᵉ (is-contr-subgroup-is-trivial-Groupᵉ Gᵉ (ᵉ_ ,ᵉ Kᵉ)))))
      ( starᵉ)
```