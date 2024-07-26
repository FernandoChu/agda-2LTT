# Cayley's theorem

```agda
module group-theory.cayleys-theoremᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.embeddings-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.symmetric-groupsᵉ
```

</details>

## Theorem

### Direct proof of Cayley's theorem

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  map-Cayleys-theoremᵉ :
    type-Groupᵉ Gᵉ → type-Groupᵉ (symmetric-Groupᵉ (set-Groupᵉ Gᵉ))
  map-Cayleys-theoremᵉ = equiv-mul-Groupᵉ Gᵉ

  preserves-mul-map-Cayleys-theoremᵉ :
    preserves-mul-Groupᵉ Gᵉ (symmetric-Groupᵉ (set-Groupᵉ Gᵉ)) map-Cayleys-theoremᵉ
  preserves-mul-map-Cayleys-theoremᵉ {xᵉ} {yᵉ} =
    eq-htpy-equivᵉ (associative-mul-Groupᵉ Gᵉ xᵉ yᵉ)

  hom-Cayleys-theoremᵉ : hom-Groupᵉ Gᵉ (symmetric-Groupᵉ (set-Groupᵉ Gᵉ))
  pr1ᵉ hom-Cayleys-theoremᵉ = map-Cayleys-theoremᵉ
  pr2ᵉ hom-Cayleys-theoremᵉ = preserves-mul-map-Cayleys-theoremᵉ

  is-injective-map-Cayleys-theoremᵉ : is-injectiveᵉ map-Cayleys-theoremᵉ
  is-injective-map-Cayleys-theoremᵉ {xᵉ} {yᵉ} pᵉ =
    ( invᵉ (right-unit-law-mul-Groupᵉ Gᵉ xᵉ)) ∙ᵉ
    ( htpy-eq-equivᵉ pᵉ (unit-Groupᵉ Gᵉ)) ∙ᵉ
    ( right-unit-law-mul-Groupᵉ Gᵉ yᵉ)

  is-emb-map-Cayleys-theoremᵉ : is-embᵉ map-Cayleys-theoremᵉ
  is-emb-map-Cayleys-theoremᵉ =
    is-emb-is-injectiveᵉ
      ( is-set-type-Groupᵉ (symmetric-Groupᵉ (set-Groupᵉ Gᵉ)))
      ( is-injective-map-Cayleys-theoremᵉ)

  Cayleys-theoremᵉ : emb-Groupᵉ Gᵉ (symmetric-Groupᵉ (set-Groupᵉ Gᵉ))
  pr1ᵉ Cayleys-theoremᵉ = hom-Cayleys-theoremᵉ
  pr2ᵉ Cayleys-theoremᵉ = is-emb-map-Cayleys-theoremᵉ
```

### Cayley's theorem as a corollary of the Yoneda lemma

Thisᵉ isᵉ Corollaryᵉ 2.2.10ᵉ ofᵉ {{#citeᵉ Rie17}},ᵉ andᵉ remainsᵉ to beᵉ formalized.ᵉ

## References

{{#bibliographyᵉ}}

## External links

-ᵉ [Cayley'sᵉ Theorem](https://1lab.dev/Algebra.Group.Cayley.htmlᵉ) atᵉ 1labᵉ
-ᵉ [Cayley'sᵉ theorem](https://ncatlab.org/nlab/show/Cayley%27s+theoremᵉ) atᵉ $n$Labᵉ
-ᵉ [Cayley'sᵉ theorem](https://en.wikipedia.org/wiki/Cayley%27s_theoremᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [Cayley'sᵉ theorem](https://www.wikidata.org/wiki/Q179208ᵉ) atᵉ Wikidataᵉ