# Category theory

## Examples of categories and large categories

{{#includeᵉ tables/categories.mdᵉ}}

## Examples of precategories and large precategories

{{#includeᵉ tables/precategories.mdᵉ}}

## Files in the category theory folder

```agda
module category-theoryᵉ where

open import category-theory.adjunctions-large-categoriesᵉ public
open import category-theory.adjunctions-large-precategoriesᵉ public
open import category-theory.anafunctors-categoriesᵉ public
open import category-theory.anafunctors-precategoriesᵉ public
open import category-theory.augmented-simplex-categoryᵉ public
open import category-theory.categoriesᵉ public
open import category-theory.category-of-functorsᵉ public
open import category-theory.category-of-functors-from-small-to-large-categoriesᵉ public
open import category-theory.category-of-maps-categoriesᵉ public
open import category-theory.category-of-maps-from-small-to-large-categoriesᵉ public
open import category-theory.commuting-squares-of-morphisms-in-large-precategoriesᵉ public
open import category-theory.commuting-squares-of-morphisms-in-precategoriesᵉ public
open import category-theory.commuting-squares-of-morphisms-in-set-magmoidsᵉ public
open import category-theory.composition-operations-on-binary-families-of-setsᵉ public
open import category-theory.conservative-functors-precategoriesᵉ public
open import category-theory.constant-functorsᵉ public
open import category-theory.copresheaf-categoriesᵉ public
open import category-theory.coproducts-in-precategoriesᵉ public
open import category-theory.cores-categoriesᵉ public
open import category-theory.cores-precategoriesᵉ public
open import category-theory.dependent-products-of-categoriesᵉ public
open import category-theory.dependent-products-of-large-categoriesᵉ public
open import category-theory.dependent-products-of-large-precategoriesᵉ public
open import category-theory.dependent-products-of-precategoriesᵉ public
open import category-theory.discrete-categoriesᵉ public
open import category-theory.embedding-maps-precategoriesᵉ public
open import category-theory.embeddings-precategoriesᵉ public
open import category-theory.endomorphisms-in-categoriesᵉ public
open import category-theory.endomorphisms-in-precategoriesᵉ public
open import category-theory.epimorphisms-in-large-precategoriesᵉ public
open import category-theory.equivalences-of-categoriesᵉ public
open import category-theory.equivalences-of-large-precategoriesᵉ public
open import category-theory.equivalences-of-precategoriesᵉ public
open import category-theory.essential-fibers-of-functors-precategoriesᵉ public
open import category-theory.essentially-injective-functors-precategoriesᵉ public
open import category-theory.essentially-surjective-functors-precategoriesᵉ public
open import category-theory.exponential-objects-precategoriesᵉ public
open import category-theory.faithful-functors-precategoriesᵉ public
open import category-theory.faithful-maps-precategoriesᵉ public
open import category-theory.full-functors-precategoriesᵉ public
open import category-theory.full-large-subcategoriesᵉ public
open import category-theory.full-large-subprecategoriesᵉ public
open import category-theory.full-maps-precategoriesᵉ public
open import category-theory.full-subcategoriesᵉ public
open import category-theory.full-subprecategoriesᵉ public
open import category-theory.fully-faithful-functors-precategoriesᵉ public
open import category-theory.fully-faithful-maps-precategoriesᵉ public
open import category-theory.function-categoriesᵉ public
open import category-theory.function-precategoriesᵉ public
open import category-theory.functors-categoriesᵉ public
open import category-theory.functors-from-small-to-large-categoriesᵉ public
open import category-theory.functors-from-small-to-large-precategoriesᵉ public
open import category-theory.functors-large-categoriesᵉ public
open import category-theory.functors-large-precategoriesᵉ public
open import category-theory.functors-nonunital-precategoriesᵉ public
open import category-theory.functors-precategoriesᵉ public
open import category-theory.functors-set-magmoidsᵉ public
open import category-theory.gaunt-categoriesᵉ public
open import category-theory.groupoidsᵉ public
open import category-theory.homotopies-natural-transformations-large-precategoriesᵉ public
open import category-theory.indiscrete-precategoriesᵉ public
open import category-theory.initial-categoryᵉ public
open import category-theory.initial-objects-large-categoriesᵉ public
open import category-theory.initial-objects-large-precategoriesᵉ public
open import category-theory.initial-objects-precategoriesᵉ public
open import category-theory.isomorphism-induction-categoriesᵉ public
open import category-theory.isomorphism-induction-precategoriesᵉ public
open import category-theory.isomorphisms-in-categoriesᵉ public
open import category-theory.isomorphisms-in-large-categoriesᵉ public
open import category-theory.isomorphisms-in-large-precategoriesᵉ public
open import category-theory.isomorphisms-in-precategoriesᵉ public
open import category-theory.isomorphisms-in-subprecategoriesᵉ public
open import category-theory.large-categoriesᵉ public
open import category-theory.large-function-categoriesᵉ public
open import category-theory.large-function-precategoriesᵉ public
open import category-theory.large-precategoriesᵉ public
open import category-theory.large-subcategoriesᵉ public
open import category-theory.large-subprecategoriesᵉ public
open import category-theory.maps-categoriesᵉ public
open import category-theory.maps-from-small-to-large-categoriesᵉ public
open import category-theory.maps-from-small-to-large-precategoriesᵉ public
open import category-theory.maps-precategoriesᵉ public
open import category-theory.maps-set-magmoidsᵉ public
open import category-theory.monads-on-categoriesᵉ public
open import category-theory.monads-on-precategoriesᵉ public
open import category-theory.monomorphisms-in-large-precategoriesᵉ public
open import category-theory.natural-isomorphisms-functors-categoriesᵉ public
open import category-theory.natural-isomorphisms-functors-large-precategoriesᵉ public
open import category-theory.natural-isomorphisms-functors-precategoriesᵉ public
open import category-theory.natural-isomorphisms-maps-categoriesᵉ public
open import category-theory.natural-isomorphisms-maps-precategoriesᵉ public
open import category-theory.natural-numbers-object-precategoriesᵉ public
open import category-theory.natural-transformations-functors-categoriesᵉ public
open import category-theory.natural-transformations-functors-from-small-to-large-categoriesᵉ public
open import category-theory.natural-transformations-functors-from-small-to-large-precategoriesᵉ public
open import category-theory.natural-transformations-functors-large-categoriesᵉ public
open import category-theory.natural-transformations-functors-large-precategoriesᵉ public
open import category-theory.natural-transformations-functors-precategoriesᵉ public
open import category-theory.natural-transformations-maps-categoriesᵉ public
open import category-theory.natural-transformations-maps-from-small-to-large-precategoriesᵉ public
open import category-theory.natural-transformations-maps-precategoriesᵉ public
open import category-theory.nonunital-precategoriesᵉ public
open import category-theory.one-object-precategoriesᵉ public
open import category-theory.opposite-categoriesᵉ public
open import category-theory.opposite-large-precategoriesᵉ public
open import category-theory.opposite-precategoriesᵉ public
open import category-theory.opposite-preunivalent-categoriesᵉ public
open import category-theory.pointed-endofunctors-categoriesᵉ public
open import category-theory.pointed-endofunctors-precategoriesᵉ public
open import category-theory.precategoriesᵉ public
open import category-theory.precategory-of-elements-of-a-presheafᵉ public
open import category-theory.precategory-of-functorsᵉ public
open import category-theory.precategory-of-functors-from-small-to-large-precategoriesᵉ public
open import category-theory.precategory-of-maps-from-small-to-large-precategoriesᵉ public
open import category-theory.precategory-of-maps-precategoriesᵉ public
open import category-theory.pregroupoidsᵉ public
open import category-theory.presheaf-categoriesᵉ public
open import category-theory.preunivalent-categoriesᵉ public
open import category-theory.products-in-precategoriesᵉ public
open import category-theory.products-of-precategoriesᵉ public
open import category-theory.pseudomonic-functors-precategoriesᵉ public
open import category-theory.pullbacks-in-precategoriesᵉ public
open import category-theory.replete-subprecategoriesᵉ public
open import category-theory.representable-functors-categoriesᵉ public
open import category-theory.representable-functors-large-precategoriesᵉ public
open import category-theory.representable-functors-precategoriesᵉ public
open import category-theory.representing-arrow-categoryᵉ public
open import category-theory.restrictions-functors-cores-precategoriesᵉ public
open import category-theory.rigid-objects-categoriesᵉ public
open import category-theory.rigid-objects-precategoriesᵉ public
open import category-theory.set-magmoidsᵉ public
open import category-theory.sieves-in-categoriesᵉ public
open import category-theory.simplex-categoryᵉ public
open import category-theory.slice-precategoriesᵉ public
open import category-theory.split-essentially-surjective-functors-precategoriesᵉ public
open import category-theory.strict-categoriesᵉ public
open import category-theory.structure-equivalences-set-magmoidsᵉ public
open import category-theory.subcategoriesᵉ public
open import category-theory.subprecategoriesᵉ public
open import category-theory.subterminal-precategoriesᵉ public
open import category-theory.terminal-categoryᵉ public
open import category-theory.terminal-objects-precategoriesᵉ public
open import category-theory.wide-subcategoriesᵉ public
open import category-theory.wide-subprecategoriesᵉ public
open import category-theory.yoneda-lemma-categoriesᵉ public
open import category-theory.yoneda-lemma-precategoriesᵉ public
```