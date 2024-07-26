# Univalent combinatorics

## Idea

Univalentᵉ combinatoricsᵉ isᵉ theᵉ studyᵉ ofᵉ finiteᵉ univalentᵉ mathematics.ᵉ Finitenessᵉ
in univalentᵉ mathematicsᵉ isᵉ expressedᵉ byᵉ aᵉ mereᵉ equivalenceᵉ to aᵉ standardᵉ finiteᵉ
object.ᵉ

Manyᵉ finiteᵉ structuresᵉ naturallyᵉ organizeᵉ themselvesᵉ intoᵉ groupoids,ᵉ in whichᵉ
theᵉ isomorphicᵉ objectsᵉ areᵉ identifiedᵉ byᵉ theᵉ univalenceᵉ axiom.ᵉ Univalenceᵉ canᵉ
thereforeᵉ helpᵉ with countingᵉ finiteᵉ structuresᵉ upᵉ to isomorphism.ᵉ Theᵉ mainᵉ pieceᵉ
ofᵉ machineryᵉ thatᵉ helpsᵉ in thisᵉ taskᵉ isᵉ theᵉ generalᵉ notionᵉ ofᵉ π-finiteness.ᵉ Aᵉ
levelᵉ `k`ᵉ π-finiteᵉ typeᵉ isᵉ aᵉ typeᵉ thatᵉ hasᵉ finitelyᵉ manyᵉ connectedᵉ components,ᵉ
suchᵉ thatᵉ allᵉ itsᵉ homotopyᵉ groupsᵉ upᵉ to levelᵉ `k`ᵉ areᵉ finite.ᵉ Theᵉ π-finiteᵉ typesᵉ
enjoyᵉ usefulᵉ closureᵉ properties,ᵉ suchᵉ asᵉ closednessᵉ underᵉ Σ,ᵉ cartesianᵉ products,ᵉ
coproducts,ᵉ andᵉ closednessᵉ underᵉ Πᵉ underᵉ aᵉ mildᵉ condition.ᵉ

## Files in the univalent combinatorics folder

```agda
module univalent-combinatoricsᵉ where

open import univalent-combinatorics.2-element-decidable-subtypesᵉ public
open import univalent-combinatorics.2-element-subtypesᵉ public
open import univalent-combinatorics.2-element-typesᵉ public
open import univalent-combinatorics.binomial-typesᵉ public
open import univalent-combinatorics.braceletsᵉ public
open import univalent-combinatorics.cartesian-product-typesᵉ public
open import univalent-combinatorics.classical-finite-typesᵉ public
open import univalent-combinatorics.complements-isolated-elementsᵉ public
open import univalent-combinatorics.coproduct-typesᵉ public
open import univalent-combinatorics.countingᵉ public
open import univalent-combinatorics.counting-decidable-subtypesᵉ public
open import univalent-combinatorics.counting-dependent-pair-typesᵉ public
open import univalent-combinatorics.counting-fibers-of-mapsᵉ public
open import univalent-combinatorics.counting-maybeᵉ public
open import univalent-combinatorics.cubesᵉ public
open import univalent-combinatorics.cycle-partitionsᵉ public
open import univalent-combinatorics.cycle-prime-decomposition-natural-numbersᵉ public
open import univalent-combinatorics.cyclic-finite-typesᵉ public
open import univalent-combinatorics.decidable-dependent-function-typesᵉ public
open import univalent-combinatorics.decidable-dependent-pair-typesᵉ public
open import univalent-combinatorics.decidable-equivalence-relationsᵉ public
open import univalent-combinatorics.decidable-propositionsᵉ public
open import univalent-combinatorics.decidable-subtypesᵉ public
open import univalent-combinatorics.dedekind-finite-setsᵉ public
open import univalent-combinatorics.dependent-function-typesᵉ public
open import univalent-combinatorics.dependent-pair-typesᵉ public
open import univalent-combinatorics.discrete-sigma-decompositionsᵉ public
open import univalent-combinatorics.distributivity-of-set-truncation-over-finite-productsᵉ public
open import univalent-combinatorics.double-countingᵉ public
open import univalent-combinatorics.embeddingsᵉ public
open import univalent-combinatorics.embeddings-standard-finite-typesᵉ public
open import univalent-combinatorics.equality-finite-typesᵉ public
open import univalent-combinatorics.equality-standard-finite-typesᵉ public
open import univalent-combinatorics.equivalencesᵉ public
open import univalent-combinatorics.equivalences-cubesᵉ public
open import univalent-combinatorics.equivalences-standard-finite-typesᵉ public
open import univalent-combinatorics.ferrers-diagramsᵉ public
open import univalent-combinatorics.fibers-of-mapsᵉ public
open import univalent-combinatorics.finite-choiceᵉ public
open import univalent-combinatorics.finite-connected-componentsᵉ public
open import univalent-combinatorics.finite-presentationsᵉ public
open import univalent-combinatorics.finite-typesᵉ public
open import univalent-combinatorics.finitely-presented-typesᵉ public
open import univalent-combinatorics.function-typesᵉ public
open import univalent-combinatorics.image-of-mapsᵉ public
open import univalent-combinatorics.inequality-types-with-countingᵉ public
open import univalent-combinatorics.inhabited-finite-typesᵉ public
open import univalent-combinatorics.injective-mapsᵉ public
open import univalent-combinatorics.involution-standard-finite-typesᵉ public
open import univalent-combinatorics.isotopies-latin-squaresᵉ public
open import univalent-combinatorics.kuratowsky-finite-setsᵉ public
open import univalent-combinatorics.latin-squaresᵉ public
open import univalent-combinatorics.main-classes-of-latin-hypercubesᵉ public
open import univalent-combinatorics.main-classes-of-latin-squaresᵉ public
open import univalent-combinatorics.maybeᵉ public
open import univalent-combinatorics.necklacesᵉ public
open import univalent-combinatorics.orientations-complete-undirected-graphᵉ public
open import univalent-combinatorics.orientations-cubesᵉ public
open import univalent-combinatorics.partitionsᵉ public
open import univalent-combinatorics.petri-netsᵉ public
open import univalent-combinatorics.pi-finite-typesᵉ public
open import univalent-combinatorics.pigeonhole-principleᵉ public
open import univalent-combinatorics.presented-pi-finite-typesᵉ public
open import univalent-combinatorics.quotients-finite-typesᵉ public
open import univalent-combinatorics.ramsey-theoryᵉ public
open import univalent-combinatorics.repetitions-of-valuesᵉ public
open import univalent-combinatorics.repetitions-of-values-sequencesᵉ public
open import univalent-combinatorics.retracts-of-finite-typesᵉ public
open import univalent-combinatorics.sequences-finite-typesᵉ public
open import univalent-combinatorics.set-quotients-of-index-twoᵉ public
open import univalent-combinatorics.sigma-decompositionsᵉ public
open import univalent-combinatorics.skipping-element-standard-finite-typesᵉ public
open import univalent-combinatorics.small-typesᵉ public
open import univalent-combinatorics.standard-finite-pruned-treesᵉ public
open import univalent-combinatorics.standard-finite-treesᵉ public
open import univalent-combinatorics.standard-finite-typesᵉ public
open import univalent-combinatorics.steiner-systemsᵉ public
open import univalent-combinatorics.steiner-triple-systemsᵉ public
open import univalent-combinatorics.sums-of-natural-numbersᵉ public
open import univalent-combinatorics.surjective-mapsᵉ public
open import univalent-combinatorics.symmetric-differenceᵉ public
open import univalent-combinatorics.trivial-sigma-decompositionsᵉ public
open import univalent-combinatorics.type-dualityᵉ public
open import univalent-combinatorics.unions-subtypesᵉ public
open import univalent-combinatorics.universal-property-standard-finite-typesᵉ public
open import univalent-combinatorics.unlabeled-partitionsᵉ public
open import univalent-combinatorics.unlabeled-rooted-treesᵉ public
open import univalent-combinatorics.unlabeled-treesᵉ public
```