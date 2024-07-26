# Sequential Colimits in Homotopy Type Theory

Thisᵉ fileᵉ collectsᵉ referencesᵉ to formalizationᵉ ofᵉ constructionsᵉ andᵉ theoremsᵉ
fromᵉ {{#citeᵉ SvDR20}}.ᵉ

```agda
module literature.sequential-colimits-in-homotopy-type-theoryᵉ where
```

## 2 Homotopy Type Theory

Theᵉ secondᵉ sectionᵉ introducesᵉ basicᵉ notionsᵉ fromᵉ homotopyᵉ typeᵉ theory,ᵉ whichᵉ weᵉ
import belowᵉ forᵉ completeness.ᵉ

```agda
open import foundation.universe-levelsᵉ using
  ( UUᵉ
  )
open import foundation.identity-typesᵉ using
  ( Idᵉ --ᵉ "path"ᵉ
  ; reflᵉ --ᵉ "constantᵉ path"ᵉ
  ; invᵉ --ᵉ "inverseᵉ path"ᵉ
  ; concatᵉ --ᵉ "concatenationᵉ ofᵉ paths"ᵉ
  ; assocᵉ --ᵉ "associativityᵉ ofᵉ concatenation"ᵉ
  )
open import foundation.action-on-identifications-functionsᵉ using
  ( apᵉ --ᵉ "functionsᵉ respectᵉ paths"ᵉ
  )
open import foundation.homotopiesᵉ using
  ( _~ᵉ_ --ᵉ "homotopy"ᵉ
  )
open import foundation.equivalencesᵉ using
  ( equivᵉ --ᵉ "equivalence"ᵉ
  )
open import foundation.univalenceᵉ using
  ( univalenceᵉ --ᵉ "theᵉ univalenceᵉ axiom"ᵉ
  ; map-eqᵉ --ᵉ "functionᵉ p̅ᵉ associatedᵉ to aᵉ path"ᵉ
  )
open import foundation.function-extensionalityᵉ using
  ( funextᵉ --ᵉ "theᵉ functionᵉ extensionalityᵉ axiom"ᵉ
  )
open import foundation.fibers-of-mapsᵉ using
  ( fiberᵉ --ᵉ "theᵉ homotopyᵉ fiberᵉ ofᵉ aᵉ function"ᵉ
  )
open import foundation.transport-along-identificationsᵉ using
  ( trᵉ --ᵉ "transport"ᵉ
  )
open import foundation.action-on-identifications-dependent-functionsᵉ using
  ( apdᵉ --ᵉ "dependentᵉ functionsᵉ respectᵉ paths"ᵉ
  )
open import foundation.truncated-typesᵉ using
  ( is-truncᵉ --ᵉ "`n`-truncatedᵉ types"ᵉ
  )
open import foundation.truncationsᵉ using
  ( truncᵉ --ᵉ "theᵉ `n`-truncationᵉ ofᵉ aᵉ type"ᵉ
  ; unit-truncᵉ --ᵉ "theᵉ unitᵉ mapᵉ intoᵉ aᵉ type'sᵉ `n`-truncation"ᵉ
  ; is-truncation-truncᵉ --ᵉ "precomposingᵉ byᵉ theᵉ unitᵉ isᵉ anᵉ equivalence"ᵉ
  )
open import foundation.connected-typesᵉ using
  ( is-connectedᵉ --ᵉ "`n`-connectedᵉ types"ᵉ
  )
open import foundation.truncated-mapsᵉ using
  ( is-trunc-mapᵉ --ᵉ "`n`-truncatedᵉ functions"ᵉ
  )
open import foundation.connected-mapsᵉ using
  ( is-connected-mapᵉ --ᵉ "`n`-connectedᵉ functions"ᵉ
  )
```

## 3 Sequences and Sequential Colimits

Theᵉ thirdᵉ sectionᵉ definesᵉ categoricalᵉ propertiesᵉ ofᵉ sequencesᵉ (whichᵉ areᵉ calledᵉ
_sequentialᵉ diagramsᵉ_ in agda-unimathᵉ) andᵉ theᵉ colimitingᵉ functor.ᵉ Itᵉ concludesᵉ
byᵉ definingᵉ shiftsᵉ ofᵉ sequences,ᵉ showingᵉ thatᵉ theyᵉ induceᵉ equivalencesᵉ onᵉ
sequentialᵉ colimits,ᵉ andᵉ definesᵉ liftsᵉ ofᵉ elementsᵉ in aᵉ sequentialᵉ diagram.ᵉ

**Definitionᵉ 3.1.**ᵉ Sequences.ᵉ

```agda
open import synthetic-homotopy-theory.sequential-diagramsᵉ using
  ( sequential-diagramᵉ
  )
```

**Definitionᵉ 3.2.**ᵉ Sequentialᵉ colimitsᵉ andᵉ theirᵉ inductionᵉ andᵉ recursionᵉ
principles.ᵉ

Inductionᵉ andᵉ recursionᵉ areᵉ givenᵉ byᵉ theᵉ dependentᵉ andᵉ non-dependentᵉ universalᵉ
properties,ᵉ respectively.ᵉ Sinceᵉ weᵉ workᵉ in aᵉ settingᵉ withoutᵉ computationalᵉ
higherᵉ inductive types,ᵉ theᵉ mapsᵉ inducedᵉ byᵉ inductionᵉ andᵉ recursionᵉ onlyᵉ computeᵉ
upᵉ to aᵉ path,ᵉ evenᵉ onᵉ points.ᵉ Ourᵉ homotopiesᵉ in theᵉ definitionsᵉ ofᵉ coconesᵉ goᵉ
fromᵉ leftᵉ to rightᵉ (i.e.ᵉ `iₙᵉ ~ᵉ iₙ₊₁ᵉ ∘ᵉ aₙ`),ᵉ insteadᵉ ofᵉ rightᵉ to left.ᵉ

Ourᵉ formalizationᵉ worksᵉ with sequentialᵉ colimitsᵉ specifiedᵉ byᵉ aᵉ coconeᵉ with aᵉ
universalᵉ property,ᵉ andᵉ resultsᵉ aboutᵉ theᵉ standardᵉ constructionᵉ ofᵉ colimitsᵉ areᵉ
obtainedᵉ byᵉ specializationᵉ to theᵉ canonicalᵉ cocone.ᵉ

```agda
open import synthetic-homotopy-theory.sequential-colimitsᵉ using
  ( standard-sequential-colimitᵉ --ᵉ theᵉ canonicalᵉ colimitᵉ typeᵉ
  ; map-cocone-standard-sequential-colimitᵉ --ᵉ "theᵉ canonicalᵉ injection"ᵉ
  ; coherence-cocone-standard-sequential-colimitᵉ --ᵉ "theᵉ glue"ᵉ
  ; dup-standard-sequential-colimitᵉ --ᵉ "theᵉ inductionᵉ principle"ᵉ
  ; up-standard-sequential-colimitᵉ --ᵉ "theᵉ recursionᵉ principle"ᵉ
  )
```

**Lemmaᵉ 3.3.**ᵉ Uniquenessᵉ propertyᵉ ofᵉ theᵉ sequentialᵉ colimit.ᵉ

Theᵉ data ofᵉ aᵉ homotopyᵉ betweenᵉ twoᵉ functionsᵉ outᵉ ofᵉ theᵉ standardᵉ sequentialᵉ
colimitᵉ isᵉ specifiedᵉ byᵉ theᵉ typeᵉ `htpy-out-of-standard-sequential-colimit`,ᵉ
whichᵉ weᵉ canᵉ thenᵉ turnᵉ intoᵉ aᵉ properᵉ homotopy.ᵉ

```agda
open import synthetic-homotopy-theory.sequential-colimitsᵉ using
  ( htpy-out-of-standard-sequential-colimitᵉ --ᵉ data ofᵉ aᵉ homotopyᵉ
  ; htpy-htpy-out-of-standard-sequential-colimitᵉ --ᵉ "dataᵉ ofᵉ aᵉ homotopyᵉ inducesᵉ aᵉ homotopy"ᵉ
  )
```

**Definitionᵉ 3.4.**ᵉ Naturalᵉ transformationsᵉ andᵉ naturalᵉ equivalencesᵉ betweenᵉ
sequentialᵉ diagrams.ᵉ

Weᵉ callᵉ naturalᵉ transformationsᵉ _morphismsᵉ ofᵉ sequentialᵉ diagrams_,ᵉ andᵉ naturalᵉ
equivalencesᵉ _equivalencesᵉ ofᵉ sequentialᵉ diagrams_.ᵉ

```agda
open import synthetic-homotopy-theory.morphisms-sequential-diagramsᵉ using
  ( hom-sequential-diagramᵉ --ᵉ "naturalᵉ transformation"ᵉ
  ; id-hom-sequential-diagramᵉ --ᵉ "identityᵉ naturalᵉ transformation"ᵉ
  ; comp-hom-sequential-diagramᵉ --ᵉ "compositionᵉ ofᵉ naturalᵉ transformations"ᵉ
  )
open import synthetic-homotopy-theory.equivalences-sequential-diagramsᵉ using
  ( equiv-sequential-diagramᵉ --ᵉ "naturalᵉ equivalence"ᵉ
  )
```

**Lemmaᵉ 3.5.**ᵉ Functorialityᵉ ofᵉ theᵉ Sequentialᵉ Colimit.ᵉ

```agda
open import synthetic-homotopy-theory.functoriality-sequential-colimitsᵉ using
  ( map-hom-standard-sequential-colimitᵉ --ᵉ "aᵉ naturalᵉ transformationᵉ inducesᵉ aᵉ map"ᵉ
  ; preserves-id-map-hom-standard-sequential-colimitᵉ --ᵉ "1∞ᵉ ~ᵉ id(A∞)"ᵉ
  ; preserves-comp-map-hom-standard-sequential-colimitᵉ --ᵉ "(σᵉ ∘ᵉ τ)∞ᵉ ~ᵉ σ∞ᵉ ∘ᵉ τ∞"ᵉ
  ; htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagramᵉ --ᵉ "homotopyᵉ ofᵉ naturalᵉ transformationsᵉ inducesᵉ aᵉ homotopy"ᵉ
  ; equiv-equiv-standard-sequential-colimitᵉ --ᵉ "ifᵉ τᵉ isᵉ anᵉ equivalence,ᵉ thenᵉ τ∞ᵉ isᵉ anᵉ equivalence"ᵉ
  )
```

**Lemmaᵉ 3.6.**ᵉ Droppingᵉ aᵉ headᵉ ofᵉ aᵉ sequentialᵉ diagramᵉ preservesᵉ theᵉ sequentialᵉ
colimit.ᵉ

**Lemmaᵉ 3.7.**ᵉ Droppingᵉ finitelyᵉ manyᵉ verticesᵉ fromᵉ theᵉ beginningᵉ ofᵉ aᵉ
sequentialᵉ diagramᵉ preservesᵉ theᵉ sequentialᵉ colimit.ᵉ

Denotingᵉ byᵉ `A[k]`ᵉ theᵉ sequenceᵉ `A`ᵉ with theᵉ firstᵉ `k`ᵉ verticesᵉ removed,ᵉ weᵉ showᵉ
thatᵉ theᵉ typeᵉ ofᵉ coconesᵉ underᵉ `A[k]`ᵉ isᵉ equivalentᵉ to theᵉ typeᵉ ofᵉ coconesᵉ underᵉ
`A`,ᵉ andᵉ concludeᵉ thatᵉ anyᵉ sequentialᵉ colimitᵉ ofᵉ `A[k]`ᵉ alsoᵉ hasᵉ theᵉ universalᵉ
propertyᵉ ofᵉ aᵉ colimitᵉ ofᵉ `A`.ᵉ Specializingᵉ to theᵉ standardᵉ sequentialᵉ colimit,ᵉ
weᵉ getᵉ andᵉ equivalenceᵉ `A[k]∞ᵉ ≃ᵉ A∞`.ᵉ

```agda
open import synthetic-homotopy-theory.shifts-sequential-diagramsᵉ using
  ( compute-sequential-colimit-shift-sequential-diagramᵉ --ᵉ "A[k]∞ᵉ ≃ᵉ A∞"ᵉ
  )
compute-sequential-colimit-shift-sequential-diagram-onceᵉ =
  λ lᵉ (Aᵉ : sequential-diagramᵉ lᵉ) →
    compute-sequential-colimit-shift-sequential-diagramᵉ Aᵉ 1
```

## 4 Fibered Sequences

Theᵉ fourthᵉ sectionᵉ definesᵉ fiberedᵉ sequences,ᵉ whichᵉ weᵉ callᵉ _dependentᵉ
sequentialᵉ diagramsᵉ_ in theᵉ library.ᵉ Itᵉ introducesᵉ theᵉ "Σᵉ ofᵉ aᵉ sequence",ᵉ whichᵉ
weᵉ callᵉ theᵉ _totalᵉ sequentialᵉ diagram_,ᵉ andᵉ asksᵉ theᵉ mainᵉ questionᵉ aboutᵉ theᵉ
interplayᵉ betweenᵉ Σᵉ andᵉ takingᵉ theᵉ colimit.ᵉ

Theᵉ paperᵉ definesᵉ fiberedᵉ sequencesᵉ asᵉ aᵉ familyᵉ overᵉ theᵉ totalᵉ spaceᵉ
`Bᵉ : Σᵉ ℕᵉ Aᵉ → 𝒰`,ᵉ butᵉ weᵉ useᵉ theᵉ curriedᵉ definitionᵉ `Bᵉ : (nᵉ : ℕᵉ) → A(nᵉ) → 𝒰`.ᵉ

**Definitionᵉ 4.1.**ᵉ Fiberedᵉ sequences.ᵉ Equifiberedᵉ sequences.ᵉ

```agda
open import synthetic-homotopy-theory.dependent-sequential-diagramsᵉ using
  ( dependent-sequential-diagramᵉ --ᵉ "Aᵉ sequenceᵉ (B,ᵉ bᵉ) fiberedᵉ overᵉ (A,ᵉ a)"ᵉ
  )
```

**Lemmaᵉ 4.2.**ᵉ Theᵉ typeᵉ ofᵉ familiesᵉ overᵉ aᵉ colimitᵉ isᵉ equivalentᵉ to theᵉ typeᵉ ofᵉ
equifiberedᵉ sequences.ᵉ

Thisᵉ propertyᵉ isᵉ alsoᵉ calledᵉ theᵉ _descentᵉ propertyᵉ ofᵉ sequentialᵉ colimits_,ᵉ
becauseᵉ itᵉ characterizesᵉ familiesᵉ overᵉ aᵉ sequentialᵉ colimit.ᵉ

```agda
--ᵉ TODOᵉ
```

**Definitionᵉ 4.3.**ᵉ Σᵉ ofᵉ aᵉ fiberedᵉ sequence.ᵉ

```agda
open import synthetic-homotopy-theory.total-sequential-diagramsᵉ using
  ( total-sequential-diagramᵉ --ᵉ "Σᵉ (A,ᵉ aᵉ) (B,ᵉ b)"ᵉ
  ; pr1-total-sequential-diagramᵉ --ᵉ "theᵉ canonicalᵉ projection"ᵉ
  )
```

**Construction.**ᵉ Theᵉ equifiberedᵉ familyᵉ associatedᵉ to aᵉ fiberedᵉ sequence.ᵉ

```agda
--ᵉ TODOᵉ
```

## 5 Colimits and Sums

**Theoremᵉ 5.1.**ᵉ Interactionᵉ betweenᵉ `colim`ᵉ andᵉ `Σ`.ᵉ

```agda
--ᵉ TODOᵉ
```

## 6 Induction on the Sum of Sequential Colimits

```agda
--ᵉ TODOᵉ
```

## 7 Applications of the Main Theorem

**Lemmaᵉ 7.1.**ᵉ TODOᵉ description.ᵉ

```agda
--ᵉ TODOᵉ
```

**Lemmaᵉ 7.2.**ᵉ Colimitᵉ ofᵉ theᵉ terminalᵉ sequentialᵉ diagramᵉ isᵉ contractible.ᵉ

```agda
--ᵉ TODOᵉ
```

**Lemmaᵉ 7.3.**ᵉ Encode-decode.ᵉ

Thisᵉ principleᵉ isᵉ calledᵉ theᵉ _Fundamentalᵉ theoremᵉ ofᵉ identityᵉ typesᵉ_ in theᵉ
library.ᵉ

```agda
open import foundation.fundamental-theorem-of-identity-typesᵉ using
  ( fundamental-theorem-idᵉ)
```

**Lemmaᵉ 7.4.**ᵉ Characterizationᵉ ofᵉ pathᵉ spacesᵉ ofᵉ imagesᵉ ofᵉ theᵉ canonicalᵉ mapsᵉ
intoᵉ theᵉ sequentialᵉ colimit.ᵉ

```agda
--ᵉ TODOᵉ
```

**Corollaryᵉ 7.5.**ᵉ Theᵉ loopᵉ spaceᵉ ofᵉ aᵉ sequentialᵉ colimitᵉ isᵉ theᵉ sequentialᵉ
colimitᵉ ofᵉ loopᵉ spaces.ᵉ

```agda
--ᵉ TODOᵉ
```

**Corollaryᵉ 7.6.**ᵉ Forᵉ aᵉ morphismᵉ ofᵉ sequentialᵉ diagrams,ᵉ theᵉ fibersᵉ ofᵉ theᵉ
inducedᵉ mapᵉ betweenᵉ sequentialᵉ colimitsᵉ areᵉ characterizedᵉ asᵉ sequentialᵉ colimitsᵉ
ofᵉ theᵉ fibers.ᵉ

```agda
--ᵉ TODOᵉ
```

**Corollaryᵉ 7.7.1.**ᵉ Ifᵉ eachᵉ typeᵉ in aᵉ sequentialᵉ diagramᵉ isᵉ `k`-truncated,ᵉ thenᵉ
theᵉ colimitᵉ isᵉ `k`-truncated.ᵉ

```agda
--ᵉ TODOᵉ
```

**Corollaryᵉ 7.7.2.**ᵉ Theᵉ `k`-truncationᵉ ofᵉ aᵉ sequentialᵉ colimitᵉ isᵉ theᵉ
sequentialᵉ colimitᵉ ofᵉ `k`-truncations.ᵉ

```agda
--ᵉ TODOᵉ
```

**Corollaryᵉ 7.7.3.**ᵉ Ifᵉ eachᵉ typeᵉ in aᵉ sequentialᵉ diagramᵉ isᵉ `k`-connected,ᵉ thenᵉ
theᵉ colimitᵉ isᵉ `k`-connected.ᵉ

```agda
--ᵉ TODOᵉ
```

**Corollaryᵉ 7.7.4.**ᵉ Ifᵉ eachᵉ componentᵉ ofᵉ aᵉ morphismᵉ betweenᵉ sequentialᵉ diagramsᵉ
isᵉ `k`-truncated/`k`-connected,ᵉ thenᵉ theᵉ inducedᵉ mapᵉ ofᵉ sequentialᵉ colimitsᵉ isᵉ
`k`-truncated/`k`-connected.ᵉ

```agda
--ᵉ TODOᵉ
```

**Corollaryᵉ 7.7.5.**ᵉ Ifᵉ eachᵉ mapᵉ in aᵉ sequentialᵉ diagramᵉ isᵉ
`k`-truncated/`k`-connected,ᵉ thenᵉ theᵉ firstᵉ injectionᵉ intoᵉ theᵉ colimitᵉ isᵉ
`k`-truncated/`k`-connected.ᵉ

```agda
--ᵉ TODOᵉ
```