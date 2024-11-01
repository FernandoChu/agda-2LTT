# Negation

<pre class="Agda"><a id="21" class="Keyword">module</a> <a id="28" href="foundation-core.negation.html" class="Module">foundation-core.negation</a> <a id="53" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="109" class="Keyword">open</a> <a id="114" class="Keyword">import</a> <a id="121" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="149" class="Keyword">open</a> <a id="154" class="Keyword">import</a> <a id="161" href="foundation-core.empty-types.html" class="Module">foundation-core.empty-types</a>
</pre>
</details>

## Idea

The
[Curry–Howard interpretation](https://en.wikipedia.org/wiki/Curry–Howard_correspondence)
of _negation_ in type theory is the interpretation of the proposition `P ⇒ ⊥`
using propositions as types. Thus, the
{{#concept "negation" Disambiguation="of a type" WDID=Q190558 WD="logical negation" Agda=¬_}}
of a type `A` is the type `A → empty`.

## Definition

<pre class="Agda"><a id="582" class="Keyword">infix</a> <a id="588" class="Number">25</a> <a id="591" href="foundation-core.negation.html#595" class="Function Operator">¬_</a>

<a id="¬_"></a><a id="595" href="foundation-core.negation.html#595" class="Function Operator">¬_</a> <a id="598" class="Symbol">:</a> <a id="600" class="Symbol">{</a><a id="601" href="foundation-core.negation.html#601" class="Bound">l</a> <a id="603" class="Symbol">:</a> <a id="605" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="610" class="Symbol">}</a> <a id="612" class="Symbol">→</a> <a id="614" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="617" href="foundation-core.negation.html#601" class="Bound">l</a> <a id="619" class="Symbol">→</a> <a id="621" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="624" href="foundation-core.negation.html#601" class="Bound">l</a>
<a id="626" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="628" href="foundation-core.negation.html#628" class="Bound">A</a> <a id="630" class="Symbol">=</a> <a id="632" href="foundation-core.negation.html#628" class="Bound">A</a> <a id="634" class="Symbol">→</a> <a id="636" href="foundation-core.empty-types.html#801" class="Datatype">empty</a>

<a id="map-neg"></a><a id="643" href="foundation-core.negation.html#643" class="Function">map-neg</a> <a id="651" class="Symbol">:</a>
  <a id="655" class="Symbol">{</a><a id="656" href="foundation-core.negation.html#656" class="Bound">l1</a> <a id="659" href="foundation-core.negation.html#659" class="Bound">l2</a> <a id="662" class="Symbol">:</a> <a id="664" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="669" class="Symbol">}</a> <a id="671" class="Symbol">{</a><a id="672" href="foundation-core.negation.html#672" class="Bound">P</a> <a id="674" class="Symbol">:</a> <a id="676" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="679" href="foundation-core.negation.html#656" class="Bound">l1</a><a id="681" class="Symbol">}</a> <a id="683" class="Symbol">{</a><a id="684" href="foundation-core.negation.html#684" class="Bound">Q</a> <a id="686" class="Symbol">:</a> <a id="688" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="691" href="foundation-core.negation.html#659" class="Bound">l2</a><a id="693" class="Symbol">}</a> <a id="695" class="Symbol">→</a>
  <a id="699" class="Symbol">(</a><a id="700" href="foundation-core.negation.html#672" class="Bound">P</a> <a id="702" class="Symbol">→</a> <a id="704" href="foundation-core.negation.html#684" class="Bound">Q</a><a id="705" class="Symbol">)</a> <a id="707" class="Symbol">→</a> <a id="709" class="Symbol">(</a><a id="710" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="712" href="foundation-core.negation.html#684" class="Bound">Q</a> <a id="714" class="Symbol">→</a> <a id="716" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="718" href="foundation-core.negation.html#672" class="Bound">P</a><a id="719" class="Symbol">)</a>
<a id="721" href="foundation-core.negation.html#643" class="Function">map-neg</a> <a id="729" href="foundation-core.negation.html#729" class="Bound">f</a> <a id="731" href="foundation-core.negation.html#731" class="Bound">nq</a> <a id="734" href="foundation-core.negation.html#734" class="Bound">p</a> <a id="736" class="Symbol">=</a> <a id="738" href="foundation-core.negation.html#731" class="Bound">nq</a> <a id="741" class="Symbol">(</a><a id="742" href="foundation-core.negation.html#729" class="Bound">f</a> <a id="744" href="foundation-core.negation.html#734" class="Bound">p</a><a id="745" class="Symbol">)</a>
</pre>
## External links

- [negation](https://ncatlab.org/nlab/show/negation) at $n$Lab
- [Negation](https://en.wikipedia.org/wiki/Negation) at Wikipedia
