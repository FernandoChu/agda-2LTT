# Negation

<pre class="Agda"><a id="21" class="Keyword">module</a> <a id="28" href="foundation-core.negation%25E1%25B5%2589.html" class="Module">foundation-core.negationᵉ</a> <a id="54" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="110" class="Keyword">open</a> <a id="115" class="Keyword">import</a> <a id="122" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="151" class="Keyword">open</a> <a id="156" class="Keyword">import</a> <a id="163" href="foundation-core.empty-types%25E1%25B5%2589.html" class="Module">foundation-core.empty-typesᵉ</a>
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

<pre class="Agda"><a id="585" class="Keyword">infix</a> <a id="591" class="Number">25</a> <a id="594" href="foundation-core.negation%25E1%25B5%2589.html#599" class="Function Operator">¬ᵉ_</a>

<a id="¬ᵉ_"></a><a id="599" href="foundation-core.negation%25E1%25B5%2589.html#599" class="Function Operator">¬ᵉ_</a> <a id="603" class="Symbol">:</a> <a id="605" class="Symbol">{</a><a id="606" href="foundation-core.negation%25E1%25B5%2589.html#606" class="Bound">lᵉ</a> <a id="609" class="Symbol">:</a> <a id="611" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="616" class="Symbol">}</a> <a id="618" class="Symbol">→</a> <a id="620" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="624" href="foundation-core.negation%25E1%25B5%2589.html#606" class="Bound">lᵉ</a> <a id="627" class="Symbol">→</a> <a id="629" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="633" href="foundation-core.negation%25E1%25B5%2589.html#606" class="Bound">lᵉ</a>
<a id="636" href="foundation-core.negation%25E1%25B5%2589.html#599" class="Function Operator">¬ᵉ</a> <a id="639" href="foundation-core.negation%25E1%25B5%2589.html#639" class="Bound">Aᵉ</a> <a id="642" class="Symbol">=</a> <a id="644" href="foundation-core.negation%25E1%25B5%2589.html#639" class="Bound">Aᵉ</a> <a id="647" class="Symbol">→</a> <a id="649" href="foundation-core.empty-types%25E1%25B5%2589.html#811" class="Datatype">emptyᵉ</a>

<a id="map-negᵉ"></a><a id="657" href="foundation-core.negation%25E1%25B5%2589.html#657" class="Function">map-negᵉ</a> <a id="666" class="Symbol">:</a>
  <a id="670" class="Symbol">{</a><a id="671" href="foundation-core.negation%25E1%25B5%2589.html#671" class="Bound">l1ᵉ</a> <a id="675" href="foundation-core.negation%25E1%25B5%2589.html#675" class="Bound">l2ᵉ</a> <a id="679" class="Symbol">:</a> <a id="681" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="686" class="Symbol">}</a> <a id="688" class="Symbol">{</a><a id="689" href="foundation-core.negation%25E1%25B5%2589.html#689" class="Bound">Pᵉ</a> <a id="692" class="Symbol">:</a> <a id="694" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="698" href="foundation-core.negation%25E1%25B5%2589.html#671" class="Bound">l1ᵉ</a><a id="701" class="Symbol">}</a> <a id="703" class="Symbol">{</a><a id="704" href="foundation-core.negation%25E1%25B5%2589.html#704" class="Bound">Qᵉ</a> <a id="707" class="Symbol">:</a> <a id="709" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="713" href="foundation-core.negation%25E1%25B5%2589.html#675" class="Bound">l2ᵉ</a><a id="716" class="Symbol">}</a> <a id="718" class="Symbol">→</a>
  <a id="722" class="Symbol">(</a><a id="723" href="foundation-core.negation%25E1%25B5%2589.html#689" class="Bound">Pᵉ</a> <a id="726" class="Symbol">→</a> <a id="728" href="foundation-core.negation%25E1%25B5%2589.html#704" class="Bound">Qᵉ</a><a id="730" class="Symbol">)</a> <a id="732" class="Symbol">→</a> <a id="734" class="Symbol">(</a><a id="735" href="foundation-core.negation%25E1%25B5%2589.html#599" class="Function Operator">¬ᵉ</a> <a id="738" href="foundation-core.negation%25E1%25B5%2589.html#704" class="Bound">Qᵉ</a> <a id="741" class="Symbol">→</a> <a id="743" href="foundation-core.negation%25E1%25B5%2589.html#599" class="Function Operator">¬ᵉ</a> <a id="746" href="foundation-core.negation%25E1%25B5%2589.html#689" class="Bound">Pᵉ</a><a id="748" class="Symbol">)</a>
<a id="750" href="foundation-core.negation%25E1%25B5%2589.html#657" class="Function">map-negᵉ</a> <a id="759" href="foundation-core.negation%25E1%25B5%2589.html#759" class="Bound">fᵉ</a> <a id="762" href="foundation-core.negation%25E1%25B5%2589.html#762" class="Bound">nqᵉ</a> <a id="766" href="foundation-core.negation%25E1%25B5%2589.html#766" class="Bound">pᵉ</a> <a id="769" class="Symbol">=</a> <a id="771" href="foundation-core.negation%25E1%25B5%2589.html#762" class="Bound">nqᵉ</a> <a id="775" class="Symbol">(</a><a id="776" href="foundation-core.negation%25E1%25B5%2589.html#759" class="Bound">fᵉ</a> <a id="779" href="foundation-core.negation%25E1%25B5%2589.html#766" class="Bound">pᵉ</a><a id="781" class="Symbol">)</a>
</pre>
## External links

- [negation](https://ncatlab.org/nlab/show/negation) at $n$Lab
- [Negation](https://en.wikipedia.org/wiki/Negation) at Wikipedia