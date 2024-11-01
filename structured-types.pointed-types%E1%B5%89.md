# Pointed types

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="structured-types.pointed-types%25E1%25B5%2589.html" class="Module">structured-types.pointed-typesᵉ</a> <a id="65" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="121" class="Keyword">open</a> <a id="126" class="Keyword">import</a> <a id="133" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="166" class="Keyword">open</a> <a id="171" class="Keyword">import</a> <a id="178" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
</pre>
</details>

## Idea

A **pointed type** is a type `A` equipped with an element `a : A`.

## Definition

### The universe of pointed types

<pre class="Agda"><a id="Pointed-Typeᵉ"></a><a id="358" href="structured-types.pointed-types%25E1%25B5%2589.html#358" class="Function">Pointed-Typeᵉ</a> <a id="372" class="Symbol">:</a> <a id="374" class="Symbol">(</a><a id="375" href="structured-types.pointed-types%25E1%25B5%2589.html#375" class="Bound">lᵉ</a> <a id="378" class="Symbol">:</a> <a id="380" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="385" class="Symbol">)</a> <a id="387" class="Symbol">→</a> <a id="389" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="393" class="Symbol">(</a><a id="394" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="399" href="structured-types.pointed-types%25E1%25B5%2589.html#375" class="Bound">lᵉ</a><a id="401" class="Symbol">)</a>
<a id="403" href="structured-types.pointed-types%25E1%25B5%2589.html#358" class="Function">Pointed-Typeᵉ</a> <a id="417" href="structured-types.pointed-types%25E1%25B5%2589.html#417" class="Bound">lᵉ</a> <a id="420" class="Symbol">=</a> <a id="422" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="425" class="Symbol">(</a><a id="426" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="430" href="structured-types.pointed-types%25E1%25B5%2589.html#417" class="Bound">lᵉ</a><a id="432" class="Symbol">)</a> <a id="434" class="Symbol">(λ</a> <a id="437" href="structured-types.pointed-types%25E1%25B5%2589.html#437" class="Bound">Xᵉ</a> <a id="440" class="Symbol">→</a> <a id="442" href="structured-types.pointed-types%25E1%25B5%2589.html#437" class="Bound">Xᵉ</a><a id="444" class="Symbol">)</a>

<a id="447" class="Keyword">module</a> <a id="454" href="structured-types.pointed-types%25E1%25B5%2589.html#454" class="Module">_</a>
  <a id="458" class="Symbol">{</a><a id="459" href="structured-types.pointed-types%25E1%25B5%2589.html#459" class="Bound">lᵉ</a> <a id="462" class="Symbol">:</a> <a id="464" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="469" class="Symbol">}</a> <a id="471" class="Symbol">(</a><a id="472" href="structured-types.pointed-types%25E1%25B5%2589.html#472" class="Bound">Aᵉ</a> <a id="475" class="Symbol">:</a> <a id="477" href="structured-types.pointed-types%25E1%25B5%2589.html#358" class="Function">Pointed-Typeᵉ</a> <a id="491" href="structured-types.pointed-types%25E1%25B5%2589.html#459" class="Bound">lᵉ</a><a id="493" class="Symbol">)</a>
  <a id="497" class="Keyword">where</a>

  <a id="506" href="structured-types.pointed-types%25E1%25B5%2589.html#506" class="Function">type-Pointed-Typeᵉ</a> <a id="525" class="Symbol">:</a> <a id="527" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="531" href="structured-types.pointed-types%25E1%25B5%2589.html#459" class="Bound">lᵉ</a>
  <a id="536" href="structured-types.pointed-types%25E1%25B5%2589.html#506" class="Function">type-Pointed-Typeᵉ</a> <a id="555" class="Symbol">=</a> <a id="557" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="562" href="structured-types.pointed-types%25E1%25B5%2589.html#472" class="Bound">Aᵉ</a>

  <a id="568" href="structured-types.pointed-types%25E1%25B5%2589.html#568" class="Function">point-Pointed-Typeᵉ</a> <a id="588" class="Symbol">:</a> <a id="590" href="structured-types.pointed-types%25E1%25B5%2589.html#506" class="Function">type-Pointed-Typeᵉ</a>
  <a id="611" href="structured-types.pointed-types%25E1%25B5%2589.html#568" class="Function">point-Pointed-Typeᵉ</a> <a id="631" class="Symbol">=</a> <a id="633" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="638" href="structured-types.pointed-types%25E1%25B5%2589.html#472" class="Bound">Aᵉ</a>
</pre>
### Evaluation at the base point

<pre class="Agda"><a id="ev-point-Pointed-Typeᵉ"></a><a id="688" href="structured-types.pointed-types%25E1%25B5%2589.html#688" class="Function">ev-point-Pointed-Typeᵉ</a> <a id="711" class="Symbol">:</a>
  <a id="715" class="Symbol">{</a><a id="716" href="structured-types.pointed-types%25E1%25B5%2589.html#716" class="Bound">l1ᵉ</a> <a id="720" href="structured-types.pointed-types%25E1%25B5%2589.html#720" class="Bound">l2ᵉ</a> <a id="724" class="Symbol">:</a> <a id="726" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="731" class="Symbol">}</a> <a id="733" class="Symbol">(</a><a id="734" href="structured-types.pointed-types%25E1%25B5%2589.html#734" class="Bound">Aᵉ</a> <a id="737" class="Symbol">:</a> <a id="739" href="structured-types.pointed-types%25E1%25B5%2589.html#358" class="Function">Pointed-Typeᵉ</a> <a id="753" href="structured-types.pointed-types%25E1%25B5%2589.html#716" class="Bound">l1ᵉ</a><a id="756" class="Symbol">)</a> <a id="758" class="Symbol">{</a><a id="759" href="structured-types.pointed-types%25E1%25B5%2589.html#759" class="Bound">Bᵉ</a> <a id="762" class="Symbol">:</a> <a id="764" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="768" href="structured-types.pointed-types%25E1%25B5%2589.html#720" class="Bound">l2ᵉ</a><a id="771" class="Symbol">}</a> <a id="773" class="Symbol">→</a>
  <a id="777" class="Symbol">(</a><a id="778" href="structured-types.pointed-types%25E1%25B5%2589.html#506" class="Function">type-Pointed-Typeᵉ</a> <a id="797" href="structured-types.pointed-types%25E1%25B5%2589.html#734" class="Bound">Aᵉ</a> <a id="800" class="Symbol">→</a> <a id="802" href="structured-types.pointed-types%25E1%25B5%2589.html#759" class="Bound">Bᵉ</a><a id="804" class="Symbol">)</a> <a id="806" class="Symbol">→</a> <a id="808" href="structured-types.pointed-types%25E1%25B5%2589.html#759" class="Bound">Bᵉ</a>
<a id="811" href="structured-types.pointed-types%25E1%25B5%2589.html#688" class="Function">ev-point-Pointed-Typeᵉ</a> <a id="834" href="structured-types.pointed-types%25E1%25B5%2589.html#834" class="Bound">Aᵉ</a> <a id="837" href="structured-types.pointed-types%25E1%25B5%2589.html#837" class="Bound">fᵉ</a> <a id="840" class="Symbol">=</a> <a id="842" href="structured-types.pointed-types%25E1%25B5%2589.html#837" class="Bound">fᵉ</a> <a id="845" class="Symbol">(</a><a id="846" href="structured-types.pointed-types%25E1%25B5%2589.html#568" class="Function">point-Pointed-Typeᵉ</a> <a id="866" href="structured-types.pointed-types%25E1%25B5%2589.html#834" class="Bound">Aᵉ</a><a id="868" class="Symbol">)</a>
</pre>
## See also

- The notion of _nonempty types_ is treated in
  [`foundation.empty-types`](foundation.empty-types.md).
- The notion of _inhabited types_ is treated in
  [`foundation.inhabited-types`](foundation.inhabited-types.md).