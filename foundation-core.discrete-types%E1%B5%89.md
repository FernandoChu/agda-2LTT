# Discrete types

<pre class="Agda"><a id="27" class="Keyword">module</a> <a id="34" href="foundation-core.discrete-types%25E1%25B5%2589.html" class="Module">foundation-core.discrete-typesᵉ</a> <a id="66" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="122" class="Keyword">open</a> <a id="127" class="Keyword">import</a> <a id="134" href="foundation.decidable-equality%25E1%25B5%2589.html" class="Module">foundation.decidable-equalityᵉ</a>
<a id="165" class="Keyword">open</a> <a id="170" class="Keyword">import</a> <a id="177" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="210" class="Keyword">open</a> <a id="215" class="Keyword">import</a> <a id="222" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="251" class="Keyword">open</a> <a id="256" class="Keyword">import</a> <a id="263" href="foundation-core.sets%25E1%25B5%2589.html" class="Module">foundation-core.setsᵉ</a>
</pre>
</details>

## Idea

A {{#concept "discrete type" Agda=Discrete-Type}} is a type that has
[decidable equality](foundation.decidable-equality.md). Consequently, discrete
types are [sets](foundation-core.sets.md) by Hedberg's theorem.

## Definition

<pre class="Agda"><a id="Discrete-Typeᵉ"></a><a id="547" href="foundation-core.discrete-types%25E1%25B5%2589.html#547" class="Function">Discrete-Typeᵉ</a> <a id="562" class="Symbol">:</a> <a id="564" class="Symbol">(</a><a id="565" href="foundation-core.discrete-types%25E1%25B5%2589.html#565" class="Bound">lᵉ</a> <a id="568" class="Symbol">:</a> <a id="570" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="575" class="Symbol">)</a> <a id="577" class="Symbol">→</a> <a id="579" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="583" class="Symbol">(</a><a id="584" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="589" href="foundation-core.discrete-types%25E1%25B5%2589.html#565" class="Bound">lᵉ</a><a id="591" class="Symbol">)</a>
<a id="593" href="foundation-core.discrete-types%25E1%25B5%2589.html#547" class="Function">Discrete-Typeᵉ</a> <a id="608" href="foundation-core.discrete-types%25E1%25B5%2589.html#608" class="Bound">lᵉ</a> <a id="611" class="Symbol">=</a> <a id="613" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="616" class="Symbol">(</a><a id="617" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="621" href="foundation-core.discrete-types%25E1%25B5%2589.html#608" class="Bound">lᵉ</a><a id="623" class="Symbol">)</a> <a id="625" href="foundation.decidable-equality%25E1%25B5%2589.html#1290" class="Function">has-decidable-equalityᵉ</a>

<a id="650" class="Keyword">module</a> <a id="657" href="foundation-core.discrete-types%25E1%25B5%2589.html#657" class="Module">_</a>
  <a id="661" class="Symbol">{</a><a id="662" href="foundation-core.discrete-types%25E1%25B5%2589.html#662" class="Bound">lᵉ</a> <a id="665" class="Symbol">:</a> <a id="667" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="672" class="Symbol">}</a> <a id="674" class="Symbol">(</a><a id="675" href="foundation-core.discrete-types%25E1%25B5%2589.html#675" class="Bound">Xᵉ</a> <a id="678" class="Symbol">:</a> <a id="680" href="foundation-core.discrete-types%25E1%25B5%2589.html#547" class="Function">Discrete-Typeᵉ</a> <a id="695" href="foundation-core.discrete-types%25E1%25B5%2589.html#662" class="Bound">lᵉ</a><a id="697" class="Symbol">)</a>
  <a id="701" class="Keyword">where</a>

  <a id="710" href="foundation-core.discrete-types%25E1%25B5%2589.html#710" class="Function">type-Discrete-Typeᵉ</a> <a id="730" class="Symbol">:</a> <a id="732" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="736" href="foundation-core.discrete-types%25E1%25B5%2589.html#662" class="Bound">lᵉ</a>
  <a id="741" href="foundation-core.discrete-types%25E1%25B5%2589.html#710" class="Function">type-Discrete-Typeᵉ</a> <a id="761" class="Symbol">=</a> <a id="763" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="768" href="foundation-core.discrete-types%25E1%25B5%2589.html#675" class="Bound">Xᵉ</a>

  <a id="774" href="foundation-core.discrete-types%25E1%25B5%2589.html#774" class="Function">has-decidable-equality-type-Discrete-Typeᵉ</a> <a id="817" class="Symbol">:</a>
    <a id="823" href="foundation.decidable-equality%25E1%25B5%2589.html#1290" class="Function">has-decidable-equalityᵉ</a> <a id="847" href="foundation-core.discrete-types%25E1%25B5%2589.html#710" class="Function">type-Discrete-Typeᵉ</a>
  <a id="869" href="foundation-core.discrete-types%25E1%25B5%2589.html#774" class="Function">has-decidable-equality-type-Discrete-Typeᵉ</a> <a id="912" class="Symbol">=</a> <a id="914" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="919" href="foundation-core.discrete-types%25E1%25B5%2589.html#675" class="Bound">Xᵉ</a>

  <a id="925" href="foundation-core.discrete-types%25E1%25B5%2589.html#925" class="Function">is-set-type-Discrete-Typeᵉ</a> <a id="952" class="Symbol">:</a> <a id="954" href="foundation-core.sets%25E1%25B5%2589.html#807" class="Function">is-setᵉ</a> <a id="962" href="foundation-core.discrete-types%25E1%25B5%2589.html#710" class="Function">type-Discrete-Typeᵉ</a>
  <a id="984" href="foundation-core.discrete-types%25E1%25B5%2589.html#925" class="Function">is-set-type-Discrete-Typeᵉ</a> <a id="1011" class="Symbol">=</a>
    <a id="1017" href="foundation.decidable-equality%25E1%25B5%2589.html#7089" class="Function">is-set-has-decidable-equalityᵉ</a> <a id="1048" href="foundation-core.discrete-types%25E1%25B5%2589.html#774" class="Function">has-decidable-equality-type-Discrete-Typeᵉ</a>

  <a id="1094" href="foundation-core.discrete-types%25E1%25B5%2589.html#1094" class="Function">set-Discrete-Typeᵉ</a> <a id="1113" class="Symbol">:</a> <a id="1115" href="foundation-core.sets%25E1%25B5%2589.html#897" class="Function">Setᵉ</a> <a id="1120" href="foundation-core.discrete-types%25E1%25B5%2589.html#662" class="Bound">lᵉ</a>
  <a id="1125" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="1130" href="foundation-core.discrete-types%25E1%25B5%2589.html#1094" class="Function">set-Discrete-Typeᵉ</a> <a id="1149" class="Symbol">=</a> <a id="1151" href="foundation-core.discrete-types%25E1%25B5%2589.html#710" class="Function">type-Discrete-Typeᵉ</a>
  <a id="1173" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="1178" href="foundation-core.discrete-types%25E1%25B5%2589.html#1094" class="Function">set-Discrete-Typeᵉ</a> <a id="1197" class="Symbol">=</a> <a id="1199" href="foundation-core.discrete-types%25E1%25B5%2589.html#925" class="Function">is-set-type-Discrete-Typeᵉ</a>
</pre>
## External links

- [classical set](https://ncatlab.org/nlab/show/classical+set) at $n$Lab
- [decidable object](https://ncatlab.org/nlab/show/decidable+object) at $n$Lab