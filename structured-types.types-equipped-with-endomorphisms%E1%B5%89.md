# Types equipped with endomorphisms

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html" class="Module">structured-types.types-equipped-with-endomorphismsᵉ</a> <a id="105" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="161" class="Keyword">open</a> <a id="166" class="Keyword">import</a> <a id="173" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="foundation.endomorphisms%25E1%25B5%2589.html" class="Module">foundation.endomorphismsᵉ</a>
<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="foundation.function-types%25E1%25B5%2589.html" class="Module">foundation.function-typesᵉ</a>
<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="foundation.unit-type%25E1%25B5%2589.html" class="Module">foundation.unit-typeᵉ</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
</pre>
</details>

## Idea

A type equipped with an endomorphism consists of a type `A` equipped with a map
`A → A`.

## Definitions

### Types equipped with endomorphisms

<pre class="Agda"><a id="Type-With-Endomorphismᵉ"></a><a id="536" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#536" class="Function">Type-With-Endomorphismᵉ</a> <a id="560" class="Symbol">:</a> <a id="562" class="Symbol">(</a><a id="563" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#563" class="Bound">lᵉ</a> <a id="566" class="Symbol">:</a> <a id="568" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="573" class="Symbol">)</a> <a id="575" class="Symbol">→</a> <a id="577" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="581" class="Symbol">(</a><a id="582" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="587" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#563" class="Bound">lᵉ</a><a id="589" class="Symbol">)</a>
<a id="591" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#536" class="Function">Type-With-Endomorphismᵉ</a> <a id="615" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#615" class="Bound">lᵉ</a> <a id="618" class="Symbol">=</a> <a id="620" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="623" class="Symbol">(</a><a id="624" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="628" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#615" class="Bound">lᵉ</a><a id="630" class="Symbol">)</a> <a id="632" href="foundation-core.endomorphisms%25E1%25B5%2589.html#514" class="Function">endoᵉ</a>

<a id="639" class="Keyword">module</a> <a id="646" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#646" class="Module">_</a>
  <a id="650" class="Symbol">{</a><a id="651" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#651" class="Bound">lᵉ</a> <a id="654" class="Symbol">:</a> <a id="656" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="661" class="Symbol">}</a> <a id="663" class="Symbol">(</a><a id="664" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#664" class="Bound">Xᵉ</a> <a id="667" class="Symbol">:</a> <a id="669" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#536" class="Function">Type-With-Endomorphismᵉ</a> <a id="693" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#651" class="Bound">lᵉ</a><a id="695" class="Symbol">)</a>
  <a id="699" class="Keyword">where</a>

  <a id="708" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#708" class="Function">type-Type-With-Endomorphismᵉ</a> <a id="737" class="Symbol">:</a> <a id="739" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="743" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#651" class="Bound">lᵉ</a>
  <a id="748" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#708" class="Function">type-Type-With-Endomorphismᵉ</a> <a id="777" class="Symbol">=</a> <a id="779" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="784" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#664" class="Bound">Xᵉ</a>

  <a id="790" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#790" class="Function">endomorphism-Type-With-Endomorphismᵉ</a> <a id="827" class="Symbol">:</a>
    <a id="833" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#708" class="Function">type-Type-With-Endomorphismᵉ</a> <a id="862" class="Symbol">→</a> <a id="864" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#708" class="Function">type-Type-With-Endomorphismᵉ</a>
  <a id="895" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#790" class="Function">endomorphism-Type-With-Endomorphismᵉ</a> <a id="932" class="Symbol">=</a> <a id="934" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="939" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#664" class="Bound">Xᵉ</a>
</pre>
## Example

### Unit type equipped with endomorphisms

<pre class="Agda"><a id="trivial-Type-With-Endomorphismᵉ"></a><a id="1010" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#1010" class="Function">trivial-Type-With-Endomorphismᵉ</a> <a id="1042" class="Symbol">:</a> <a id="1044" class="Symbol">{</a><a id="1045" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#1045" class="Bound">lᵉ</a> <a id="1048" class="Symbol">:</a> <a id="1050" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1055" class="Symbol">}</a> <a id="1057" class="Symbol">→</a> <a id="1059" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#536" class="Function">Type-With-Endomorphismᵉ</a> <a id="1083" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#1045" class="Bound">lᵉ</a>
<a id="1086" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="1091" class="Symbol">(</a><a id="1092" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#1010" class="Function">trivial-Type-With-Endomorphismᵉ</a> <a id="1124" class="Symbol">{</a><a id="1125" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#1125" class="Bound">lᵉ</a><a id="1127" class="Symbol">})</a> <a id="1130" class="Symbol">=</a> <a id="1132" href="foundation.unit-type%25E1%25B5%2589.html#1438" class="Function">raise-unitᵉ</a> <a id="1144" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#1125" class="Bound">lᵉ</a>
<a id="1147" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="1152" href="structured-types.types-equipped-with-endomorphisms%25E1%25B5%2589.html#1010" class="Function">trivial-Type-With-Endomorphismᵉ</a> <a id="1184" class="Symbol">=</a> <a id="1186" href="foundation-core.function-types%25E1%25B5%2589.html#309" class="Function">idᵉ</a>
</pre>