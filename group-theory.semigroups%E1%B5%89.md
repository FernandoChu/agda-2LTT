# Semigroups

<pre class="Agda"><a id="23" class="Keyword">module</a> <a id="30" href="group-theory.semigroups%25E1%25B5%2589.html" class="Module">group-theory.semigroupsᵉ</a> <a id="55" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="111" class="Keyword">open</a> <a id="116" class="Keyword">import</a> <a id="123" href="foundation.action-on-identifications-binary-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-binary-functionsᵉ</a>
<a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-functionsᵉ</a>
<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="foundation.identity-types%25E1%25B5%2589.html" class="Module">foundation.identity-typesᵉ</a>
<a id="322" class="Keyword">open</a> <a id="327" class="Keyword">import</a> <a id="334" href="foundation.sets%25E1%25B5%2589.html" class="Module">foundation.setsᵉ</a>
<a id="351" class="Keyword">open</a> <a id="356" class="Keyword">import</a> <a id="363" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
</pre>
</details>

## Idea

**Semigroups** are [sets](foundation-core.sets.md) equipped with an associative
binary operation.

## Definitions

<pre class="Agda"><a id="has-associative-mulᵉ"></a><a id="540" href="group-theory.semigroups%25E1%25B5%2589.html#540" class="Function">has-associative-mulᵉ</a> <a id="561" class="Symbol">:</a> <a id="563" class="Symbol">{</a><a id="564" href="group-theory.semigroups%25E1%25B5%2589.html#564" class="Bound">lᵉ</a> <a id="567" class="Symbol">:</a> <a id="569" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="574" class="Symbol">}</a> <a id="576" class="Symbol">(</a><a id="577" href="group-theory.semigroups%25E1%25B5%2589.html#577" class="Bound">Xᵉ</a> <a id="580" class="Symbol">:</a> <a id="582" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="586" href="group-theory.semigroups%25E1%25B5%2589.html#564" class="Bound">lᵉ</a><a id="588" class="Symbol">)</a> <a id="590" class="Symbol">→</a> <a id="592" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="596" href="group-theory.semigroups%25E1%25B5%2589.html#564" class="Bound">lᵉ</a>
<a id="599" href="group-theory.semigroups%25E1%25B5%2589.html#540" class="Function">has-associative-mulᵉ</a> <a id="620" href="group-theory.semigroups%25E1%25B5%2589.html#620" class="Bound">Xᵉ</a> <a id="623" class="Symbol">=</a>
  <a id="627" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="630" class="Symbol">(</a><a id="631" href="group-theory.semigroups%25E1%25B5%2589.html#620" class="Bound">Xᵉ</a> <a id="634" class="Symbol">→</a> <a id="636" href="group-theory.semigroups%25E1%25B5%2589.html#620" class="Bound">Xᵉ</a> <a id="639" class="Symbol">→</a> <a id="641" href="group-theory.semigroups%25E1%25B5%2589.html#620" class="Bound">Xᵉ</a><a id="643" class="Symbol">)</a> <a id="645" class="Symbol">(λ</a> <a id="648" href="group-theory.semigroups%25E1%25B5%2589.html#648" class="Bound">μᵉ</a> <a id="651" class="Symbol">→</a> <a id="653" class="Symbol">(</a><a id="654" href="group-theory.semigroups%25E1%25B5%2589.html#654" class="Bound">xᵉ</a> <a id="657" href="group-theory.semigroups%25E1%25B5%2589.html#657" class="Bound">yᵉ</a> <a id="660" href="group-theory.semigroups%25E1%25B5%2589.html#660" class="Bound">zᵉ</a> <a id="663" class="Symbol">:</a> <a id="665" href="group-theory.semigroups%25E1%25B5%2589.html#620" class="Bound">Xᵉ</a><a id="667" class="Symbol">)</a> <a id="669" class="Symbol">→</a> <a id="671" href="foundation-core.identity-types%25E1%25B5%2589.html#2647" class="Datatype">Idᵉ</a> <a id="675" class="Symbol">(</a><a id="676" href="group-theory.semigroups%25E1%25B5%2589.html#648" class="Bound">μᵉ</a> <a id="679" class="Symbol">(</a><a id="680" href="group-theory.semigroups%25E1%25B5%2589.html#648" class="Bound">μᵉ</a> <a id="683" href="group-theory.semigroups%25E1%25B5%2589.html#654" class="Bound">xᵉ</a> <a id="686" href="group-theory.semigroups%25E1%25B5%2589.html#657" class="Bound">yᵉ</a><a id="688" class="Symbol">)</a> <a id="690" href="group-theory.semigroups%25E1%25B5%2589.html#660" class="Bound">zᵉ</a><a id="692" class="Symbol">)</a> <a id="694" class="Symbol">(</a><a id="695" href="group-theory.semigroups%25E1%25B5%2589.html#648" class="Bound">μᵉ</a> <a id="698" href="group-theory.semigroups%25E1%25B5%2589.html#654" class="Bound">xᵉ</a> <a id="701" class="Symbol">(</a><a id="702" href="group-theory.semigroups%25E1%25B5%2589.html#648" class="Bound">μᵉ</a> <a id="705" href="group-theory.semigroups%25E1%25B5%2589.html#657" class="Bound">yᵉ</a> <a id="708" href="group-theory.semigroups%25E1%25B5%2589.html#660" class="Bound">zᵉ</a><a id="710" class="Symbol">)))</a>

<a id="has-associative-mul-Setᵉ"></a><a id="715" href="group-theory.semigroups%25E1%25B5%2589.html#715" class="Function">has-associative-mul-Setᵉ</a> <a id="740" class="Symbol">:</a>
  <a id="744" class="Symbol">{</a><a id="745" href="group-theory.semigroups%25E1%25B5%2589.html#745" class="Bound">lᵉ</a> <a id="748" class="Symbol">:</a> <a id="750" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="755" class="Symbol">}</a> <a id="757" class="Symbol">(</a><a id="758" href="group-theory.semigroups%25E1%25B5%2589.html#758" class="Bound">Xᵉ</a> <a id="761" class="Symbol">:</a> <a id="763" href="foundation-core.sets%25E1%25B5%2589.html#897" class="Function">Setᵉ</a> <a id="768" href="group-theory.semigroups%25E1%25B5%2589.html#745" class="Bound">lᵉ</a><a id="770" class="Symbol">)</a> <a id="772" class="Symbol">→</a> <a id="774" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="778" href="group-theory.semigroups%25E1%25B5%2589.html#745" class="Bound">lᵉ</a>
<a id="781" href="group-theory.semigroups%25E1%25B5%2589.html#715" class="Function">has-associative-mul-Setᵉ</a> <a id="806" href="group-theory.semigroups%25E1%25B5%2589.html#806" class="Bound">Xᵉ</a> <a id="809" class="Symbol">=</a>
  <a id="813" href="group-theory.semigroups%25E1%25B5%2589.html#540" class="Function">has-associative-mulᵉ</a> <a id="834" class="Symbol">(</a><a id="835" href="foundation-core.sets%25E1%25B5%2589.html#1014" class="Function">type-Setᵉ</a> <a id="845" href="group-theory.semigroups%25E1%25B5%2589.html#806" class="Bound">Xᵉ</a><a id="847" class="Symbol">)</a>

<a id="Semigroupᵉ"></a><a id="850" href="group-theory.semigroups%25E1%25B5%2589.html#850" class="Function">Semigroupᵉ</a> <a id="861" class="Symbol">:</a>
  <a id="865" class="Symbol">(</a><a id="866" href="group-theory.semigroups%25E1%25B5%2589.html#866" class="Bound">lᵉ</a> <a id="869" class="Symbol">:</a> <a id="871" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="876" class="Symbol">)</a> <a id="878" class="Symbol">→</a> <a id="880" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="884" class="Symbol">(</a><a id="885" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="890" href="group-theory.semigroups%25E1%25B5%2589.html#866" class="Bound">lᵉ</a><a id="892" class="Symbol">)</a>
<a id="894" href="group-theory.semigroups%25E1%25B5%2589.html#850" class="Function">Semigroupᵉ</a> <a id="905" href="group-theory.semigroups%25E1%25B5%2589.html#905" class="Bound">lᵉ</a> <a id="908" class="Symbol">=</a> <a id="910" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="913" class="Symbol">(</a><a id="914" href="foundation-core.sets%25E1%25B5%2589.html#897" class="Function">Setᵉ</a> <a id="919" href="group-theory.semigroups%25E1%25B5%2589.html#905" class="Bound">lᵉ</a><a id="921" class="Symbol">)</a> <a id="923" href="group-theory.semigroups%25E1%25B5%2589.html#715" class="Function">has-associative-mul-Setᵉ</a>

<a id="949" class="Keyword">module</a> <a id="956" href="group-theory.semigroups%25E1%25B5%2589.html#956" class="Module">_</a>
  <a id="960" class="Symbol">{</a><a id="961" href="group-theory.semigroups%25E1%25B5%2589.html#961" class="Bound">lᵉ</a> <a id="964" class="Symbol">:</a> <a id="966" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="971" class="Symbol">}</a> <a id="973" class="Symbol">(</a><a id="974" href="group-theory.semigroups%25E1%25B5%2589.html#974" class="Bound">Gᵉ</a> <a id="977" class="Symbol">:</a> <a id="979" href="group-theory.semigroups%25E1%25B5%2589.html#850" class="Function">Semigroupᵉ</a> <a id="990" href="group-theory.semigroups%25E1%25B5%2589.html#961" class="Bound">lᵉ</a><a id="992" class="Symbol">)</a>
  <a id="996" class="Keyword">where</a>

  <a id="1005" href="group-theory.semigroups%25E1%25B5%2589.html#1005" class="Function">set-Semigroupᵉ</a> <a id="1020" class="Symbol">:</a> <a id="1022" href="foundation-core.sets%25E1%25B5%2589.html#897" class="Function">Setᵉ</a> <a id="1027" href="group-theory.semigroups%25E1%25B5%2589.html#961" class="Bound">lᵉ</a>
  <a id="1032" href="group-theory.semigroups%25E1%25B5%2589.html#1005" class="Function">set-Semigroupᵉ</a> <a id="1047" class="Symbol">=</a> <a id="1049" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="1054" href="group-theory.semigroups%25E1%25B5%2589.html#974" class="Bound">Gᵉ</a>

  <a id="1060" href="group-theory.semigroups%25E1%25B5%2589.html#1060" class="Function">type-Semigroupᵉ</a> <a id="1076" class="Symbol">:</a> <a id="1078" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1082" href="group-theory.semigroups%25E1%25B5%2589.html#961" class="Bound">lᵉ</a>
  <a id="1087" href="group-theory.semigroups%25E1%25B5%2589.html#1060" class="Function">type-Semigroupᵉ</a> <a id="1103" class="Symbol">=</a> <a id="1105" href="foundation-core.sets%25E1%25B5%2589.html#1014" class="Function">type-Setᵉ</a> <a id="1115" href="group-theory.semigroups%25E1%25B5%2589.html#1005" class="Function">set-Semigroupᵉ</a>

  <a id="1133" href="group-theory.semigroups%25E1%25B5%2589.html#1133" class="Function">is-set-type-Semigroupᵉ</a> <a id="1156" class="Symbol">:</a> <a id="1158" href="foundation-core.sets%25E1%25B5%2589.html#807" class="Function">is-setᵉ</a> <a id="1166" href="group-theory.semigroups%25E1%25B5%2589.html#1060" class="Function">type-Semigroupᵉ</a>
  <a id="1184" href="group-theory.semigroups%25E1%25B5%2589.html#1133" class="Function">is-set-type-Semigroupᵉ</a> <a id="1207" class="Symbol">=</a> <a id="1209" href="foundation-core.sets%25E1%25B5%2589.html#1071" class="Function">is-set-type-Setᵉ</a> <a id="1226" href="group-theory.semigroups%25E1%25B5%2589.html#1005" class="Function">set-Semigroupᵉ</a>

  <a id="1244" href="group-theory.semigroups%25E1%25B5%2589.html#1244" class="Function">has-associative-mul-Semigroupᵉ</a> <a id="1275" class="Symbol">:</a> <a id="1277" href="group-theory.semigroups%25E1%25B5%2589.html#540" class="Function">has-associative-mulᵉ</a> <a id="1298" href="group-theory.semigroups%25E1%25B5%2589.html#1060" class="Function">type-Semigroupᵉ</a>
  <a id="1316" href="group-theory.semigroups%25E1%25B5%2589.html#1244" class="Function">has-associative-mul-Semigroupᵉ</a> <a id="1347" class="Symbol">=</a> <a id="1349" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="1354" href="group-theory.semigroups%25E1%25B5%2589.html#974" class="Bound">Gᵉ</a>

  <a id="1360" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="1375" class="Symbol">:</a> <a id="1377" href="group-theory.semigroups%25E1%25B5%2589.html#1060" class="Function">type-Semigroupᵉ</a> <a id="1393" class="Symbol">→</a> <a id="1395" href="group-theory.semigroups%25E1%25B5%2589.html#1060" class="Function">type-Semigroupᵉ</a> <a id="1411" class="Symbol">→</a> <a id="1413" href="group-theory.semigroups%25E1%25B5%2589.html#1060" class="Function">type-Semigroupᵉ</a>
  <a id="1431" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="1446" class="Symbol">=</a> <a id="1448" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="1453" href="group-theory.semigroups%25E1%25B5%2589.html#1244" class="Function">has-associative-mul-Semigroupᵉ</a>

  <a id="1487" href="group-theory.semigroups%25E1%25B5%2589.html#1487" class="Function">mul-Semigroup&#39;ᵉ</a> <a id="1503" class="Symbol">:</a> <a id="1505" href="group-theory.semigroups%25E1%25B5%2589.html#1060" class="Function">type-Semigroupᵉ</a> <a id="1521" class="Symbol">→</a> <a id="1523" href="group-theory.semigroups%25E1%25B5%2589.html#1060" class="Function">type-Semigroupᵉ</a> <a id="1539" class="Symbol">→</a> <a id="1541" href="group-theory.semigroups%25E1%25B5%2589.html#1060" class="Function">type-Semigroupᵉ</a>
  <a id="1559" href="group-theory.semigroups%25E1%25B5%2589.html#1487" class="Function">mul-Semigroup&#39;ᵉ</a> <a id="1575" href="group-theory.semigroups%25E1%25B5%2589.html#1575" class="Bound">xᵉ</a> <a id="1578" href="group-theory.semigroups%25E1%25B5%2589.html#1578" class="Bound">yᵉ</a> <a id="1581" class="Symbol">=</a> <a id="1583" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="1598" href="group-theory.semigroups%25E1%25B5%2589.html#1578" class="Bound">yᵉ</a> <a id="1601" href="group-theory.semigroups%25E1%25B5%2589.html#1575" class="Bound">xᵉ</a>

  <a id="1607" href="group-theory.semigroups%25E1%25B5%2589.html#1607" class="Function">ap-mul-Semigroupᵉ</a> <a id="1625" class="Symbol">:</a>
    <a id="1631" class="Symbol">{</a><a id="1632" href="group-theory.semigroups%25E1%25B5%2589.html#1632" class="Bound">xᵉ</a> <a id="1635" href="group-theory.semigroups%25E1%25B5%2589.html#1635" class="Bound">x&#39;ᵉ</a> <a id="1639" href="group-theory.semigroups%25E1%25B5%2589.html#1639" class="Bound">yᵉ</a> <a id="1642" href="group-theory.semigroups%25E1%25B5%2589.html#1642" class="Bound">y&#39;ᵉ</a> <a id="1646" class="Symbol">:</a> <a id="1648" href="group-theory.semigroups%25E1%25B5%2589.html#1060" class="Function">type-Semigroupᵉ</a><a id="1663" class="Symbol">}</a> <a id="1665" class="Symbol">→</a>
    <a id="1671" href="group-theory.semigroups%25E1%25B5%2589.html#1632" class="Bound">xᵉ</a> <a id="1674" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="1677" href="group-theory.semigroups%25E1%25B5%2589.html#1635" class="Bound">x&#39;ᵉ</a> <a id="1681" class="Symbol">→</a> <a id="1683" href="group-theory.semigroups%25E1%25B5%2589.html#1639" class="Bound">yᵉ</a> <a id="1686" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="1689" href="group-theory.semigroups%25E1%25B5%2589.html#1642" class="Bound">y&#39;ᵉ</a> <a id="1693" class="Symbol">→</a> <a id="1695" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="1710" href="group-theory.semigroups%25E1%25B5%2589.html#1632" class="Bound">xᵉ</a> <a id="1713" href="group-theory.semigroups%25E1%25B5%2589.html#1639" class="Bound">yᵉ</a> <a id="1716" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="1719" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="1734" href="group-theory.semigroups%25E1%25B5%2589.html#1635" class="Bound">x&#39;ᵉ</a> <a id="1738" href="group-theory.semigroups%25E1%25B5%2589.html#1642" class="Bound">y&#39;ᵉ</a>
  <a id="1744" href="group-theory.semigroups%25E1%25B5%2589.html#1607" class="Function">ap-mul-Semigroupᵉ</a> <a id="1762" href="group-theory.semigroups%25E1%25B5%2589.html#1762" class="Bound">pᵉ</a> <a id="1765" href="group-theory.semigroups%25E1%25B5%2589.html#1765" class="Bound">qᵉ</a> <a id="1768" class="Symbol">=</a> <a id="1770" href="foundation.action-on-identifications-binary-functions%25E1%25B5%2589.html#1542" class="Function">ap-binaryᵉ</a> <a id="1781" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="1796" href="group-theory.semigroups%25E1%25B5%2589.html#1762" class="Bound">pᵉ</a> <a id="1799" href="group-theory.semigroups%25E1%25B5%2589.html#1765" class="Bound">qᵉ</a>

  <a id="1805" href="group-theory.semigroups%25E1%25B5%2589.html#1805" class="Function">associative-mul-Semigroupᵉ</a> <a id="1832" class="Symbol">:</a>
    <a id="1838" class="Symbol">(</a><a id="1839" href="group-theory.semigroups%25E1%25B5%2589.html#1839" class="Bound">xᵉ</a> <a id="1842" href="group-theory.semigroups%25E1%25B5%2589.html#1842" class="Bound">yᵉ</a> <a id="1845" href="group-theory.semigroups%25E1%25B5%2589.html#1845" class="Bound">zᵉ</a> <a id="1848" class="Symbol">:</a> <a id="1850" href="group-theory.semigroups%25E1%25B5%2589.html#1060" class="Function">type-Semigroupᵉ</a><a id="1865" class="Symbol">)</a> <a id="1867" class="Symbol">→</a>
    <a id="1873" href="foundation-core.identity-types%25E1%25B5%2589.html#2647" class="Datatype">Idᵉ</a>
      <a id="1883" class="Symbol">(</a> <a id="1885" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="1900" class="Symbol">(</a><a id="1901" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="1916" href="group-theory.semigroups%25E1%25B5%2589.html#1839" class="Bound">xᵉ</a> <a id="1919" href="group-theory.semigroups%25E1%25B5%2589.html#1842" class="Bound">yᵉ</a><a id="1921" class="Symbol">)</a> <a id="1923" href="group-theory.semigroups%25E1%25B5%2589.html#1845" class="Bound">zᵉ</a><a id="1925" class="Symbol">)</a>
      <a id="1933" class="Symbol">(</a> <a id="1935" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="1950" href="group-theory.semigroups%25E1%25B5%2589.html#1839" class="Bound">xᵉ</a> <a id="1953" class="Symbol">(</a><a id="1954" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="1969" href="group-theory.semigroups%25E1%25B5%2589.html#1842" class="Bound">yᵉ</a> <a id="1972" href="group-theory.semigroups%25E1%25B5%2589.html#1845" class="Bound">zᵉ</a><a id="1974" class="Symbol">))</a>
  <a id="1979" href="group-theory.semigroups%25E1%25B5%2589.html#1805" class="Function">associative-mul-Semigroupᵉ</a> <a id="2006" class="Symbol">=</a> <a id="2008" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2013" href="group-theory.semigroups%25E1%25B5%2589.html#1244" class="Function">has-associative-mul-Semigroupᵉ</a>

  <a id="2047" href="group-theory.semigroups%25E1%25B5%2589.html#2047" class="Function">left-swap-mul-Semigroupᵉ</a> <a id="2072" class="Symbol">:</a>
    <a id="2078" class="Symbol">{</a><a id="2079" href="group-theory.semigroups%25E1%25B5%2589.html#2079" class="Bound">xᵉ</a> <a id="2082" href="group-theory.semigroups%25E1%25B5%2589.html#2082" class="Bound">yᵉ</a> <a id="2085" href="group-theory.semigroups%25E1%25B5%2589.html#2085" class="Bound">zᵉ</a> <a id="2088" class="Symbol">:</a> <a id="2090" href="group-theory.semigroups%25E1%25B5%2589.html#1060" class="Function">type-Semigroupᵉ</a><a id="2105" class="Symbol">}</a> <a id="2107" class="Symbol">→</a> <a id="2109" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2124" href="group-theory.semigroups%25E1%25B5%2589.html#2079" class="Bound">xᵉ</a> <a id="2127" href="group-theory.semigroups%25E1%25B5%2589.html#2082" class="Bound">yᵉ</a> <a id="2130" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="2133" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2148" href="group-theory.semigroups%25E1%25B5%2589.html#2082" class="Bound">yᵉ</a> <a id="2151" href="group-theory.semigroups%25E1%25B5%2589.html#2079" class="Bound">xᵉ</a> <a id="2154" class="Symbol">→</a>
    <a id="2160" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2175" href="group-theory.semigroups%25E1%25B5%2589.html#2079" class="Bound">xᵉ</a> <a id="2178" class="Symbol">(</a><a id="2179" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2194" href="group-theory.semigroups%25E1%25B5%2589.html#2082" class="Bound">yᵉ</a> <a id="2197" href="group-theory.semigroups%25E1%25B5%2589.html#2085" class="Bound">zᵉ</a><a id="2199" class="Symbol">)</a> <a id="2201" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a>
    <a id="2208" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2223" href="group-theory.semigroups%25E1%25B5%2589.html#2082" class="Bound">yᵉ</a> <a id="2226" class="Symbol">(</a><a id="2227" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2242" href="group-theory.semigroups%25E1%25B5%2589.html#2079" class="Bound">xᵉ</a> <a id="2245" href="group-theory.semigroups%25E1%25B5%2589.html#2085" class="Bound">zᵉ</a><a id="2247" class="Symbol">)</a>
  <a id="2251" href="group-theory.semigroups%25E1%25B5%2589.html#2047" class="Function">left-swap-mul-Semigroupᵉ</a> <a id="2276" href="group-theory.semigroups%25E1%25B5%2589.html#2276" class="Bound">Hᵉ</a> <a id="2279" class="Symbol">=</a>
    <a id="2285" class="Symbol">(</a> <a id="2287" href="foundation-core.identity-types%25E1%25B5%2589.html#6276" class="Function">invᵉ</a> <a id="2292" class="Symbol">(</a><a id="2293" href="group-theory.semigroups%25E1%25B5%2589.html#1805" class="Function">associative-mul-Semigroupᵉ</a> <a id="2320" class="Symbol">_</a> <a id="2322" class="Symbol">_</a> <a id="2324" class="Symbol">_))</a> <a id="2328" href="foundation-core.identity-types%25E1%25B5%2589.html#5906" class="Function Operator">∙ᵉ</a>
    <a id="2335" class="Symbol">(</a> <a id="2337" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="2341" class="Symbol">(</a><a id="2342" href="group-theory.semigroups%25E1%25B5%2589.html#1487" class="Function">mul-Semigroup&#39;ᵉ</a> <a id="2358" class="Symbol">_)</a> <a id="2361" href="group-theory.semigroups%25E1%25B5%2589.html#2276" class="Bound">Hᵉ</a><a id="2363" class="Symbol">)</a> <a id="2365" href="foundation-core.identity-types%25E1%25B5%2589.html#5906" class="Function Operator">∙ᵉ</a>
    <a id="2372" class="Symbol">(</a> <a id="2374" href="group-theory.semigroups%25E1%25B5%2589.html#1805" class="Function">associative-mul-Semigroupᵉ</a> <a id="2401" class="Symbol">_</a> <a id="2403" class="Symbol">_</a> <a id="2405" class="Symbol">_)</a>

  <a id="2411" href="group-theory.semigroups%25E1%25B5%2589.html#2411" class="Function">right-swap-mul-Semigroupᵉ</a> <a id="2437" class="Symbol">:</a>
    <a id="2443" class="Symbol">{</a><a id="2444" href="group-theory.semigroups%25E1%25B5%2589.html#2444" class="Bound">xᵉ</a> <a id="2447" href="group-theory.semigroups%25E1%25B5%2589.html#2447" class="Bound">yᵉ</a> <a id="2450" href="group-theory.semigroups%25E1%25B5%2589.html#2450" class="Bound">zᵉ</a> <a id="2453" class="Symbol">:</a> <a id="2455" href="group-theory.semigroups%25E1%25B5%2589.html#1060" class="Function">type-Semigroupᵉ</a><a id="2470" class="Symbol">}</a> <a id="2472" class="Symbol">→</a> <a id="2474" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2489" href="group-theory.semigroups%25E1%25B5%2589.html#2447" class="Bound">yᵉ</a> <a id="2492" href="group-theory.semigroups%25E1%25B5%2589.html#2450" class="Bound">zᵉ</a> <a id="2495" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="2498" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2513" href="group-theory.semigroups%25E1%25B5%2589.html#2450" class="Bound">zᵉ</a> <a id="2516" href="group-theory.semigroups%25E1%25B5%2589.html#2447" class="Bound">yᵉ</a> <a id="2519" class="Symbol">→</a>
    <a id="2525" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2540" class="Symbol">(</a><a id="2541" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2556" href="group-theory.semigroups%25E1%25B5%2589.html#2444" class="Bound">xᵉ</a> <a id="2559" href="group-theory.semigroups%25E1%25B5%2589.html#2447" class="Bound">yᵉ</a><a id="2561" class="Symbol">)</a> <a id="2563" href="group-theory.semigroups%25E1%25B5%2589.html#2450" class="Bound">zᵉ</a> <a id="2566" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a>
    <a id="2573" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2588" class="Symbol">(</a><a id="2589" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2604" href="group-theory.semigroups%25E1%25B5%2589.html#2444" class="Bound">xᵉ</a> <a id="2607" href="group-theory.semigroups%25E1%25B5%2589.html#2450" class="Bound">zᵉ</a><a id="2609" class="Symbol">)</a> <a id="2611" href="group-theory.semigroups%25E1%25B5%2589.html#2447" class="Bound">yᵉ</a>
  <a id="2616" href="group-theory.semigroups%25E1%25B5%2589.html#2411" class="Function">right-swap-mul-Semigroupᵉ</a> <a id="2642" href="group-theory.semigroups%25E1%25B5%2589.html#2642" class="Bound">Hᵉ</a> <a id="2645" class="Symbol">=</a>
    <a id="2651" class="Symbol">(</a> <a id="2653" href="group-theory.semigroups%25E1%25B5%2589.html#1805" class="Function">associative-mul-Semigroupᵉ</a> <a id="2680" class="Symbol">_</a> <a id="2682" class="Symbol">_</a> <a id="2684" class="Symbol">_)</a> <a id="2687" href="foundation-core.identity-types%25E1%25B5%2589.html#5906" class="Function Operator">∙ᵉ</a>
    <a id="2694" class="Symbol">(</a> <a id="2696" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="2700" class="Symbol">(</a><a id="2701" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2716" class="Symbol">_)</a> <a id="2719" href="group-theory.semigroups%25E1%25B5%2589.html#2642" class="Bound">Hᵉ</a><a id="2721" class="Symbol">)</a> <a id="2723" href="foundation-core.identity-types%25E1%25B5%2589.html#5906" class="Function Operator">∙ᵉ</a>
    <a id="2730" class="Symbol">(</a> <a id="2732" href="foundation-core.identity-types%25E1%25B5%2589.html#6276" class="Function">invᵉ</a> <a id="2737" class="Symbol">(</a><a id="2738" href="group-theory.semigroups%25E1%25B5%2589.html#1805" class="Function">associative-mul-Semigroupᵉ</a> <a id="2765" class="Symbol">_</a> <a id="2767" class="Symbol">_</a> <a id="2769" class="Symbol">_))</a>

  <a id="2776" href="group-theory.semigroups%25E1%25B5%2589.html#2776" class="Function">interchange-mul-mul-Semigroupᵉ</a> <a id="2807" class="Symbol">:</a>
    <a id="2813" class="Symbol">{</a><a id="2814" href="group-theory.semigroups%25E1%25B5%2589.html#2814" class="Bound">xᵉ</a> <a id="2817" href="group-theory.semigroups%25E1%25B5%2589.html#2817" class="Bound">yᵉ</a> <a id="2820" href="group-theory.semigroups%25E1%25B5%2589.html#2820" class="Bound">zᵉ</a> <a id="2823" href="group-theory.semigroups%25E1%25B5%2589.html#2823" class="Bound">wᵉ</a> <a id="2826" class="Symbol">:</a> <a id="2828" href="group-theory.semigroups%25E1%25B5%2589.html#1060" class="Function">type-Semigroupᵉ</a><a id="2843" class="Symbol">}</a> <a id="2845" class="Symbol">→</a> <a id="2847" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2862" href="group-theory.semigroups%25E1%25B5%2589.html#2817" class="Bound">yᵉ</a> <a id="2865" href="group-theory.semigroups%25E1%25B5%2589.html#2820" class="Bound">zᵉ</a> <a id="2868" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="2871" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2886" href="group-theory.semigroups%25E1%25B5%2589.html#2820" class="Bound">zᵉ</a> <a id="2889" href="group-theory.semigroups%25E1%25B5%2589.html#2817" class="Bound">yᵉ</a> <a id="2892" class="Symbol">→</a>
    <a id="2898" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2913" class="Symbol">(</a><a id="2914" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2929" href="group-theory.semigroups%25E1%25B5%2589.html#2814" class="Bound">xᵉ</a> <a id="2932" href="group-theory.semigroups%25E1%25B5%2589.html#2817" class="Bound">yᵉ</a><a id="2934" class="Symbol">)</a> <a id="2936" class="Symbol">(</a><a id="2937" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2952" href="group-theory.semigroups%25E1%25B5%2589.html#2820" class="Bound">zᵉ</a> <a id="2955" href="group-theory.semigroups%25E1%25B5%2589.html#2823" class="Bound">wᵉ</a><a id="2957" class="Symbol">)</a> <a id="2959" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a>
    <a id="2966" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2981" class="Symbol">(</a><a id="2982" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="2997" href="group-theory.semigroups%25E1%25B5%2589.html#2814" class="Bound">xᵉ</a> <a id="3000" href="group-theory.semigroups%25E1%25B5%2589.html#2820" class="Bound">zᵉ</a><a id="3002" class="Symbol">)</a> <a id="3004" class="Symbol">(</a><a id="3005" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="3020" href="group-theory.semigroups%25E1%25B5%2589.html#2817" class="Bound">yᵉ</a> <a id="3023" href="group-theory.semigroups%25E1%25B5%2589.html#2823" class="Bound">wᵉ</a><a id="3025" class="Symbol">)</a>
  <a id="3029" href="group-theory.semigroups%25E1%25B5%2589.html#2776" class="Function">interchange-mul-mul-Semigroupᵉ</a> <a id="3060" href="group-theory.semigroups%25E1%25B5%2589.html#3060" class="Bound">Hᵉ</a> <a id="3063" class="Symbol">=</a>
    <a id="3069" class="Symbol">(</a> <a id="3071" href="group-theory.semigroups%25E1%25B5%2589.html#1805" class="Function">associative-mul-Semigroupᵉ</a> <a id="3098" class="Symbol">_</a> <a id="3100" class="Symbol">_</a> <a id="3102" class="Symbol">_)</a> <a id="3105" href="foundation-core.identity-types%25E1%25B5%2589.html#5906" class="Function Operator">∙ᵉ</a>
    <a id="3112" class="Symbol">(</a> <a id="3114" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="3118" class="Symbol">(</a><a id="3119" href="group-theory.semigroups%25E1%25B5%2589.html#1360" class="Function">mul-Semigroupᵉ</a> <a id="3134" class="Symbol">_)</a> <a id="3137" class="Symbol">(</a><a id="3138" href="group-theory.semigroups%25E1%25B5%2589.html#2047" class="Function">left-swap-mul-Semigroupᵉ</a> <a id="3163" href="group-theory.semigroups%25E1%25B5%2589.html#3060" class="Bound">Hᵉ</a><a id="3165" class="Symbol">))</a> <a id="3168" href="foundation-core.identity-types%25E1%25B5%2589.html#5906" class="Function Operator">∙ᵉ</a>
    <a id="3175" class="Symbol">(</a> <a id="3177" href="foundation-core.identity-types%25E1%25B5%2589.html#6276" class="Function">invᵉ</a> <a id="3182" class="Symbol">(</a><a id="3183" href="group-theory.semigroups%25E1%25B5%2589.html#1805" class="Function">associative-mul-Semigroupᵉ</a> <a id="3210" class="Symbol">_</a> <a id="3212" class="Symbol">_</a> <a id="3214" class="Symbol">_))</a>
</pre>
### The structure of a semigroup

<pre class="Agda"><a id="structure-semigroupᵉ"></a><a id="3265" href="group-theory.semigroups%25E1%25B5%2589.html#3265" class="Function">structure-semigroupᵉ</a> <a id="3286" class="Symbol">:</a>
  <a id="3290" class="Symbol">{</a><a id="3291" href="group-theory.semigroups%25E1%25B5%2589.html#3291" class="Bound">l1ᵉ</a> <a id="3295" class="Symbol">:</a> <a id="3297" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3302" class="Symbol">}</a> <a id="3304" class="Symbol">→</a> <a id="3306" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3310" href="group-theory.semigroups%25E1%25B5%2589.html#3291" class="Bound">l1ᵉ</a> <a id="3314" class="Symbol">→</a> <a id="3316" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3320" href="group-theory.semigroups%25E1%25B5%2589.html#3291" class="Bound">l1ᵉ</a>
<a id="3324" href="group-theory.semigroups%25E1%25B5%2589.html#3265" class="Function">structure-semigroupᵉ</a> <a id="3345" href="group-theory.semigroups%25E1%25B5%2589.html#3345" class="Bound">Xᵉ</a> <a id="3348" class="Symbol">=</a>
  <a id="3352" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="3355" class="Symbol">(</a><a id="3356" href="foundation-core.sets%25E1%25B5%2589.html#807" class="Function">is-setᵉ</a> <a id="3364" href="group-theory.semigroups%25E1%25B5%2589.html#3345" class="Bound">Xᵉ</a><a id="3366" class="Symbol">)</a> <a id="3368" class="Symbol">(λ</a> <a id="3371" href="group-theory.semigroups%25E1%25B5%2589.html#3371" class="Bound">pᵉ</a> <a id="3374" class="Symbol">→</a> <a id="3376" href="group-theory.semigroups%25E1%25B5%2589.html#715" class="Function">has-associative-mul-Setᵉ</a> <a id="3401" class="Symbol">(</a><a id="3402" href="group-theory.semigroups%25E1%25B5%2589.html#3345" class="Bound">Xᵉ</a> <a id="3405" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="3408" href="group-theory.semigroups%25E1%25B5%2589.html#3371" class="Bound">pᵉ</a><a id="3410" class="Symbol">))</a>

<a id="semigroup-structure-semigroupᵉ"></a><a id="3414" href="group-theory.semigroups%25E1%25B5%2589.html#3414" class="Function">semigroup-structure-semigroupᵉ</a> <a id="3445" class="Symbol">:</a>
  <a id="3449" class="Symbol">{</a><a id="3450" href="group-theory.semigroups%25E1%25B5%2589.html#3450" class="Bound">l1ᵉ</a> <a id="3454" class="Symbol">:</a> <a id="3456" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3461" class="Symbol">}</a> <a id="3463" class="Symbol">→</a> <a id="3465" class="Symbol">(</a><a id="3466" href="group-theory.semigroups%25E1%25B5%2589.html#3466" class="Bound">Xᵉ</a> <a id="3469" class="Symbol">:</a> <a id="3471" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3475" href="group-theory.semigroups%25E1%25B5%2589.html#3450" class="Bound">l1ᵉ</a><a id="3478" class="Symbol">)</a> <a id="3480" class="Symbol">→</a> <a id="3482" href="group-theory.semigroups%25E1%25B5%2589.html#3265" class="Function">structure-semigroupᵉ</a> <a id="3503" href="group-theory.semigroups%25E1%25B5%2589.html#3466" class="Bound">Xᵉ</a> <a id="3506" class="Symbol">→</a> <a id="3508" href="group-theory.semigroups%25E1%25B5%2589.html#850" class="Function">Semigroupᵉ</a> <a id="3519" href="group-theory.semigroups%25E1%25B5%2589.html#3450" class="Bound">l1ᵉ</a>
<a id="3523" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="3528" class="Symbol">(</a><a id="3529" href="group-theory.semigroups%25E1%25B5%2589.html#3414" class="Function">semigroup-structure-semigroupᵉ</a> <a id="3560" href="group-theory.semigroups%25E1%25B5%2589.html#3560" class="Bound">Xᵉ</a> <a id="3563" class="Symbol">(</a><a id="3564" href="group-theory.semigroups%25E1%25B5%2589.html#3564" class="Bound">sᵉ</a> <a id="3567" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="3570" href="group-theory.semigroups%25E1%25B5%2589.html#3570" class="Bound">gᵉ</a><a id="3572" class="Symbol">))</a> <a id="3575" class="Symbol">=</a> <a id="3577" href="group-theory.semigroups%25E1%25B5%2589.html#3560" class="Bound">Xᵉ</a> <a id="3580" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="3583" href="group-theory.semigroups%25E1%25B5%2589.html#3564" class="Bound">sᵉ</a>
<a id="3586" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="3591" class="Symbol">(</a><a id="3592" href="group-theory.semigroups%25E1%25B5%2589.html#3414" class="Function">semigroup-structure-semigroupᵉ</a> <a id="3623" href="group-theory.semigroups%25E1%25B5%2589.html#3623" class="Bound">Xᵉ</a> <a id="3626" class="Symbol">(</a><a id="3627" href="group-theory.semigroups%25E1%25B5%2589.html#3627" class="Bound">sᵉ</a> <a id="3630" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="3633" href="group-theory.semigroups%25E1%25B5%2589.html#3633" class="Bound">gᵉ</a><a id="3635" class="Symbol">))</a> <a id="3638" class="Symbol">=</a> <a id="3640" href="group-theory.semigroups%25E1%25B5%2589.html#3633" class="Bound">gᵉ</a>
</pre>