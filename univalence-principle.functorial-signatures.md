# Functorial signatures

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="univalence-principle.functorial-signatures.html" class="Module">univalence-principle.functorial-signatures</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="140" class="Keyword">open</a> <a id="145" class="Keyword">import</a> <a id="152" href="category-theory.discrete-categories%25E1%25B5%2589.html" class="Module">category-theory.discrete-categoriesᵉ</a>
<a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="category-theory.functors-precategories%25E1%25B5%2589.html" class="Module">category-theory.functors-precategoriesᵉ</a>
<a id="241" class="Keyword">open</a> <a id="246" class="Keyword">import</a> <a id="253" href="category-theory.isomorphisms-in-precategories%25E1%25B5%2589.html" class="Module">category-theory.isomorphisms-in-precategoriesᵉ</a>
<a id="300" class="Keyword">open</a> <a id="305" class="Keyword">import</a> <a id="312" href="category-theory.natural-transformations-functors-precategories%25E1%25B5%2589.html" class="Module">category-theory.natural-transformations-functors-precategoriesᵉ</a>
<a id="376" class="Keyword">open</a> <a id="381" class="Keyword">import</a> <a id="388" href="category-theory.opposite-precategories%25E1%25B5%2589.html" class="Module">category-theory.opposite-precategoriesᵉ</a>
<a id="428" class="Keyword">open</a> <a id="433" class="Keyword">import</a> <a id="440" href="category-theory.precategories%25E1%25B5%2589.html" class="Module">category-theory.precategoriesᵉ</a>
<a id="471" class="Keyword">open</a> <a id="476" class="Keyword">import</a> <a id="483" href="category-theory.precategory-of-functors%25E1%25B5%2589.html" class="Module">category-theory.precategory-of-functorsᵉ</a>

<a id="525" class="Keyword">open</a> <a id="530" class="Keyword">import</a> <a id="537" href="category-theory-2LTT.inverse-precategories.html" class="Module">category-theory-2LTT.inverse-precategories</a>

<a id="581" class="Keyword">open</a> <a id="586" class="Keyword">import</a> <a id="593" href="elementary-number-theory.inequality-natural-numbers%25E1%25B5%2589.html" class="Module">elementary-number-theory.inequality-natural-numbersᵉ</a>
<a id="646" class="Keyword">open</a> <a id="651" class="Keyword">import</a> <a id="658" href="elementary-number-theory.natural-numbers%25E1%25B5%2589.html" class="Module">elementary-number-theory.natural-numbersᵉ</a>

<a id="701" class="Keyword">open</a> <a id="706" class="Keyword">import</a> <a id="713" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-functionsᵉ</a>
<a id="761" class="Keyword">open</a> <a id="766" class="Keyword">import</a> <a id="773" href="foundation.binary-transport%25E1%25B5%2589.html" class="Module">foundation.binary-transportᵉ</a>
<a id="802" class="Keyword">open</a> <a id="807" class="Keyword">import</a> <a id="814" href="foundation.category-of-sets%25E1%25B5%2589.html" class="Module">foundation.category-of-setsᵉ</a>
<a id="843" class="Keyword">open</a> <a id="848" class="Keyword">import</a> <a id="855" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="888" class="Keyword">open</a> <a id="893" class="Keyword">import</a> <a id="900" href="foundation.equality-dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.equality-dependent-pair-typesᵉ</a>
<a id="942" class="Keyword">open</a> <a id="947" class="Keyword">import</a> <a id="954" href="foundation.identity-types%25E1%25B5%2589.html" class="Module">foundation.identity-typesᵉ</a>
<a id="981" class="Keyword">open</a> <a id="986" class="Keyword">import</a> <a id="993" href="foundation.propositions%25E1%25B5%2589.html" class="Module">foundation.propositionsᵉ</a>
<a id="1018" class="Keyword">open</a> <a id="1023" class="Keyword">import</a> <a id="1030" href="foundation.raising-universe-levels%25E1%25B5%2589.html" class="Module">foundation.raising-universe-levelsᵉ</a>
<a id="1066" class="Keyword">open</a> <a id="1071" class="Keyword">import</a> <a id="1078" href="foundation.sets%25E1%25B5%2589.html" class="Module">foundation.setsᵉ</a>
<a id="1095" class="Keyword">open</a> <a id="1100" class="Keyword">import</a> <a id="1107" href="foundation.transport-along-identifications%25E1%25B5%2589.html" class="Module">foundation.transport-along-identificationsᵉ</a>
<a id="1151" class="Keyword">open</a> <a id="1156" class="Keyword">import</a> <a id="1163" href="foundation.unit-type%25E1%25B5%2589.html" class="Module">foundation.unit-typeᵉ</a>
<a id="1185" class="Keyword">open</a> <a id="1190" class="Keyword">import</a> <a id="1197" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="1226" class="Keyword">open</a> <a id="1231" class="Keyword">import</a> <a id="1238" href="foundation-2LTT.cofibrant-types.html" class="Module">foundation-2LTT.cofibrant-types</a>
<a id="1270" class="Keyword">open</a> <a id="1275" class="Keyword">import</a> <a id="1282" href="foundation-2LTT.exotypes.html" class="Module">foundation-2LTT.exotypes</a>
<a id="1307" class="Keyword">open</a> <a id="1312" class="Keyword">import</a> <a id="1319" href="foundation-2LTT.fibrant-types.html" class="Module">foundation-2LTT.fibrant-types</a>
<a id="1349" class="Keyword">open</a> <a id="1354" class="Keyword">import</a> <a id="1361" href="foundation-2LTT.sharp-types.html" class="Module">foundation-2LTT.sharp-types</a>
</pre>
</details>

## Definitions

<pre class="Agda"><a id="terminal-Precategoryᵉ"></a><a id="1430" href="univalence-principle.functorial-signatures.html#1430" class="Function">terminal-Precategoryᵉ</a> <a id="1452" class="Symbol">:</a> <a id="1454" class="Symbol">(</a><a id="1455" href="univalence-principle.functorial-signatures.html#1455" class="Bound">l1</a> <a id="1458" href="univalence-principle.functorial-signatures.html#1458" class="Bound">l2</a> <a id="1461" class="Symbol">:</a> <a id="1463" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1468" class="Symbol">)</a> <a id="1470" class="Symbol">→</a> <a id="1472" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="1485" href="univalence-principle.functorial-signatures.html#1455" class="Bound">l1</a> <a id="1488" href="univalence-principle.functorial-signatures.html#1458" class="Bound">l2</a>
<a id="1491" href="univalence-principle.functorial-signatures.html#1430" class="Function">terminal-Precategoryᵉ</a> <a id="1513" href="univalence-principle.functorial-signatures.html#1513" class="Bound">l1</a> <a id="1516" href="univalence-principle.functorial-signatures.html#1516" class="Bound">l2</a> <a id="1519" class="Symbol">=</a>
  <a id="1523" href="category-theory.precategories%25E1%25B5%2589.html#3788" class="Function">make-Precategoryᵉ</a>
    <a id="1545" class="Symbol">(</a> <a id="1547" href="foundation.unit-type%25E1%25B5%2589.html#1438" class="Function">raise-unitᵉ</a> <a id="1559" href="univalence-principle.functorial-signatures.html#1513" class="Bound">l1</a><a id="1561" class="Symbol">)</a>
    <a id="1567" class="Symbol">(</a> <a id="1569" class="Symbol">λ</a> <a id="1571" href="univalence-principle.functorial-signatures.html#1571" class="Bound">_</a> <a id="1573" href="univalence-principle.functorial-signatures.html#1573" class="Bound">_</a> <a id="1575" class="Symbol">→</a> <a id="1577" href="foundation.unit-type%25E1%25B5%2589.html#4054" class="Function">raise-unit-Setᵉ</a> <a id="1593" href="univalence-principle.functorial-signatures.html#1516" class="Bound">l2</a><a id="1595" class="Symbol">)</a>
    <a id="1601" class="Symbol">(</a> <a id="1603" class="Symbol">λ</a> <a id="1605" href="univalence-principle.functorial-signatures.html#1605" class="Bound">_</a> <a id="1607" href="univalence-principle.functorial-signatures.html#1607" class="Bound">_</a> <a id="1609" class="Symbol">→</a> <a id="1611" href="foundation.unit-type%25E1%25B5%2589.html#1508" class="Function">raise-starᵉ</a><a id="1622" class="Symbol">)</a>
    <a id="1628" class="Symbol">(</a> <a id="1630" class="Symbol">λ</a> <a id="1632" href="univalence-principle.functorial-signatures.html#1632" class="Bound">_</a> <a id="1634" class="Symbol">→</a> <a id="1636" href="foundation.unit-type%25E1%25B5%2589.html#1508" class="Function">raise-starᵉ</a><a id="1647" class="Symbol">)</a>
    <a id="1653" class="Symbol">(</a> <a id="1655" class="Symbol">λ</a> <a id="1657" href="univalence-principle.functorial-signatures.html#1657" class="Bound">_</a> <a id="1659" href="univalence-principle.functorial-signatures.html#1659" class="Bound">_</a> <a id="1661" href="univalence-principle.functorial-signatures.html#1661" class="Bound">_</a> <a id="1663" class="Symbol">→</a> <a id="1665" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a><a id="1670" class="Symbol">)</a>
    <a id="1676" class="Symbol">(</a> <a id="1678" class="Symbol">λ</a> <a id="1680" class="Symbol">{(</a><a id="1682" href="foundation.raising-universe-levels%25E1%25B5%2589.html#1086" class="InductiveConstructor">map-raiseᵉ</a> <a id="1693" href="foundation.unit-type%25E1%25B5%2589.html#873" class="InductiveConstructor">starᵉ</a><a id="1698" class="Symbol">)</a> <a id="1700" class="Symbol">→</a> <a id="1702" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a><a id="1707" class="Symbol">})</a>
    <a id="1714" class="Symbol">(</a> <a id="1716" class="Symbol">λ</a> <a id="1718" class="Symbol">{(</a><a id="1720" href="foundation.raising-universe-levels%25E1%25B5%2589.html#1086" class="InductiveConstructor">map-raiseᵉ</a> <a id="1731" href="foundation.unit-type%25E1%25B5%2589.html#873" class="InductiveConstructor">starᵉ</a><a id="1736" class="Symbol">)</a> <a id="1738" class="Symbol">→</a> <a id="1740" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a><a id="1745" class="Symbol">})</a>

<a id="discrete-functor-Precategoryᵉ"></a><a id="1749" href="univalence-principle.functorial-signatures.html#1749" class="Function">discrete-functor-Precategoryᵉ</a> <a id="1779" class="Symbol">:</a>
  <a id="1783" class="Symbol">{</a><a id="1784" href="univalence-principle.functorial-signatures.html#1784" class="Bound">l1</a> <a id="1787" class="Symbol">:</a> <a id="1789" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1794" class="Symbol">}</a> <a id="1796" class="Symbol">→</a> <a id="1798" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1802" href="univalence-principle.functorial-signatures.html#1784" class="Bound">l1</a> <a id="1805" class="Symbol">→</a> <a id="1807" class="Symbol">(</a><a id="1808" href="univalence-principle.functorial-signatures.html#1808" class="Bound">l2</a> <a id="1811" class="Symbol">:</a> <a id="1813" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1818" class="Symbol">)</a> <a id="1820" class="Symbol">→</a>
  <a id="1824" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="1837" class="Symbol">(</a><a id="1838" href="univalence-principle.functorial-signatures.html#1784" class="Bound">l1</a> <a id="1841" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1843" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1848" href="univalence-principle.functorial-signatures.html#1808" class="Bound">l2</a><a id="1850" class="Symbol">)</a> <a id="1852" class="Symbol">(</a><a id="1853" href="univalence-principle.functorial-signatures.html#1784" class="Bound">l1</a> <a id="1856" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1858" href="univalence-principle.functorial-signatures.html#1808" class="Bound">l2</a><a id="1860" class="Symbol">)</a>
<a id="1862" href="univalence-principle.functorial-signatures.html#1749" class="Function">discrete-functor-Precategoryᵉ</a> <a id="1892" href="univalence-principle.functorial-signatures.html#1892" class="Bound">X</a> <a id="1894" href="univalence-principle.functorial-signatures.html#1894" class="Bound">l</a> <a id="1896" class="Symbol">=</a>
  <a id="1900" href="category-theory.precategory-of-functors%25E1%25B5%2589.html#5998" class="Function">functor-precategory-Precategoryᵉ</a>
    <a id="1937" class="Symbol">(</a> <a id="1939" href="category-theory.discrete-categories%25E1%25B5%2589.html#611" class="Function">discrete-precategory-Setᵉ</a> <a id="1965" class="Symbol">(</a><a id="1966" href="foundation-2LTT.exotypes.html#2444" class="Function">exotype-Setᵉ</a> <a id="1979" href="univalence-principle.functorial-signatures.html#1892" class="Bound">X</a><a id="1980" class="Symbol">))</a>
    <a id="1987" class="Symbol">(</a> <a id="1989" href="foundation.category-of-sets%25E1%25B5%2589.html#3733" class="Function">Set-Precategoryᵉ</a> <a id="2006" href="univalence-principle.functorial-signatures.html#1894" class="Bound">l</a><a id="2007" class="Symbol">)</a>

<a id="2010" class="Comment">-- FSig-Precategoryᵉ : (l1 l2 ls lU : Level) → ℕᵉ → Precategoryᵉ l1 l2</a>
<a id="2081" class="Comment">-- obj-FSig-Precategoryᵉ :</a>
<a id="2108" class="Comment">--   (l1 l2 ls lU : Level) → ℕᵉ → UUᵉ (lsuc l1 ⊔ l2 ⊔ lsuc ls ⊔ lsuc lU)</a>
<a id="2181" class="Comment">-- hom-FSig-Precategoryᵉ :</a>
<a id="2208" class="Comment">--   (l1 l2 ls lU : Level) → (n : ℕᵉ) →</a>
<a id="2248" class="Comment">--   obj-FSig-Precategoryᵉ l1 l2 ls lU n →</a>
<a id="2291" class="Comment">--   obj-FSig-Precategoryᵉ l1 l2 ls lU n →</a>
<a id="2334" class="Comment">--   UUᵉ (lsuc l1 ⊔ l2 ⊔ lsuc ls ⊔ lsuc lU)</a>

<a id="2379" class="Comment">-- hom-FSig-Precategoryᵉ l1 l2 ls lU 0ᵉ 𝓛 𝓜 = raise-unitᵉ _</a>
<a id="2439" class="Comment">-- hom-FSig-Precategoryᵉ l1 l2 ls lU (succ-ℕᵉ n) 𝓛 𝓜 = {!!}</a>

<a id="2500" class="Comment">-- obj-FSig-Precategoryᵉ l1 l2 ls lU 0ᵉ = raise-unitᵉ _</a>
<a id="2556" class="Comment">-- obj-FSig-Precategoryᵉ l1 l2 ls lU (succ-ℕᵉ n) =</a>
<a id="2607" class="Comment">--   Σᵉ (Sharp-Type l1 ls)</a>
<a id="2634" class="Comment">--     ( λ 𝓛⊥ →</a>
<a id="2650" class="Comment">--       functor-Precategoryᵉ</a>
<a id="2680" class="Comment">--         ( discrete-functor-Precategoryᵉ (type-Sharp-Type 𝓛⊥) lU)</a>
<a id="2748" class="Comment">--         ( FSig-Precategoryᵉ l1 l2 ls lU n))</a>

<a id="2796" class="Comment">-- FSig-Precategoryᵉ l1 l2 ls lU n = _</a>
</pre>