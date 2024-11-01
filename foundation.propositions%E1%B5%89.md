# Propositions

<pre class="Agda"><a id="25" class="Keyword">module</a> <a id="32" href="foundation.propositions%25E1%25B5%2589.html" class="Module">foundation.propositionsᵉ</a> <a id="57" class="Keyword">where</a>

<a id="64" class="Keyword">open</a> <a id="69" class="Keyword">import</a> <a id="76" href="foundation-core.propositions%25E1%25B5%2589.html" class="Module">foundation-core.propositionsᵉ</a> <a id="106" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="163" class="Keyword">open</a> <a id="168" class="Keyword">import</a> <a id="175" href="foundation.contractible-types%25E1%25B5%2589.html" class="Module">foundation.contractible-typesᵉ</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="251" class="Keyword">open</a> <a id="256" class="Keyword">import</a> <a id="263" href="foundation.logical-equivalences%25E1%25B5%2589.html" class="Module">foundation.logical-equivalencesᵉ</a>
<a id="296" class="Keyword">open</a> <a id="301" class="Keyword">import</a> <a id="308" href="foundation.retracts-of-types%25E1%25B5%2589.html" class="Module">foundation.retracts-of-typesᵉ</a>
<a id="338" class="Keyword">open</a> <a id="343" class="Keyword">import</a> <a id="350" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="379" class="Keyword">open</a> <a id="384" class="Keyword">import</a> <a id="391" href="foundation-core.embeddings%25E1%25B5%2589.html" class="Module">foundation-core.embeddingsᵉ</a>
<a id="419" class="Keyword">open</a> <a id="424" class="Keyword">import</a> <a id="431" href="foundation-core.equivalences%25E1%25B5%2589.html" class="Module">foundation-core.equivalencesᵉ</a>
<a id="461" class="Keyword">open</a> <a id="466" class="Keyword">import</a> <a id="473" href="foundation-core.truncated-types%25E1%25B5%2589.html" class="Module">foundation-core.truncated-typesᵉ</a>
<a id="506" class="Keyword">open</a> <a id="511" class="Keyword">import</a> <a id="518" href="foundation-core.truncation-levels%25E1%25B5%2589.html" class="Module">foundation-core.truncation-levelsᵉ</a>
</pre>
</details>

## Properties

### Propositions are `k+1`-truncated for any `k`

<pre class="Agda"><a id="643" class="Keyword">abstract</a>
  <a id="is-trunc-is-propᵉ"></a><a id="654" href="foundation.propositions%25E1%25B5%2589.html#654" class="Function">is-trunc-is-propᵉ</a> <a id="672" class="Symbol">:</a>
    <a id="678" class="Symbol">{</a><a id="679" href="foundation.propositions%25E1%25B5%2589.html#679" class="Bound">lᵉ</a> <a id="682" class="Symbol">:</a> <a id="684" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="689" class="Symbol">}</a> <a id="691" class="Symbol">(</a><a id="692" href="foundation.propositions%25E1%25B5%2589.html#692" class="Bound">kᵉ</a> <a id="695" class="Symbol">:</a> <a id="697" href="foundation-core.truncation-levels%25E1%25B5%2589.html#523" class="Datatype">𝕋ᵉ</a><a id="699" class="Symbol">)</a> <a id="701" class="Symbol">{</a><a id="702" href="foundation.propositions%25E1%25B5%2589.html#702" class="Bound">Aᵉ</a> <a id="705" class="Symbol">:</a> <a id="707" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="711" href="foundation.propositions%25E1%25B5%2589.html#679" class="Bound">lᵉ</a><a id="713" class="Symbol">}</a> <a id="715" class="Symbol">→</a> <a id="717" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="726" href="foundation.propositions%25E1%25B5%2589.html#702" class="Bound">Aᵉ</a> <a id="729" class="Symbol">→</a> <a id="731" href="foundation-core.truncated-types%25E1%25B5%2589.html#1253" class="Function">is-truncᵉ</a> <a id="741" class="Symbol">(</a><a id="742" href="foundation-core.truncation-levels%25E1%25B5%2589.html#564" class="InductiveConstructor">succ-𝕋ᵉ</a> <a id="750" href="foundation.propositions%25E1%25B5%2589.html#692" class="Bound">kᵉ</a><a id="752" class="Symbol">)</a> <a id="754" href="foundation.propositions%25E1%25B5%2589.html#702" class="Bound">Aᵉ</a>
  <a id="759" href="foundation.propositions%25E1%25B5%2589.html#654" class="Function">is-trunc-is-propᵉ</a> <a id="777" href="foundation.propositions%25E1%25B5%2589.html#777" class="Bound">kᵉ</a> <a id="780" href="foundation.propositions%25E1%25B5%2589.html#780" class="Bound">is-prop-Aᵉ</a> <a id="791" href="foundation.propositions%25E1%25B5%2589.html#791" class="Bound">xᵉ</a> <a id="794" href="foundation.propositions%25E1%25B5%2589.html#794" class="Bound">yᵉ</a> <a id="797" class="Symbol">=</a> <a id="799" href="foundation.contractible-types%25E1%25B5%2589.html#4365" class="Function">is-trunc-is-contrᵉ</a> <a id="818" href="foundation.propositions%25E1%25B5%2589.html#777" class="Bound">kᵉ</a> <a id="821" class="Symbol">(</a><a id="822" href="foundation.propositions%25E1%25B5%2589.html#780" class="Bound">is-prop-Aᵉ</a> <a id="833" href="foundation.propositions%25E1%25B5%2589.html#791" class="Bound">xᵉ</a> <a id="836" href="foundation.propositions%25E1%25B5%2589.html#794" class="Bound">yᵉ</a><a id="838" class="Symbol">)</a>

<a id="truncated-type-Propᵉ"></a><a id="841" href="foundation.propositions%25E1%25B5%2589.html#841" class="Function">truncated-type-Propᵉ</a> <a id="862" class="Symbol">:</a> <a id="864" class="Symbol">{</a><a id="865" href="foundation.propositions%25E1%25B5%2589.html#865" class="Bound">lᵉ</a> <a id="868" class="Symbol">:</a> <a id="870" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="875" class="Symbol">}</a> <a id="877" class="Symbol">(</a><a id="878" href="foundation.propositions%25E1%25B5%2589.html#878" class="Bound">kᵉ</a> <a id="881" class="Symbol">:</a> <a id="883" href="foundation-core.truncation-levels%25E1%25B5%2589.html#523" class="Datatype">𝕋ᵉ</a><a id="885" class="Symbol">)</a> <a id="887" class="Symbol">→</a> <a id="889" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="895" href="foundation.propositions%25E1%25B5%2589.html#865" class="Bound">lᵉ</a> <a id="898" class="Symbol">→</a> <a id="900" href="foundation-core.truncated-types%25E1%25B5%2589.html#1597" class="Function">Truncated-Typeᵉ</a> <a id="916" href="foundation.propositions%25E1%25B5%2589.html#865" class="Bound">lᵉ</a> <a id="919" class="Symbol">(</a><a id="920" href="foundation-core.truncation-levels%25E1%25B5%2589.html#564" class="InductiveConstructor">succ-𝕋ᵉ</a> <a id="928" href="foundation.propositions%25E1%25B5%2589.html#878" class="Bound">kᵉ</a><a id="930" class="Symbol">)</a>
<a id="932" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="937" class="Symbol">(</a><a id="938" href="foundation.propositions%25E1%25B5%2589.html#841" class="Function">truncated-type-Propᵉ</a> <a id="959" href="foundation.propositions%25E1%25B5%2589.html#959" class="Bound">kᵉ</a> <a id="962" href="foundation.propositions%25E1%25B5%2589.html#962" class="Bound">Pᵉ</a><a id="964" class="Symbol">)</a> <a id="966" class="Symbol">=</a> <a id="968" href="foundation-core.propositions%25E1%25B5%2589.html#1288" class="Function">type-Propᵉ</a> <a id="979" href="foundation.propositions%25E1%25B5%2589.html#962" class="Bound">Pᵉ</a>
<a id="982" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="987" class="Symbol">(</a><a id="988" href="foundation.propositions%25E1%25B5%2589.html#841" class="Function">truncated-type-Propᵉ</a> <a id="1009" href="foundation.propositions%25E1%25B5%2589.html#1009" class="Bound">kᵉ</a> <a id="1012" href="foundation.propositions%25E1%25B5%2589.html#1012" class="Bound">Pᵉ</a><a id="1014" class="Symbol">)</a> <a id="1016" class="Symbol">=</a> <a id="1018" href="foundation.propositions%25E1%25B5%2589.html#654" class="Function">is-trunc-is-propᵉ</a> <a id="1036" href="foundation.propositions%25E1%25B5%2589.html#1009" class="Bound">kᵉ</a> <a id="1039" class="Symbol">(</a><a id="1040" href="foundation-core.propositions%25E1%25B5%2589.html#1361" class="Function">is-prop-type-Propᵉ</a> <a id="1059" href="foundation.propositions%25E1%25B5%2589.html#1012" class="Bound">Pᵉ</a><a id="1061" class="Symbol">)</a>
</pre>
### Propositions are closed under retracts

<pre class="Agda"><a id="1120" class="Keyword">module</a> <a id="1127" href="foundation.propositions%25E1%25B5%2589.html#1127" class="Module">_</a>
  <a id="1131" class="Symbol">{</a><a id="1132" href="foundation.propositions%25E1%25B5%2589.html#1132" class="Bound">l1ᵉ</a> <a id="1136" href="foundation.propositions%25E1%25B5%2589.html#1136" class="Bound">l2ᵉ</a> <a id="1140" class="Symbol">:</a> <a id="1142" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1147" class="Symbol">}</a> <a id="1149" class="Symbol">{</a><a id="1150" href="foundation.propositions%25E1%25B5%2589.html#1150" class="Bound">Aᵉ</a> <a id="1153" class="Symbol">:</a> <a id="1155" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1159" href="foundation.propositions%25E1%25B5%2589.html#1132" class="Bound">l1ᵉ</a><a id="1162" class="Symbol">}</a> <a id="1164" class="Symbol">{</a><a id="1165" href="foundation.propositions%25E1%25B5%2589.html#1165" class="Bound">Bᵉ</a> <a id="1168" class="Symbol">:</a> <a id="1170" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1174" href="foundation.propositions%25E1%25B5%2589.html#1136" class="Bound">l2ᵉ</a><a id="1177" class="Symbol">}</a>
  <a id="1181" class="Keyword">where</a>

  <a id="1190" href="foundation.propositions%25E1%25B5%2589.html#1190" class="Function">is-prop-retract-ofᵉ</a> <a id="1210" class="Symbol">:</a> <a id="1212" href="foundation.propositions%25E1%25B5%2589.html#1150" class="Bound">Aᵉ</a> <a id="1215" href="foundation-core.retracts-of-types%25E1%25B5%2589.html#1785" class="Function Operator">retract-ofᵉ</a> <a id="1227" href="foundation.propositions%25E1%25B5%2589.html#1165" class="Bound">Bᵉ</a> <a id="1230" class="Symbol">→</a> <a id="1232" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="1241" href="foundation.propositions%25E1%25B5%2589.html#1165" class="Bound">Bᵉ</a> <a id="1244" class="Symbol">→</a> <a id="1246" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="1255" href="foundation.propositions%25E1%25B5%2589.html#1150" class="Bound">Aᵉ</a>
  <a id="1260" href="foundation.propositions%25E1%25B5%2589.html#1190" class="Function">is-prop-retract-ofᵉ</a> <a id="1280" class="Symbol">=</a> <a id="1282" href="foundation-core.truncated-types%25E1%25B5%2589.html#3863" class="Function">is-trunc-retract-ofᵉ</a>
</pre>
### If a type embeds into a proposition, then it is a proposition

<pre class="Agda"><a id="1383" class="Keyword">abstract</a>
  <a id="is-prop-is-embᵉ"></a><a id="1394" href="foundation.propositions%25E1%25B5%2589.html#1394" class="Function">is-prop-is-embᵉ</a> <a id="1410" class="Symbol">:</a>
    <a id="1416" class="Symbol">{</a><a id="1417" href="foundation.propositions%25E1%25B5%2589.html#1417" class="Bound">l1ᵉ</a> <a id="1421" href="foundation.propositions%25E1%25B5%2589.html#1421" class="Bound">l2ᵉ</a> <a id="1425" class="Symbol">:</a> <a id="1427" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1432" class="Symbol">}</a> <a id="1434" class="Symbol">{</a><a id="1435" href="foundation.propositions%25E1%25B5%2589.html#1435" class="Bound">Aᵉ</a> <a id="1438" class="Symbol">:</a> <a id="1440" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1444" href="foundation.propositions%25E1%25B5%2589.html#1417" class="Bound">l1ᵉ</a><a id="1447" class="Symbol">}</a> <a id="1449" class="Symbol">{</a><a id="1450" href="foundation.propositions%25E1%25B5%2589.html#1450" class="Bound">Bᵉ</a> <a id="1453" class="Symbol">:</a> <a id="1455" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1459" href="foundation.propositions%25E1%25B5%2589.html#1421" class="Bound">l2ᵉ</a><a id="1462" class="Symbol">}</a> <a id="1464" class="Symbol">(</a><a id="1465" href="foundation.propositions%25E1%25B5%2589.html#1465" class="Bound">fᵉ</a> <a id="1468" class="Symbol">:</a> <a id="1470" href="foundation.propositions%25E1%25B5%2589.html#1435" class="Bound">Aᵉ</a> <a id="1473" class="Symbol">→</a> <a id="1475" href="foundation.propositions%25E1%25B5%2589.html#1450" class="Bound">Bᵉ</a><a id="1477" class="Symbol">)</a> <a id="1479" class="Symbol">→</a>
    <a id="1485" href="foundation-core.embeddings%25E1%25B5%2589.html#1101" class="Function">is-embᵉ</a> <a id="1493" href="foundation.propositions%25E1%25B5%2589.html#1465" class="Bound">fᵉ</a> <a id="1496" class="Symbol">→</a> <a id="1498" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="1507" href="foundation.propositions%25E1%25B5%2589.html#1450" class="Bound">Bᵉ</a> <a id="1510" class="Symbol">→</a> <a id="1512" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="1521" href="foundation.propositions%25E1%25B5%2589.html#1435" class="Bound">Aᵉ</a>
  <a id="1526" href="foundation.propositions%25E1%25B5%2589.html#1394" class="Function">is-prop-is-embᵉ</a> <a id="1542" class="Symbol">=</a> <a id="1544" href="foundation-core.truncated-types%25E1%25B5%2589.html#5458" class="Function">is-trunc-is-embᵉ</a> <a id="1561" href="foundation-core.truncation-levels%25E1%25B5%2589.html#546" class="InductiveConstructor">neg-two-𝕋ᵉ</a>

<a id="1573" class="Keyword">abstract</a>
  <a id="is-prop-embᵉ"></a><a id="1584" href="foundation.propositions%25E1%25B5%2589.html#1584" class="Function">is-prop-embᵉ</a> <a id="1597" class="Symbol">:</a>
    <a id="1603" class="Symbol">{</a><a id="1604" href="foundation.propositions%25E1%25B5%2589.html#1604" class="Bound">l1ᵉ</a> <a id="1608" href="foundation.propositions%25E1%25B5%2589.html#1608" class="Bound">l2ᵉ</a> <a id="1612" class="Symbol">:</a> <a id="1614" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1619" class="Symbol">}</a> <a id="1621" class="Symbol">{</a><a id="1622" href="foundation.propositions%25E1%25B5%2589.html#1622" class="Bound">Aᵉ</a> <a id="1625" class="Symbol">:</a> <a id="1627" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1631" href="foundation.propositions%25E1%25B5%2589.html#1604" class="Bound">l1ᵉ</a><a id="1634" class="Symbol">}</a> <a id="1636" class="Symbol">{</a><a id="1637" href="foundation.propositions%25E1%25B5%2589.html#1637" class="Bound">Bᵉ</a> <a id="1640" class="Symbol">:</a> <a id="1642" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1646" href="foundation.propositions%25E1%25B5%2589.html#1608" class="Bound">l2ᵉ</a><a id="1649" class="Symbol">}</a> <a id="1651" class="Symbol">(</a><a id="1652" href="foundation.propositions%25E1%25B5%2589.html#1652" class="Bound">fᵉ</a> <a id="1655" class="Symbol">:</a> <a id="1657" href="foundation.propositions%25E1%25B5%2589.html#1622" class="Bound">Aᵉ</a> <a id="1660" href="foundation-core.embeddings%25E1%25B5%2589.html#1585" class="Function Operator">↪ᵉ</a> <a id="1663" href="foundation.propositions%25E1%25B5%2589.html#1637" class="Bound">Bᵉ</a><a id="1665" class="Symbol">)</a> <a id="1667" class="Symbol">→</a> <a id="1669" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="1678" href="foundation.propositions%25E1%25B5%2589.html#1637" class="Bound">Bᵉ</a> <a id="1681" class="Symbol">→</a> <a id="1683" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="1692" href="foundation.propositions%25E1%25B5%2589.html#1622" class="Bound">Aᵉ</a>
  <a id="1697" href="foundation.propositions%25E1%25B5%2589.html#1584" class="Function">is-prop-embᵉ</a> <a id="1710" class="Symbol">=</a> <a id="1712" href="foundation-core.truncated-types%25E1%25B5%2589.html#5774" class="Function">is-trunc-embᵉ</a> <a id="1726" href="foundation-core.truncation-levels%25E1%25B5%2589.html#546" class="InductiveConstructor">neg-two-𝕋ᵉ</a>
</pre>
### Two equivalent types are equivalently propositions

<pre class="Agda"><a id="equiv-is-prop-equivᵉ"></a><a id="1806" href="foundation.propositions%25E1%25B5%2589.html#1806" class="Function">equiv-is-prop-equivᵉ</a> <a id="1827" class="Symbol">:</a> <a id="1829" class="Symbol">{</a><a id="1830" href="foundation.propositions%25E1%25B5%2589.html#1830" class="Bound">l1ᵉ</a> <a id="1834" href="foundation.propositions%25E1%25B5%2589.html#1834" class="Bound">l2ᵉ</a> <a id="1838" class="Symbol">:</a> <a id="1840" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1845" class="Symbol">}</a> <a id="1847" class="Symbol">{</a><a id="1848" href="foundation.propositions%25E1%25B5%2589.html#1848" class="Bound">Aᵉ</a> <a id="1851" class="Symbol">:</a> <a id="1853" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1857" href="foundation.propositions%25E1%25B5%2589.html#1830" class="Bound">l1ᵉ</a><a id="1860" class="Symbol">}</a> <a id="1862" class="Symbol">{</a><a id="1863" href="foundation.propositions%25E1%25B5%2589.html#1863" class="Bound">Bᵉ</a> <a id="1866" class="Symbol">:</a> <a id="1868" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1872" href="foundation.propositions%25E1%25B5%2589.html#1834" class="Bound">l2ᵉ</a><a id="1875" class="Symbol">}</a> <a id="1877" class="Symbol">→</a>
  <a id="1881" href="foundation.propositions%25E1%25B5%2589.html#1848" class="Bound">Aᵉ</a> <a id="1884" href="foundation-core.equivalences%25E1%25B5%2589.html#2662" class="Function Operator">≃ᵉ</a> <a id="1887" href="foundation.propositions%25E1%25B5%2589.html#1863" class="Bound">Bᵉ</a> <a id="1890" class="Symbol">→</a> <a id="1892" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="1901" href="foundation.propositions%25E1%25B5%2589.html#1848" class="Bound">Aᵉ</a> <a id="1904" href="foundation-core.equivalences%25E1%25B5%2589.html#2662" class="Function Operator">≃ᵉ</a> <a id="1907" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="1916" href="foundation.propositions%25E1%25B5%2589.html#1863" class="Bound">Bᵉ</a>
<a id="1919" href="foundation.propositions%25E1%25B5%2589.html#1806" class="Function">equiv-is-prop-equivᵉ</a> <a id="1940" class="Symbol">{</a><a id="1941" class="Argument">Aᵉ</a> <a id="1944" class="Symbol">=</a> <a id="1946" href="foundation.propositions%25E1%25B5%2589.html#1946" class="Bound">Aᵉ</a><a id="1948" class="Symbol">}</a> <a id="1950" class="Symbol">{</a><a id="1951" class="Argument">Bᵉ</a> <a id="1954" class="Symbol">=</a> <a id="1956" href="foundation.propositions%25E1%25B5%2589.html#1956" class="Bound">Bᵉ</a><a id="1958" class="Symbol">}</a> <a id="1960" href="foundation.propositions%25E1%25B5%2589.html#1960" class="Bound">eᵉ</a> <a id="1963" class="Symbol">=</a>
  <a id="1967" href="foundation.logical-equivalences%25E1%25B5%2589.html#5045" class="Function">equiv-iff-is-propᵉ</a>
    <a id="1990" class="Symbol">(</a> <a id="1992" href="foundation-core.propositions%25E1%25B5%2589.html#10530" class="Function">is-prop-is-propᵉ</a> <a id="2009" href="foundation.propositions%25E1%25B5%2589.html#1946" class="Bound">Aᵉ</a><a id="2011" class="Symbol">)</a>
    <a id="2017" class="Symbol">(</a> <a id="2019" href="foundation-core.propositions%25E1%25B5%2589.html#10530" class="Function">is-prop-is-propᵉ</a> <a id="2036" href="foundation.propositions%25E1%25B5%2589.html#1956" class="Bound">Bᵉ</a><a id="2038" class="Symbol">)</a>
    <a id="2044" class="Symbol">(</a> <a id="2046" href="foundation-core.propositions%25E1%25B5%2589.html#4311" class="Function">is-prop-equiv&#39;ᵉ</a> <a id="2062" href="foundation.propositions%25E1%25B5%2589.html#1960" class="Bound">eᵉ</a><a id="2064" class="Symbol">)</a>
    <a id="2070" class="Symbol">(</a> <a id="2072" href="foundation-core.propositions%25E1%25B5%2589.html#3917" class="Function">is-prop-equivᵉ</a> <a id="2087" href="foundation.propositions%25E1%25B5%2589.html#1960" class="Bound">eᵉ</a><a id="2089" class="Symbol">)</a>
</pre>
## See also

### Operations on propositions

There is a wide range of operations on propositions due to the rich structure of
intuitionistic logic. Below we give a structured overview of a notable selection
of such operations and their notation in the library.

The list is split into two sections, the first consists of operations that
generalize to arbitrary types and even sufficiently nice
[subuniverses](foundation.subuniverses.md), such as
$n$-[types](foundation-core.truncated-types.md).

| Name                                                        | Operator on types | Operator on propositions/subtypes |
| ----------------------------------------------------------- | ----------------- | --------------------------------- |
| [Dependent sum](foundation.dependent-pair-types.md)         | `Σ`               | `Σ-Prop`                          |
| [Dependent product](foundation.dependent-function-types.md) | `Π`               | `Π-Prop`                          |
| [Functions](foundation-core.function-types.md)              | `→`               | `⇒`                               |
| [Logical equivalence](foundation.logical-equivalences.md)   | `↔`               | `⇔`                               |
| [Product](foundation-core.cartesian-product-types.md)       | `×`               | `product-Prop`                    |
| [Join](synthetic-homotopy-theory.joins-of-types.md)         | `*`               | `join-Prop`                       |
| [Exclusive sum](foundation.exclusive-sum.md)                | `exclusive-sum`   | `exclusive-sum-Prop`              |
| [Coproduct](foundation-core.coproduct-types.md)             | `+`               | _N/A_                             |

Note that for many operations in the second section, there is an equivalent
operation on propositions in the first.

| Name                                                                         | Operator on types           | Operator on propositions/subtypes        |
| ---------------------------------------------------------------------------- | --------------------------- | ---------------------------------------- |
| [Initial object](foundation-core.empty-types.md)                             | `empty`                     | `empty-Prop`                             |
| [Terminal object](foundation.unit-type.md)                                   | `unit`                      | `unit-Prop`                              |
| [Existential quantification](foundation.existential-quantification.md)       | `exists-structure`          | `∃`                                      |
| [Unique existential quantification](foundation.uniqueness-quantification.md) | `uniquely-exists-structure` | `∃!`                                     |
| [Universal quantification](foundation.universal-quantification.md)           |                             | `∀'` (equivalent to `Π-Prop`)            |
| [Conjunction](foundation.conjunction.md)                                     |                             | `∧` (equivalent to `product-Prop`)       |
| [Disjunction](foundation.disjunction.md)                                     | `disjunction-type`          | `∨` (equivalent to `join-Prop`)          |
| [Exclusive disjunction](foundation.exclusive-disjunction.md)                 | `xor-type`                  | `⊻` (equivalent to `exclusive-sum-Prop`) |
| [Negation](foundation.negation.md)                                           | `¬`                         | `¬'`                                     |
| [Double negation](foundation.double-negation.md)                             | `¬¬`                        | `¬¬'`                                    |

We can also organize these operations by indexed and binary variants, giving us
the following table:

| Name                   | Binary | Indexed |
| ---------------------- | ------ | ------- |
| Product                | `×`    | `Π`     |
| Conjunction            | `∧`    | `∀'`    |
| Constructive existence | `+`    | `Σ`     |
| Existence              | `∨`    | `∃`     |
| Unique existence       | `⊻`    | `∃!`    |

### Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}