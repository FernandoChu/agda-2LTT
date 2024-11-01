# Binary embeddings

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="foundation.binary-embeddings%25E1%25B5%2589.html" class="Module">foundation.binary-embeddingsᵉ</a> <a id="67" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="123" class="Keyword">open</a> <a id="128" class="Keyword">import</a> <a id="135" href="foundation.action-on-identifications-binary-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-binary-functionsᵉ</a>
<a id="190" class="Keyword">open</a> <a id="195" class="Keyword">import</a> <a id="202" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-functionsᵉ</a>
<a id="250" class="Keyword">open</a> <a id="255" class="Keyword">import</a> <a id="262" href="foundation.binary-equivalences%25E1%25B5%2589.html" class="Module">foundation.binary-equivalencesᵉ</a>
<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="339" class="Keyword">open</a> <a id="344" class="Keyword">import</a> <a id="351" href="foundation.identity-types%25E1%25B5%2589.html" class="Module">foundation.identity-typesᵉ</a>
<a id="378" class="Keyword">open</a> <a id="383" class="Keyword">import</a> <a id="390" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="419" class="Keyword">open</a> <a id="424" class="Keyword">import</a> <a id="431" href="foundation-core.embeddings%25E1%25B5%2589.html" class="Module">foundation-core.embeddingsᵉ</a>
<a id="459" class="Keyword">open</a> <a id="464" class="Keyword">import</a> <a id="471" href="foundation-core.equivalences%25E1%25B5%2589.html" class="Module">foundation-core.equivalencesᵉ</a>
</pre>
</details>

## Idea

A binary operation `f : A → B → C` is said to be a binary embedding if the
functions `λ x → f x b` and `λ y → f a y` are embeddings for each `a : A` and
`b : B` respectively.

## Definition

<pre class="Agda"><a id="is-binary-embᵉ"></a><a id="726" href="foundation.binary-embeddings%25E1%25B5%2589.html#726" class="Function">is-binary-embᵉ</a> <a id="741" class="Symbol">:</a>
  <a id="745" class="Symbol">{</a><a id="746" href="foundation.binary-embeddings%25E1%25B5%2589.html#746" class="Bound">l1ᵉ</a> <a id="750" href="foundation.binary-embeddings%25E1%25B5%2589.html#750" class="Bound">l2ᵉ</a> <a id="754" href="foundation.binary-embeddings%25E1%25B5%2589.html#754" class="Bound">l3ᵉ</a> <a id="758" class="Symbol">:</a> <a id="760" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="765" class="Symbol">}</a> <a id="767" class="Symbol">{</a><a id="768" href="foundation.binary-embeddings%25E1%25B5%2589.html#768" class="Bound">Aᵉ</a> <a id="771" class="Symbol">:</a> <a id="773" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="777" href="foundation.binary-embeddings%25E1%25B5%2589.html#746" class="Bound">l1ᵉ</a><a id="780" class="Symbol">}</a> <a id="782" class="Symbol">{</a><a id="783" href="foundation.binary-embeddings%25E1%25B5%2589.html#783" class="Bound">Bᵉ</a> <a id="786" class="Symbol">:</a> <a id="788" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="792" href="foundation.binary-embeddings%25E1%25B5%2589.html#750" class="Bound">l2ᵉ</a><a id="795" class="Symbol">}</a> <a id="797" class="Symbol">{</a><a id="798" href="foundation.binary-embeddings%25E1%25B5%2589.html#798" class="Bound">Cᵉ</a> <a id="801" class="Symbol">:</a> <a id="803" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="807" href="foundation.binary-embeddings%25E1%25B5%2589.html#754" class="Bound">l3ᵉ</a><a id="810" class="Symbol">}</a> <a id="812" class="Symbol">→</a>
  <a id="816" class="Symbol">(</a><a id="817" href="foundation.binary-embeddings%25E1%25B5%2589.html#768" class="Bound">Aᵉ</a> <a id="820" class="Symbol">→</a> <a id="822" href="foundation.binary-embeddings%25E1%25B5%2589.html#783" class="Bound">Bᵉ</a> <a id="825" class="Symbol">→</a> <a id="827" href="foundation.binary-embeddings%25E1%25B5%2589.html#798" class="Bound">Cᵉ</a><a id="829" class="Symbol">)</a> <a id="831" class="Symbol">→</a> <a id="833" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="837" class="Symbol">(</a><a id="838" href="foundation.binary-embeddings%25E1%25B5%2589.html#746" class="Bound">l1ᵉ</a> <a id="842" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="844" href="foundation.binary-embeddings%25E1%25B5%2589.html#750" class="Bound">l2ᵉ</a> <a id="848" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="850" href="foundation.binary-embeddings%25E1%25B5%2589.html#754" class="Bound">l3ᵉ</a><a id="853" class="Symbol">)</a>
<a id="855" href="foundation.binary-embeddings%25E1%25B5%2589.html#726" class="Function">is-binary-embᵉ</a> <a id="870" class="Symbol">{</a><a id="871" class="Argument">Aᵉ</a> <a id="874" class="Symbol">=</a> <a id="876" href="foundation.binary-embeddings%25E1%25B5%2589.html#876" class="Bound">Aᵉ</a><a id="878" class="Symbol">}</a> <a id="880" class="Symbol">{</a><a id="881" class="Argument">Bᵉ</a> <a id="884" class="Symbol">=</a> <a id="886" href="foundation.binary-embeddings%25E1%25B5%2589.html#886" class="Bound">Bᵉ</a><a id="888" class="Symbol">}</a> <a id="890" href="foundation.binary-embeddings%25E1%25B5%2589.html#890" class="Bound">fᵉ</a> <a id="893" class="Symbol">=</a>
  <a id="897" class="Symbol">{</a><a id="898" href="foundation.binary-embeddings%25E1%25B5%2589.html#898" class="Bound">xᵉ</a> <a id="901" href="foundation.binary-embeddings%25E1%25B5%2589.html#901" class="Bound">x&#39;ᵉ</a> <a id="905" class="Symbol">:</a> <a id="907" href="foundation.binary-embeddings%25E1%25B5%2589.html#876" class="Bound">Aᵉ</a><a id="909" class="Symbol">}</a> <a id="911" class="Symbol">{</a><a id="912" href="foundation.binary-embeddings%25E1%25B5%2589.html#912" class="Bound">yᵉ</a> <a id="915" href="foundation.binary-embeddings%25E1%25B5%2589.html#915" class="Bound">y&#39;ᵉ</a> <a id="919" class="Symbol">:</a> <a id="921" href="foundation.binary-embeddings%25E1%25B5%2589.html#886" class="Bound">Bᵉ</a><a id="923" class="Symbol">}</a> <a id="925" class="Symbol">→</a>
    <a id="931" href="foundation.binary-equivalences%25E1%25B5%2589.html#832" class="Function">is-binary-equivᵉ</a> <a id="948" class="Symbol">(λ</a> <a id="951" class="Symbol">(</a><a id="952" href="foundation.binary-embeddings%25E1%25B5%2589.html#952" class="Bound">pᵉ</a> <a id="955" class="Symbol">:</a> <a id="957" href="foundation.binary-embeddings%25E1%25B5%2589.html#898" class="Bound">xᵉ</a> <a id="960" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="963" href="foundation.binary-embeddings%25E1%25B5%2589.html#901" class="Bound">x&#39;ᵉ</a><a id="966" class="Symbol">)</a> <a id="968" class="Symbol">(</a><a id="969" href="foundation.binary-embeddings%25E1%25B5%2589.html#969" class="Bound">qᵉ</a> <a id="972" class="Symbol">:</a> <a id="974" href="foundation.binary-embeddings%25E1%25B5%2589.html#912" class="Bound">yᵉ</a> <a id="977" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="980" href="foundation.binary-embeddings%25E1%25B5%2589.html#915" class="Bound">y&#39;ᵉ</a><a id="983" class="Symbol">)</a> <a id="985" class="Symbol">→</a> <a id="987" href="foundation.action-on-identifications-binary-functions%25E1%25B5%2589.html#1542" class="Function">ap-binaryᵉ</a> <a id="998" href="foundation.binary-embeddings%25E1%25B5%2589.html#890" class="Bound">fᵉ</a> <a id="1001" href="foundation.binary-embeddings%25E1%25B5%2589.html#952" class="Bound">pᵉ</a> <a id="1004" href="foundation.binary-embeddings%25E1%25B5%2589.html#969" class="Bound">qᵉ</a><a id="1006" class="Symbol">)</a>
</pre>
## Properties

### Any binary equivalence is a binary embedding

<pre class="Agda"><a id="is-emb-fix-left-is-binary-equivᵉ"></a><a id="1086" href="foundation.binary-embeddings%25E1%25B5%2589.html#1086" class="Function">is-emb-fix-left-is-binary-equivᵉ</a> <a id="1119" class="Symbol">:</a>
  <a id="1123" class="Symbol">{</a><a id="1124" href="foundation.binary-embeddings%25E1%25B5%2589.html#1124" class="Bound">l1ᵉ</a> <a id="1128" href="foundation.binary-embeddings%25E1%25B5%2589.html#1128" class="Bound">l2ᵉ</a> <a id="1132" href="foundation.binary-embeddings%25E1%25B5%2589.html#1132" class="Bound">l3ᵉ</a> <a id="1136" class="Symbol">:</a> <a id="1138" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1143" class="Symbol">}</a> <a id="1145" class="Symbol">{</a><a id="1146" href="foundation.binary-embeddings%25E1%25B5%2589.html#1146" class="Bound">Aᵉ</a> <a id="1149" class="Symbol">:</a> <a id="1151" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1155" href="foundation.binary-embeddings%25E1%25B5%2589.html#1124" class="Bound">l1ᵉ</a><a id="1158" class="Symbol">}</a> <a id="1160" class="Symbol">{</a><a id="1161" href="foundation.binary-embeddings%25E1%25B5%2589.html#1161" class="Bound">Bᵉ</a> <a id="1164" class="Symbol">:</a> <a id="1166" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1170" href="foundation.binary-embeddings%25E1%25B5%2589.html#1128" class="Bound">l2ᵉ</a><a id="1173" class="Symbol">}</a> <a id="1175" class="Symbol">{</a><a id="1176" href="foundation.binary-embeddings%25E1%25B5%2589.html#1176" class="Bound">Cᵉ</a> <a id="1179" class="Symbol">:</a> <a id="1181" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1185" href="foundation.binary-embeddings%25E1%25B5%2589.html#1132" class="Bound">l3ᵉ</a><a id="1188" class="Symbol">}</a> <a id="1190" class="Symbol">(</a><a id="1191" href="foundation.binary-embeddings%25E1%25B5%2589.html#1191" class="Bound">fᵉ</a> <a id="1194" class="Symbol">:</a> <a id="1196" href="foundation.binary-embeddings%25E1%25B5%2589.html#1146" class="Bound">Aᵉ</a> <a id="1199" class="Symbol">→</a> <a id="1201" href="foundation.binary-embeddings%25E1%25B5%2589.html#1161" class="Bound">Bᵉ</a> <a id="1204" class="Symbol">→</a> <a id="1206" href="foundation.binary-embeddings%25E1%25B5%2589.html#1176" class="Bound">Cᵉ</a><a id="1208" class="Symbol">)</a> <a id="1210" class="Symbol">→</a>
  <a id="1214" href="foundation.binary-equivalences%25E1%25B5%2589.html#832" class="Function">is-binary-equivᵉ</a> <a id="1231" href="foundation.binary-embeddings%25E1%25B5%2589.html#1191" class="Bound">fᵉ</a> <a id="1234" class="Symbol">→</a> <a id="1236" class="Symbol">{</a><a id="1237" href="foundation.binary-embeddings%25E1%25B5%2589.html#1237" class="Bound">aᵉ</a> <a id="1240" class="Symbol">:</a> <a id="1242" href="foundation.binary-embeddings%25E1%25B5%2589.html#1146" class="Bound">Aᵉ</a><a id="1244" class="Symbol">}</a> <a id="1246" class="Symbol">→</a> <a id="1248" href="foundation-core.embeddings%25E1%25B5%2589.html#1101" class="Function">is-embᵉ</a> <a id="1256" class="Symbol">(</a><a id="1257" href="foundation.binary-equivalences%25E1%25B5%2589.html#538" class="Function">fix-leftᵉ</a> <a id="1267" href="foundation.binary-embeddings%25E1%25B5%2589.html#1191" class="Bound">fᵉ</a> <a id="1270" href="foundation.binary-embeddings%25E1%25B5%2589.html#1237" class="Bound">aᵉ</a><a id="1272" class="Symbol">)</a>
<a id="1274" href="foundation.binary-embeddings%25E1%25B5%2589.html#1086" class="Function">is-emb-fix-left-is-binary-equivᵉ</a> <a id="1307" href="foundation.binary-embeddings%25E1%25B5%2589.html#1307" class="Bound">fᵉ</a> <a id="1310" href="foundation.binary-embeddings%25E1%25B5%2589.html#1310" class="Bound">Hᵉ</a> <a id="1313" class="Symbol">{</a><a id="1314" href="foundation.binary-embeddings%25E1%25B5%2589.html#1314" class="Bound">aᵉ</a><a id="1316" class="Symbol">}</a> <a id="1318" class="Symbol">=</a>
  <a id="1322" href="foundation-core.equivalences%25E1%25B5%2589.html#22050" class="Function">is-emb-is-equivᵉ</a> <a id="1339" class="Symbol">(</a><a id="1340" href="foundation.binary-equivalences%25E1%25B5%2589.html#1096" class="Function">is-equiv-fix-leftᵉ</a> <a id="1359" href="foundation.binary-embeddings%25E1%25B5%2589.html#1307" class="Bound">fᵉ</a> <a id="1362" href="foundation.binary-embeddings%25E1%25B5%2589.html#1310" class="Bound">Hᵉ</a><a id="1364" class="Symbol">)</a>

<a id="is-emb-fix-right-is-binary-equivᵉ"></a><a id="1367" href="foundation.binary-embeddings%25E1%25B5%2589.html#1367" class="Function">is-emb-fix-right-is-binary-equivᵉ</a> <a id="1401" class="Symbol">:</a>
  <a id="1405" class="Symbol">{</a><a id="1406" href="foundation.binary-embeddings%25E1%25B5%2589.html#1406" class="Bound">l1ᵉ</a> <a id="1410" href="foundation.binary-embeddings%25E1%25B5%2589.html#1410" class="Bound">l2ᵉ</a> <a id="1414" href="foundation.binary-embeddings%25E1%25B5%2589.html#1414" class="Bound">l3ᵉ</a> <a id="1418" class="Symbol">:</a> <a id="1420" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1425" class="Symbol">}</a> <a id="1427" class="Symbol">{</a><a id="1428" href="foundation.binary-embeddings%25E1%25B5%2589.html#1428" class="Bound">Aᵉ</a> <a id="1431" class="Symbol">:</a> <a id="1433" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1437" href="foundation.binary-embeddings%25E1%25B5%2589.html#1406" class="Bound">l1ᵉ</a><a id="1440" class="Symbol">}</a> <a id="1442" class="Symbol">{</a><a id="1443" href="foundation.binary-embeddings%25E1%25B5%2589.html#1443" class="Bound">Bᵉ</a> <a id="1446" class="Symbol">:</a> <a id="1448" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1452" href="foundation.binary-embeddings%25E1%25B5%2589.html#1410" class="Bound">l2ᵉ</a><a id="1455" class="Symbol">}</a> <a id="1457" class="Symbol">{</a><a id="1458" href="foundation.binary-embeddings%25E1%25B5%2589.html#1458" class="Bound">Cᵉ</a> <a id="1461" class="Symbol">:</a> <a id="1463" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1467" href="foundation.binary-embeddings%25E1%25B5%2589.html#1414" class="Bound">l3ᵉ</a><a id="1470" class="Symbol">}</a> <a id="1472" class="Symbol">(</a><a id="1473" href="foundation.binary-embeddings%25E1%25B5%2589.html#1473" class="Bound">fᵉ</a> <a id="1476" class="Symbol">:</a> <a id="1478" href="foundation.binary-embeddings%25E1%25B5%2589.html#1428" class="Bound">Aᵉ</a> <a id="1481" class="Symbol">→</a> <a id="1483" href="foundation.binary-embeddings%25E1%25B5%2589.html#1443" class="Bound">Bᵉ</a> <a id="1486" class="Symbol">→</a> <a id="1488" href="foundation.binary-embeddings%25E1%25B5%2589.html#1458" class="Bound">Cᵉ</a><a id="1490" class="Symbol">)</a> <a id="1492" class="Symbol">→</a>
  <a id="1496" href="foundation.binary-equivalences%25E1%25B5%2589.html#832" class="Function">is-binary-equivᵉ</a> <a id="1513" href="foundation.binary-embeddings%25E1%25B5%2589.html#1473" class="Bound">fᵉ</a> <a id="1516" class="Symbol">→</a> <a id="1518" class="Symbol">{</a><a id="1519" href="foundation.binary-embeddings%25E1%25B5%2589.html#1519" class="Bound">bᵉ</a> <a id="1522" class="Symbol">:</a> <a id="1524" href="foundation.binary-embeddings%25E1%25B5%2589.html#1443" class="Bound">Bᵉ</a><a id="1526" class="Symbol">}</a> <a id="1528" class="Symbol">→</a> <a id="1530" href="foundation-core.embeddings%25E1%25B5%2589.html#1101" class="Function">is-embᵉ</a> <a id="1538" class="Symbol">(</a><a id="1539" href="foundation.binary-equivalences%25E1%25B5%2589.html#681" class="Function">fix-rightᵉ</a> <a id="1550" href="foundation.binary-embeddings%25E1%25B5%2589.html#1473" class="Bound">fᵉ</a> <a id="1553" href="foundation.binary-embeddings%25E1%25B5%2589.html#1519" class="Bound">bᵉ</a><a id="1555" class="Symbol">)</a>
<a id="1557" href="foundation.binary-embeddings%25E1%25B5%2589.html#1367" class="Function">is-emb-fix-right-is-binary-equivᵉ</a> <a id="1591" href="foundation.binary-embeddings%25E1%25B5%2589.html#1591" class="Bound">fᵉ</a> <a id="1594" href="foundation.binary-embeddings%25E1%25B5%2589.html#1594" class="Bound">Hᵉ</a> <a id="1597" class="Symbol">{</a><a id="1598" href="foundation.binary-embeddings%25E1%25B5%2589.html#1598" class="Bound">bᵉ</a><a id="1600" class="Symbol">}</a> <a id="1602" class="Symbol">=</a>
  <a id="1606" href="foundation-core.equivalences%25E1%25B5%2589.html#22050" class="Function">is-emb-is-equivᵉ</a> <a id="1623" class="Symbol">(</a><a id="1624" href="foundation.binary-equivalences%25E1%25B5%2589.html#1316" class="Function">is-equiv-fix-rightᵉ</a> <a id="1644" href="foundation.binary-embeddings%25E1%25B5%2589.html#1591" class="Bound">fᵉ</a> <a id="1647" href="foundation.binary-embeddings%25E1%25B5%2589.html#1594" class="Bound">Hᵉ</a><a id="1649" class="Symbol">)</a>

<a id="is-binary-emb-is-binary-equivᵉ"></a><a id="1652" href="foundation.binary-embeddings%25E1%25B5%2589.html#1652" class="Function">is-binary-emb-is-binary-equivᵉ</a> <a id="1683" class="Symbol">:</a>
  <a id="1687" class="Symbol">{</a><a id="1688" href="foundation.binary-embeddings%25E1%25B5%2589.html#1688" class="Bound">l1ᵉ</a> <a id="1692" href="foundation.binary-embeddings%25E1%25B5%2589.html#1692" class="Bound">l2ᵉ</a> <a id="1696" href="foundation.binary-embeddings%25E1%25B5%2589.html#1696" class="Bound">l3ᵉ</a> <a id="1700" class="Symbol">:</a> <a id="1702" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1707" class="Symbol">}</a> <a id="1709" class="Symbol">{</a><a id="1710" href="foundation.binary-embeddings%25E1%25B5%2589.html#1710" class="Bound">Aᵉ</a> <a id="1713" class="Symbol">:</a> <a id="1715" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1719" href="foundation.binary-embeddings%25E1%25B5%2589.html#1688" class="Bound">l1ᵉ</a><a id="1722" class="Symbol">}</a> <a id="1724" class="Symbol">{</a><a id="1725" href="foundation.binary-embeddings%25E1%25B5%2589.html#1725" class="Bound">Bᵉ</a> <a id="1728" class="Symbol">:</a> <a id="1730" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1734" href="foundation.binary-embeddings%25E1%25B5%2589.html#1692" class="Bound">l2ᵉ</a><a id="1737" class="Symbol">}</a> <a id="1739" class="Symbol">{</a><a id="1740" href="foundation.binary-embeddings%25E1%25B5%2589.html#1740" class="Bound">Cᵉ</a> <a id="1743" class="Symbol">:</a> <a id="1745" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1749" href="foundation.binary-embeddings%25E1%25B5%2589.html#1696" class="Bound">l3ᵉ</a><a id="1752" class="Symbol">}</a> <a id="1754" class="Symbol">{</a><a id="1755" href="foundation.binary-embeddings%25E1%25B5%2589.html#1755" class="Bound">fᵉ</a> <a id="1758" class="Symbol">:</a> <a id="1760" href="foundation.binary-embeddings%25E1%25B5%2589.html#1710" class="Bound">Aᵉ</a> <a id="1763" class="Symbol">→</a> <a id="1765" href="foundation.binary-embeddings%25E1%25B5%2589.html#1725" class="Bound">Bᵉ</a> <a id="1768" class="Symbol">→</a> <a id="1770" href="foundation.binary-embeddings%25E1%25B5%2589.html#1740" class="Bound">Cᵉ</a><a id="1772" class="Symbol">}</a> <a id="1774" class="Symbol">→</a>
  <a id="1778" href="foundation.binary-equivalences%25E1%25B5%2589.html#832" class="Function">is-binary-equivᵉ</a> <a id="1795" href="foundation.binary-embeddings%25E1%25B5%2589.html#1755" class="Bound">fᵉ</a> <a id="1798" class="Symbol">→</a> <a id="1800" href="foundation.binary-embeddings%25E1%25B5%2589.html#726" class="Function">is-binary-embᵉ</a> <a id="1815" href="foundation.binary-embeddings%25E1%25B5%2589.html#1755" class="Bound">fᵉ</a>
<a id="1818" href="foundation.binary-embeddings%25E1%25B5%2589.html#1652" class="Function">is-binary-emb-is-binary-equivᵉ</a> <a id="1849" class="Symbol">{</a><a id="1850" class="Argument">fᵉ</a> <a id="1853" class="Symbol">=</a> <a id="1855" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a><a id="1857" class="Symbol">}</a> <a id="1859" href="foundation.binary-embeddings%25E1%25B5%2589.html#1859" class="Bound">Hᵉ</a> <a id="1862" class="Symbol">{</a><a id="1863" href="foundation.binary-embeddings%25E1%25B5%2589.html#1863" class="Bound">xᵉ</a><a id="1865" class="Symbol">}</a> <a id="1867" class="Symbol">{</a><a id="1868" href="foundation.binary-embeddings%25E1%25B5%2589.html#1868" class="Bound">x&#39;ᵉ</a><a id="1871" class="Symbol">}</a> <a id="1873" class="Symbol">{</a><a id="1874" href="foundation.binary-embeddings%25E1%25B5%2589.html#1874" class="Bound">yᵉ</a><a id="1876" class="Symbol">}</a> <a id="1878" class="Symbol">{</a><a id="1879" href="foundation.binary-embeddings%25E1%25B5%2589.html#1879" class="Bound">y&#39;ᵉ</a><a id="1882" class="Symbol">}</a> <a id="1884" class="Symbol">=</a>
  <a id="1888" href="foundation.dependent-pair-types%25E1%25B5%2589.html#679" class="InductiveConstructor">pairᵉ</a>
    <a id="1898" class="Symbol">(</a> <a id="1900" class="Symbol">λ</a> <a id="1902" href="foundation.binary-embeddings%25E1%25B5%2589.html#1902" class="Bound">qᵉ</a> <a id="1905" class="Symbol">→</a>
      <a id="1913" href="foundation-core.equivalences%25E1%25B5%2589.html#10728" class="Function">is-equiv-left-map-triangleᵉ</a>
        <a id="1949" class="Symbol">(</a> <a id="1951" class="Symbol">λ</a> <a id="1953" href="foundation.binary-embeddings%25E1%25B5%2589.html#1953" class="Bound">pᵉ</a> <a id="1956" class="Symbol">→</a> <a id="1958" href="foundation.action-on-identifications-binary-functions%25E1%25B5%2589.html#1542" class="Function">ap-binaryᵉ</a> <a id="1969" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="1972" href="foundation.binary-embeddings%25E1%25B5%2589.html#1953" class="Bound">pᵉ</a> <a id="1975" href="foundation.binary-embeddings%25E1%25B5%2589.html#1902" class="Bound">qᵉ</a><a id="1977" class="Symbol">)</a>
        <a id="1987" class="Symbol">(</a> <a id="1989" href="foundation-core.identity-types%25E1%25B5%2589.html#6085" class="Function">concat&#39;ᵉ</a> <a id="1998" class="Symbol">(</a><a id="1999" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="2002" href="foundation.binary-embeddings%25E1%25B5%2589.html#1863" class="Bound">xᵉ</a> <a id="2005" href="foundation.binary-embeddings%25E1%25B5%2589.html#1874" class="Bound">yᵉ</a><a id="2007" class="Symbol">)</a> <a id="2009" class="Symbol">(</a><a id="2010" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="2014" class="Symbol">(</a><a id="2015" href="foundation.binary-equivalences%25E1%25B5%2589.html#538" class="Function">fix-leftᵉ</a> <a id="2025" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="2028" href="foundation.binary-embeddings%25E1%25B5%2589.html#1868" class="Bound">x&#39;ᵉ</a><a id="2031" class="Symbol">)</a> <a id="2033" href="foundation.binary-embeddings%25E1%25B5%2589.html#1902" class="Bound">qᵉ</a><a id="2035" class="Symbol">))</a>
        <a id="2046" class="Symbol">(</a> <a id="2048" class="Symbol">λ</a> <a id="2050" href="foundation.binary-embeddings%25E1%25B5%2589.html#2050" class="Bound">pᵉ</a> <a id="2053" class="Symbol">→</a> <a id="2055" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="2059" class="Symbol">(</a><a id="2060" href="foundation.binary-equivalences%25E1%25B5%2589.html#681" class="Function">fix-rightᵉ</a> <a id="2071" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="2074" href="foundation.binary-embeddings%25E1%25B5%2589.html#1874" class="Bound">yᵉ</a><a id="2076" class="Symbol">)</a> <a id="2078" href="foundation.binary-embeddings%25E1%25B5%2589.html#2050" class="Bound">pᵉ</a><a id="2080" class="Symbol">)</a>
        <a id="2090" class="Symbol">(</a> <a id="2092" class="Symbol">λ</a> <a id="2094" href="foundation.binary-embeddings%25E1%25B5%2589.html#2094" class="Bound">pᵉ</a> <a id="2097" class="Symbol">→</a> <a id="2099" href="foundation.action-on-identifications-binary-functions%25E1%25B5%2589.html#2294" class="Function">triangle-ap-binaryᵉ</a> <a id="2119" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="2122" href="foundation.binary-embeddings%25E1%25B5%2589.html#2094" class="Bound">pᵉ</a> <a id="2125" href="foundation.binary-embeddings%25E1%25B5%2589.html#1902" class="Bound">qᵉ</a><a id="2127" class="Symbol">)</a>
        <a id="2137" class="Symbol">(</a> <a id="2139" href="foundation.binary-embeddings%25E1%25B5%2589.html#1367" class="Function">is-emb-fix-right-is-binary-equivᵉ</a> <a id="2173" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="2176" href="foundation.binary-embeddings%25E1%25B5%2589.html#1859" class="Bound">Hᵉ</a> <a id="2179" href="foundation.binary-embeddings%25E1%25B5%2589.html#1863" class="Bound">xᵉ</a> <a id="2182" href="foundation.binary-embeddings%25E1%25B5%2589.html#1868" class="Bound">x&#39;ᵉ</a><a id="2185" class="Symbol">)</a>
        <a id="2195" class="Symbol">(</a> <a id="2197" href="foundation.identity-types%25E1%25B5%2589.html#4236" class="Function">is-equiv-concat&#39;ᵉ</a> <a id="2215" class="Symbol">(</a><a id="2216" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="2219" href="foundation.binary-embeddings%25E1%25B5%2589.html#1863" class="Bound">xᵉ</a> <a id="2222" href="foundation.binary-embeddings%25E1%25B5%2589.html#1874" class="Bound">yᵉ</a><a id="2224" class="Symbol">)</a> <a id="2226" class="Symbol">(</a><a id="2227" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="2231" class="Symbol">(</a><a id="2232" href="foundation.binary-equivalences%25E1%25B5%2589.html#538" class="Function">fix-leftᵉ</a> <a id="2242" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="2245" href="foundation.binary-embeddings%25E1%25B5%2589.html#1868" class="Bound">x&#39;ᵉ</a><a id="2248" class="Symbol">)</a> <a id="2250" href="foundation.binary-embeddings%25E1%25B5%2589.html#1902" class="Bound">qᵉ</a><a id="2252" class="Symbol">)))</a>
    <a id="2260" class="Symbol">(</a> <a id="2262" class="Symbol">λ</a> <a id="2264" href="foundation.binary-embeddings%25E1%25B5%2589.html#2264" class="Bound">pᵉ</a> <a id="2267" class="Symbol">→</a>
      <a id="2275" href="foundation-core.equivalences%25E1%25B5%2589.html#10728" class="Function">is-equiv-left-map-triangleᵉ</a>
        <a id="2311" class="Symbol">(</a> <a id="2313" class="Symbol">λ</a> <a id="2315" href="foundation.binary-embeddings%25E1%25B5%2589.html#2315" class="Bound">qᵉ</a> <a id="2318" class="Symbol">→</a> <a id="2320" href="foundation.action-on-identifications-binary-functions%25E1%25B5%2589.html#1542" class="Function">ap-binaryᵉ</a> <a id="2331" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="2334" href="foundation.binary-embeddings%25E1%25B5%2589.html#2264" class="Bound">pᵉ</a> <a id="2337" href="foundation.binary-embeddings%25E1%25B5%2589.html#2315" class="Bound">qᵉ</a><a id="2339" class="Symbol">)</a>
        <a id="2349" class="Symbol">(</a> <a id="2351" href="foundation-core.identity-types%25E1%25B5%2589.html#5984" class="Function">concatᵉ</a> <a id="2359" class="Symbol">(</a><a id="2360" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="2364" class="Symbol">(</a><a id="2365" href="foundation.binary-equivalences%25E1%25B5%2589.html#681" class="Function">fix-rightᵉ</a> <a id="2376" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="2379" href="foundation.binary-embeddings%25E1%25B5%2589.html#1874" class="Bound">yᵉ</a><a id="2381" class="Symbol">)</a> <a id="2383" href="foundation.binary-embeddings%25E1%25B5%2589.html#2264" class="Bound">pᵉ</a><a id="2385" class="Symbol">)</a> <a id="2387" class="Symbol">(</a><a id="2388" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="2391" href="foundation.binary-embeddings%25E1%25B5%2589.html#1868" class="Bound">x&#39;ᵉ</a> <a id="2395" href="foundation.binary-embeddings%25E1%25B5%2589.html#1879" class="Bound">y&#39;ᵉ</a><a id="2398" class="Symbol">))</a>
        <a id="2409" class="Symbol">(</a> <a id="2411" class="Symbol">λ</a> <a id="2413" href="foundation.binary-embeddings%25E1%25B5%2589.html#2413" class="Bound">qᵉ</a> <a id="2416" class="Symbol">→</a> <a id="2418" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="2422" class="Symbol">(</a><a id="2423" href="foundation.binary-equivalences%25E1%25B5%2589.html#538" class="Function">fix-leftᵉ</a> <a id="2433" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="2436" href="foundation.binary-embeddings%25E1%25B5%2589.html#1868" class="Bound">x&#39;ᵉ</a><a id="2439" class="Symbol">)</a> <a id="2441" href="foundation.binary-embeddings%25E1%25B5%2589.html#2413" class="Bound">qᵉ</a><a id="2443" class="Symbol">)</a>
        <a id="2453" class="Symbol">(</a> <a id="2455" class="Symbol">λ</a> <a id="2457" href="foundation.binary-embeddings%25E1%25B5%2589.html#2457" class="Bound">qᵉ</a> <a id="2460" class="Symbol">→</a> <a id="2462" href="foundation.action-on-identifications-binary-functions%25E1%25B5%2589.html#2294" class="Function">triangle-ap-binaryᵉ</a> <a id="2482" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="2485" href="foundation.binary-embeddings%25E1%25B5%2589.html#2264" class="Bound">pᵉ</a> <a id="2488" href="foundation.binary-embeddings%25E1%25B5%2589.html#2457" class="Bound">qᵉ</a><a id="2490" class="Symbol">)</a>
        <a id="2500" class="Symbol">(</a> <a id="2502" href="foundation.binary-embeddings%25E1%25B5%2589.html#1086" class="Function">is-emb-fix-left-is-binary-equivᵉ</a> <a id="2535" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="2538" href="foundation.binary-embeddings%25E1%25B5%2589.html#1859" class="Bound">Hᵉ</a> <a id="2541" href="foundation.binary-embeddings%25E1%25B5%2589.html#1874" class="Bound">yᵉ</a> <a id="2544" href="foundation.binary-embeddings%25E1%25B5%2589.html#1879" class="Bound">y&#39;ᵉ</a><a id="2547" class="Symbol">)</a>
        <a id="2557" class="Symbol">(</a> <a id="2559" href="foundation.identity-types%25E1%25B5%2589.html#2235" class="Function">is-equiv-concatᵉ</a> <a id="2576" class="Symbol">(</a><a id="2577" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="2581" class="Symbol">(</a><a id="2582" href="foundation.binary-equivalences%25E1%25B5%2589.html#681" class="Function">fix-rightᵉ</a> <a id="2593" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="2596" href="foundation.binary-embeddings%25E1%25B5%2589.html#1874" class="Bound">yᵉ</a><a id="2598" class="Symbol">)</a> <a id="2600" href="foundation.binary-embeddings%25E1%25B5%2589.html#2264" class="Bound">pᵉ</a><a id="2602" class="Symbol">)</a> <a id="2604" class="Symbol">(</a><a id="2605" href="foundation.binary-embeddings%25E1%25B5%2589.html#1855" class="Bound">fᵉ</a> <a id="2608" href="foundation.binary-embeddings%25E1%25B5%2589.html#1868" class="Bound">x&#39;ᵉ</a> <a id="2612" href="foundation.binary-embeddings%25E1%25B5%2589.html#1879" class="Bound">y&#39;ᵉ</a><a id="2615" class="Symbol">)))</a>
</pre>