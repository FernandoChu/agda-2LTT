# Evaluation of functions

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="foundation.evaluation-functions%25E1%25B5%2589.html" class="Module">foundation.evaluation-functionsᵉ</a> <a id="76" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="132" class="Keyword">open</a> <a id="137" class="Keyword">import</a> <a id="144" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-functionsᵉ</a>
<a id="192" class="Keyword">open</a> <a id="197" class="Keyword">import</a> <a id="204" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="233" class="Keyword">open</a> <a id="238" class="Keyword">import</a> <a id="245" href="foundation-core.identity-types%25E1%25B5%2589.html" class="Module">foundation-core.identity-typesᵉ</a>
</pre>
</details>

## Idea

Consider a family of types `B` over `A` and let `a : A` be an element. The
{{#concept "evaluation function" Agda=ev}} at `a`

```text
  ev : ((x : A) → B x) → B a
```

is the map given by `f ↦ f a`, evaluating dependent functions at `a`.

## Definitions

### The evaluation function

<pre class="Agda"><a id="595" class="Keyword">module</a> <a id="602" href="foundation.evaluation-functions%25E1%25B5%2589.html#602" class="Module">_</a>
  <a id="606" class="Symbol">{</a><a id="607" href="foundation.evaluation-functions%25E1%25B5%2589.html#607" class="Bound">l1ᵉ</a> <a id="611" href="foundation.evaluation-functions%25E1%25B5%2589.html#611" class="Bound">l2ᵉ</a> <a id="615" class="Symbol">:</a> <a id="617" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="622" class="Symbol">}</a> <a id="624" class="Symbol">{</a><a id="625" href="foundation.evaluation-functions%25E1%25B5%2589.html#625" class="Bound">Aᵉ</a> <a id="628" class="Symbol">:</a> <a id="630" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="634" href="foundation.evaluation-functions%25E1%25B5%2589.html#607" class="Bound">l1ᵉ</a><a id="637" class="Symbol">}</a> <a id="639" class="Symbol">{</a><a id="640" href="foundation.evaluation-functions%25E1%25B5%2589.html#640" class="Bound">Bᵉ</a> <a id="643" class="Symbol">:</a> <a id="645" href="foundation.evaluation-functions%25E1%25B5%2589.html#625" class="Bound">Aᵉ</a> <a id="648" class="Symbol">→</a> <a id="650" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="654" href="foundation.evaluation-functions%25E1%25B5%2589.html#611" class="Bound">l2ᵉ</a><a id="657" class="Symbol">}</a> <a id="659" class="Symbol">(</a><a id="660" href="foundation.evaluation-functions%25E1%25B5%2589.html#660" class="Bound">aᵉ</a> <a id="663" class="Symbol">:</a> <a id="665" href="foundation.evaluation-functions%25E1%25B5%2589.html#625" class="Bound">Aᵉ</a><a id="667" class="Symbol">)</a>
  <a id="671" class="Keyword">where</a>

  <a id="680" href="foundation.evaluation-functions%25E1%25B5%2589.html#680" class="Function">evᵉ</a> <a id="684" class="Symbol">:</a> <a id="686" class="Symbol">((</a><a id="688" href="foundation.evaluation-functions%25E1%25B5%2589.html#688" class="Bound">xᵉ</a> <a id="691" class="Symbol">:</a> <a id="693" href="foundation.evaluation-functions%25E1%25B5%2589.html#625" class="Bound">Aᵉ</a><a id="695" class="Symbol">)</a> <a id="697" class="Symbol">→</a> <a id="699" href="foundation.evaluation-functions%25E1%25B5%2589.html#640" class="Bound">Bᵉ</a> <a id="702" href="foundation.evaluation-functions%25E1%25B5%2589.html#688" class="Bound">xᵉ</a><a id="704" class="Symbol">)</a> <a id="706" class="Symbol">→</a> <a id="708" href="foundation.evaluation-functions%25E1%25B5%2589.html#640" class="Bound">Bᵉ</a> <a id="711" href="foundation.evaluation-functions%25E1%25B5%2589.html#660" class="Bound">aᵉ</a>
  <a id="716" href="foundation.evaluation-functions%25E1%25B5%2589.html#680" class="Function">evᵉ</a> <a id="720" href="foundation.evaluation-functions%25E1%25B5%2589.html#720" class="Bound">fᵉ</a> <a id="723" class="Symbol">=</a> <a id="725" href="foundation.evaluation-functions%25E1%25B5%2589.html#720" class="Bound">fᵉ</a> <a id="728" href="foundation.evaluation-functions%25E1%25B5%2589.html#660" class="Bound">aᵉ</a>
</pre>
### The evaluation function with an explicit type family

<pre class="Agda"><a id="802" class="Keyword">module</a> <a id="809" href="foundation.evaluation-functions%25E1%25B5%2589.html#809" class="Module">_</a>
  <a id="813" class="Symbol">{</a><a id="814" href="foundation.evaluation-functions%25E1%25B5%2589.html#814" class="Bound">l1ᵉ</a> <a id="818" href="foundation.evaluation-functions%25E1%25B5%2589.html#818" class="Bound">l2ᵉ</a> <a id="822" class="Symbol">:</a> <a id="824" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="829" class="Symbol">}</a> <a id="831" class="Symbol">{</a><a id="832" href="foundation.evaluation-functions%25E1%25B5%2589.html#832" class="Bound">Aᵉ</a> <a id="835" class="Symbol">:</a> <a id="837" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="841" href="foundation.evaluation-functions%25E1%25B5%2589.html#814" class="Bound">l1ᵉ</a><a id="844" class="Symbol">}</a> <a id="846" class="Symbol">(</a><a id="847" href="foundation.evaluation-functions%25E1%25B5%2589.html#847" class="Bound">Bᵉ</a> <a id="850" class="Symbol">:</a> <a id="852" href="foundation.evaluation-functions%25E1%25B5%2589.html#832" class="Bound">Aᵉ</a> <a id="855" class="Symbol">→</a> <a id="857" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="861" href="foundation.evaluation-functions%25E1%25B5%2589.html#818" class="Bound">l2ᵉ</a><a id="864" class="Symbol">)</a> <a id="866" class="Symbol">(</a><a id="867" href="foundation.evaluation-functions%25E1%25B5%2589.html#867" class="Bound">aᵉ</a> <a id="870" class="Symbol">:</a> <a id="872" href="foundation.evaluation-functions%25E1%25B5%2589.html#832" class="Bound">Aᵉ</a><a id="874" class="Symbol">)</a>
  <a id="878" class="Keyword">where</a>

  <a id="887" href="foundation.evaluation-functions%25E1%25B5%2589.html#887" class="Function">ev-dependent-functionᵉ</a> <a id="910" class="Symbol">:</a> <a id="912" class="Symbol">((</a><a id="914" href="foundation.evaluation-functions%25E1%25B5%2589.html#914" class="Bound">xᵉ</a> <a id="917" class="Symbol">:</a> <a id="919" href="foundation.evaluation-functions%25E1%25B5%2589.html#832" class="Bound">Aᵉ</a><a id="921" class="Symbol">)</a> <a id="923" class="Symbol">→</a> <a id="925" href="foundation.evaluation-functions%25E1%25B5%2589.html#847" class="Bound">Bᵉ</a> <a id="928" href="foundation.evaluation-functions%25E1%25B5%2589.html#914" class="Bound">xᵉ</a><a id="930" class="Symbol">)</a> <a id="932" class="Symbol">→</a> <a id="934" href="foundation.evaluation-functions%25E1%25B5%2589.html#847" class="Bound">Bᵉ</a> <a id="937" href="foundation.evaluation-functions%25E1%25B5%2589.html#867" class="Bound">aᵉ</a>
  <a id="942" href="foundation.evaluation-functions%25E1%25B5%2589.html#887" class="Function">ev-dependent-functionᵉ</a> <a id="965" class="Symbol">=</a> <a id="967" href="foundation.evaluation-functions%25E1%25B5%2589.html#680" class="Function">evᵉ</a> <a id="971" href="foundation.evaluation-functions%25E1%25B5%2589.html#867" class="Bound">aᵉ</a>
</pre>
### The evaluation function for nondependent functions

<pre class="Agda"><a id="1043" class="Keyword">module</a> <a id="1050" href="foundation.evaluation-functions%25E1%25B5%2589.html#1050" class="Module">_</a>
  <a id="1054" class="Symbol">{</a><a id="1055" href="foundation.evaluation-functions%25E1%25B5%2589.html#1055" class="Bound">l1ᵉ</a> <a id="1059" href="foundation.evaluation-functions%25E1%25B5%2589.html#1059" class="Bound">l2ᵉ</a> <a id="1063" class="Symbol">:</a> <a id="1065" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1070" class="Symbol">}</a> <a id="1072" class="Symbol">{</a><a id="1073" href="foundation.evaluation-functions%25E1%25B5%2589.html#1073" class="Bound">Aᵉ</a> <a id="1076" class="Symbol">:</a> <a id="1078" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1082" href="foundation.evaluation-functions%25E1%25B5%2589.html#1055" class="Bound">l1ᵉ</a><a id="1085" class="Symbol">}</a> <a id="1087" class="Symbol">(</a><a id="1088" href="foundation.evaluation-functions%25E1%25B5%2589.html#1088" class="Bound">Bᵉ</a> <a id="1091" class="Symbol">:</a> <a id="1093" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1097" href="foundation.evaluation-functions%25E1%25B5%2589.html#1059" class="Bound">l2ᵉ</a><a id="1100" class="Symbol">)</a> <a id="1102" class="Symbol">(</a><a id="1103" href="foundation.evaluation-functions%25E1%25B5%2589.html#1103" class="Bound">aᵉ</a> <a id="1106" class="Symbol">:</a> <a id="1108" href="foundation.evaluation-functions%25E1%25B5%2589.html#1073" class="Bound">Aᵉ</a><a id="1110" class="Symbol">)</a>
  <a id="1114" class="Keyword">where</a>

  <a id="1123" href="foundation.evaluation-functions%25E1%25B5%2589.html#1123" class="Function">ev-functionᵉ</a> <a id="1136" class="Symbol">:</a> <a id="1138" class="Symbol">(</a><a id="1139" href="foundation.evaluation-functions%25E1%25B5%2589.html#1073" class="Bound">Aᵉ</a> <a id="1142" class="Symbol">→</a> <a id="1144" href="foundation.evaluation-functions%25E1%25B5%2589.html#1088" class="Bound">Bᵉ</a><a id="1146" class="Symbol">)</a> <a id="1148" class="Symbol">→</a> <a id="1150" href="foundation.evaluation-functions%25E1%25B5%2589.html#1088" class="Bound">Bᵉ</a>
  <a id="1155" href="foundation.evaluation-functions%25E1%25B5%2589.html#1123" class="Function">ev-functionᵉ</a> <a id="1168" class="Symbol">=</a> <a id="1170" href="foundation.evaluation-functions%25E1%25B5%2589.html#680" class="Function">evᵉ</a> <a id="1174" href="foundation.evaluation-functions%25E1%25B5%2589.html#1103" class="Bound">aᵉ</a>
</pre>
### The evaluation function of implicit functions

<pre class="Agda"><a id="1241" class="Keyword">module</a> <a id="1248" href="foundation.evaluation-functions%25E1%25B5%2589.html#1248" class="Module">_</a>
  <a id="1252" class="Symbol">{</a><a id="1253" href="foundation.evaluation-functions%25E1%25B5%2589.html#1253" class="Bound">l1ᵉ</a> <a id="1257" href="foundation.evaluation-functions%25E1%25B5%2589.html#1257" class="Bound">l2ᵉ</a> <a id="1261" class="Symbol">:</a> <a id="1263" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1268" class="Symbol">}</a> <a id="1270" class="Symbol">{</a><a id="1271" href="foundation.evaluation-functions%25E1%25B5%2589.html#1271" class="Bound">Aᵉ</a> <a id="1274" class="Symbol">:</a> <a id="1276" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1280" href="foundation.evaluation-functions%25E1%25B5%2589.html#1253" class="Bound">l1ᵉ</a><a id="1283" class="Symbol">}</a> <a id="1285" class="Symbol">{</a><a id="1286" href="foundation.evaluation-functions%25E1%25B5%2589.html#1286" class="Bound">Bᵉ</a> <a id="1289" class="Symbol">:</a> <a id="1291" href="foundation.evaluation-functions%25E1%25B5%2589.html#1271" class="Bound">Aᵉ</a> <a id="1294" class="Symbol">→</a> <a id="1296" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1300" href="foundation.evaluation-functions%25E1%25B5%2589.html#1257" class="Bound">l2ᵉ</a><a id="1303" class="Symbol">}</a> <a id="1305" class="Symbol">(</a><a id="1306" href="foundation.evaluation-functions%25E1%25B5%2589.html#1306" class="Bound">aᵉ</a> <a id="1309" class="Symbol">:</a> <a id="1311" href="foundation.evaluation-functions%25E1%25B5%2589.html#1271" class="Bound">Aᵉ</a><a id="1313" class="Symbol">)</a>
  <a id="1317" class="Keyword">where</a>

  <a id="1326" href="foundation.evaluation-functions%25E1%25B5%2589.html#1326" class="Function">ev-implicit-functionᵉ</a> <a id="1348" class="Symbol">:</a> <a id="1350" class="Symbol">({</a><a id="1352" href="foundation.evaluation-functions%25E1%25B5%2589.html#1352" class="Bound">xᵉ</a> <a id="1355" class="Symbol">:</a> <a id="1357" href="foundation.evaluation-functions%25E1%25B5%2589.html#1271" class="Bound">Aᵉ</a><a id="1359" class="Symbol">}</a> <a id="1361" class="Symbol">→</a> <a id="1363" href="foundation.evaluation-functions%25E1%25B5%2589.html#1286" class="Bound">Bᵉ</a> <a id="1366" href="foundation.evaluation-functions%25E1%25B5%2589.html#1352" class="Bound">xᵉ</a><a id="1368" class="Symbol">)</a> <a id="1370" class="Symbol">→</a> <a id="1372" href="foundation.evaluation-functions%25E1%25B5%2589.html#1286" class="Bound">Bᵉ</a> <a id="1375" href="foundation.evaluation-functions%25E1%25B5%2589.html#1306" class="Bound">aᵉ</a>
  <a id="1380" href="foundation.evaluation-functions%25E1%25B5%2589.html#1326" class="Function">ev-implicit-functionᵉ</a> <a id="1402" href="foundation.evaluation-functions%25E1%25B5%2589.html#1402" class="Bound">fᵉ</a> <a id="1405" class="Symbol">=</a> <a id="1407" href="foundation.evaluation-functions%25E1%25B5%2589.html#1402" class="Bound">fᵉ</a> <a id="1410" class="Symbol">{</a><a id="1411" href="foundation.evaluation-functions%25E1%25B5%2589.html#1306" class="Bound">aᵉ</a><a id="1413" class="Symbol">}</a>
</pre>
### The evaluation function of implicit functions, specified with an explicit type family

<pre class="Agda"><a id="1519" class="Keyword">module</a> <a id="1526" href="foundation.evaluation-functions%25E1%25B5%2589.html#1526" class="Module">_</a>
  <a id="1530" class="Symbol">{</a><a id="1531" href="foundation.evaluation-functions%25E1%25B5%2589.html#1531" class="Bound">l1ᵉ</a> <a id="1535" href="foundation.evaluation-functions%25E1%25B5%2589.html#1535" class="Bound">l2ᵉ</a> <a id="1539" class="Symbol">:</a> <a id="1541" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1546" class="Symbol">}</a> <a id="1548" class="Symbol">{</a><a id="1549" href="foundation.evaluation-functions%25E1%25B5%2589.html#1549" class="Bound">Aᵉ</a> <a id="1552" class="Symbol">:</a> <a id="1554" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1558" href="foundation.evaluation-functions%25E1%25B5%2589.html#1531" class="Bound">l1ᵉ</a><a id="1561" class="Symbol">}</a> <a id="1563" class="Symbol">(</a><a id="1564" href="foundation.evaluation-functions%25E1%25B5%2589.html#1564" class="Bound">Bᵉ</a> <a id="1567" class="Symbol">:</a> <a id="1569" href="foundation.evaluation-functions%25E1%25B5%2589.html#1549" class="Bound">Aᵉ</a> <a id="1572" class="Symbol">→</a> <a id="1574" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1578" href="foundation.evaluation-functions%25E1%25B5%2589.html#1535" class="Bound">l2ᵉ</a><a id="1581" class="Symbol">)</a> <a id="1583" class="Symbol">(</a><a id="1584" href="foundation.evaluation-functions%25E1%25B5%2589.html#1584" class="Bound">aᵉ</a> <a id="1587" class="Symbol">:</a> <a id="1589" href="foundation.evaluation-functions%25E1%25B5%2589.html#1549" class="Bound">Aᵉ</a><a id="1591" class="Symbol">)</a>
  <a id="1595" class="Keyword">where</a>

  <a id="1604" href="foundation.evaluation-functions%25E1%25B5%2589.html#1604" class="Function">ev-implicit-function&#39;ᵉ</a> <a id="1627" class="Symbol">:</a> <a id="1629" class="Symbol">({</a><a id="1631" href="foundation.evaluation-functions%25E1%25B5%2589.html#1631" class="Bound">xᵉ</a> <a id="1634" class="Symbol">:</a> <a id="1636" href="foundation.evaluation-functions%25E1%25B5%2589.html#1549" class="Bound">Aᵉ</a><a id="1638" class="Symbol">}</a> <a id="1640" class="Symbol">→</a> <a id="1642" href="foundation.evaluation-functions%25E1%25B5%2589.html#1564" class="Bound">Bᵉ</a> <a id="1645" href="foundation.evaluation-functions%25E1%25B5%2589.html#1631" class="Bound">xᵉ</a><a id="1647" class="Symbol">)</a> <a id="1649" class="Symbol">→</a> <a id="1651" href="foundation.evaluation-functions%25E1%25B5%2589.html#1564" class="Bound">Bᵉ</a> <a id="1654" href="foundation.evaluation-functions%25E1%25B5%2589.html#1584" class="Bound">aᵉ</a>
  <a id="1659" href="foundation.evaluation-functions%25E1%25B5%2589.html#1604" class="Function">ev-implicit-function&#39;ᵉ</a> <a id="1682" class="Symbol">=</a> <a id="1684" href="foundation.evaluation-functions%25E1%25B5%2589.html#1326" class="Function">ev-implicit-functionᵉ</a> <a id="1706" href="foundation.evaluation-functions%25E1%25B5%2589.html#1584" class="Bound">aᵉ</a>
</pre>
## See also

- The
  [action on identifications](foundation.action-on-identifications-functions.md)
  of the evaluation map is the function `a ↦ λ p → htpy-eq p a` defined in
  [Function extensionality](foundation.function-extensionality.md).