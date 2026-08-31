# GElectrical, QElectroTech, circuitikz: data types and machinery conventions

Sources (shallow clones, read-only, under the session scratchpad `refs/`): GElectrical `47082c7` (2025-12-17, `misc.PROGRAM_VER = '1'`), qelectrotech-source-mirror `899f105` + qelectrotech-elements `78b2624`, circuitikz `b882b15` (2026-07-11). Paths below are relative to `refs/<repo>/`. Snippets are verbatim, trimmed by line.

---

## 1. GElectrical

### 1.1 Identity

Python 3 / GTK 3 / cairo single-line-diagram editor for LV/MV power distribution, with pandapower as the analysis backend (power flow, time series, symmetric and line-to-ground short circuit), protection-curve coordination, and a rules engine. One process, one `ProjectModel`, N `DrawingModel` sheets, elements are Python objects with dict fields.

### 1.2 Core data types

The base element (`gelectrical/elementmodel/element.py:38-71`) is *drawing + ports + typed fields + result fields*:

```python
class ElementModel:
    def __init__(self, cordinates=(0,0), **kwargs):
        self.x = int(cordinates[0]); self.y = int(cordinates[1])
        self.database_path = None
        self.orientation = 'vertical'
        self.ports = []
        self.fields = dict()
        # State data
        self.res_fields = dict()
        self.gid = None
        self.gid_assembly = None
        # Model parameters
        self.text_model = None
        self.schem_model = None
```

A field is a uniform typed record (`gelectrical/misc.py:1234-1276`): `get_field_dict(field_type, caption, unit, value, max_chars, validation_func, selection_list, selection_image_list, decimal, status_enable, status_inactivate, status_floating, click_to_edit_message, alter_structure, alter_values_dict, tooltip)` with `field_type` in `('int','float','str','multiline_str','bool','font','graph')`. Persistence truncates each field to `{'value', 'type'}` (`misc.get_fields_trunc`, `:1278`). `misc.FieldDict`/`misc.Element` (`:924-953`) expose `e.f.<code>` (fields) and `e.r.<code>` (results) for expression evaluation.

Drawing primitives are a list-of-lists DSL in grid units (`misc.M = 8` px), `element.py:275-283`:

```python
# [['LINE',(x0,y0),(x1,y1), (d1,d2,...), <'normal'/'thick'/'thin'>],
#  ['CURVE',(x0,y0),(x1,y2),(x3,y3),(x4,y4), (d1,d2,...), ...],
#  ['ARC', (x0,y0), r, t0, t1, (d1,d2,...), ...],
#  ['CIRCLE', (x0,y0), r, True/False, (d1,d2,...), ...],
#  ['RECT', (x0,y0), w, h, True/False, (d1,d2,...), ...],
#  ['PATH', (x0,y0), True/False, (d1,d2,...), 'normal'/..., [['LINE', (dx1,dy1)], ['CURVE', ...], ['ARC', ...]]]
```

Text is a Mako-templated overlay: `text_model = [[(x,y), Expr, display, size, weight, alignment], ...]` rendered with `ExprTemplate(expr).render(**self.get_field_value_dict())` (`:483-488`); `y=None` auto-increments a line. Orientation is a single 90-degree matrix `cairo.Matrix(0,-1,1,0,0,0)` applied to both drawing and ports (`:154-170`, `:300`).

A concrete element (`elementmodel/load.py:30-101`):

```python
class Load(ElementModel):
    code = 'element_load'; name = 'Load 3ph'; group = 'Loads'
    def __init__(self, cordinates=(0,0), **kwargs):
        self.ports = [[1, 0]]
        self.fields = {'ref': self.get_field_dict('str', 'Reference', '', 'X?'),
                       'sn_kva': self.get_field_dict('float', 'Rated power', 'kVA', 1),
                       'cos_phi': self.get_field_dict('float', 'PF', '', 0.8), ...}
        self.schem_model = [['LINE',(1,0),(1,5), []], ['LINE',(0.5,5),(1.5,5), []], ...]
    def get_nodes(self, code):
        ports = tuple(tuple(x) for x in self.get_ports_global())
        p0 = code + ':0'
        return ((p0, (ports[0],)),)
    def get_power_model(self, code, mode=misc.POWER_MODEL_POWERFLOW):
        p0 = code + ':0'
        return (('load', (p0,), {'name': self.fields['ref']['value'], 'sn_mva': self.fields['sn_kva']['value']/1000, ...}),)
```

The two projections are documented contracts (`element.py:506-545`): `get_nodes` returns `(('code:p', ((x0,y0), (<page>,x1,y1), ...)), ...)` where each tuple is a set of ports that *form the same node*; `get_power_model` returns `(('model_code', ('code:p0','code:p1',...), model_dict), ...)`, i.e. a pandapower element kind, its local node names, and its kwargs. `mode` selects powerflow / line-fault / ground-fault variants (`line.py:169-213` swaps zero-sequence parameters). Protection devices additionally carry `line_protection_model` / `ground_protection_model` (`switch.py:157-166`), built from `get_line_protection_model()` which returns `(parameters, curves)` with curves as symbolic point lists over `f.In`, `d.t_m_max` (`switch.py:717-745`), evaluated by `model/protection.py:ProtectionModel`. Element catalogues bind through `self.database_path = misc.open_library('cable_iec.csv')` (`line.py:264`) and semicolon CSVs headed `item_name;item_category;...` whose remaining columns are field codes (`database/cb.csv:1`, loaded by `view/database.py:104-131`).

Special elements: `Wire` (`wire.py:37-138`) is a polyline whose first and last points are its two ports and whose single node contains both; `BusBar` exposes n_top/n_btm ports in one node (`busbar.py:74-79`); `Reference` (`reference.py:92-98`) appends its *ref string* as a coordinate-less port so cross-sheet references merge:

```python
ports = tuple(tuple(x) for x in self.get_ports_global())
ports = ports + ((self.fields['ref']['value'],),)
nodes = ((p0, ports),)
```

`DisplayElementNode` (`displayelements.py:37-59`) is the result overlay glyph, `ElementAssembly` (`elementassembly.py:37-150`) is a named group holding `children_codes`.

### 1.3 File format (.gepro)

A `.gepro` is a stored-only ZIP (`gelectrical/__init__.py:285-311`): `document.json` + `proj_drawing_page_<n>.json` + `proj_loadprofiles.json`. From `sample_files/sample.gepro`:

```json
// document.json
{"_file_version": "GELECTRICAL_FILE_REFERENCE_VER_0",
 "_files": ["proj_drawing_page_0.json", "proj_drawing_page_1.json", "proj_loadprofiles.json"],
 "proj_drawing_names": ["proj_drawing_page_0.json", "proj_drawing_page_1.json"],
 "proj_fields": {"Information": {"project_name": {"value": "PROJECT", "type": "str"}, ...},
                 "Simulation": {"power_flow_3ph": {"value": true, "type": "bool"}, ...}}}
// proj_drawing_page_0.json
["DrawingModel", {"fields": {"name": {"value": "Main scheme", "type": "str"}, "page_size": {"value": "A3", "type": "str"}, ...},
  "elements": [
   {"code": "element_load", "x": 280.0, "y": 672.0, "orientation": "vertical", "ports": [[1, 0]],
    "fields": {"ref": {"value": "X1", "type": "str"}, "sn_kva": {"value": 100.0, "type": "float"},
               "load_profile": {"value": "ccea7d6b-d35c-45c9-bd7a-1560e243a484", "type": "graph"}}},
   {"code": "element_wire", "x": 160.0, "y": 512.0, "orientation": "vertical", "ports": [[0.0, 0.0], [0.0, 4.0]],
    "fields": {"text1": {"value": "", "type": "str"}}, "points": [[160.0, 512.0], [160.0, 544.0]]}]}]
```

Elements are re-instantiated by `code` from the registry `program_state['element_models']` (`__init__.py:925-944`); `set_model` copies only values of known field codes (`element.py:191-204`), so the schema lives in code.

### 1.4 Machinery

**Port coincidence -> nodes -> graph** (`model/networkmodel.py:93-188`). Every element contributes node tuples; each port becomes a key `(page, x, y)` (or a bare string for reference ports) in `port_mapping`; multi-port tuples are unioned by connected components over a networkx graph (`combine_connected_nodes`, `:576-594`); gnodes are then renumbered densely:

```python
for (p0, ports) in nodes:
    gnode = cur_gnode_num
    for port in ports:
        map_port = (k1, *port) if len(port) == 2 else port
        self.port_mapping[map_port] = gnode
        if len(ports) > 1: duplicate_ports.add(map_port)
...
duplicate_ports_list_comb = self.combine_connected_nodes(duplicate_ports_list)
subs_dict = {gnode:new_gnode for new_gnode, gnode in enumerate(sorted(gnodes), start=1)}
```

Wires therefore are not edges: a wire is an element whose two ports lie in one node, and node identity is purely geometric coincidence of integer pixel coordinates on a 16 px grid (`DrawingModel.get_grid_point`, `model/drawing.py:287`). `build_graph_model` (`:220-276`) makes an `nx.Graph` with gnodes as vertices and elements as edges keyed by `(page, slno)`; one-port supplies get a synthetic source vertex, one-port loads a sink vertex, three-port transformers two edges. `get_upstream_element` / `get_downstream_element` (`:376-477`) walk `nx.all_simple_paths` towards sources or sinks; `graph_with_status` drops open switches and out-of-service lines.

**Analysis binding** (`model/pandapower.py:83-240`): `get_node(local_node)` lazily creates a pandapower bus per gnode; each `(kind, local_nodes, kwargs)` tuple dispatches to `pp.create_<kind>` (`switch`, `ext_grid`, `trafo`, `trafo3w`, `gen`, `sgen`, `storage`, `impedance`, `line`, `dcline`, ...). Results flow back as typed fields (`:719-739`): `node_result['vm_pu'] = misc.get_field_dict('str', 'V', 'pu < deg', ...)`, then `update_results` (`:1728-1770`) copies `element_results[e_code]` into `element.res_fields`; `ProjectModel.setup_base_model` (`model/project.py:375-396`) inserts one `DisplayElementNode` per (page, gnode) into the drawing as an undoable group, so results are *elements in the drawing* rather than a separate layer.

**Rules check** (`model/rulescheck.py:68-138`): each rule is `(check_expression, (codes, match_expr, 'all'|'all_ifexist'|'any'|'any_ifexist'), *args)`, args being `('self', expr)`, `('upstream', codes, expr)`, `('downstream_node', expr)`, `('constant', c)`, `('match', codes, cond, expr)`; expressions are `eval`ed with `e`, `sr`, `ss` bound (`:172-270`), e.g.

```python
'Breaker short circuit current < Fault level': ("arg1 > arg2",
                    (misc.PROTECTION_ELEMENT_CODES, 'True', 'all'),
                    ('self', 'e.f.Isc*1000'),
                    ('downstream_node', 'max(e.r.ikss_ka_3ph_max, e.r.ikss_ka_1ph_max)*1000')),
```

**Numbering and cross-reference**: `renumber_elements` (`project.py:519+`) sorts by `np.lexsort((x, y))` (`networkmodel.py:318-331`) and counts per prefix (`X?`, `Q?`, `B?`); `link_references` (`project.py:722-754`) assigns one `CR<n>` code to a set of `Reference` elements across sheets and writes the other sheet numbers into each `sheet` field; the node merge above then makes them electrically one node.

### 1.5 UI anatomy

`interface/mainwindow.glade`: `GtkApplicationWindow window_main` with `GtkHeaderBar`, a `GtkPaned paned1` holding `GtkStack stack_toolbar_left` (`insert_element_listbox` with search `draw_element_searchbox`, grouped by `ElementModel.group`) and `GtkNotebook drawing_notebook` (one `DrawingView` per sheet, `view/drawing.py:43`), a right `GtkNotebook properties_notebook` with `draw_properties_listbox` / `draw_result_listbox` / `draw_diagnostic_listbox` (`FieldView` and `MessageView`, wired at `__init__.py:1041-1060`), and `GtkToolbar insert_toolbar` with `toolbutton_draw_{wire,group,linkref,renumber,rulescheck,analyse,protectioncord,editloadprofiles,export}`. Modes are `MODE_DEFAULT/SELECTION/INSERT/ADD_WIRE` (`misc.py:123-126`); left-click on a port starts a wire (`view/drawing.py:349-353`), double/middle click ends it on a snapped port (`:328-338`). Undo is a command stack (`gelectrical/undo.py`, `@undoable` on `DrawingModel` mutators).

---

## 2. QElectroTech

### 2.1 Identity

C++/Qt multi-folio electrical schematic editor (`sources/`), documentary rather than simulating: elements instantiated from an XML library, conductors between terminals, folio grids with title blocks, master/slave and folio-report cross-references, formula-driven autonumbering. Caveat: `sources/factory/` (`ElementFactory`, `ElementPictureFactory`) and `sources/autoNumbering/` (`NumerotationContext`) were not in the sparse checkout; findings cite the serializers and readers that are present.

### 2.2 Core data types

Element XML, verbatim (`qet-elements/10_electric/10_allpole/100_folio_referencing/02going_arrow.elmt`, 31 lines, names trimmed):

```xml
<definition version="0.80" type="element" link_type="next_report" width="30" height="20" hotspot_x="23" hotspot_y="10">
    <uuid uuid="{5ec3a096-68e7-9b2c-d1b8-b960176e2512}"/>
    <names>
        <name lang="en">Going arrow</name>
        <name lang="fr">Folio suivant</name>
    </names>
    <informations>Author: The QElectroTech team
License: see http://qelectrotech.org/wiki/doc/elements_license</informations>
    <description>
        <polygon x1="-9" y1="-4" x2="-9" y2="4" x3="2" y3="0" antialias="true" style="line-style:normal;line-weight:normal;filling:none;color:black"/>
        <line x1="-9" y1="0" x2="-12" y2="0" end1="none" end2="none" length1="1.5" length2="1.5" style="line-style:normal;line-weight:normal;filling:none;color:black" antialias="false"/>
        <dynamic_text x="6" y="-11.5" z="3" text_width="-1" Halignment="AlignLeft" Valignment="AlignTop" frame="false" rotation="0" text_from="ElementInfo" uuid="{93888a84-3ffd-438d-acef-5396acba0750}" font="Liberation Sans,9,-1,5,50,0,0,0,0,0,Regular">
            <text></text>
            <info_name>label</info_name>
        </dynamic_text>
        <terminal uuid="{975add6f-4ba5-44af-a4c0-e1f1c2024601}" name="1" x="-13" y="0" orientation="w" type="Generic"/>
    </description>
</definition>
```

Primitive tags as written by the editor parts (`sources/editor/graphicspart/`): `line x1 y1 x2 y2 end1 length1 end2 length2` (partline.cpp:118-126); `rect x y width height rx ry` (partrectangle.cpp:85-99); `circle diameter x y` / `ellipse width height x y` (partellipse.cpp:86-102); `polygon x1 y1 ... xN yN [closed="false"]` (partpolygon.cpp:118-130); `arc x y width height start angle` (partarc.cpp:100-116); `text x y text font rotation color Halignment Valignment` (parttext.cpp:161-183); `dynamic_text` with children `<text> <info_name> <composite_text> <color>` (partdynamictextfield.cpp:136-191); `terminal x y uuid name orientation type` (`properties/terminaldata.cpp:107-122`). Every graphic carries one CSS-like style string (`customelementgraphicpart.cpp:325-510`):

```cpp
css_like_styles += "line-style:";   // normal | dashed | dotted | dashdotted
css_like_styles += ";line-weight:"; // none | thin | normal | hight | eleve
css_like_styles += ";filling:";     // none | black | white | green | red | blue | gray | ...
css_like_styles += ";color:";       // black | white | green | red | blue | gray | ...
qde.setAttribute("style", css_like_styles);
qde.setAttribute("antialias", _antialiased ? "true" : "false");
```

Kind-specific semantics live in `<kindInformations>`: a master coil has `<kindInformation name="type">coil</kindInformation>` (`310_relays_contactors_contacts/01_coils/bobine3.elmt:21-23`), a slave contact `type=simple state=NO number=1` (`03_contacts/contact_gv_no.elmt:13-17`), a terminal `type=generic function=generic` (`110_network_supplies/ground1.elmt:22-25`). The runtime parses the root and the terminals itself and delegates graphics to the picture factory (`sources/qetgraphicsitem/element.cpp:411-573`):

```cpp
if (!QET::attributeIsAnInteger(xml_def_elmt, QStringLiteral("width"), &w) || ... "height" ... "hotspot_x" ... "hotspot_y" ...) { if (state) *state = 5; ... }
setSize(w, h); setHotspot(QPoint(hot_x, hot_y));
m_data.fromXml(xml_def_elmt);
m_kind_informations.fromXml(xml_def_elmt.firstChildElement(QStringLiteral("kindInformations")), QStringLiteral("kindInformation"));
...
bool Element::parseElement(const QDomElement &dom) {
	if      (dom.tagName() == QLatin1String("terminal"))     return(parseTerminal(dom));
	else if (dom.tagName() == QLatin1String("input"))        return(parseInput(dom));
	else if (dom.tagName() == QLatin1String("dynamic_text")) return(parseDynamicText(dom));
	else return(true); }
```

Link kinds (`element.h:55-64`; strings `simple next_report previous_report master slave terminal thumbnail` at `properties/elementdata.cpp:666-679`):

```cpp
enum kind { Simple = 1, NextReport = 2, PreviousReport = 4, AllReport = 6,
            Master = 8, Slave = 16, Terminale = 32, Thumbnail = 64, ConductorDefinition = 128};
```

`ElementData` (`properties/elementdata.h`) refines them: `enum MasterType { Coil, Protection, Commutator, PLC }; enum SlaveType { SSimple, Power, DelayOn, DelayOff, delayOnOff, PLCSlave }; enum SlaveState { NO, NC, SW, Other }; enum TerminalType { TTGeneric, TTFuse, TTSectional, TTDiode, TTGround }; enum TerminalFunction { TFGeneric, TFPhase, TFNeutral }`, plus `DiagramContext m_informations; NamesList m_names_list`.

Element state (`element.h:245-282`): `QList<Element*> connected_elements; QUuid m_uuid; kind m_link_type; DiagramContext m_kind_informations; autonum::sequentialNumbers m_autoNum_seq; ElementsLocation m_location; QList<Terminal*> m_terminals; ElementData m_data; QPoint hotspot_coord; QString m_prefix; QList<DynamicElementTextItem*> m_dynamic_text_list;` with `orientation()` = rotation/90. `Terminal` (`terminal.h:36-151`) owns `TerminalData* d` (`m_uuid m_name m_pos m_orientation m_type`; `enum Type { Generic, Inner, Outer, No, Nc, Common }`, `properties/terminaldata.h:43-96`) and `QList<Conductor*> m_conductors_list`; `canBeLinkedTo(other)` is `other != this && !isLinkedTo(other)` (`terminal.cpp:691-697`). `Conductor` (`conductor.h:43-237`): `Terminal *terminal1, *terminal2; ConductorProperties m_properties; ConductorSegment *segments; ConductorProfilesGroup conductor_profiles; autonum::sequentialNumbers m_autoNum_seq; QUuid m_uuid; ConductorTextItem *m_text_item`. `ConductorProperties` (`conductorproperties.h:79-121`): `enum ConductorType { Single, Multi }; QColor color, m_color_2; QString text, m_function, m_tension_protocol, m_wire_color, m_wire_section, m_formula, m_bus, m_cable; SingleLineProperties singleLineProperties` (`hasGround hasNeutral phases isPen()`). `Diagram : QGraphicsScene` (`diagram.h:53-302`): `BorderTitleBlock border_and_titleblock; static int xGrid, yGrid; QString m_conductors_autonum_name; QUuid m_uuid; folioIndex(); toXml(); fromXml()`. `BorderTitleBlock` (`bordertitleblock.h:248-287`) holds `columns_count_ columns_width_ rows_count_ rows_height_ folio_index_ folio_total_ additional_fields_` and derives the folio-grid address (`bordertitleblock.cpp:864-878`):

```cpp
int row_number    = int(ceil(relative_pos.x() / columnsWidth()));
int column_number = int(ceil(relative_pos.y() / rowsHeight()));
QString letter = "A"; for (int i = 1 ; i < column_number ; ++ i) letter = incrementLetters(letter);
return(DiagramPosition(letter, row_number));
```

`QETProject` (`qetproject.h:76-336`): `QList<Diagram*> m_diagrams_list; XmlElementCollection *m_elements_collection; BorderProperties default_border_properties_; ConductorProperties default_conductor_properties_; TitleBlockProperties default_titleblock_properties_; QHash<QString,XRefProperties> m_default_xref_properties; QHash<QString,NumerotationContext> m_conductor_autonum, m_folio_autonum, m_element_autonum; QUndoStack *m_undo_stack; QUuid m_uuid`. `ElementsLocation` (`ElementsCollection/elementslocation.cpp:236-310`) resolves `common://`, `company://`, `custom://`, `macros://` to directories and `embed://` to the project's embedded XML collection (`isFileSystem() isProject() xml() uuid()`).

### 2.3 File format (.qet)

`examples/741.qet:1-25` plus a modern element and conductor from `examples/photovoltaique.qet`, trimmed:

```xml
<project title="Operational amplifier uA741" version="0.90">
  <properties><property show="1" name="saveddate-us">2021-04-17</property>...</properties>
  <newdiagrams>
    <border colsize="60" rows="8" rowsize="80" cols="17" displayrows="true" displaycols="true"/>
    <inset displayAt="bottom" title="..." author="pawel32640" folio="%id/%total" date="20100921" .../>
    <conductors condsize="1" type="multi" formula="" num="" .../>
    <report label="%f-%l%c"/>
    <xrefs><xref type="coil" displayhas="contacts" snapto="bottom" master_label="%f-%l%c" slave_label="(%f-%l%c)" offset="40" .../>...</xrefs>
    <conductors_autonums current_autonum="" freeze_new_conductors="false"/>
  </newdiagrams>
  <diagram order="1" title="..." rows="8" rowsize="80" cols="17" colsize="60" displaycols="true" displayrows="true" folio="%id/%total" height="660" freezeNewConductor="false" freezeNewElement="false" ...>
    <elements>
      <element uuid="{fb0256f2-...}" type="embed://import/10_electric/10_allpole/200_fuses_protective_gears/90_overvoltage_protections/parafoudre.elmt" x="330" y="260" z="10" orientation="0" prefix="F" freezeLabel="false">
        <terminals><terminal id="0" orientation="0" x="0" y="-17"/><terminal id="1" orientation="2" x="0" y="17"/></terminals>
        <elementInformations><elementInformation show="1" name="label"></elementInformation></elementInformations>
        <dynamic_texts><dynamic_elmt_text uuid="{e28913d6-...}" text_from="ElementInfo" x="-20" y="10" ...><text></text><info_name>label</info_name></dynamic_elmt_text></dynamic_texts>
      </element>
    </elements>
    <conductors>
      <conductor terminal1="{3c0b22bb-...}" element1="{4d390f01-...}" terminal2="{f2e49ff6-...}" element2="{3f385397-...}" type="multi" num="" formula="" color="#00ff00" x="-50" y="360" freezeLabel="false" ...>
        <sequentialNumbers/>
      </conductor>
    </conductors>
  </diagram>
  <collection><category name="import">...<element name="zacisk.elmt"><definition type="element" .../></element>...</category></collection>
</project>
```

Linked elements add `<links_uuids><link_uuid uuid="{...}"/></links_uuids>` (`element.cpp:912-1030`); `Diagram::toXml` also writes `<elementautonumfoliosequentials>` / `<conductorautonumfoliosequentials>` (`sequf_ seqtf_ seqhf_`). Note the diagram-side `<terminal id x y orientation(int)>` differs from the library-side `<terminal uuid name orientation(letter) type>`; both are legitimate serializers of the same terminal.

### 2.4 Machinery

The electrical potential is computed on demand by DFS over terminal-conductor adjacency (`conductor.cpp:1707-1745 relatedPotentialConductors`), bridged through elements by `terminal.cpp:963-987`:

```cpp
QList<Terminal *> relatedPotentialTerminal (const Terminal *terminal, const bool all_diagram)
{
	if (all_diagram && terminal -> parentElement() -> linkType() & Element::AllReport)
	{
		QList <Element *> elmt_list = terminal -> parentElement() -> linkedElements();
		if (!elmt_list.isEmpty()) { return (elmt_list.first()->terminals()); }
	}
	else if (terminal -> parentElement() -> linkType() & Element::Terminale)
	{
		if (terminal->parentElement()->elementInformations().value(QStringLiteral("potential_isolating")).toString() == QLatin1String("true")) {
			return QList<Terminal *>();
		}
		QList <Terminal *> terminals = terminal->parentElement()->terminals();
		terminals.removeAll(const_cast<Terminal *>(terminal));
		return terminals;
	}
	return QList<Terminal *>();
}
```

So a potential crosses folios only through a linked next/previous report pair and passes through a terminal-kind element unless `potential_isolating="true"`. `ConductorAutoNumerotation::numerate` (`conductorautonumerotation.cpp:57-63, 176-261`) copies properties and `sequenceNum` from the existing potential, else derives `m_formula = autonum::numerotationContextToFormula(project()->conductorAutoNum(diagram->conductorsAutonumName()))` and advances `NumerotationContextCommands(context, diagram).next()`. Formula variables visible in the checkout: `%sequf_ %seqtf_ %seqhf_` (unit/ten/hundred per folio), `%id`/`%f` folio index, `%F` folio label, `%l` row letter, `%c` column number, `%M %LM` (`diagram.cpp:1975-1995`, `dynamicelementtextitem.cpp:965-985`, `ui/potentialselectordialog.cpp:478-487`).

Cross-reference: `MasterElement::linkToElement` accepts any number of `Slave`s and instantiates a `CrossRefItem`; `SlaveElement::linkToElement` (`slaveelement.cpp:51-61`) accepts one `Master` after `unlinkAllElements()`; `ReportElement` pairs one `next_report` with one `previous_report` (`reportelement.cpp:27-30`). `CrossRefItem` (`crossrefitem.h:46-150`) renders a cross or a contact table from each slave's `kindInformations()["number"|"state"|"type"]` and its `DiagramPosition`, formatted by `XRefProperties` (`master_label="%f-%l%c"`, `slave_label="(%f-%l%c)"`, `enum DisplayHas { Cross, Contacts }; enum SnapTo { Bottom, Label }`, `properties/xrefproperties.h:35-96`). Title blocks are grids of `TitleBlockCell` (`EmptyCell TextCell LogoCell`) whose text substitutes `%{key}` / `%key` from a `DiagramContext` (`titleblocktemplate.cpp interpreteVariables`) with keys `author date title filename plant locmach indexrev version folio folio-id folio-total previous-folio-num next-folio-num` (`bordertitleblock.cpp:905-996`); `titleblocks/default.titleblock` reads `<titleblocktemplate name="default"><information/><logos/><grid cols="t22%;r100%;t22%;" rows="25;25;"><field row="0" col="0" name="author" displaylabel="true" align="left"><value><translation lang="en">%author</translation></value><label>...</label></field>...`.

### 2.5 UI anatomy

`QETDiagramEditor` (`qetdiagrameditor.h:168-262`, `.cpp:169-269`): `QMdiArea m_workspace` of `DiagramView`s (tabbed or windowed), docks "Projets" (`ProjectView` tree), "Collections" (`ElementsCollectionWidget`), "Annulations" (`QUndoGroup`), `DiagramPropertiesEditorDockWidget`, `AutoNumberingDockWidget`; toolbars `main view diagram m_add_item m_depth`; add-item actions text, image, PDF, line, rectangle, ellipse, polyline, terminal-strip plan; `m_auto_conductor`, `m_add_nomenclature`, `m_project_export_conductor_num`. The element editor (`editor/elementscene.h:45-98`, `enum Behavior { Normal, PasteArea, AddPart }`) edits one `.elmt`: `ElementData m_element_data`, parts `PartLine PartRectangle PartEllipse PartPolygon PartArc PartText PartDynamicTextField PartTerminal PartPlcTable` implementing `CustomElementPart::{fromXml, toXml, setProperty, property, sceneGeometricRect, handleUserTransformation}` (`customelementpart.h:40-121`), a `StyleEditor` for the four style properties, and hotspot/size written by `ElementScene::toXml`.

---

## 3. circuitikz

### 3.1 Identity

A TikZ/pgf library (`tex/circuitikz.sty`, bodies `tex/pgfcirc*.tex`): components are pgf *shapes*; a bipole is used either along a `to[...]` path or as a `node[...]`. All keys live under `/tikz/circuitikz` (`tex/pgfcirc.defines.tex:30-36`):

```tex
\def\circuitikzbasekey{/tikz/circuitikz}
\def\circuitikzset{\expandafter\pgfqkeys\expandafter{\circuitikzbasekey}}
\let\ctikzset\circuitikzset
\def\ctikzvalof#1{\pgfkeysvalueof{\circuitikzbasekey/#1}}
\pgfkeys{\circuitikzbasekey/.search also={/tikz}}
```

### 3.2 Core data types

The bipole constructor (`pgfcirc.defines.tex:714-734`) takes a *class* (for `<class>/scale` and `<class>/thickness` styling), extra anchors, lower extent, name, upper extent, width, drawing code:

```tex
% #1 - scale factor   (actually the class: resistors, capacitors, ...)
% #2 - additional anchors
% #3 - lower y-size of the bipole (from the center).
% #4 - #shape is the name of the shape
% #5 - upper y-size of the bipole (from the center)
% #6 - width of the bipole
% #7 - macros drawing the bipole
\long\def\pgfcircdeclarebipolescaled#1#2#3#4#5#6#7{
    \pgfdeclareshape{#4shape}{
        \savedmacro{\ctikzclass}{\edef\ctikzclass{#1}}
        \savedanchor{\northeast}{ ... \pgf@y=#5\pgf@circ@scaled@Rlen \pgf@y=.5\pgf@y \pgf@x=#6\pgf@circ@scaled@Rlen \pgf@x=.5\pgf@x }
        \savedanchor{\southwest}{ ... \pgf@y=-#3\pgf@circ@scaled@Rlen ... }
        \anchor{center}{\pgfpointorigin}
        \anchor{left}{\southwest\pgf@y=0cm } \anchor{right}{\northeast\pgf@y=0cm }
        \anchor{a}{\northeast\pgf@y=0cm } \anchor{b}{\southwest\pgf@y=0cm }
        \anchor{north}{\northeast\pgf@x=0cm } \anchor{south}{\southwest\pgf@x=0cm }
        \anchor{text}{\textanchor}
        \anchorborder{ ... \pgfpointborderrectangle{...}{\northeastborder} ... }
        #2%
        \pgf@circ@draw@component{
            \northeast \pgf@circ@res@up = \pgf@y \pgf@circ@res@left = -\pgf@x \pgf@circ@res@right = \pgf@x
            \southwest \pgf@circ@res@down = \pgf@y
            #7%
        }}}
```

All extents are multiples of `\pgf@circ@Rlen` = `bipoles/length` (`1.4cm`, `:50-72`) times `<class>/scale`; the border anchor is the box stretched by `bipoles/border margin=1.1` (`:1035`). Concrete instance (`pgfcircbipoles.tex:699-712`, defaults `:61-62`):

```tex
\ctikzset{bipoles/resistor/height/.initial=.3}
\ctikzset{bipoles/resistor/width/.initial=.8}
\pgfcircdeclarebipolescaled{resistors}
{\savedmacro{\zigs}{\edef\zigs{\ctikzvalof{resistors/zigs}}}}
{\ctikzvalof{bipoles/resistor/height}}{resistor}{\ctikzvalof{bipoles/resistor/height}}{\ctikzvalof{bipoles/resistor/width}}
{ \pgf@circ@setlinewidth{bipoles}{\pgfstartlinewidth} ... \pgf@circ@zigzag{1} }
```

Node-style shapes are hand-declared with named anchors, e.g. op amp (`pgfcirctripoles.tex:6354-6445`, keys `:6216-6221` `tripoles/op amp/{width=1.7, port width=.7, height=1.4, input height=.5, up pos=.45}`):

```tex
\pgfdeclareshape{op amp}{
    \savedmacro{\ctikzclass}{\edef\ctikzclass{amplifiers}}
    \savedanchor\inOne{ ... \pgf@y=\ctikzvalof{tripoles/op amp/input height}\pgf@y ... \ifpgf@circuit@oa@iplusup\pgf@y=-\pgf@y\fi }
    \anchor{-}{ \inOne }
    \anchor{+}{ \inOne \pgf@y=-\pgf@y }
    \anchor{up}{ \up }  \anchor{down}{ \up \pgf@y=-\pgf@y }
    \anchor{out}{ \northwest \pgf@y=0pt \pgf@x=-\pgf@x }
```

Transistors come from `\pgfcircdeclaretransistor` (`pgfcirctripoles.tex:3642`) with anchors `B/base/G/gate`, `C/D`, `E/S` computed from `tripoles/<name>/curr direction` (`:3878-3985`); transformers from `\pgfcircdeclarequadpole` (`pgfcircquadpoles.tex:75-145`) with `A1 A2 B1 B2`, `inner dot A1`, and sub-nodes `T-L1`, `T-L2`; chips generate `pin N` anchors on demand (`pgfcircmultipoles.tex:134-141`, `:666-675`, keys `num pins`, `hide numbers`, `external pins width`); `muxdemux def={Lh, Rh, w, NL, NR, NB, NT}` (`:1151-1174`) yields `lpin i / rpin i / bpin i / tpin i`. Grounds are a monopole factory `\pgf@circ@declareground{name}{width}{depth}{code}` (`pgfcircmonopoles.tex:57-94`) whose `north/left/right/center` all sit at the origin; `vcc`/`vee` are hand-written (`:270-332`).

### 3.3 Grammar

Path-style: `\draw (a) to[<kind>[=<label>], l=|l_=|l^=, a=, v=|v<=|v>=|v_=|v^=, i=|i_=|i^=|i<=|i>=|i>^=, f=|f<=|f>=, name=, mirror, invert, *-*|o-o|-*|*-|d-d, bipoles/length=...] (b);`. `R` is `\pgfcirc@style@to@style{resistor}{R}` (`pgfcircbipoles.tex:883`), and `l` is the argument key: `to[R=$R_1$]` = `to[resistor, l=$R_1$]`. Node-style: `\node[op amp] (A) at (0,0) {};` then `(A.+) (A.-) (A.out) (A.up) (A.down)`; any bipole is also `node[resistorshape]` with `.left/.right/.center/.north/.south/.text/.n/.s/.a/.b`. Direction suffixes are generated (`pgfcircvoltage.tex:25-46`):

```tex
\def\ctikzactivatevoltagedirections#1{%
    \ctikzset{#1^>/.style = {#1={##1}, ...voltage/direction = forward, ...voltage/position = above }}
    \ctikzset{#1_</.style = {#1={##1}, ...direction = backward, ...position = below }}
    \ctikzset{#1_/.style = {#1={##1}, \circuitikzbasekey/bipole/voltage/position = below} }
    \ctikzset{#1>/.style = {#1={##1}, \circuitikzbasekey/bipole/voltage/direction = forward} }
}
\ctikzactivatevoltagedirections{v}
```

(currents add `x position = before|after`, `pgfcirccurrent.tex:26-77`; flows mirror this, `pgfcircflow.tex:27-73`). A minimal RC loop, composed from the manual's verified fragments (`doc/circuitikzmanual.tex:545-552`, `:9081-9115` `to[R=$R_1$, i=$i_1$, v=$v_1$]`):

```tex
\begin{circuitikz}[american]
  \draw (0,0) to[V, v=$V_0$] (0,3)
        to[R=$R$, i=$i$] (3,3)
        to[C=$C$, v=$v_C$] (3,0) -- (0,0);
\end{circuitikz}
```

### 3.4 Machinery

The `to` path (`pgfcircpath.tex:180-268`) names the component (random if `name=` absent), measures the start-to-end angle, drops the shape node at the midpoint rotated by that angle with `yscale=mirror value`, `xscale=invert value`, draws the two leads to `.left`/`.right`, then emits decorations:

```tex
    coordinate (\ctikzvalof{bipole/name}start) at (\tikztostart)
    coordinate (\ctikzvalof{bipole/name}end) at (\tikztotarget)
    \pgfextra{ \pgfmathanglebetweenpoints{...start}{...end} \edef\pgf@circ@direction{\pgfmathresult} }
    node[#3#1, rotate=\pgf@circ@direction, yscale=\ctikzvalof{mirror value}, xscale=\ctikzvalof{invert value}]
        (\ctikzvalof{bipole/name}) at ($(\tikztostart) ! .5 ! (\tikztotarget)$) {#2}
    ... -- (pgfcirc@anchorstartnode)
    \drawpoles
    \pgf@circ@ifkeyempty{bipole/label/name}\else\pgf@circ@drawlabels{label}\fi
    {\pgfcirc@if@has@v{\pgf@circ@drawvoltage}{}}%
    {\pgfcirc@if@has@i{\pgf@circ@drawcurrent}{}}%
    {\pgfcirc@if@has@f{\pgf@circ@drawflow}{}}%
    (pgfcirc@anchorendnode)  -- (\tikztotarget)
```

Label placement is local-frame (`pgfcirclabel.tex:113-160`): take `direction - 90`, add 180 for `l_`, add 180 again if inverted or mirrored, and use that angle as the *border anchor* of the shape (`(\ctikzvalof{bipole/name}.\pgf@circ@temp) coordinate (pgfcirc@labelcoor)`); `label/align = straight|rotate|smart` then chooses upright vs rotated text. Voltages place `pgfcirc@Vfrom` at `(\tikztostart)!distance from node!(anchorstartnode)` and bulge by `voltage/bump b` (`pgfcircvoltage.tex:134`), selecting American arrows / European curved / `straight voltages` by `\ctikzset{voltage=american|european|straight|raised}` (`pgfcirc.defines.tex:1200-1232`) and sign convention by `voltage dir=old|noold|RP|EF` (`:936-945`). Currents put a `currarrow` node at `(Ifrom)!current/distance!(Ito)` on the lead before or after the body (`pgfcirccurrent.tex:118-224`). Pole decorations are `bipole/nodes/left|right = circ|ocirc|diamondpole|none` set by the `*-*` family (`pgfcircpath.tex:334-361`).

Style is a key hierarchy: `\tikzset{american/.style={american currents, american voltages, american resistors, american inductors, american ports, ...}}` (`pgfcirc.defines.tex:1185-1187`), per-class `resistors/scale`, `capacitors/thickness`, `bipoles/thickness=2` (`:1034-1039`, `:1061-1179`), loadable style files `\ctikzloadstyle{romano}` = one `\tikzset{romano circuit style/.style={american, cute inductors, \circuitikzbasekey/.cd, resistors/scale=0.8, ...}}` (`tex/ctikzstyle-romano.tex:4-32`).

Subcircuits (`pgfcircutils.tex:107-125`): `\ctikzsubcircuitdef{name}{anchor list}{body}` defines `\name{inst}{anchor}`; the body must define `coordinate(#1-<anchor>)` for every anchor; `\ctikzsubcircuitactivate{name}` draws it once in a scratch box and `\xdef`s the offset from each anchor to the reference so an instance can be dropped *by any anchor*:

```tex
\pgfutil@protected\def\ctikzsubcircuitdef#1#2#3{%
    \expandafter\gdef\csname #1@setanchors\endcsname{%
        \setbox\ctikz@scratchbox=\hbox{\tikzpicture
        \draw (0,0) \csname#1\endcsname{T-#1}{};
        \foreach [count=\i] \anchor in {#2}
        \draw (0,{2-\i/2}) let \p1 = ($(T-#1-subckt@reference)-(T-#1-\anchor)$) in
            node[right]{\anchor: \x1,\y1 \expandafter\xdef\csname #1@Anchor\anchor\endcsname{++(\x1,\y1)}};
        \endtikzpicture}}%
    \expandafter\gdef\csname#1\endcsname##1##2{%
        \csname #1@Anchor##2\endcsname coordinate(##1-subckt@reference)#3%
    }}
```

Manual usage (`doc/circuitikzmanual.tex:1860-1917`): `\ctikzsubcircuitdef{optovishay}{in 1, out 1, in 2, out 2, center}{ coordinate(#1-center) ... (#1-center) ++(-1.2,0.8) coordinate (#1-in 1) ... }`, then `\draw (0,0) \optovishay{one}{}; \draw (one-out 1) -- ++(1,0) \optovishay{two}{in 1};`.

### 3.5 UI anatomy

None; the "UI" is the key grammar and the manual's order (`circuitikzmanual.tex`: Path-style `:1249`, Anchors `:1265`, Node-style `:1542`, Styling `:1630`, Subcircuits `:1841`; catalogue: Grounds `:2112`, Resistive `:2222`, Capacitors/inductors `:2459`, Diodes `:2672`, Sources `:2903`, Instruments `:3354`, Mechanical `:3694`, Transistors `:4799`, Transformers `:6240`, Amplifiers `:6598`, Switches `:6944`, Logic gates `:7426` (`logic ports=american|european|ieee`, anchors `in 1`, `in 2`, `out`), Mux/demux `:8328`, Chips `:8809`, Labels/voltages/currents `:9077`, Defining components `:11327`).

## 4. Abstractions to lift for a Lean-based mathematics CAD

1. **Element = glyph + terminals + typed record + projections.** All three separate drawing (`schem_model`, `<description>`, shape body), connection points (`ports`, `<terminal>`, anchors) and semantics (`fields`, `<kindInformations>`, pgf keys); GElectrical adds explicit projections `get_nodes` and `get_power_model`. A mathematical object should be a glyph with named anchors, a typed record, and a projection to the checker's term.
2. **Port coincidence derives nodes; nodes derive the analysis graph.** GElectrical unions coincident `(page,x,y)` ports by connected components and only then builds the networkx graph; QET derives potentials by DFS at query time. Node identity is never stored. For proofs: shared hypotheses or shared terms are one node by coincidence of anchors, and the dependency graph is derived.
3. **A wire is an element whose two ports form one node, not an edge.** GElectrical `Wire.get_nodes` returns both endpoints in one tuple; QET's `Conductor` is an object between two terminal uuids with its own properties. Choose per layer whether connection is identity glue or a first-class carrier of data.
4. **Path-style vs node-style.** A component is either a decorated edge placed at the midpoint of a `to` path and rotated to it, or a vertex with named anchors (`op amp.+`, `npn.B`, `dipchip.pin 3`); circuitikz lets one shape be both (`node[resistorshape]`). A lemma applied along an arrow vs. a definition sitting at a vertex.
5. **Annotations are positioned in the component's local frame.** circuitikz labels sit on the border anchor at `direction +- 90`, voltages at `start!d!anchorstart`, currents at `Ifrom!d!Ito`; QET dynamic texts are offsets from the hotspot. Placement is a function of the frame, so rotation, mirror and invert are free.
6. **Typed, oriented decorations on edges.** `v`, `i`, `f` with the `^ _ < >` suffix grammar generated by one macro (`\ctikzactivatevoltagedirections{v}`) and convention switches (`voltage=american|european|straight`, `voltage dir=RP|EF`). Directional annotations (inequality sense, transport direction, variance) should be typed decorations with orientation relative to the edge, rendered by convention.
7. **Link types give identity across folios.** `master`/`slave` make a coil and its contacts one device; `next_report`/`previous_report` make one potential across pages; GElectrical's `Reference` appends its code as a coordinate-less port so sheets merge. A definition and its instances across files are one entity; traversal follows links.
8. **Cross-reference glyphs are derived from links plus a grid address.** `CrossRefItem` renders `%f-%l%c` (folio-row-column) from `DiagramPosition`, computed from the folio grid, so references are stable human-readable coordinates rather than pointers.
9. **Numbering is formula-driven, positional, and propagated over the net.** QET `NumerotationContext` formulas with per-folio counters (`%sequf_`) copied across a potential; GElectrical renumbers by `lexsort((x,y))` with per-prefix counters and `freeze` flags. Names are derived from kind and position, with explicit freezing.
10. **Results are elements with the same field schema as inputs.** `DisplayElementNode` is inserted per `(page, gnode)` as an undoable group; `res_fields` use `get_field_dict` like inputs; the properties pane shows both. Proof-state overlays should be objects in the drawing, typed like data.
11. **Rules are data over the derived graph.** `(check_expr, (codes, match, all|any|_ifexist), ('self'|'upstream'|'downstream_node'|'constant'|'match', ...))` navigating `get_upstream_element`. A lint layer with quantifier semantics over the dependency graph, separate from the checker.
12. **Style is a key hierarchy separate from geometry and semantics.** Per-class `resistors/scale`, one base length `bipoles/length`, convention bundles `american`/`european`, loadable style files; QET's single `style="line-style:..;line-weight:..;filling:..;color:.."` string. Notation conventions should be switchable without touching the model.
13. **Library addressing by scheme, with embedding.** `common://`, `custom://`, `embed://` (the project carries copies of every element it uses in `<collection>`), versus GElectrical's code registry with schema in code and CSV catalogues keyed by field code. A document should either embed its definitions or bind by scheme, never by path alone.
14. **Subcircuits expose anchors and are placed by any anchor.** `\ctikzsubcircuitdef` pre-measures each anchor's offset to a reference so `\name{inst}{anchor}` drops the block by that anchor; GElectrical `ElementAssembly` groups children and cycles an attachment port during insertion. Composite objects need named anchors and anchor-relative placement.
15. **Schema in code, values in file, versioned.** GElectrical persists `{value,type}` per field and reinstantiates by `code` (`_file_version`); QET persists full element XML (`version=`, `definition version=`). Decide explicitly which side owns the schema and stamp every file.
