# KiCad: data types and machinery conventions (source-level study)

Sources: sparse clone of `gitlab.com/kicad/code/kicad` master (post-9.0 tree; writers emit `kicad_sch` version `20250114`, `kicad_pcb` `20241229`), dev-docs.kicad.org file-format pages, the in-tree DRC help (`pcbnew/dialogs/panel_setup_rules_help_*.md`), and `demos/complex_hierarchy`, `demos/cm5_minima`, `demos/vme-wren`. Paths are repository-relative.

## 1. Identity and purpose

KiCad is a suite of cooperating editors (schematic `eeschema`, board `pcbnew`, symbol/footprint editors, SPICE simulator, 3D viewer, `cvpcb`) sharing one item model (`EDA_ITEM`), one serialization discipline (lowercase s-expression tokens, mm, UUIDs) and one process model: `KIWAY` (`include/kiway.h`) loads each editor as a DSO face (`FACE_SCH`, `FACE_PCB`, `FACE_CVPCB`, ...) and routes typed mail (`include/mail_type.h`: `MAIL_CROSS_PROBE`, `MAIL_PCB_UPDATE`, `MAIL_SCH_UPDATE`, `MAIL_SCH_GET_NETLIST`, ...). The schematic authors symbols, wires and labels; a connection graph derives nets; the board authors footprints, copper and zones against those nets; ERC/DRC check both against typed rules.

## 2. Core data types

### 2.1 Common base

`include/eda_item.h`: `class EDA_ITEM : public KIGFX::VIEW_ITEM, public SERIALIZABLE { const KIID m_Uuid; KICAD_T m_structType; EDA_ITEM_FLAGS m_flags; EDA_ITEM* m_parent; EDA_GROUP* m_group; ... }` with `Clone()`, `Visit()`, `HitTest()`, `GetBoundingBox()`. `include/core/typeinfo.h` `enum KICAD_T` fixes the taxonomy and locate order: `LIB_SYMBOL_T, SCH_SHAPE_T, SCH_FIELD_T, SCH_TEXT_T, SCH_TEXTBOX_T, SCH_PIN_T, SCH_MARKER_T, SCH_JUNCTION_T, SCH_NO_CONNECT_T, SCH_BUS_WIRE_ENTRY_T, SCH_BUS_BUS_ENTRY_T, SCH_LINE_T, ..., SCH_LABEL_T, SCH_GLOBAL_LABEL_T, SCH_HIER_LABEL_T, SCH_RULE_AREA_T, SCH_DIRECTIVE_LABEL_T, SCH_SYMBOL_T, SCH_GROUP_T, SCH_SHEET_PIN_T, SCH_SHEET_T`; PCB: `PCB_FOOTPRINT_T, PCB_PAD_T, PCB_TRACE_T, PCB_VIA_T, PCB_ARC_T, PCB_ZONE_T, PCB_NETINFO_T, PCB_GROUP_T, PCB_CONSTRAINT_T`. A comment notes ordinals are frozen because "IPC clients with stale protobuf-generated headers depend on stable values".

Identity (`include/kiid.h`): `class KIID { boost::uuids::uuid m_uuid; }`; `class KIID_PATH : public std::vector<KIID>` with `AsString()`, `MakeRelativeTo()`, `EndsWith()`. Library reference (`include/lib_id.h`): `class LIB_ID { UTF8 m_libraryName; UTF8 m_itemName; }`, `Format()` gives `"NICKNAME:ITEMNAME"`.

### 2.2 Schematic items

`eeschema/sch_item.h`, `class SCH_ITEM : public EDA_ITEM`:

```cpp
SCH_LAYER_ID m_layer; int m_unit; /* 0 if common to all units */ int m_bodyStyle; bool m_private;
std::map<SCH_SHEET_PATH, std::vector<SCH_ITEM*>, SHEET_PATH_CMP> m_connected_items;
std::unordered_map<SCH_SHEET_PATH, SCH_CONNECTION*> m_connection_map;
virtual bool CanConnect( const SCH_ITEM* aItem ) const { return m_layer == aItem->GetLayer(); }
virtual bool IsConnectable() const { return false; }
virtual std::vector<VECTOR2I> GetConnectionPoints() const { return {}; }
```

Connectivity is keyed per sheet path, i.e. per instance. `enum BODY_STYLE : int { BASE = 1, DEMORGAN = 2 }`; `DANGLING_END_T { WIRE_END, BUS_END, JUNCTION_END, PIN_END, LABEL_END, BUS_ENTRY_END, WIRE_ENTRY_END, SHEET_LABEL_END, NO_CONNECT_END }`. `SCH_LAYER_ID` (`include/layer_ids.h`): `LAYER_WIRE, LAYER_BUS, LAYER_JUNCTION, LAYER_LOCLABEL, LAYER_GLOBLABEL, LAYER_HIERLABEL, LAYER_PINNUM, LAYER_PINNAM, ..., LAYER_NETCLASS_REFS, LAYER_RULE_AREAS, LAYER_DEVICE, LAYER_NOTES, ..., LAYER_OP_VOLTAGES, LAYER_OP_CURRENTS`.

`LIB_SYMBOL` (`eeschema/lib_symbol.h`) is the library definition: `std::weak_ptr<LIB_SYMBOL> m_parent; /* inherited symbols */ LIB_ID m_libId; int m_unitCount; bool m_unitsLocked; bool m_demorgan; LIBRENTRYOPTIONS m_options; LIB_ITEMS_CONTAINER m_drawings; wxArrayString m_fpFilters; PIN_MAP_SET m_pinMaps; std::vector<std::set<wxString>> m_jumperPinGroups; std::map<int, wxString> m_unitDisplayNames;` with `enum LIBRENTRYOPTIONS { ENTRY_NORMAL, ENTRY_GLOBAL_POWER, ENTRY_LOCAL_POWER }`, `IsDerived()`, `Flatten()`.

`SCH_PIN` (`eeschema/sch_pin.h`) serves library and instance pins: `SCH_PIN* m_libPin; /* nullptr for a pin *in* the LIB_SYMBOL */ std::map<wxString, ALT> m_alternates; VECTOR2I m_position; std::optional<int> m_length; PIN_ORIENTATION m_orientation; GRAPHIC_PINSHAPE m_shape; ELECTRICAL_PINTYPE m_type; wxString m_name, m_number, m_alt; bool m_isDangling; std::map<const SCH_SHEET_PATH, std::pair<wxString, bool>> m_net_name_map;`, `struct ALT { wxString m_Name; GRAPHIC_PINSHAPE m_Shape; ELECTRICAL_PINTYPE m_Type; }`. From `common/pin_type.h`:

```cpp
enum class ELECTRICAL_PINTYPE {
    PT_INPUT, PT_OUTPUT, PT_BIDI, PT_TRISTATE,
    PT_PASSIVE,       /// must be connected, and can be connected to any pin
    PT_NIC,           ///< not internally connected (may be connected to anything)
    PT_UNSPECIFIED,   ///< unknown electrical properties: creates always a warning when connected
    PT_POWER_IN,      ///< power input (GND, VCC for ICs). Must be connected to a power output.
    PT_POWER_OUT,     ///< output of a regulator: intended to be connected to power input pins
    PT_OPENCOLLECTOR, PT_OPENEMITTER,
    PT_NC,            ///< not connected (must be left open)
    PT_LAST_OPTION = PT_NC, PT_INHERIT };
enum class GRAPHIC_PINSHAPE { LINE, INVERTED, CLOCK, INVERTED_CLOCK, INPUT_LOW, CLOCK_LOW,
    OUTPUT_LOW, FALLING_EDGE_CLOCK, NONLOGIC, LAST_OPTION = NONLOGIC, INHERIT };
enum class PIN_ORIENTATION { PIN_RIGHT, PIN_LEFT, PIN_UP, PIN_DOWN, INHERIT };
```

`SCH_SYMBOL` (`eeschema/sch_symbol.h`) is the placed instance: `VECTOR2I m_pos; LIB_ID m_lib_id; wxString m_prefix; std::vector<SCH_FIELD> m_fields; std::unique_ptr<LIB_SYMBOL> m_part; /* flattened copy */ bool m_isInNetlist; std::vector<std::unique_ptr<SCH_PIN>> m_pins; std::vector<SCH_SYMBOL_INSTANCE> m_instances; std::unordered_map<KIID_PATH, size_t> m_instancePathIndex;`. `eeschema/sch_sheet_path.h`: `struct SCH_SYMBOL_INSTANCE { KIID_PATH m_Path; wxString m_Reference; int m_Unit = 1; wxString m_ProjectName; bool m_DNP = false; }`; `GetRef(sheet)` does `m_instancePathIndex.find( sheet->Path() )`, falling back to the Reference field. `SCH_FIELD : SCH_ITEM, EDA_TEXT { FIELD_T m_id; wxString m_name; bool m_showName, m_allowAutoPlace; }` with `enum class FIELD_T { USER, REFERENCE, VALUE, FOOTPRINT, DATASHEET, DESCRIPTION, INTERSHEET_REFS, SHEET_NAME, SHEET_FILENAME, SHEET_USER }` (`include/template_fieldnames.h`; canonical names `"Reference" "Value" "Footprint" "Datasheet" "Description" "Sheetname" "Sheetfile" "Intersheetrefs"`).

Wires: `SCH_LINE { VECTOR2I m_start, m_end; STROKE_PARAMS m_stroke; }` — wire/bus/graphic is the layer (`LAYER_WIRE`, `LAYER_BUS`, `LAYER_NOTES`), not a subclass. `SCH_JUNCTION { VECTOR2I m_pos; int m_diameter; COLOR4D m_color; }`; `SCH_NO_CONNECT { VECTOR2I m_pos; int m_size; }`; `SCH_BUS_ENTRY_BASE { VECTOR2I m_pos, m_size; STROKE_PARAMS m_stroke; }` → `SCH_BUS_WIRE_ENTRY`, `SCH_BUS_BUS_ENTRY`; `SCH_TEXT : SCH_ITEM, EDA_TEXT { bool m_excludedFromSim; }`.

Labels (`eeschema/sch_label.h`): `SCH_LABEL_BASE : SCH_TEXT { std::vector<SCH_FIELD> m_fields; LABEL_FLAG_SHAPE m_shape; CONNECTION_TYPE m_connectionType; bool m_isDangling; }`, `enum LABEL_FLAG_SHAPE { L_INPUT, L_OUTPUT, L_BIDI, L_TRISTATE, L_UNSPECIFIED, F_DOT, F_ROUND, F_DIAMOND, F_RECTANGLE }`, `SPIN_STYLE { LEFT=0, UP=1, RIGHT=2, BOTTOM=3 }`. Subclasses: `SCH_LABEL` (sheet-local), `SCH_GLOBALLABEL` (design-wide), `SCH_HIERLABEL` (sheet port), `SCH_DIRECTIVE_LABEL { int m_pinLength, m_symbolSize; std::unordered_set<SCH_RULE_AREA*> m_connected_rule_areas; }` (carries a `"Netclass"` field; "cannot be used to name a net"), `SCH_SHEET_PIN : SCH_HIERLABEL { int m_number; SHEET_SIDE m_edge; }` with `SHEET_SIDE { LEFT = 0, RIGHT, TOP, BOTTOM, UNDEFINED }`. `SCH_RULE_AREA : SCH_SHAPE { std::unordered_set<SCH_ITEM*> m_items; std::unordered_set<SCH_DIRECTIVE_LABEL*> m_directives; }`.

`SCH_SHEET` (`eeschema/sch_sheet.h`): `SCH_SCREEN* m_screen; std::vector<SCH_SHEET_PIN*> m_pins; std::vector<SCH_FIELD> m_fields; bool m_excludedFromSim, m_excludedFromBOM, m_excludedFromBoard, m_DNP; std::vector<SCH_SHEET_INSTANCE> m_instances;` where `struct SCH_SHEET_INSTANCE { KIID_PATH m_Path; wxString m_PageNumber; wxString m_ProjectName; bool m_DNP, m_ExcludedFromBOM, m_ExcludedFromSim, m_ExcludedFromBoard; }`. `SCH_SCREEN : BASE_SCREEN` is the file-level container: `EE_RTREE m_rtree` (spatial index), `m_fileName`, `m_paper`, `m_titles`, `m_libSymbols`, `m_refCount` (one screen shared by many sheets), bus aliases, `IsExplicitJunctionNeeded()`, `GetNeededJunctions()`.

`SCH_SHEET_PATH`: `std::vector<SCH_SHEET*> m_sheets; size_t m_current_hash; KIID_PATH m_path;`; `Path()` is the UUID chain; `PathAsString()` returns `"/"` then `uuid + "/"` per non-root sheet (`eeschema/sch_sheet_path.cpp:486`); `PathHumanReadable()` uses names. `class SCH_SHEET_LIST : public std::vector<SCH_SHEET_PATH>` has `BuildSheetList()`, `SortByPageNumbers()`, `GetSymbols( SCH_REFERENCE_LIST& )`, `FindAllSheetsForScreen()`.

### 2.3 Connections and the connection graph

`eeschema/sch_connection.h`: `enum class CONNECTION_TYPE { NONE, NET, BUS, BUS_GROUP }`; `class SCH_CONNECTION { SCH_SHEET_PATH m_sheet, m_local_sheet; SCH_ITEM* m_parent; SCH_ITEM* m_driver; CONNECTION_TYPE m_type; wxString m_name, m_cached_name, m_cached_name_with_path, m_local_name, m_prefix, m_local_prefix, m_bus_prefix, m_suffix; long m_vector_start, m_vector_end, m_vector_index; int m_net_code, m_bus_code, m_subgraph_code; std::vector<std::shared_ptr<SCH_CONNECTION>> m_members; }`. `ConfigureFromLabel()` calls `NET_SETTINGS::ParseBusVector` (→ `BUS`, one `NET` member per index) or `ParseBusGroup` (→ `BUS_GROUP`); `recacheName()` yields `prefix+name+suffix` or `"<NO NET>"` and prepends the sheet path for non-global names.

`eeschema/connection_graph.h`: a `CONNECTION_SUBGRAPH` is one connected component on one sheet — `long m_code; bool m_multiple_drivers, m_strong_driver, m_local_driver; std::set<SCH_ITEM*> m_drivers, m_items; SCH_ITEM* m_driver; SCH_ITEM* m_no_connect; SCH_SHEET_PATH m_sheet; SCH_CONNECTION* m_driver_connection; ... m_bus_neighbors, m_bus_parents; std::set<SCH_SHEET_PIN*> m_hier_pins; std::set<SCH_HIERLABEL*> m_hier_ports; CONNECTION_SUBGRAPH* m_hier_parent; bool m_absorbed; CONNECTION_SUBGRAPH* m_absorbed_by;` — with the driver lattice

```cpp
enum class PRIORITY { INVALID = -1, NONE = 0, PIN, SHEET_PIN, HIER_LABEL, LOCAL_LABEL,
                      LOCAL_POWER_PIN, GLOBAL_POWER_PIN, GLOBAL };
```

`CONNECTION_GRAPH::Recalculate()` runs `buildItemSubGraphs → resolveAllDriversAndSubgraphs → collectAllDriverValues → generateGlobalPowerPinSubGraphs → generateBusAliasMembers → processSubGraphs → propagateToNeighbors → assignNewNetCode / assignNetCodesToBus`; `RunERC()` runs `ercCheckMultipleDrivers, ercCheckBusToNetConflicts, ercCheckBusToBusConflicts, ercCheckBusToBusEntryConflicts, ercCheckNoConnects, ercCheckFloatingWires, ercCheckDanglingWireEndpoints, ercCheckLabels, ercCheckDirectiveLabels, ercCheckHierSheets, ercCheckSingleGlobalLabel`. Result: `m_net_code_to_subgraphs_map` (`NET_MAP`). `class BUS_ALIAS { wxString m_name; std::vector<wxString> m_members; }`.

### 2.4 Netclasses and ERC settings

`include/netclass.h`: `wxString m_Name; int m_Priority; std::optional<int> m_Clearance, m_TrackWidth, m_ViaDia, m_ViaDrill, m_uViaDia, m_uViaDrill, m_diffPairWidth, m_diffPairGap, m_diffPairViaGap, m_wireWidth, m_busWidth; COLOR4D m_schematicColor, m_pcbColor; std::optional<int> m_lineStyle; std::vector<NETCLASS*> m_constituents; NETCLASS* m_clearanceParent; ...` (one `*Parent` per attribute records the supplying constituent). `include/project/net_settings.h` `NET_SETTINGS : NESTED_SETTINGS { m_defaultNetClass; std::map<wxString, std::shared_ptr<NETCLASS>> m_netClasses; std::map<wxString, std::set<wxString>> m_netClassLabelAssignments; m_netClassPatternAssignments; m_compositeNetClasses; m_netColorAssignments; }` with `GetEffectiveNetClass(netName)`.

`eeschema/erc/erc_settings.h`: `enum class PIN_ERROR { OK, WARNING, PP_ERROR, UNCONNECTED }`; `PIN_ERROR m_PinMap[ELECTRICAL_PINTYPES_TOTAL][ELECTRICAL_PINTYPES_TOTAL]; static int m_PinMinDrive[...]; std::map<int, SEVERITY> m_ERCSeverities;`. `enum ERCE_T` has 60+ codes, e.g. `ERCE_PIN_NOT_CONNECTED, ERCE_PIN_NOT_DRIVEN, ERCE_POWERPIN_NOT_DRIVEN, ERCE_HIERACHICAL_LABEL, ERCE_LABEL_NOT_CONNECTED, ERCE_SINGLE_GLOBAL_LABEL, ERCE_DIFFERENT_UNIT_FP, ERCE_MISSING_UNIT, ERCE_BUS_ALIAS_CONFLICT, ERCE_DRIVER_CONFLICT, ERCE_BUS_TO_NET_CONFLICT, ERCE_UNDEFINED_NETCLASS, ERCE_SIMULATION_MODEL, ERCE_LIB_SYMBOL_MISMATCH, ERCE_FOOTPRINT_LINK_ISSUES, ERCE_PIN_MAP_UNMAPPED_PIN, ERCE_PIN_TO_PIN_WARNING, ERCE_PIN_TO_PIN_ERROR`.

### 2.5 Board types

`BOARD_CONNECTED_ITEM : BOARD_ITEM { NETINFO_ITEM* m_netinfo; }` (`pcbnew/board_connected_item.h`) with `GetNetCode()`, `GetOwnClearance(layer)`, `GetEffectiveNetClass()`. `pcbnew/board.h`: `class BOARD : public BOARD_ITEM_CONTAINER, public EMBEDDED_FILES, public PROJECT::_ELEM` owning `m_footprints, m_tracks, m_zones, m_drawings, m_markers, m_groups, m_generators, NETINFO_LIST m_NetInfo, m_designSettings, m_connectivity (CONNECTIVITY_DATA), m_boardOutline`; `enum LAYER_T { LT_UNDEFINED = -1, LT_SIGNAL, LT_POWER, LT_MIXED, LT_JUMPER, LT_AUX, LT_FRONT, LT_BACK }`.

`pcbnew/footprint.h` `FOOTPRINT`: `std::deque<PCB_FIELD*> m_fields; std::deque<BOARD_ITEM*> m_drawings; std::deque<PAD*> m_pads; std::vector<ZONE*> m_zones; std::deque<PCB_CONSTRAINT*> m_constraints; LIB_ID m_fpid; int m_attributes; ZONE_CONNECTION m_zoneConnection; std::optional<int> m_clearance, m_solderMaskMargin; KIID_PATH m_path; /* Path to associated symbol ([sheetUUID, .., symbolUUID]) */ wxString m_sheetname, m_sheetfile, m_filters; std::vector<FP_3DMODEL> m_3D_Drawings; std::vector<std::set<wxString>> m_jumperPadGroups;`; `enum FOOTPRINT_ATTR_T { FP_THROUGH_HOLE = 0x1, FP_SMD = 0x2, FP_EXCLUDE_FROM_POS_FILES = 0x4, FP_EXCLUDE_FROM_BOM = 0x8, FP_BOARD_ONLY = 0x10, FP_JUST_ADDED = 0x20, FP_DNP = 0x40, FP_EXCLUDE_FROM_SIM = 0x80 }`; `class FP_3DMODEL { VECTOR3D m_Scale, m_Rotation, m_Offset; double m_Opacity; wxString m_Filename; bool m_Show; }`.

`pcbnew/pad.h` `PAD`: `wxString m_number; /* pin number in schematic */ wxString m_pinFunction; /* pin name */ wxString m_pinType; /* electrical type in schematic */ VECTOR2I m_libPos; EDA_ANGLE m_libOrientation; PADSTACK m_padStack; PAD_ATTRIB m_attribute; PAD_PROP m_property; int m_lengthPadToDie, m_delayPadToDie;`. `pcbnew/padstack.h`: `PAD_SHAPE { CIRCLE, RECTANGLE, OVAL, TRAPEZOID, ROUNDRECT, CHAMFERED_RECT, CUSTOM }`, `PAD_DRILL_SHAPE { UNDEFINED, CIRCLE, OBLONG }`, `PAD_ATTRIB { PTH, SMD, CONN, NPTH }`, `PAD_PROP { NONE, BGA, FIDUCIAL_GLBL, FIDUCIAL_LOCAL, TESTPOINT, HEATSINK, CASTELLATED, MECHANICAL, PRESSFIT }`.

`pcbnew/pcb_track.h`: `PCB_TRACK : BOARD_CONNECTED_ITEM { VECTOR2I m_Start, m_End; int m_width; bool m_hasSolderMask; }`, `PCB_ARC : PCB_TRACK { VECTOR2I m_Mid; }`, `PCB_VIA` with a `PADSTACK` and `enum class VIATYPE : int { THROUGH = 4, BURIED = 3, BLIND = 2, MICROVIA = 1, NOT_DEFINED = 0 }` (`pcbnew/pcb_track_types.h`). `pcbnew/zone.h` `ZONE : BOARD_CONNECTED_ITEM { SHAPE_POLY_SET* m_Poly; std::map<PCB_LAYER_ID, std::shared_ptr<SHAPE_POLY_SET>> m_FilledPolysList; LSET m_layerSet; unsigned m_priority; bool m_isRuleArea; wxString m_zoneName; int m_ZoneMinThickness; ZONE_CONNECTION m_PadConnection; int m_thermalReliefGap, m_thermalReliefSpokeWidth; ZONE_FILL_MODE m_fillMode /* POLYGONS, HATCH_PATTERN, COPPER_THIEVING */; }`. `pcbnew/netinfo.h`: `NETINFO_ITEM : BOARD_ITEM { int m_netCode; wxString m_netname; /* like /sheet/subsheet/vout */ wxString m_shortNetname; std::shared_ptr<NETCLASS> m_netClass; }`, `NETINFO_LIST` with `NETNAMES_MAP`, `NETCODES_MAP`, `UNCONNECTED`, `ORPHANED`.

`include/layer_ids.h` `enum PCB_LAYER_ID : int`: copper layers are even (`F_Cu = 0, B_Cu = 2, In1_Cu = 4 ... In30_Cu = 62`), technical layers odd (`F_Mask = 1, B_Mask = 3, F_SilkS = 5, B_SilkS = 7, F_Adhes = 9, B_Adhes = 11, F_Paste = 13, B_Paste = 15, Dwgs_User = 17, Cmts_User = 19, Eco1_User = 21, Eco2_User = 23, Edge_Cuts = 25, Margin = 27, B_CrtYd = 29, F_CrtYd = 31, B_Fab = 33, F_Fab = 35, Rescue = 37, User_1 = 39, ...`), collected in the `LSET` bitset.

## 3. File format grammar

Common conventions (dev-docs `sexpr-intro`): "All tokens are lowercase"; "All values are given in millimeters"; `(at X Y [ANGLE])`; `(stroke (width W) (type solid|dash|dot|dash_dot|dash_dot_dot|default) (color R G B A))`; `(effects (font (size H W) [bold] [italic]) [(justify ...)] [hide])`; `(uuid "...")` is a v4 UUID; library ids are `"LIBRARY_NICKNAME:ENTRY_NAME"`.

**`kicad_sch`** (`demos/complex_hierarchy/*.kicad_sch`; writer `eeschema/sch_io/kicad_sexpr/sch_io_kicad_sexpr.cpp`), abbreviated but verbatim:

```
(kicad_sch (version 20250114) (generator "eeschema") (generator_version "9.0")
  (uuid "5b9623a5-6d01-41fc-9865-e1bc779418c8") (paper "A4")
  (lib_symbols (symbol "complex_hierarchy:+12V" (power) (pin_names (offset 0)) (exclude_from_sim no) (in_bom yes) (on_board yes)
     (property "Reference" "#PWR" (at 0 -3.81 0) (effects (font (size 1.27 1.27)) (hide yes))) ...))
  (junction (at 138.43 60.96) (diameter 1.016) (color 0 0 0 0) (uuid "0dfdfa9f-..."))
  (wire (pts (xy 86.36 50.8) (xy 91.44 50.8)) (stroke (width 0) (type solid)) (uuid "0055142f-..."))
  (label "Vpil_0_3,3V" (at 132.08 134.62 0) (effects ...) (uuid "1cd6f71d-..."))
  (symbol (lib_id "complex_hierarchy:POT") (at 148.59 162.56 0) (unit 1) (exclude_from_sim no) (in_bom yes) (on_board yes) (dnp no)
    (uuid "00000000-0000-0000-0000-00004b3a1357")
    (property "Reference" "RV201" (at 148.59 165.1 0) ...) (property "Value" "4,7K" ...)
    (property "Footprint" "Potentiometer_THT:Potentiometer_Bourns_3266W_Vertical" ...)
    (pin "1" (uuid "0096e1bb-...")) (pin "2" (uuid "c96031df-...")) (pin "3" (uuid "89a48842-..."))
    (instances (project "complex_hierarchy"
      (path "/5b9623a5-6d01-41fc-9865-e1bc779418c8/00000000-0000-0000-0000-00004b3a1333" (reference "RV201") (unit 1))
      (path "/5b9623a5-6d01-41fc-9865-e1bc779418c8/00000000-0000-0000-0000-00004b3a13a4" (reference "RV301") (unit 1)))))
  (sheet (at 71.12 111.76) (size 50.8 36.83) (exclude_from_sim no) (in_bom yes) (on_board yes) (dnp no)
    (stroke (width 0) (type solid)) (fill (color 0 0 0 0.0000)) (uuid "00000000-0000-0000-0000-00004b3a1333")
    (property "Sheetname" "ampli_ht_vertical" ...) (property "Sheetfile" "ampli_ht.kicad_sch" ...)
    (pin "NAME" input|output|bidirectional|tri_state|passive (at X Y ANGLE) (effects ...) (uuid "..."))
    (instances (project "complex_hierarchy" (path "/5b9623a5-6d01-41fc-9865-e1bc779418c8" (page "2")))))
  (sheet_instances (path "/" (page "1"))) (embedded_fonts no))
```

Other writer tokens: `(no_connect (at X Y) (uuid ...))`, `(bus_entry (at X Y) (size X Y) (stroke ...))`, `(bus (pts ...))`, `(global_label "T" (shape input|output|bidirectional|tri_state|passive) (at ...) (property "Intersheetrefs" ...))`, `(hierarchical_label "T" (shape ...) ...)`, `(netclass_flag "" (length L) (shape round|dot|diamond|rectangle) (at ...) (property "Netclass" "HV"))`, `(rule_area (polyline ...))`, `(bus_alias "N" (members ...))`, `(mirror x|y)`, `(body_style N)`, `(pin "N" (uuid ...) (alternate "ALT"))`.

**`kicad_sym`** (`demos/cm5_minima/CM5IO.pretty/CM5_IO.kicad_sym`; writer `sch_io_kicad_sexpr_lib_cache.cpp`):

```
(kicad_symbol_lib (version 20231120) (generator "kicad_symbol_editor") (generator_version "8.0")
  (symbol "ComputeModule5-CM5_GPIO" (exclude_from_sim no) (in_bom yes) (on_board yes)
    (property "Reference" "Module301" (at -2.54 61.595 0) (effects (font (size 1.27 1.27))))
    (property "Footprint" "CM5IO:Raspberry-Pi-5-Compute-Module_GPIO" ... (hide yes))
    (symbol "ComputeModule5-CM5_GPIO_1_0" (text "GPIO" (at 0 6.35 0) ...))          ; unit 1, all body styles
    (symbol "ComputeModule5-CM5_GPIO_1_1" (rectangle (start -30.48 -71.12) (end 25.4 58.42) ...)
      (pin power_in line (at 27.94 55.88 180) (length 2.54)
        (name "GND" (effects (font (size 1.27 1.27)))) (number "1" (effects (font (size 1.27 1.27))))))))
```

Sub-symbols are written `"%s_%d_%d"` = `NAME_UNIT_BODYSTYLE` ("A UNIT value of zero indicates that the symbol is common to all units"); derived symbols are `(symbol "NAME" (extends "PARENT"))`; power symbols emit `(power global)` or `(power local)`; other tokens `(pin_numbers (hide yes))`, `(pin_names (offset N) (hide yes))`, `(body_styles demorgan)`, `(unit_name "...")`, `(alternate "NAME" TYPE SHAPE)`. Pin type tokens: `input output bidirectional tri_state passive free unspecified power_in power_out open_collector open_emitter no_connect`; shapes: `line inverted clock inverted_clock input_low clock_low output_low edge_clock_high non_logic`.

**`kicad_pcb`** (`demos/complex_hierarchy/complex_hierarchy.kicad_pcb`; writer `pcbnew/pcb_io/kicad_sexpr/pcb_io_kicad_sexpr.cpp`):

```
(kicad_pcb (version 20241229) (generator "pcbnew") (generator_version "9.0")
  (general (thickness 1.6) (legacy_teardrops no)) (paper "A4")
  (layers (0 "F.Cu" power "top_copper") (2 "B.Cu" signal "bottom_copper") (9 "F.Adhes" user "F.Adhesive") ...)
  (setup (stackup (layer "F.Cu" (type "copper") (thickness 0.035)) ...) ...)
  (net 0 "") (net 1 "-VAA") (net 2 "/12Vext") (net 3 "/ampli_ht_horizontal/PIEZO_IN")
  (footprint "complex_hierarchy:CP_Axial_L10.0mm_D4.5mm_P15.00mm_Horizontal" (layer "F.Cu") (uuid ...) (at 126.619 60.706)
    (property "Reference" "C104" (at 7.5 -3.37 0) (layer "F.SilkS") ...) (property "Value" "47uF/20V" ...)
    (property ki_fp_filters "CP* Elko* TantalC* C*elec c_elec* SMD*_Pol")
    (path "/00000000-0000-0000-0000-00004ae173cf") (sheetname "/") (sheetfile "complex_hierarchy.kicad_sch")
    (attr through_hole) (fp_line ...)
    (pad "1" thru_hole rect (at 0 0) (size 2 2) (drill 1) (layers "*.Cu" "*.Mask") (net 40 "+12V") (pintype "passive") (uuid ...))
    (model "${KICAD6_3DMODEL_DIR}/Capacitor_THT.3dshapes/CP_Axial_...wrl" (offset (xyz 0 0 0)) (scale (xyz 1 1 1)) (rotate (xyz 0 0 0))))
  (segment (start 107.061 104.521) (end 104.775 106.807) (width 0.6096) (layer "F.Cu") (net 1) (uuid ...))
  (via [blind|micro] (at X Y) (size D) (drill D) (layers "F.Cu" "B.Cu") [(free)] (net N) (uuid ...))
  (arc (start ...) (mid ...) (end ...) (width W) (layer ...) (net N))
  (zone (net 34) (net_name "Net-(Q201-E)") (layer "F.Cu") (uuid ...) (hatch full 0.1) (priority 30006)
    (connect_pads yes (clearance 0)) (min_thickness 0.0254)
    (fill yes (thermal_gap 0.5) (thermal_bridge_width 0.5) (island_removal_mode 1) (island_area_min 10))
    (polygon (pts (xy ...) ...)) (filled_polygon (layer ...) (pts ...))))
```

Pads also take `(pinfunction "NAME")`, `(die_length L)`, `(zone_connect N)`, `(roundrect_rratio R)`, `(primitives ...)`, `(padstack (mode front_inner_back|custom) ...)`.

**`kicad_pro`** (JSON; `common/project/project_file.cpp`). Top-level keys in the demo: `["board","boards","cvpcb","erc","libraries","meta","net_settings","pcbnew","schematic","sheets","text_variables"]`; `board.design_settings{defaults, rules{min_clearance:0.2,...}, rule_severities, track_widths, via_dimensions}`, `board.layer_presets`, `board.viewports`; `net_settings.classes:[{name:"Default", clearance:0.3, track_width:0.4, via_diameter:1.651, via_drill:0.6, wire_width:6, bus_width:12, priority:2147483647,...}]`, `netclass_patterns:[{netclass:"power", pattern:"GND"},...]`, `netclass_assignments`, `net_colors`; `sheets:[["5b9623a5-...","Root"],["...4b3a1333","ampli_ht_vertical"],["...4b3a13a4","ampli_ht_horizontal"]]`; `schematic.{annotate_start_num, bom_settings, drawing, ngspice, spice_*, subpart_id_separator}`. Library tables (`demos/complex_hierarchy/sym-lib-table`): `(sym_lib_table (version 7) (lib (name "complex_hierarchy")(type "KiCad")(uri "${KIPRJMOD}/complex_hierarchy.kicad_sym")(options "")(descr "")))`; `fp_lib_table` likewise with `.pretty`.

**Netlist export**: `NETLIST_EXPORTER_XML::makeRoot()` builds an `XNODE` tree that `NETLIST_EXPORTER_KICAD::Format()` prints as s-expressions, so both share one vocabulary (`eeschema/netlist_exporters/netlist_exporter_xml.cpp`): `(export (version "E") (design (source)(date)(tool)(sheet (number)(name)(tstamps))) (components (comp (ref "R1") (value) (footprint) (libsource (lib)(part)(description)) (property (name)(value)) (sheetpath (names)(tstamps)) (tstamps))) (libparts (libpart (lib)(part) (pins (pin (num)(name)(type))))) (libraries (library (logical)(uri))) (nets (net (code)(name)(class) (node (ref)(pin)(pinfunction)(pintype)))))`.

**`kicad_dru`** (`panel_setup_rules_help_1clauses.md`): `(version 2)`, `(rule <rule_name> <rule_clause> ...)` with `(constraint <constraint_type> ...)`, `(condition "<expression>")`, `(layer "<layer_name>")`, `(severity <severity_name>)`. From `demos/vme-wren/vme-wren.kicad_dru`:

```
(rule "zdiff_100R_outer" (layer outer)
  (constraint track_width (min 0.115mm) (max 0.115mm) (opt 0.115mm))
  (constraint diff_pair_gap (min 0.1mm) (max 1mm) (opt 0.1mm))
  (constraint diff_pair_uncoupled (max 5mm))
  (condition "A.inDiffPair('*')"))
(rule "length_DDR_CMD_FPGA_To_IC13"
  (constraint length (min 42.5mm) (max 43.5mm) (opt 43mm))
  (condition "A.NetClass == 'DDR4_CMD' && A.fromTo('IC14-*','IC13-*')"))
```

## 4. Machinery conventions

**Symbol ↔ footprint ↔ 3D.** The symbol's `Footprint` field holds a `LIB_ID`; `ki_fp_filters` restricts candidates; nicknames resolve through global and project `LIBRARY_TABLE`s (`include/libraries/library_table.h`: `LIBRARY_TABLE_ROW { m_uri, m_type, m_options, m_description, LIBRARY_TABLE_SCOPE m_scope }`, `LIBRARY_TABLE_TYPE { SYMBOL, FOOTPRINT, DESIGN_BLOCK }`) with `${KIPRJMOD}`/`${KICAD9_*_DIR}` substitution. The back-link is `FOOTPRINT::m_path` (`(path "/sheetuuid/.../symboluuid")`) plus `(sheetname)(sheetfile)`; `PAD::m_pinFunction`/`m_pinType` are copies of the schematic pin name/type delivered by the netlist. 3D bodies are `FP_3DMODEL` records by filename.

**Units and De Morgan.** `LIB_SYMBOL::m_unitCount`, `m_unitsLocked`, `m_demorgan`; draw items carry `m_unit`/`m_bodyStyle` (0 = shared); sub-symbols `NAME_U_B`; a placed `SCH_SYMBOL` selects `unit` and `body_style`, and the unit is per instance (`SCH_SYMBOL_INSTANCE::m_Unit`). ERC checks `ERCE_MISSING_UNIT`, `ERCE_DIFFERENT_UNIT_FP`, `ERCE_DIFFERENT_UNIT_NET`.

**Power symbols and flags.** `ENTRY_GLOBAL_POWER`/`ENTRY_LOCAL_POWER` (`(power global|local)`), reference prefix `#PWR`, one invisible `power_in` pin whose *value* is the net name; the graph gives such pins `PRIORITY::GLOBAL_POWER_PIN`/`LOCAL_POWER_PIN`. `PWR_FLAG` is a power symbol with a `power_out` pin; without it ERC raises `ERCE_POWERPIN_NOT_DRIVEN`.

**ERC pin matrix** (`eeschema/erc/erc_settings.cpp` `m_defaultPinMap`; rows/cols `I O Bi 3S Pas NIC UnS PwrI PwrO OC OE NC`):

```
/* I  */ { OK,  OK,   OK,   OK,   OK,   OK,   WAR,  OK,   OK,   OK,   OK,   ERR },
/* O  */ { OK,  ERR,  OK,   WAR,  OK,   OK,   WAR,  OK,   ERR,  ERR,  ERR,  ERR },
/* Bi */ { OK,  OK,   OK,   OK,   OK,   OK,   WAR,  OK,   WAR,  OK,   WAR,  ERR },
/* 3S */ { OK,  WAR,  OK,   OK,   OK,   OK,   WAR,  WAR,  ERR,  WAR,  WAR,  ERR },
/*Pas */ { OK,  OK,   OK,   OK,   OK,   OK,   WAR,  OK,   OK,   OK,   OK,   ERR },
/*NIC */ { OK,  OK,   OK,   OK,   OK,   OK,   OK,   OK,   OK,   OK,   OK,   ERR },
/*UnS */ { WAR, WAR,  WAR,  WAR,  WAR,  OK,   WAR,  WAR,  WAR,  WAR,  WAR,  ERR },
/*PwrI*/ { OK,  OK,   OK,   WAR,  OK,   OK,   WAR,  OK,   OK,   OK,   OK,   ERR },
/*PwrO*/ { OK,  ERR,  WAR,  ERR,  OK,   OK,   WAR,  OK,   ERR,  ERR,  ERR,  ERR },
/* OC */ { OK,  ERR,  OK,   WAR,  OK,   OK,   WAR,  OK,   ERR,  OK,   OK,   ERR },
/* OE */ { OK,  ERR,  WAR,  WAR,  OK,   OK,   WAR,  OK,   ERR,  OK,   OK,   ERR },
/* NC */ { ERR, ERR,  ERR,  ERR,  ERR,  ERR,  ERR,  ERR,  ERR,  ERR,  ERR,  ERR }
```

A second table `m_PinMinDrive` is a drive lattice: "The initial state of a net is NOC ... It can be updated to NPI, NET_NC, NOD or DRV ... Nets are OK when their final state is NET_NC or DRV"; the `PwrI` row is `DRV` only against `O` and `PwrO`. `ERC_TESTER::TestPinToPin()` folds every net through both tables.

**Hierarchical instancing.** A sheet file is one `SCH_SCREEN`; several `SCH_SHEET`s may share it (`m_refCount`), so `ampli_ht.kicad_sch` is placed twice in the demo. Instance identity is the `SCH_SHEET_PATH`; one `SCH_SYMBOL` object holds two `SCH_SYMBOL_INSTANCE`s (`RV201` on `/…4b3a1333`, `RV301` on `/…4b3a13a4`), every `SCH_ITEM` keeps connections per path, and local net names get the human path prefix (`"/ampli_ht_horizontal/PIEZO_IN"`). Sheet pins must match hierarchical labels inside the child (`ERCE_HIERACHICAL_LABEL`); `m_hier_pins`/`m_hier_ports` join subgraphs across the boundary.

**Buses.** Vector `DATA[0..7]`, group `USB1{DP DM}` → `USB1.DP`, alias `{USB}`; `ParseBusVector/ParseBusGroup` expand them into member `SCH_CONNECTION`s; a `SCH_BUS_WIRE_ENTRY` joins a wire to a bus and membership is checked (`ERCE_BUS_ENTRY_CONFLICT`, `ERCE_BUS_TO_NET_CONFLICT`).

**Netclasses** are assigned by a `"Netclass"` field on a label, a `SCH_DIRECTIVE_LABEL` touching a wire, a `SCH_RULE_AREA` containing items (`GetResolvedNetclasses()`), or name patterns; `GetEffectiveNetClass()` composes an aggregate by priority, each attribute remembering its source.

**Custom DRC rules.** `pcbnew/drc/drc_rule.h`: `DRC_RULE { wxString m_Name; LSET m_LayerCondition; DRC_RULE_CONDITION* m_Condition; std::vector<DRC_CONSTRAINT> m_Constraints; SEVERITY m_Severity; DRC_IMPLICIT_SOURCE m_implicitSource; }`, `DRC_CONSTRAINT { DRC_CONSTRAINT_T m_Type; MINOPTMAX<int> m_Value; int m_DisallowFlags; ZONE_CONNECTION m_ZoneConnection; }`, `DRC_RULE_CONDITION { wxString m_expression; std::unique_ptr<PCBEXPR_UCODE> m_ucode; }` (compiled to a small VM). Constraint types (`common/drc_rules.keywords`): `clearance hole_clearance edge_clearance courtyard_clearance physical_clearance physical_hole_clearance creepage track_width track_angle annular_width via_diameter via_count via_dangling hole_size hole_to_hole length net_chain_length stub_length return_path skew diff_pair_gap diff_pair_uncoupled disallow zone_connection thermal_relief_gap thermal_spoke_width min_resolved_spokes silk_clearance text_height text_thickness connection_width solder_mask_expansion bridged_mask assertion`. Items are `A`, `B`, `L`; functions include `A.intersectsArea('z')`, `A.enclosedByArea()`, `A.intersectsCourtyard('U3')`, `A.memberOfFootprint('J*')`, `A.memberOfSheet()`, `A.existsOnLayer('F.Cu')`, `A.isMicroVia()`, `A.inDiffPair('/CLK')`, `AB.isCoupledDiffPair()`, `A.fromTo('R1-Pad1','U2-*')`, `A.hasNetclass()`, `A.getField()`; properties `A.Type, A.Net, A.NetClass, A.Layer, A.Pad_Type, A.Reference`. "Later rules take precedence over earlier rules; once a matching rule is found no further rules will be checked."

**SPICE binding.** Fields `Sim.Device`, `Sim.Type`, `Sim.Pins`, `Sim.Params`, `Sim.Library`, `Sim.Name` (`eeschema/sim/sim_model.h`; legacy `Spice_Primitive`, `Spice_Model`, `Spice_Node_Sequence`). `SIM_MODEL { const TYPE m_type; const SIM_MODEL* m_baseModel; std::vector<SIM_MODEL_PIN> m_modelPins; std::vector<PARAM> m_params; std::unique_ptr<SIM_MODEL_SERIALIZER> m_serializer; std::unique_ptr<SPICE_GENERATOR> m_spiceGenerator; }`, `struct SIM_MODEL_PIN { const std::string modelPinName; wxString symbolPinNumber; }`. `DEVICE_T` = `NONE R C L K TLINE SW D NPN PNP NJFET PJFET NMES PMES NMOS PMOS V I E F G H SUBCKT XSPICE KIBIS SPICE`; `TYPE` refines it (`R_POT`, `R_BEHAVIORAL` = `Sim.Type "="`, `NPN_GUMMELPOON`, `NMOS_BSIM4`, `TLINE_RLGC`, `SW_V`, ...); `SpiceInfo()` maps each to a primitive letter/model (`R_POT → "A"`, `NPN_VBIC → "Q","NPN", level "4"`). `Sim.Pins` serializes as `"1=2 3=1"` (symbol pin = model pin), `Sim.Params` as `name=value` lists. Analyses: `SIM_TYPE { ST_AC, ST_DC, ST_DISTO, ST_NOISE, ST_OP, ST_PZ, ST_SENS, ST_TF, ST_TRAN, ST_SP, ST_FFT }`.

**IPC API and plugins.** `KICAD_API_SERVER` (`include/api/api_server.h`) listens on an `ipc://` nng socket; messages are protobuf `ApiRequest { ApiRequestHeader { kicad_token, client_name }; google.protobuf.Any message }` (`api/proto/common/envelope.proto`) with item messages in `api/proto/schematic/schematic_types.proto` (`SchematicLine`, `Junction`, `LocalLabel`, `SheetPin`, `SheetSymbol`, `SchematicSymbolType { SST_NORMAL, SST_GLOBAL_POWER, SST_LOCAL_POWER }`) and `api/proto/board/board_types.proto` (`Track`, `Via`, `PadStack`, `Zone`). Plugins are JSON manifests (`include/api/api_plugin.h`: `PLUGIN_RUNTIME { PLUGIN_RUNTIME_TYPE { PYTHON, EXEC } type; min_version }`, `PLUGIN_ACTION { identifier, name, description, show_button, entrypoint, scopes, args }`) run by `API_PLUGIN_MANAGER::InvokeAction()` through `PYTHON_MANAGER` (per-plugin venv). No SWIG `pcbnew.i` exists in this tree (the only `swig` hits are under `thirdparty/`), so the out-of-process protobuf API is the scripting surface.

**Undo/commit.** `include/commit.h`: `enum CHANGE_TYPE { CHT_ADD = 1, CHT_REMOVE = 2, CHT_MODIFY = 4, CHT_DONE = 32 }`; `COMMIT::Add/Added/Remove/Removed/Modify/Modified/Stage/Unstage`, `virtual void Push( const wxString& aMessage, int aFlags ) = 0; virtual void Revert() = 0;`, `struct COMMIT_LINE { EDA_ITEM* m_item; EDA_ITEM* m_copy; CHANGE_TYPE m_type; BASE_SCREEN* m_screen; }` — `Modify` snapshots a pre-image via `makeImage()`; `SCH_COMMIT::Push` writes the undo list and marks connectivity dirty.

**Tool framework.** `include/tool/tool_base.h`: `TOOL_TYPE { INTERACTIVE = 0x01, BATCH = 0x02 }`, `RESET_REASON { RUN, MODEL_RELOAD, SUPERMODEL_RELOAD, GAL_SWITCH, REDRAW, SHUTDOWN }`. `TOOL_MANAGER` has `RegisterTool`, `InvokeTool`, `RunAction`, `PostAction`, `RunSynchronousAction(aAction, COMMIT*)`, `ProcessEvent`; each `TOOL_STATE` holds a `COROUTINE`, `pendingWait`, `wakeupEvent`, and a transition table. `TOOL_ACTION` (`include/tool/tool_action.h`): `std::string m_name; TOOL_ACTION_SCOPE m_scope /* AS_CONTEXT, AS_ACTIVE, AS_GLOBAL */; int m_defaultHotKey, m_hotKey; std::optional<wxString> m_menuLabel; TOOL_ACTION_FLAGS m_flags /* AF_ACTIVATE, AF_NOTIFY */; std::any m_param`. Verbatim, `eeschema/tools/sch_actions.cpp`:

```cpp
TOOL_ACTION SCH_ACTIONS::placeSymbol( TOOL_ACTION_ARGS()
        .Name( "eeschema.InteractiveDrawing.placeSymbol" ).Scope( AS_GLOBAL )
        .DefaultHotkey( 'A' ).LegacyHotkeyName( "Add Symbol" ).FriendlyName( _( "Place Symbols" ) )
        .ToolbarState( TOOLBAR_STATE::TOGGLE ).Icon( BITMAPS::add_component ).Flags( AF_ACTIVATE )
        .Parameter<SCH_ACTIONS::PLACE_SYMBOL_PARAMS>( {} ) );
```

**Project vs local.** `.kicad_pro` (`PROJECT_FILE`) holds design semantics; `.kicad_prl` (`include/project/project_local_settings.h`) holds view state: `LSET m_VisibleLayers; GAL_SET m_VisibleItems; PCB_LAYER_ID m_ActiveLayer; wxString m_ActiveLayerPreset; HIGH_CONTRAST_MODE m_ContrastModeDisplay; NET_COLOR_MODE m_NetColorMode; ZONE_DISPLAY_MODE m_ZoneDisplayMode; double m_TrackOpacity, m_ViaOpacity, m_PadOpacity, m_ZoneOpacity; std::vector<wxString> m_HiddenNets; PCB_SELECTION_FILTER_OPTIONS m_PcbSelectionFilter; SCH_SELECTION_FILTER_OPTIONS m_SchSelectionFilter; std::vector<wxString> m_SchHierarchyCollapsed;`.

## 5. UI / wireframe anatomy

**Schematic editor** (`eeschema/sch_edit_frame.cpp`, wxAUI panes `"TopMainToolbar"`, `"MsgPanel"`, `"LeftToolbar"`, Hierarchy, `PropertiesManager`, `SelectionFilter`, `DesignBlocks`, `SearchPane`, `NetNavigator`). Hierarchy pane = `HIERARCHY_PANE` (`wxTreeCtrl` of `SCH_SHEET_PATH`s). Properties = `SCH_PROPERTIES_PANEL : PROPERTIES_PANEL` over `wxPropertyGrid`, driven by `PROPERTY_MANAGER` metadata (`PROPERTY_DISPLAY { PT_DEFAULT, PT_SIZE, PT_AREA, PT_COORD, PT_DEGREE, PT_DECIDEGREE, PT_RATIO, PT_TIME }`). Selection filter (`SCH_SELECTION_FILTER_OPTIONS`): `lockedItems, symbols, text, wires, labels, pins, graphics, images, ruleAreas, otherItems`. Net navigator: `wxGenericTreeCtrl` net → sheet path → item (`eeschema/net_navigator.cpp`). Right palette (`eeschema/toolbars_sch_editor.cpp`): select, `highlightNetTool`, `placeSymbol`, `placePower`, `drawWire`, `drawBus`, `placeBusWireEntry`, `placeNoConnect`, `placeJunction`, label group (`placeLabel`, `placeClassLabel`, `placeGlobalLabel`, `placeHierLabel`), `drawRuleArea`, `drawSheet`, `placeSheetPin`, `syncAllSheetsPins`, text/textbox, table, rectangle, circle/ellipse, arc, bezier, polygon, lines, image. Left palette: grid/units, hidden pins, line mode free/90/45, auto-annotate, `showHierarchy`. Top toolbar: file ops, `schematicSetup`, navigate back/up/forward, rotate/mirror, `annotate`, `runERC`, `showSimulator`, `assignFootprints`, `editSymbolFields`, `generateBOM`, `showPcbNew`, variant chooser, IPC plugin buttons. Symbol chooser (`eeschema/widgets/panel_symbol_chooser.h`): `LIB_TREE` over `LIB_TREE_MODEL_ADAPTER`, `SYMBOL_PREVIEW_WIDGET`, footprint preview/select, "keep symbol" and "place all units" checkboxes. ERC dialog (`eeschema/dialogs/dialog_erc.h`): `RC_TREE_MODEL` over `RC_ITEMS_PROVIDER`, severity filters, exclusions. Simulator (`eeschema/sim/simulator_frame_ui.h`): `m_plotNotebook` of `SIM_TAB`/`SIM_PLOT_TAB` (an `mpWindow` with `TRACE`, `CURSOR`, `SMITH_TRACE`), a signals grid with dynamic "Cursor n" columns, measurements grid, `TUNER_SLIDER`s via `AddTuner( sheetPath, symbol )`, workbook load/save; traces typed by `SIM_TRACE_TYPE { SPT_VOLTAGE, SPT_CURRENT, SPT_AC_PHASE, SPT_AC_GAIN, SPT_POWER, ... SPT_TIME, SPT_LIN_FREQUENCY, SPT_LOG_FREQUENCY, SPT_SWEEP }`.

**PCB editor** (`pcbnew/toolbars_pcb_editor.cpp`). Right palette: select (rect/lasso), `localRatsnestTool`, `placeFootprint`, route group (`routeSingleTrack`, `routeDiffPair`, highlight/shove/walkaround modes), tuning (`tuneSingleTrack`, `tuneDiffPair`, `tuneSkew`), `drawVia`/`drawViaStitchArea`, `drawZone`, `drawRuleArea`, graphics (line, arc, rectangle, circle/ellipse, geometric constraints `addConstraintCoincident … addConstraintAngular`, polygon, bezier, image, text, table, dimensions, barcode), delete, origins, `placePoint`, `measureTool`. Left palette: grid, polar coords, units, cursor style, line mode, `toggleAutoConstraints`, `showRatsnest`, `highContrastMode`, `toggleNetHighlight`, zone/pad/via/track display modes, `showLayersManager`, `showProperties`. Appearance manager (`pcbnew/widgets/appearance_controls.h`): tabs Layers / Objects / Nets (`NET_GRID_TABLE`), per-row `APPEARANCE_SETTING` (swatch, visibility, opacity sliders), `LAYER_PRESET`s, `VIEWPORT`s, net-color mode, ratsnest visibility, flip board. Selection filter (`PCB_SELECTION_FILTER_OPTIONS`): `lockedItems, footprints, text, tracks, vias, pads, graphics, zones, keepouts, dimensions, points, gridItems, otherItems`. DRC dialog holds three trees: markers, unconnected, footprint warnings. 3D viewer (`3d-viewer/3d_viewer/eda_3d_viewer_frame.h`): `EDA_3D_CANVAS`, `BOARD_ADAPTER`, `CAMERA`/`TRACK_BALL`, `APPEARANCE_CONTROLS_3D`, OpenGL/raytracing capture, STEP/GLB/VRML export.

**Keyboard-driven placement.** Hotkeys are `AS_GLOBAL` actions with `AF_ACTIVATE`: the key arms the tool, a ghost item follows the cursor, click commits, the tool stays armed, Esc cancels; edits act on the item under the cursor without prior selection. Schematic defaults (`sch_actions.cpp`): `A` symbol, `W` wire, `B` bus, `Z` bus entry, `L` label, `Ctrl+L` global label, `H` hierarchical label, `J` junction, `Q` no-connect, `T` text, `M` move, `R`/`Shift+R` rotate, `X`/`Y` mirror, `E` properties, `U`/`V`/`F` edit archive/reference/value/footprint, `O` autoplace fields, `Insert` repeat last, `Alt+Backspace` leave sheet. PCB (`pcb_actions.cpp`): `X` route, `6` diff pair, `7` tune, `M` move, `D` drag, `R`/`Shift+R` rotate, `F` flip, `E` properties, `W`/`Shift+W` track width, `'`/`\` via size, `` ` `` highlight net, `PgUp`/`PgDn` top/bottom layer, `+`/`-` next/prev layer, `Backspace` undo last segment, `Ctrl+E` continue from end, `Ctrl+B` unfill zones, `Ctrl+Shift+K` rule area, `Ctrl+Shift+X` via.

## 6. Abstractions to lift for a Lean-based mathematics CAD

1. **Three linked views of one component.** Symbol (`LIB_SYMBOL`), footprint (via the `Footprint` field `LIB_ID`), 3D body (`FP_3DMODEL`) live in separate libraries joined by string keys and a back-link (`m_path`). A Complex Parametron should likewise have presentation, lattice realization and rendered body as three artifacts related by typed references.
2. **Definition vs instance with flattening.** `LIB_SYMBOL` (possibly `extends` a parent) is flattened into `SCH_SYMBOL::m_part`; instance fields override — a parametrized definition specialized per placement.
3. **Typed ports make composition checkable.** The `ELECTRICAL_PINTYPE` × `PIN_ERROR` matrix plus the drive lattice (`NOC < NPI < NET_NC < NOD < DRV`) makes "is this net well-formed?" a table lookup; port kinds on Parametrons can carry an analogous decidable relation.
4. **Nets are derived, never authored.** `CONNECTION_GRAPH` computes equivalence classes from geometry + labels and picks a driver by `PRIORITY`; transported action on a lattice should be computed from placements with an explicit priority lattice for naming.
5. **Per-path identity for reuse.** One `SCH_SCREEN`, many `SCH_SHEET`s; identity = `KIID_PATH`; per-instance archive/reference/unit; connections indexed by `SCH_SHEET_PATH` — instancing without copying via context-indexed attributes.
6. **Checked interface of a sub-design.** `SCH_SHEET_PIN` must match an inner `SCH_HIERLABEL`, else `ERCE_HIERACHICAL_LABEL`; a sub-lattice's boundary is a typed port list.
7. **Structured names as bundles.** Buses `A[0..7]`, `N{X Y}`, aliases expand to member connections whose membership is checked at joins.
8. **Layered optional attributes with provenance.** `NETCLASS` values are `std::optional<int>` composed by priority, each remembering its source (`*Parent`) — a model for parameter inheritance where every resolved value names the rule that supplied it.
9. **Declarative rules over typed items.** `DRC_RULE` = condition over `A`, `B`, `L` + `min/opt/max` constraint + severity, later rules win; a rule layer separate from data, compiled once, evaluated per item pair.
10. **Strata as a first-class axis.** `PCB_LAYER_ID` (even copper / odd technical) and per-item `LSET`; a lattice CAD can treat "which sheets does this element occupy" identically.
11. **Stable UUID identity + path.** Every item has a v4 `KIID`; instance context is a UUID chain; files diff cleanly and cross-tool links survive edits.
12. **Staged commits with pre-images.** `COMMIT` stages add/remove/modify with cloned pre-images and pushes atomically, then re-derives connectivity — the right shape for undo plus incremental recomputation.
13. **Actions as named, scoped, hotkeyed events; tools as coroutines.** One `TOOL_ACTION` table drives menus, toolbars and hotkeys; interactive tools are event-driven state machines.
14. **Design semantics vs view state.** `.kicad_pro` vs `.kicad_prl`, library tables vs libraries: keep proof-relevant data apart from presentation.
15. **External dynamics as a field-level binding.** `Sim.Device/Type/Pins/Params` map ports to an enumerated model kind (`DEVICE_T`/`TYPE`) with a two-way serializer, leaving the schematic itself static.

**What KiCad does not model.** The schematic has no dynamics of its own — behaviour exists only through SPICE export (`SPICE_GENERATOR`) and back-annotated operating points (`m_operatingPoint`, `LAYER_OP_VOLTAGES`). There is no constraint solver in the schematic (the board has new geometric `PCB_CONSTRAINT`s, but nets, values and parameters are never solved). Nets are undirected equivalence classes; pin types are ERC hints, not a flow semantics; there is no time, causality or composition algebra. Geometry is 2.5D: stacked planar layers plus imported 3D bodies for viewing and export only. Fields are strings (only `${VAR}` substitution), so symbols are not parametric. ERC/DRC are heuristics with per-rule severities and manual exclusions, not proof obligations, and library drift is detected (`ERCE_LIB_SYMBOL_MISMATCH`) but not reconciled.
