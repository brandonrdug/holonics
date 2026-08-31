# FreeCAD and LibreCAD: data types and machinery conventions

Snapshot: shallow sparse clones taken 2026-08-30 into `$S/refs/freecad` (FreeCAD `main` @ 3b2c969) and `$S/refs/librecad` (LibreCAD `master` @ a05b426); paths are relative to those roots. The FreeCAD wiki (File_Format_FCStd, Topological_naming_problem, Expressions) returned an Anubis "Access Denied", so everything here is taken from source.

## Part A. FreeCAD

### A1. Identity

Parametric 3D CAD kernel (`src/App`, GUI-free) over OpenCASCADE, with `src/Gui` and workbenches under `src/Mod/*`. The App layer is a property graph: every model element is a `DocumentObject` holding typed `Property` members; the `Document` recomputes objects in topological order of link/expression dependencies; every mutation is captured in a `Transaction`; the persistent form is `.FCStd` (zip of XML + BREP).

### A2. Core data types

**Property** (`src/App/Property.h:63`): `class AppExport Property: public Base::Persistence` with `std::bitset<32> StatusBits`, pure virtual `Copy()`/`Paste()` (used by undo), `hasSetValue()/aboutToSetValue()` hooks, `getID()`. `enum Status`: `Touched=0, Immutable=1, ReadOnly=2, Hidden=3, Transient=4, Output=7, LockDynamic=8, NoModify=9, NoRecompute=11, Input=12, Ordered=13, EvalOnRestore=14, Busy=15, CopyOnChange=16, ..., PropDynamic=21 ... PropInput=28, User1..User4=29..32`.

**PropertyContainer** (`src/App/PropertyContainer.h:299`): a static per-class `PropertyData` table registered by `PROPERTY_HEADER(_class_)` (line 762) plus `DynamicProperty` for runtime-added members. `enum PropertyType { Prop_None=0, Prop_ReadOnly=1, Prop_Transient=2, Prop_Hidden=4, Prop_Output=8, Prop_NoRecompute=16, Prop_NoPersist=32, Prop_Input=64 }` (line 57). API: `getPropertyByName`, `getPropertyMap`, `getPropertyList`, `getPropertyType`, `addDynamicProperty`, virtual `onChanged(const Property*)`, `onBeforeChange`.

**Property catalogue** (all `class AppExport`):
- `PropertyStandard.h`: `PropertyInteger, PropertyPath, PropertyEnumeration, PropertyIntegerConstraint, PropertyPercent, PropertyIntegerList, PropertyIntegerSet, PropertyMap, PropertyFloat, PropertyFloatConstraint, PropertyPrecision, PropertyFloatList, PropertyString, PropertyUUID, PropertyFont, PropertyStringList, PropertyBool, PropertyBoolList, PropertyColor, PropertyColorList, PropertyMaterial, PropertyMaterialList`.
- `PropertyUnits.h`: `PropertyQuantity: public PropertyFloat` (line 44), `PropertyQuantityConstraint`, then 61 dimensioned subclasses (`PropertyAcceleration, PropertyAngle, PropertyArea, PropertyDensity, PropertyDistance, PropertyElectricalCapacitance, ... PropertyLength, PropertyMass, PropertyPressure, PropertySpeed, PropertyStress, PropertyTemperature, PropertyTime, PropertyVolume, PropertyWork, PropertyYoungsModulus`).
- `PropertyGeo.h`: `PropertyVector, PropertyVectorDistance, PropertyPosition, PropertyDirection, PropertyVectorList, PropertyMatrix, PropertyPlacement, PropertyPlacementLink, PropertyPlacementList, PropertyRotation, PropertyGeometry, PropertyComplexGeoData`.
- `PropertyLinks.h`: `PropertyLinkBase: public Property, public ScopedLink` (line 112); `PropertyLink`, `PropertyLinkList`, `PropertyLinkSub` (object plus sub-element names), `PropertyLinkSubList`, each with `Child/Global/Hidden` scope variants; cross-document `PropertyXLink, PropertyXLinkSub, PropertyXLinkSubList, PropertyXLinkList, PropertyXLinkContainer`.
- `PropertyFile.h`: `PropertyFile, PropertyFileIncluded`; `PropertyPythonObject.h`; `PropertyExpressionEngine.h`: `PropertyExpressionContainer: public PropertyXLinkContainer`, `PropertyExpressionEngine`.

**DocumentObject** (`src/App/DocumentObject.h:141`): `class AppExport DocumentObject: public App::TransactionalObject` with four static properties, verbatim:

```cpp
PropertyString Label;
PropertyString Label2;
PropertyExpressionEngine ExpressionEngine;
PropertyBool Visibility;
```

`enum ObjectStatus` (line 61): `Touch=0, Error=1, New=2, Recompute=3, Restore=4, Remove=5, PythonCall=6, Destroy=7, Enforce=8, Recompute2=9, PartialObject=10, PendingRecompute=11, ObjImporting=13, NoTouch=14, GeoExcluded=15, Expand=16, NoAutoExpand=17, PendingTransactionUpdate=18, RecomputeExtension=19, TouchOnColorChange=20, Freeze=21`, held in `std::bitset<32> StatusBits`. Graph API: `getOutList()` (objects I link to), `getInList()` (objects linking to me), `getOutListProp()/getInListProp()` returning `DepEdge{DocumentObject* fromObj; std::string fromProp; DocumentObject* toObj; std::string toProp;}` (`DepEdge.h:56-105`), `enum OutListOption { OutListNoExpression=1, OutListNoHidden=2, OutListNoXLinked=4 }`. Recompute API: `touch()`, `isTouched()`, `enforceRecompute()`, `mustRecompute()`, `virtual short mustExecute() const`, `purgeTouched()`, `isError()`, protected `virtual DocumentObjectExecReturn* recompute()` and `execute()`. Success is `DocumentObject::StdReturn` (a null pointer); failure is a heap `DocumentObjectExecReturn { std::string Why; DocumentObject* Which; }` (line 100).

**GeoFeature** (`GeoFeature.h:52`): `DocumentObject` plus `PropertyPlacement Placement`, `getPropertyOfGeometry()`, `getElementName(name, ElementNameType)`, static `resolveElement(...)`. `App::Placement: public GeoFeature` and `App::Origin: public App::LocalCoordinateSystem` are ordinary objects, so origin planes and axes are DAG nodes.

**Extension** (`Extension.h:137`): mixin registered by `EXTENSION_PROPERTY_HEADER`, attached via `initExtension(ExtensionContainer*)`, with `extensionOnChanged`, `extensionGetPropertyByName`, `extensionSave/Restore`; `GroupExtension`, `GeoFeatureGroupExtension`, `OriginGroupExtension`, `SuppressibleExtension` are built this way.

**Application** (`Application.h`): singleton with `newDocument/openDocument/closeDocument/getActiveDocument`, `setActiveTransaction(name)` / `closeActiveTransaction(TransactionCloseMode)`, `GetParameterGroupByPath("User parameter:BaseApp/Preferences/...")`, `addImportType/addExportType(filter, module)`, signals `signalNewDocument, signalDeleteDocument, signalActiveDocument`.

### A3. Dependency and recompute machinery

`class AppExport Document: public PropertyContainer` (`Document.h:103`). `enum Status` (line 110): `SkipRecompute=0, KeepTrailingDigits=1, Closable=2, Restoring=3, Recomputing=4, PartialRestore=5, Importing=6, PartialDoc=7, AllowPartialRecompute=8, TempDoc=9, RestoreError=10, LinkStampChanged=11, IgnoreErrorOnRecompute=12, RecomputeOnRestore=13, MigrateLCS=14`. The dependency graph is a Boost `adjacency_list` (`DependencyList`, `Vertex`) built by `buildDependencyList()` (`Document.cpp:2565`) from `obj->getOutListProp(op)` edges; `getDependencyList(objs, options)` with `enum DependencyOption { DepSort=1, DepNoXLinked=2, DepNoCycle=4 }` (`Document.h:1100`) runs `boost::topological_sort` (`Document.cpp:2679`), falling back to strongly connected components on a cycle. `Document::topologicalSort()` (line 3241) is a Kahn-style in-degree peel that logs `"cyclic dependency detected (no root object)"`; `Document::mustExecute()` (line 4107) reuses the builder with a `touched` out-flag.

`Document::recompute(objs, force, hasError, options)` (`Document.cpp:2843`) takes `getDependencyList(objs.empty() ? d->objectArray : objs, DepSort | options)`, marks each `PendingRecompute`, and runs at most two passes (`// maximum two passes to allow some form of dependency inversion`): for each object with `mustRecompute()` it calls `_recomputeFeature(obj)`; on failure it does `obj->getInListEx(filter, true); filter.insert(obj);` to skip every dependent, otherwise `obj->purgeTouched()` and `inObjIt->enforceRecompute()` for each `getInList()` member. `_recomputeFeature` (line 3252) is the three-phase object step:

```cpp
returnCode = Feat->ExpressionEngine.execute(PropertyExpressionEngine::ExecuteNonOutput);
if (returnCode == DocumentObject::StdReturn) {
    returnCode = Feat->recompute();
    if (returnCode == DocumentObject::StdReturn) {
        returnCode = Feat->ExpressionEngine.execute(PropertyExpressionEngine::ExecuteOutput);
    }
}
```

Expressions bound to inputs run, then `execute()`, then expressions bound to outputs; on failure `returnCode->Which = Feat; d->addRecomputeLog(returnCode)` marks the object `Error` and its recursive InList is filtered out of the pass. Fine-grained mode uses `DepEdge` property names (`obj->touchedProps.contains(propTo)`) to recompute only dependents that read a changed property.

**Transactions** (`Transactions.h`): `class AppExport Transaction: public Base::Persistence` with `apply(Document&, bool forward)`, `addObjectNew/addObjectDel/addObjectChange(obj, prop)`; per-object `TransactionObject` stores `Property::Copy()` snapshots and replays via `applyNew/applyDel/applyChn(doc, obj, forward)`. `Document` API: `openTransaction(name)`, `commitTransaction()`, `abortTransaction()`, `undo(id)`, `redo(id)`, `setMaxUndoStackSize(20)`, `isPerformingTransaction()`; `AutoTransaction.h` is the RAII guard. Observers hook `App::MainThreadSignal`s such as `signalChangedObject, signalRecomputedObject, signalCommitTransaction, signalUndo, signalBecameStable` (`Document.h:207-282`).

**Expressions** (`src/App/Expression.y`, `Expression.l`, `ExpressionParser.h`). Bison grammar; AST classes `UnitExpression, NumberExpression, ConstantExpression, OperatorExpression, ConditionalExpression, FunctionExpression, VariableExpression, PyObjectExpression, StringExpression, RangeExpression` (`ExpressionParser.h:79-593`). Verbatim productions:

```yacc
unit_num: num unit_exp %prec NUM_AND_UNIT { $$ = new OperatorExpression(DocumentObject, $1, OperatorExpression::UNIT, $2); }
exp: ... | identifier            { $$ = new VariableExpression(DocumentObject, $1); }
       | exp '?' exp ':' exp     { $$ = new ConditionalExpression(DocumentObject, $1, $3, $5); }
       | FUNC  args ')'          { $$ = new FunctionExpression(DocumentObject, $1.first, std::move($1.second), $2);}
range: id_or_cell ':' id_or_cell { $$ = new RangeExpression(DocumentObject, $1, $3); }
```

Units are lexer tokens carrying a `Quantity` scaler (`"mm" ... yylval.quantity.scaler = Quantity::MilliMetre; ... return UNIT;`, `Expression.l:187`), so `10 mm * 2` is dimensionally typed at evaluation. `OperatorExpression::Operator` = `ADD SUB MUL DIV MOD POW EQ NEQ LT GT LTE GTE UNIT NEG POS`. `FunctionExpression::Function` covers scalar math (`ABS ... TRUNC`), vectors (`VANGLE, VCROSS, VDOT, VLINEDIST, VNORMALIZE, ...`), matrix/placement (`MINVERT, MROTATE, MTRANSLATE, PLACEMENT, ROTATION, VECTOR, MATRIX`), aggregates (`AVERAGE, COUNT, MAX, MIN, STDDEV, SUM`), and `HIDDENREF` ("hidden reference that has no dependency check"). `ObjectIdentifier` (`ObjectIdentifier.h:127`) is a path `Document#Object.Property.component...` with `Component::typeEnum { SIMPLE, MAP, ARRAY, RANGE }`. `PropertyExpressionEngine` holds `std::map<ObjectIdentifier, ExpressionInfo> expressions`, `setValue(path, expr)`, `execute(ExecuteOption {ExecuteAll, ExecuteOutput, ExecuteNonOutput, ExecuteOnRestore}, bool* touched)`, `computeEvaluationOrder()`, and `renameObjectIdentifiers()` so label renames rewrite bound expressions.

### A4. Constraint solver: Sketcher and planegcs

`class SketcherExport SketchObject: public Part::Part2DObject` (`src/Mod/Sketcher/App/SketchObject.h:82`) declares `Part::PropertyGeometryList Geometry; Sketcher::PropertyConstraintList Constraints; App::PropertyLinkSubList ExternalGeometry; App::PropertyIntegerList ExternalTypes; Part::PropertyGeometryList ExternalGeo; App::PropertyBool FullyConstrained;` (lines 101-107). `Sketcher::Constraint` (`Constraint.h:105`) is a record `{ConstraintType Type; double Value; int First, Second, Third; PointPos FirstPos, SecondPos, ThirdPos; std::string Name; bool isDriving, isInVirtualSpace, isActive;}` with `enum ConstraintType : int` (line 52), complete:

```
None=0, Coincident=1, Horizontal=2, Vertical=3, Parallel=4, Tangent=5, Distance=6, DistanceX=7, DistanceY=8,
Angle=9, Perpendicular=10, Radius=11, Equal=12, PointOnObject=13, Symmetric=14, InternalAlignment=15,
SnellsLaw=16, Block=17, Diameter=18, Weight=19, Group=20, Text=21, NumConstraintTypes
```

and `enum InternalAlignmentType` (line 79): `Undef=0, EllipseMajorDiameter=1, EllipseMinorDiameter=2, EllipseFocus1=3, EllipseFocus2=4, HyperbolaMajor=5, HyperbolaMinor=6, HyperbolaFocus=7, ParabolaFocus=8, BSplineControlPoint=9, BSplineKnotPoint=10, ParabolaFocalAxis=11`.

`Sketcher::Sketch` (`Sketch.h:41`) lowers this to planegcs: `enum GeoType {None, Point, Line, Arc, Circle, Ellipse, ArcOfEllipse, ArcOfHyperbola, ArcOfParabola, BSpline}` (line 562; comments give parameter counts, e.g. `Line = 2, // 2 Points(start,end), 4 Parameters(x1,y1,x2,y2)`), and members `std::vector<GeoDef> Geoms; GCS::System GCSsys; std::vector<double*> Parameters, DrivenParameters, FixParameters; std::vector<GCS::Point> Points; ... std::vector<GCS::BSpline> BSplines;` (lines 607-645). `setUpSketch()` ends with `GCSsys.declareUnknowns(Parameters); GCSsys.declareDrivenParams(DrivenParameters); GCSsys.initSolution(defaultSolverRedundant); GCSsys.getConflicting(Conflicting); GCSsys.getRedundant(Redundant); GCSsys.getPartiallyRedundant(PartiallyRedundant); return GCSsys.dofsNumber();` (`Sketch.cpp:356-434`). `Sketch::internalSolve` uses `GCSsys.solve(isFine, GCS::DogLeg)` while dragging (`isInitMove`) and otherwise `BFGS`/`LevenbergMarquardt`/`DogLeg` per `defaultSolver`; on `GCS::Success` it runs `GCSsys.applySolution(); updateGeometry();` and reverts with `GCSsys.undoSolution()` when OCC rejects the geometry (`"Invalid solution from %s solver."`).

`SketchObject::execute()` (`SketchObject.cpp`) calls `rebuildExternalGeometry(); Constraints.acceptGeometry(...); int err = this->solve(true);` and maps `-4 -> "Over-constrained sketch"`, `-3 -> "Sketch with conflicting constraints"`, `-2 -> "Sketch with redundant constraints"`, `-5 -> "Sketch with malformed constraints"` to `DocumentObjectExecReturn`.

planegcs (`src/Mod/Sketcher/App/planegcs/`): geometry is a set of pointers into a flat parameter vector, `class Point { double* x; double* y; }`, `Line { Point p1, p2; }`, `Circle { Point center; double* rad; }`, `Arc: Circle { double* startAngle, *endAngle; Point start, end; }`, `Ellipse`, `Hyperbola`, `Parabola` (+ arcs), `BSpline: Curve` (`Geo.h:39-358`). `class Constraint` (`Constraints.h:113`) holds `VEC_pD origpvec, pvec; double scale; int tag; bool driving; Alignment internalAlignment;` and virtuals `error()`, `grad(double*)`, `errorgrad(err, grad, param)`, `maxStep()`, `rescale()`. Solver-level `enum ConstraintType` (`Constraints.h`) has 37 kinds: `Equal, Difference, P2PDistance, P2PAngle, P2LDistance, PointOnLine, PointOnPerpBisector, Parallel, Perpendicular, L2LAngle, MidpointOnLine, TangentCircumf, PointOnEllipse, TangentEllipseLine, InternalAlignmentPoint2Ellipse, EqualMajorAxesConic, EllipticalArcRangeToEndPoints, AngleViaPoint, Snell, CurveValue, PointOnHyperbola, InternalAlignmentPoint2Hyperbola, PointOnParabola, EqualFocalDistance, EqualLineLength, CenterOfGravity, WeightedLinearCombination, SlopeAtBSplineKnot, PointOnBSpline, C2CDistance, C2LDistance, P2CDistance, AngleViaPointAndParam, AngleViaPointAndTwoParams, AngleViaTwoPoints, ArcLength` (this list is the enum, complete). `GCS::System` (`GCS.h:111-144`) keeps `VEC_pD plist, pdrivenlist; std::map<Constraint*, VEC_pD> c2p; std::vector<SubSystem*> subSystems, subSystemsAux; std::vector<MAP_pD_pD> reductionmaps; int dofs; VEC_I conflictingTags, redundantTags, partiallyRedundantTags; bool hasDiagnosis, isInit;`. Enums verbatim:

```cpp
enum Algorithm { BFGS = 0, LevenbergMarquardt = 1, DogLeg = 2 };
enum SolveStatus { Success = 0, Converged = 1, Failed = 2, SuccessfulSolutionInvalid = 3 };
enum QRAlgorithm { EigenDenseQR = 0, EigenSparseQR = 1 };
```

Entry points: `int solve(bool isFine = true, Algorithm alg = DogLeg, bool isRedundantsolving = false)`, `solve(SubSystem* subsysA, SubSystem* subsysB, ...)` (two-subsystem mode for dragging), `int diagnose(Algorithm)` (QR rank analysis of the Jacobian producing `dofs` and conflicting/redundant/partially-redundant tags), `applySolution()/undoSolution()`, `clearByTag(int)`, and roughly 90 builders such as `addConstraintP2PDistance(Point& p1, Point& p2, double* distance, int tagId = 0, bool driving = true)`. `SubSystem` (`SubSystem.h:38`) is the numeric kernel: `int psize, csize; VEC_D pvals; double error(); calcResidual(Eigen::VectorXd&); calcJacobi(Eigen::MatrixXd&); calcGrad(); maxStep(); applySolution();`. Equality constraints are eliminated through `reductionmaps` before solving; each independent parameter partition becomes its own `SubSystem`.

### A5. Part, PartDesign, TechDraw, Spreadsheet

- **TopoShape** (`src/Mod/Part/App/TopoShape.h:285`): `class PartExport TopoShape: public Data::ComplexGeoData` wrapping `TopoDS_Shape _Shape` plus `long Tag` and `App::StringHasherRef Hasher`. Sub-elements are addressed by `IndexedName` strings (`"Edge1"`, `"Face345"`, `src/App/IndexedName.h:49`) through `getSubShape(const char* Type)`, `shapeTypeAndIndex(name)`, `findShape`, `findAncestor`. Every `makeElement*` (`Fuse/Cut/Prism/Revolve/Fillet/Offset/Loft/...`) takes an `op` code and calls `mapSubElement(const TopoShape& other, const char* op = nullptr, bool forceHasher = false)` / `makeShapeWithElementMap(shape, const Mapper& mapper, sources, op)` (lines 1709, 1875) with `MapperMaker`/`MapperHistory` (over `BRepBuilderAPI_MakeShape::Generated/Modified()`) to derive a `MappedName` per new `IndexedName`. Encoding constants (`src/App/ElementNamingUtils.h:52-92`): `ELEMENT_MAP_PREFIX = ";"`, `MISSING_PREFIX = "?"`, `POSTFIX_TAG = ";:H"`, `POSTFIX_MOD = ";:M"`, `POSTFIX_GEN = ";:G"`, `POSTFIX_UPPER = ";:U"`, `POSTFIX_LOWER = ";:L"`, `POSTFIX_DUPLICATE = ";D"`. `Data::ElementMap` (`ElementMap.h:80`) stores `std::map<MappedName, IndexedName> mappedNames` plus `hashElementName/dehashElementName`. This is the topological-naming mitigation: links persist the mapped name and `GeoFeature::resolveElement()` translates it back to whatever `Face7` currently is.
- **PartDesign** `Body: public Part::BodyBase` (`Body.h:41`); `BodyBase` (`src/Mod/Part/App/BodyBase.h`) is `Part::Feature` plus `App::OriginGroupExtension` with `App::PropertyLink Tip; App::PropertyLink BaseFeature;` and an ordered `Group`. Each `PartDesign::Feature` has `App::PropertyLink BaseFeature; App::PropertyLinkHidden _Body;` (`Feature.h:67-68`), so the feature chain is a linked list; `Body::addObject` inserts after `Tip`, `getPrevSolidFeature/getNextSolidFeature/isAfterInsertPoint` walk it, and the body's shape is the `Tip`'s shape.
- **TechDraw** `DrawPage: public App::DocumentObject` (`DrawPage.h:37`): `PropertyLinkList Views; PropertyLink Template; PropertyBool KeepUpdated; PropertyFloatConstraint Scale; PropertyEnumeration ProjectionType; PropertyInteger NextBalloonIndex;`. `DrawView` (`DrawView.h:46`): `PropertyDistance X, Y; PropertyBool LockPosition; PropertyFloatConstraint Scale; PropertyEnumeration ScaleType; PropertyAngle Rotation; PropertyString Caption;`. `DrawViewPart: public DrawView, public CosmeticExtension` (`DrawViewPart.h:107`): `PropertyLinkList Source; PropertyXLinkList XSource; PropertyVector Direction, XDirection; PropertyBool Perspective; PropertyDistance Focus; PropertyBool HardHidden, SmoothVisible, SeamVisible, ...;` with `getSourceShape()` feeding `buildGeometryObject()` (HLR projection to 2D): a drawing is another DAG node downstream of the solids.
- **Spreadsheet** `Sheet: public App::DocumentObject` (`Sheet.h:76`) with `PropertySheet cells; PropertyColumnWidths columnWidths; PropertyRowHeights rowHeights;`. `Cell` (`Cell.h:52`) = `{App::CellAddress address; App::ExpressionPtr expression; std::string alias;}` with flags `EXPRESSION_SET, STYLE_SET, ALIAS_SET`. `Sheet::getPropertyByName` is overridden so `Sheet.B2` or `Sheet.Length` (alias) resolve to dynamically created `PropertySpreadsheetQuantity` properties; other objects bind expressions to them and the sheet is a regular recompute node (`recomputeCell`, `recomputeCells(Range)`).

### A6. File format `.FCStd`

`Document::saveToFile` (`Document.cpp:2023`) opens a `Base::ZipWriter`, `putNextEntry("Document.xml")`, streams `Document::Save`, then `writer.writeFiles()` flushes the side files each property registered via `Property::getFileName` (`PartShape.brp` per `PropertyPartShape`, `StringHasher.Table`); the Gui layer adds `GuiDocument.xml` and `thumbnails/Thumbnail.png`. Minimal `Document.xml`, reconstructed from the emitters `Document::Save` (`Document.cpp:1120`), `PropertyContainer::Save` (`PropertyContainer.cpp:256-320`), `writeObjectType/writeObjectDeps/writeObjectData` (`Document.cpp:1395-1480`), with element and attribute names verbatim:

```xml
<?xml version='1.0' encoding='utf-8'?>
<Document SchemaVersion="4" ProgramVersion="1.1R40000" FileVersion="1" StringHasher="1">
  <Properties Count="0"></Properties>
  <Objects Count="2" Dependencies="1">
    <ObjectDeps Name="Box" Count="0"/>
    <ObjectDeps Name="Fillet" Count="1"><Dep Name="Box"/></ObjectDeps>
    <Object type="Part::Box" name="Box" id="1" />
    <Object type="Part::Fillet" name="Fillet" id="2" />
  </Objects>
  <ObjectData Count="2">
    <Object name="Box">
      <Properties Count="2">
        <Property name="Length" type="App::PropertyLength"><Float value="10"/></Property>
        <Property name="Shape" type="Part::PropertyPartShape"><Part file="PartShape.brp"/></Property>
      </Properties>
    </Object>
  </ObjectData>
</Document>
```

The `<Objects>` block serialises the out-list (`ObjectDeps`/`Dep`) so partial loading can skip subgraphs; `Touched="1"`, `Invalid="1"`, `Error="..."`, `Freeze="1"` on `<Object>` persist `ObjectStatus`; each `<Property>`'s inner tag is that class's own `Save()`.

### A7. UI anatomy

(`src/Gui` is not in this checkout; components are named from their App-side hooks.) A `QMainWindow` with an MDI area of Coin3D **3D views** plus docks: the **combo view** stacks the **tree view** (expansion from `ObjectStatus::Expand`, touched/error overlays from `StatusBits`, children claimed via `GroupExtension`/`Tip`) over the **property editor** (tabs "View"/"Data"; rows from `PropertyContainer::getPropertyMap()` filtered by `Status::Hidden`, greyed by `ReadOnly`, expression-bound cells flagged from `ExpressionEngine`). The **task panel** replaces the combo view during an edit (the sketcher panel reports `SketchObject::getLastDoF/getLastHasConflict`). The **report view** shows `Base::Console` output including `addRecomputeLog` messages; the **Python console** echoes every GUI command as Python (`App.ActiveDocument.addObject("Part::Box","Box")`, `doc.recompute()`). The **workbench selector** swaps toolbars/menus per `src/Mod/<X>/Gui`; all subscribe to `signalChangedObject`/`signalRecomputed`.

## Part B. LibreCAD

### B1. Identity

2D DXF-native drafting editor (fork of QCad 2.0.5 CE). Model = a tree of `RS_Entity` inside `RS_EntityContainer`s rooted at an `RS_Graphic`; editing = a stack of `RS_ActionInterface` state machines fed by mouse, coordinate and command-line events; persistence = DXF/DWG through libdxfrw (`RS_FilterDXFRW`). No parametrics: geometry is explicit coordinates and "regeneration" is `update()` on composite entities (inserts, texts, dimensions, hatches, splines).

### B2. Core data types

`class RS_Entity : public RS_Undoable, public LC_Drawable` (`librecad/src/lib/engine/document/entities/rs_entity.h:56`). Key API: `virtual RS_Entity* clone() const = 0; virtual RS2::EntityType rtti() const; RS_EntityContainer* getParent() const; getGraphic()/getBlock()/getInsert()/getDocument(); RS_Layer* getLayer(bool resolve = true) const; RS_Pen getPen(bool resolve = true) const; getPenResolved(); virtual bool isContainer()/isAtomic() const = 0; isSelected(); isVisible(); isLocked(); getMin()/getMax(); virtual RS_Vector getStartpoint()/getEndpoint()/getCenter() const; getRadius(); getLength(); getRefPoints(); RS_Vector getNearestEndpoint(const RS_Vector& coord, RS_Entity** entity = nullptr, double* dist = nullptr) const; getNearestPointOnEntity; getNearestCenter; getNearestMiddle(coord, dist, int middlePoints = 1); getNearestDist(double distance, coord, dist); getNearestRef; getNearestOrthTan; double getDistanceToPoint(coord, RS_Entity**, RS2::ResolveLevel, double solidDist); virtual void move/rotate/scale/mirror(...) = 0; stretch; shear; offset; virtual void update();`. Flags come from `RS_Flags` (`rs.h:58`): `FlagDeleted=1<<0, FlagVisible, FlagByLayer, FlagByBlock, FlagFrozen, FlagLocked, FlagInvalid, FlagSelected=1<<8, FlagClosed, FlagTemp, FlagProcessed, FlagHighlighted, FlagInVisualSnap`.

`enum RS2::EntityType : unsigned` (`rs.h:139`), complete:

```
EntityUnknown, EntityContainer, EntityBlock, EntityFontChar, EntityInsert, EntityGraphic, EntityPoint, EntityLine,
EntityPolyline, EntityVertex, EntityArc, EntityCircle, EntityEllipse, EntityHyperbola, EntitySolid,
EntityConstructionLine, EntityMText, EntityText, EntityDimAligned, EntityDimLinear, EntityDimRadial,
EntityDimDiametric, EntityDimAngular, EntityDimArc, EntityDimOrdinate, EntityTolerance, EntityDimLeader,
EntityHatch, EntityImage, EntityWipeout, EntityMLeader, EntitySpline, EntitySplinePoints, EntityParabola,
EntityOverlayBox, EntityPreview, EntityPattern, EntityOverlayLine, EntityRefPoint, EntityRefLine,
EntityRefConstructionLine, EntityRefArc, EntityRefCircle, EntityRefEllipse, EntitySnapMark, EntitySnapLine,
EntitySnapArc, EntitySnapCircle, EntitySnapConstructionLine, EntityDimArrowBlock
```

Every concrete entity is a `Data` struct plus a class (under `document/entities/`): `RS_LineData{RS_Vector startpoint, endpoint;}` / `RS_Line: LC_CachedLengthEntity`; `RS_ArcData{RS_Vector center; double radius, angle1, angle2; bool reversed;}`; `RS_CircleData{center, radius}`; `RS_EllipseData{center, majorP; double ratio, angle1, angle2; bool reversed, isArc;}`; `RS_SplineData{controlPoints; knotslist, weights; fitPoints}` (`RS_Spline: RS_EntityContainer`); `LC_SplinePointsData{bool closed, cut, useControlPoints; splinePoints, controlPoints}`; `RS_PolylineData: RS_Flags{startpoint, endpoint}` (`RS_Polyline: RS_EntityContainer` of lines/arcs with bulge); `RS_PointData{RS_Vector pos;}`; `RS_TextData{insertionPoint, secondPoint; double height, widthRel; QString text, style; double angle;}` (`RS_Text: RS_EntityContainer`; glyphs are `RS_Insert`s of font blocks); `RS_MTextData`; `RS_DimensionData: RS_Flags{definitionPoint, middleOfText; QString text, style; double angle; bool autoText;}` with subtype data `RS_DimLinearData{extensionPoint1, extensionPoint2, angle, obliqueAngle}`, `RS_DimAlignedData`, `RS_DimAngularData{definitionPoint1..4}`, `RS_DimRadialData{definitionPoint, leader}`, and `Diametric/Arc/Ordinate` variants; `RS_HatchData{bool solid; double scale, angle; QString pattern;}` (`RS_Hatch: RS_EntityContainer` of loops); `RS_ImageData{insertionPoint, uVector, vVector, size; QString file;}`; `RS_LeaderData` (`RS_Leader: RS_Dimension`); `LC_ParabolaData{m_focus, m_axis, m_vertex}`; `LC_HyperbolaData{center, majorP; ratio, angle1, angle2; reversed}`; `RS_ConstructionLineData{point1, point2}`.

Containers and document: `RS_EntityContainer: RS_Entity` (`container/rs_entitycontainer.h:40`) owns `QList<RS_Entity*> m_entities; bool m_autoUpdateBorders, m_autoDelete;` with `addEntity/insertEntity/removeEntity/clear/count/firstEntity(RS2::ResolveLevel)/nextEntity/entityAt`, `getNearestEntity(coord, dist, ResolveLevel)`, `getNearestIntersection`, `optimizeContours`; `enum ResolveLevel { ResolveNone, ResolveAllButInserts, ResolveAllButTexts, ResolveAll }` controls descent into composites. `RS_Document: RS_EntityContainer, RS_Undo` (`rs_document.h:128`) adds `getLayerList/getBlockList/getDimStyleList/getViewList/getUCSList/getTextStyleList`, `getActivePen/setActivePen`, `isModified`, `startUndoCycle/endUndoCycle`. `RS_Graphic: RS_Document` (`rs_graphic.h:73`) owns `RS_LayerList m_layerList; RS_BlockList m_blockList; RS_VariableDict m_variableDict; LC_ViewList m_namedViewsList; LC_UCSList m_ucsList; LC_DimStylesList m_dimstyleList; LC_TextStyleList m_textStyleList; RS2::FormatType m_formatType; QString m_filename;` plus `getUnit()/setUnit(RS2::Unit)`, `addVariable(key, value, code)` (DXF header `$VAR`s), paper settings, `getCurrentUCS()`.

Layers and blocks: `RS_LayerData{QString name; RS_Pen pen; bool frozen, locked, print, construction, visibleInLayerList;}` (`layers/rs_layer.h:40`); `RS_LayerList{QList<RS_Layer*>; add/remove/edit/find/activate/toggle/toggleLock/togglePrint/freezeAll/lockAll; addListener(RS_LayerListListener*)}`. `RS_BlockData{QString name; RS_Vector basePoint; int insUnits; bool frozen;}`; `RS_Block: RS_Document` (`blocks/rs_block.h:70`), so a block is a whole sub-document; `RS_BlockList{activate/add/remove/rename/find/newName/toggle}`. `RS_InsertData{QString name; RS_Vector insertionPoint, scaleFactor; double angle; int cols, rows; RS_Vector spacing; RS_BlockList* blockSource; RS2::UpdateMode updateMode;}` and `RS_Insert: RS_EntityContainer` (`entities/rs_insert.h:139`) whose `update()` clones the block's entities (`getBlockForInsert()`) transformed by insertion point, scale and angle into its own child list: an insert is a cached instantiation, and `ByBlock` pens resolve through `getPenResolved()`.

Primitives: `RS_Vector{double x, y, z; bool valid;}` (`rs_vector.h:41`) with `static polar(rho, theta)`, `distanceTo`, `angleTo`, `magnitude`, chainable mutating `move/rotate/scale/mirror`, `dotP/crossP`; `RS_VectorSolutions` is a candidate-point list with `getClosest(coord)`. `RS_Pen: RS_Flags` (`rs_pen.h:43`) holds `RS_Color`, `RS2::LineWidth`, `RS2::LineType` with `isColorByLayer/isColorByBlock`; `enum LineType : short { LineByBlock=-2, LineByLayer=-1, NoPen=0, SolidLine=1, DotLine=2 ... }`; `enum LineWidth { Width00=0 ... Width23=211, WidthByLayer=-1, WidthByBlock=-2 }` (hundredths of a millimetre). `enum Unit { None=0, Inch=1, Foot=2, Mile=3, Millimeter=4, Centimeter=5, Meter=6, Kilometer=7, ..., Parsec=20 }` mirrors DXF `$INSUNITS`; `RS_Units` (`rs_units.h`) provides `convert(val, src, dest)`, `getFactorToMM`, `formatLinear`, `formatAngle`. `LC_Rect{minP(), maxP(), inArea(), intersects()}` (`entities/lc_rect.h`).

Undo: `RS_Undoable: RS_Flags` (`undo/rs_undoable.h:40`) with `undoRtti()` over `enum UndoableType { UndoableUnknown, UndoableEntity, UndoableLayer }`, `isDeleted()`, pure virtual `deletedStateChanged(bool undone)`. `RS_UndoCycle{std::set<RS_Undoable*> m_undoables;}`; `RS_Undo{std::vector<std::shared_ptr<RS_UndoCycle>> m_undoList; m_redoPointer; m_currentCycle; undo()/redo()/startUndoCycle()/endUndoCycle()/addUndoable()}`. Undo is "flip the deleted flag on every undoable in the cycle": entities are never destroyed while reachable from the undo list; `LC_UndoSection` is the RAII cycle guard.

### B3. Action machinery

`class RS_ActionInterface : public RS_Snapper, public LC_LateCompletionRequestor, public LC_ActionOptionsBase` (`lib/actions/rs_actioninterface.h:68`): an action *is* a snapper. State: `int m_status; bool m_finished; RS2::ActionType m_actionType; enum ActionStatus { InitialActionStatus = 0 }`. Entry points: `virtual void init(int status); mouseMoveEvent/mousePressEvent/mouseReleaseEvent(QMouseEvent*); keyPressEvent; coordinateEvent(RS_CoordinateEvent*); commandEvent(RS_CommandEvent*); QStringList getAvailableCommands(); setStatus(int); virtual void trigger(); finish(); suspend(); resume(); showOptions();`. Base implementations dispatch on status to protected hooks `onMouseLeftButtonRelease(int status, QMouseEvent*)`, `onCoordinateEvent(int status, bool isZero, const RS_Vector& coord)`, `bool doProcessCommand(int status, const QString&)`, `doGetMouseCursor(status)`, `updateActionPrompt()`. Verbatim (`rs_actioninterface.cpp`):

```cpp
void RS_ActionInterface::setStatus(const int status) {
    m_status = status; updateActionPrompt(); updateMouseCursor();
    if (status < 0) { finish(); }
}
void RS_ActionInterface::coordinateEvent(RS_CoordinateEvent* e) {
    const RS_Vector wcsPos = e->getCoordinate(); if (!wcsPos.valid) { return; }
    onCoordinateEvent(m_status, e->isZero(), wcsPos);   // "0" shortcut arrives as a 0,0 vector
}
```

`commandEvent(RS_CommandEvent*)` likewise lower-cases the text, answers `help` from `getAvailableCommands()`, and otherwise calls `doProcessCommand(getStatus(), c)`.

Status is a per-action enum, e.g. `LC_AbstractActionDrawLine::Status { SetStartPoint = InitialActionStatus, SetDirection, SetDistance, SetPoint, SetAngle, LAST }` (`actions/drawing/draw/line/lc_abstractactiondrawline.h`). A mouse click and a typed `@10<45` both reach `onCoordinateEvent(status, ...)`, because the mouse path calls `snapPoint(e)` and forwards the same `RS_Vector`. `RS_PreviewActionInterface` (`rs_previewactioninterface.h:70`) adds `std::unique_ptr<RS_Preview> m_preview; std::unique_ptr<LC_Highlight> m_highlight;`, helpers `previewLine/previewArc/previewCircle/previewRefPoint/...`, `drawPreview()/deletePreview()`, and `virtual void doTrigger()`. `enum RS2::ActionType` (`rs.h:215`) enumerates all 290 actions (`ActionDrawLine, ActionDrawArc3P, ActionZoomWindow, ActionSelectWindow, ActionEditUndo, ...`). The action stack lives in `RS_EventHandler` (`lib/gui/rs_eventhandler.h:50`, `QList<std::shared_ptr<RS_ActionInterface>> m_currentActions;`): `setCurrentAction()` suspends the predecessor (`predecessor->suspend(); predecessor->hideOptions();`), pushes, `action->init(0)`, `showOptions()`, `setPredecessor(predecessor)`; `back()` (Escape) pops; `killAllActions()` returns to `m_defaultAction` (selection). `RS_GraphicView: QWidget` (`rs_graphicview.h:73`) owns the `LC_GraphicViewport` (world/GUI transforms), forwards Qt events to the handler, and renders via `RS_Painter: QPainter, LC_CoordinatesMapper` (`render/rs_painter.h:70`: `toGui(RS_Vector)`, `drawEntityArc/Circle/Polyline`, `drawEllipseWCS`).

### B4. Snap, information, modification

`struct RS_SnapMode` (`lib/actions/rs_snapper.h`), verbatim:

```cpp
enum SnapModes { SnapIntersection = 1 << 0, SnapOnEntity = 1 << 1, SnapCenter = 1 << 2, SnapDistance = 1 << 3,
  SnapMiddle = 1 << 4, SnapEndpoint = 1 << 5, SnapGrid = 1 << 6, SnapFree = 1 << 7, RestrictHorizontal = 1 << 8,
  RestrictVertical = 1 << 9, RestrictOrthogonal = RestrictHorizontal | RestrictVertical, SnapAngle = 1 << 10,
  SnapVisual = 1 << 11, SnapVisualSurvive = 1 << 12 };
RS2::SnapRestriction restriction{RS2::RestrictNothing};
```

(one `bool` per mode, plus `static unsigned toInt(const RS_SnapMode&)` / `fromInt` for settings persistence.)

`RS_Snapper: QObject` (`rs_snapper.h:124`): `RS_Vector snapPoint(const QMouseEvent*)` runs each enabled finder (`snapEndpoint/snapCenter/snapMiddle/snapDistance/snapIntersection/snapOnEntity(const RS_Vector& mouseCoord, double& ds2Min)`, `snapGrid`, `snapFree`) keeping the minimum squared distance, then applies `restriction` relative to the relative zero; `catchEntity(pos, ResolveLevel)` searches within `m_catchEntityGuiRange = 32` pixels; the result is `ImpData{RS_Vector snapCoord, snapSpot; RS_Entity* entity, *entityOther;}`. Geometric queries live in `RS_Information` (`lib/information/rs_information.h:50`): `static RS_VectorSolutions getIntersection(const RS_Entity* e1, const RS_Entity* e2, bool onEntities = false)` dispatching to `getIntersectionLineLine/LineArc/ArcArc/EllipseEllipse/ArcEllipse/CircleEllipse/EllipseLine`, plus `isPointInsideContour`, `isTrimmable`. Edits are stateless statics in `RS_Modification` (`lib/modification/rs_modification.h:284`): `move(const RS_MoveData&, entities, forPreviewOnly, batch)`, `rotate(RS_RotateData{center, refPoint, angle, secondAngle})`, `scale(RS_ScaleData{referencePoint, factor, isotropicScaling})`, `mirror(RS_MirrorData{axisPoint1, axisPoint2})`, `offset(RS_OffsetData{coord, distance})`, `trimAmount`, `trimAtomicByEnding(atomic, point, RS2::Ending)`, `cut`, `stretch`, `explode`, `splitPolyline`, `changeAttributes`, `libraryInsert`; every data struct inherits `LC_ModifyOperationFlags{int number; bool useCurrentAttributes, useCurrentLayer, keepOriginals, multipleCopies;}` and writes through an `LC_DocumentModificationBatch` that clones (`getClone(forPreviewOnly, e)`), adds, and registers undoables. Constructions live in `RS_Creation` (`lib/creation/rs_creation.h`): `createParallel*`, `createBisector`, `createTangent*`, `createBlock(const RS_BlockData*, referencePoint, selectedEntities)`, `createInsert`.

### B5. File format: DXF through `RS_FilterDXFRW`

`class RS_FilterDXFRW : public RS_FilterInterface, DRW_Interface` (`lib/filters/rs_filterdxfrw.h:84`). Import is callback driven: libdxfrw parses group codes into `DRW_*` structs and calls `addLayer(const DRW_Layer&)`, `addBlock`, `addPoint`, `addLine`, `addCircle`, `addArc`, `addEllipse`, `addLWPolyline`, `addSpline`, `addInsert`, `addText`, `addMText`, `addDimAlign/Linear/Radial/Diametric/Angular/Arc/Ordinate`, `addLeader`, `addHatch`, `addImage` (`rs_filterdxfrw.cpp:1522-5500`). Export runs `writeHeader, writeLTypes, writeLayers, writeTextstyles, writeDimstyles, writeVports, writeBlockRecords, writeBlocks, writeEntities, writeObjects`; `writeEntity(RS_Entity*)` switches on `rtti()` (`case RS2::EntityLine: writeLine(static_cast<RS_Line*>(e))`, line 10933). Mapping (condensed):

```cpp
void RS_FilterDXFRW::addLine(const DRW_Line& data) {
    RS_Vector v1(data.basePoint.x, data.basePoint.y);
    RS_Vector v2(data.secPoint.x, data.secPoint.y);
    const auto entity = new RS_Line{m_currentContainer, {v1, v2}};
    setEntityAttributes(entity, &data);
    if (m_currentContainer) { m_currentContainer->addEntity(entity); }
}
```

`writeLine(const RS_Line* l)` (line 11149) is the inverse: `getEntityAttributes(&line, l); line.basePoint.x = l->getStartpoint().x; ... m_dxfW->writeLine(&line);`.

Header variables (`$INSUNITS`, `$EXTMIN/$EXTMAX`, `$CLAYER`, `$DIMTXT`, ...) come from `RS_Graphic::getVariableDict()` in `writeHeader` (line 7004). Minimal DXF (alternating group-code/value lines, the shape LibreCAD's own fixtures use, cf. `lib/filters/tests/large_radial_dim_dxf_tests.cpp:200`: `"0\nSECTION\n2\nENTITIES\n" ... "0\nENDSEC\n0\nEOF\n"`):

```
0
SECTION
2
ENTITIES
0
LINE
8
0
10
0.0
20
0.0
11
100.0
21
50.0
0
ENDSEC
0
EOF
```

(`8` = layer, `10/20` = start x/y into `RS_LineData::startpoint`, `11/21` = end into `endpoint`; a complete file adds `HEADER`, `TABLES` (LTYPE, LAYER, STYLE, DIMSTYLE, VPORT, BLOCK_RECORD), `BLOCKS`, `OBJECTS`.) `enum RS2::FormatType` lists the dialects: `FormatDXF1, FormatDXFRW2018 ... FormatDXFRW12, FormatDWG..., FormatLFF, FormatCXF, FormatJWW, FormatSHP`.

### B6. UI anatomy

`QC_ApplicationWindow : LC_MDIApplicationWindow` (`ui/main/qc_applicationwindow.h:97`) hosts `QMdiArea* m_mdiAreaCAD` of `QC_MDIWindow`s (each a `QG_GraphicView` over one `RS_Document`). Docks are built by `LC_WidgetFactory` (`ui/main/init/lc_widgetfactory.cpp`): the left sidebar is CAD tool button grids (`line`, `circle`, `dimension`, `modify`; `addDockWidget(Qt::LeftDockWidgetArea, ...)`, lines 145-160); `createRightSidebar` (line 358) builds `LC_NamedViewsListWidget`, `LC_LayerTreeWidget`, `LC_QuickInfoWidget`, the **block list** `QG_BlockWidget` (an `RS_BlockListListener` over `QG_BlockModel`: activate/add/remove/rename/toggle/insert/explode), the **library browser** `QG_LibraryWidget` (`QTreeView m_dirView` of part-library folders plus icon previews; `insert()` calls `RS_Modification::libraryInsert`), the **layer list** `QG_LayerWidget` (`RS_LayerListListener` over a `QG_LayerModel` table: visibility/lock/print/construction toggles, active layer), `LC_PenPaletteWidget`, `LC_UCSListWidget`. The **command line** `QG_CommandWidget` (`dock_widgets/command_line/qg_commandwidget.h:36`: `setCommand`, `appendHistory`, `handleCommand(QString)`, `handleKeycode`, `escape`) turns typed input into an `RS_CommandEvent`, or an `RS_CoordinateEvent` when `RS_EventHandler`'s `LC_CoordinatesParser` recognises a coordinate. The **snap toolbar** `QG_SnapToolBar: QToolBar` (`ui/components/toolbars/qg_snaptoolbar.h:39`) holds one checkable `QAction` per snap bit (`m_actionSnapFree, m_actionSnapGrid, m_actionSnapEnd, m_actionSnapOnEntity, m_actionSnapCenter, m_actionSnapMiddle, m_actionSnapDistance, m_actionSnapIntersection, m_actionRestrictHorizontal/Vertical/Orthogonal/Nothing, m_actionRelZero, m_actionLockRelZero`); the **pen toolbar** `QG_PenToolBar: QToolBar, RS_LayerListListener` (`qg_pentoolbar.h:43`) is `QG_ColorBox + QG_WidthBox + QG_LineTypeBox` emitting `penChanged(RS_Pen)` into `RS_Document::setActivePen`; the options toolbar is filled per action by `createOptionsWidget()`. Status bar (`lc_widgetfactory.cpp:486-498`): `QG_CoordinateWidget`, `QG_MouseWidget` (button hints), `QG_SelectionWidget`, `QG_ActiveLayerName`.

## Part C. Abstractions to lift for a Lean-based mathematics CAD

1. **Everything is a `DocumentObject` with typed, self-describing `Property` members; the document is a DAG recomputed topologically** (`Document::recompute`, `getDependencyList(DepSort)`): a definition, lemma or figure is a node whose inputs are links; recompute touches only dirty nodes and their InList.
2. **Two-level dirtiness, `Property::Touched` plus `ObjectStatus::{Touch, Enforce, PendingRecompute, Error}`, over `DepEdge{fromObj, fromProp, toObj, toProp}` edges**: a failed node carries `Error` and its InList is skipped (`filter.insert(obj)`).
3. **Execute = expressions(non-output), `execute()`, expressions(output), returning `StdReturn` or `DocumentObjectExecReturn{Why, Which}`**: errors are node data, not exceptions.
4. **Expressions bind properties across objects with units** (`OperatorExpression::UNIT`, `Quantity` scalers in the lexer, `ObjectIdentifier` paths, `HIDDENREF`): cross-node Lean terms need a parsed AST, a path resolver, dimensional typing and explicit dependency capture (`getIdentifiers()`).
5. **Links are first-class property types with scope** (`PropertyLink/LinkSub/LinkList/XLink`, `Child/Global/Hidden`): "depends on object", "on a sub-element" and "cross-document" stay distinct in the graph and in the serialised `ObjectDeps`.
6. **Topological naming, stable element names across recompute, is the hard problem**: `IndexedName` (`Face1`) versus history-derived, hashed `MappedName` (`ElementMap`, `";:M"`, `";:G"`); references into generated structure (hypothesis index, match case, mesh face) must be keyed by provenance, not enumeration order.
7. **A sketch is parameters plus tagged constraints plus a solver that reports DoF, conflicting, redundant, partially redundant and malformed** (`GCS::System::diagnose`, `conflictingTags`, per-constraint `driving`, `Algorithm {BFGS, LevenbergMarquardt, DogLeg}`): under/over-determination is a visible state; driving versus reference constraints are hypotheses versus measured consequences.
8. **Geometry objects are views over a flat `double*` parameter vector** (`GCS::Point{double* x, *y}`, `Sketch::Parameters/FixParameters/DrivenParameters`): one owner of numeric state, constraints as functions of indices, trivial `applySolution/undoSolution`.
9. **Two undo models: property snapshots (`Transaction::addObjectChange`, `Property::Copy/Paste`) versus deleted-flag toggling on immortal `RS_Undoable`s in `RS_UndoCycle`s**: the flag model suits immutable values, the snapshot model mutable properties; neither replays commands.
10. **Blocks/inserts as parameterless instancing** (`RS_Block: RS_Document`, `RS_InsertData{name, insertionPoint, scaleFactor, angle, cols, rows, spacing}`, `RS_Insert::update()` expanding a cached copy, `ByBlock` resolution): sub-diagrams instantiated by name plus an affine placement, with inherited attributes.
11. **An action is a state machine driven by coordinate and command events** (`RS_ActionInterface::{init, setStatus, onCoordinateEvent(status, ...), doProcessCommand(status, ...), trigger}`, per-action `enum Status`, a stack in `RS_EventHandler` with `suspend/resume`): clicks and typed `@dx<angle` are one event, so every construction is resumable, previewable and scriptable.
12. **Snapping is a composable bitmask of point-finders plus a restriction, each returning the nearest candidate with its evidence** (`RS_SnapMode`, `ImpData{snapCoord, snapSpot, entity, entityOther}`, `RS_VectorSolutions`): "attach this term to that subterm" needs the same protocol.
13. **Style inheritance by layer and block with tri-state attributes** (`RS_Pen` `ByLayer/ByBlock`, `RS_LayerData{frozen, locked, print, construction}`), and **a spreadsheet whose cells are alias-addressable dynamic properties** (`Sheet::getPropertyByName`): scaffolding/published separation and a parameter table bound through ordinary expressions.
14. **One XML per document plus typed side files plus serialised dependency lists** (`Document.xml` with `<Objects>`/`<ObjectDeps>`/`<Dep>` and `<ObjectData>`, `*.brp`, `GuiDocument.xml` apart from the model), with DXF's flat group-code stream as the exchange counterpart: model/view separation on disk, partial loading by subgraph, lowest-common-denominator export.
