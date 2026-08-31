# OpenSCAD: data types and machinery conventions

Source: `https://github.com/openscad/openscad`, commit `1c9ee2ba3112` (2026-08-30), sparse clone at `$S/refs/openscad`. Paths below are relative to that repository root. Fixtures quoted verbatim were fetched from `tests/data/scad/` and `tests/regression/dump/`.

## 1. Identity and purpose

OpenSCAD is a compiler, not a modeller. A `.scad` file is a program in a small, pure, functional language; the "diagram" is the deterministic result of evaluating that program into a tree of geometry nodes, then a CSG expression, then a mesh. There is no interactive geometry editing: the editor edits text, and every preview (F5) or render (F6) re-runs the pipeline from source. `src/core/node.h` states the discipline:

```
   The node tree is the result of evaluation of a module instantiation
   tree.  Both the module tree and the node tree are regenerated from
   scratch for each compile.
```

The goal is a reproducible, parametric, text-first solid modeller for mechanical parts (STL/3MF for printing, DXF/SVG for cutting), with a Customizer that infers a form UI from top-level assignments.

## 2. Core data types

### 2.1 AST layer (`src/core/AST.h`, `Expression.h`, `Assignment.h`, `ModuleInstantiation.h`, `UserModule.h`, `function.h`, `LocalScope.h`, `SourceFile.h`)

- `Location { first_line, first_col, last_line, last_col, shared_ptr<fs::path> path }` and `ASTNode { Location loc; virtual print(); dump(); }`. Every syntactic object carries its source span.
- `Expression : ASTNode` with `virtual Value evaluate(const shared_ptr<const Context>&) const = 0` and `virtual bool isLiteral()`. Subclasses, all in `Expression.h`:
  - `UnaryOp` with `enum class Op { Not, BinaryNot, Negate }`
  - `BinaryOp` with `enum class Op { LogicalAnd, LogicalOr, Exponent, Multiply, Divide, Modulo, Plus, Minus, ShiftLeft, ShiftRight, BinaryAnd, BinaryOr, Less, LessEqual, Greater, GreaterEqual, Equal, NotEqual }`
  - `TernaryOp(cond, ifexpr, elseexpr)`, `ArrayLookup(array, index)`, `MemberLookup(expr, member)`, `Lookup(name)`, `Literal(Value)`, `Range(begin, step, end)`, `Vector(children)`
  - `FunctionCall { bool isLookup; string name; shared_ptr<Expression> expr; AssignmentList arguments }` and `FunctionDefinition { context; parameters; expr }` (anonymous `function(x) ...` literals)
  - `Assert`, `Echo`, `Let`: expression-form wrappers each holding `AssignmentList arguments; shared_ptr<Expression> expr` and an `evaluateStep()` used by the tail-call loop
  - `ListComprehension` subclasses `LcIf`, `LcFor`, `LcForC` (C-style `for(init; cond; incr)`), `LcEach`, `LcLet`
- `Assignment : ASTNode { const string name; shared_ptr<Expression> expr; AnnotationMap annotations; Location locOfOverwrite }`, with `using AssignmentList = vector<shared_ptr<Assignment>>`. The same type serves parameters, arguments and `let` bindings.
- `ModuleInstantiation : ASTNode { AssignmentList arguments; const shared_ptr<LocalScope> scope; bool tag_root, tag_highlight, tag_background; string modname }` plus `IfElseModuleInstantiation` with an `else_scope`. The `*` modifier never produces an instantiation at all (the parser deletes it).
- `LocalScope { AssignmentList assignments; vector<shared_ptr<ModuleInstantiation>> moduleInstantiations; unordered_map<string, shared_ptr<UserFunction>> functions; unordered_map<string, shared_ptr<UserModule>> modules }`: every `{ ... }` block, module body and file body is one of these.
- `UserModule : AbstractModule, ASTNode { string name; AssignmentList parameters; const shared_ptr<LocalScope> body }` and `UserFunction : ASTNode { string name; AssignmentList parameters; shared_ptr<Expression> expr }` (a function is a single expression).
- `SourceFile : ASTNode { const shared_ptr<LocalScope> scope; vector<string> usedlibs; unordered_map<string,string> includes; ... }` with `instantiate(context, &file_context) -> shared_ptr<AbstractNode>` returning a `RootNode`.

### 2.2 Values (`src/core/Value.h`, `RangeType.h`, `FunctionType.h`, `UndefType.h`)

```cpp
enum class Type { UNDEFINED, BOOL, NUMBER, STRING, VECTOR, EMBEDDED_VECTOR, RANGE, FUNCTION, OBJECT };
using Variant = std::variant<UndefType, bool, double, str_utf8_wrapper, VectorType, EmbeddedVectorType,
                             RangePtr, FunctionPtr, ObjectType>;
static_assert(sizeof(Value::Variant) <= 24, "Memory size of Value too big");
```

`Value` is move-only (`Value(const Value&) = delete`, explicit `clone()`), and `type()` is literally `value.index()` of the variant. `UndefType` carries a reason (`static Value undef(const std::string& why)`). `VectorType` is a `shared_ptr<VectorObject>`; `EmbeddedVectorType` is a pseudo-element giving O(1) concatenation for list comprehensions, flattened lazily on `operator[]`. `RangeType { begin_val, step_val, end_val }` iterates lazily with `MAX_RANGE_STEPS = 10000`. `FunctionType { context, expr, parameters }` is a closure; `ObjectType` is an insertion-ordered map behind the experimental `object()` builtin. Numbers are `double` only.

### 2.3 Context and scope (`src/core/ContextFrame.h`, `Context.h`, `ScopeContext.h`, `BuiltinContext.h`, `EvaluationSession.h`, `Parameters.h`, `Arguments.h`, `callables.h`)

- `ContextFrame { ValueMap lexical_variables; ValueMap config_variables; EvaluationSession* }`: two maps, split by `is_config_variable(name)`, which is `return name[0] == '$' && name != "$children";`. Dollar variables are dynamically scoped (looked up down the session's frame stack); everything else is lexical.
- `Context : ContextFrame { shared_ptr<const Context> parent; lookup_variable / lookup_function / lookup_module }`, created only via `Context::create<C>(...)`, which returns a `ContextHandle<C>` that pushes and pops the frame on the `EvaluationSession` stack by RAII.
- `ScopeContext : Context { shared_ptr<const LocalScope> scope }` whose `init()` evaluates each assignment in order (`ScopeContext.cc`); `UserModuleContext : ScopeContext { Children children }` sets `$children` and `$parent_modules` and binds parameters via `Parameters::parse(...)`; `FileContext : ScopeContext` additionally resolves names against `use <...>`d libraries; `BuiltinContext` is the root holding builtins and the defaults from `Builtins.cc`: `$fn=0, $fs=2, $fa=12, $t=0, $preview=undef, $vpt=[0,0,0], $vpr=[0,0,0], $vpd=500, $vpf=22.5`.
- Callables: `using CallableFunction = std::variant<const BuiltinFunction*, CallableUserFunction, Value, const Value*>; struct InstantiableModule { shared_ptr<const Context> defining_context; const AbstractModule* module; }`. Lookups return the definition together with its defining context, so both functions and modules are lexical closures.
- `Arguments : vector<Argument{optional<string> name; Value value}>` are evaluated eagerly in the caller's context; `Parameters` is a flat `ContextFrame` (not a `Context`) matched positionally or by name.

### 2.4 Module instantiation and `children()`

`ModuleInstantiation::evaluate(context)` (`ModuleInstantiation.cc`) does `context->lookup_module(name)` then `module->instantiate(defining_context, this, context)`. For a `UserModule` (`UserModule.cc`):

```cpp
ContextHandle<UserModuleContext> module_context{Context::create<UserModuleContext>(
    defining_context, this, inst->location(), Arguments(inst->arguments, context),
    Children(inst->scope, context))};
ret = this->body->instantiateModules(*module_context,
        std::make_shared<GroupNode>(inst, std::string("module ") + this->name));
```

`Children { shared_ptr<const LocalScope> children_scope; shared_ptr<const Context> context }` (`Children.h`) is a thunk: the child block's AST plus the caller's context, not evaluated until the module body calls `children()`, `children(i)`, `children([a,b])` or `children([s:e])` (`control.cc: builtin_children`), which does `children_scope->instantiateModules(*scopeContext(), target, indices)`. Each call re-instantiates, so calling `children()` twice yields two subtrees. Builtin modules are `BuiltinModule` wrapping a C function pointer (`module.h`); `for`, `if`, `let`, `echo`, `assert`, `intersection_for` and `group` are ordinary builtin modules in `control.cc` / `GroupModule.cc`, `for` being `LcFor::forEach` instantiating the block once per iteration into a `GroupNode` (a `ListNode` under `Feature::ExperimentalLazyUnion`).

### 2.5 The node tree (`src/core/node.h` and per-node headers)

`AbstractNode : BaseVisitable, enable_shared_from_this { vector<shared_ptr<AbstractNode>> children; const ModuleInstantiation* modinst; int idx; virtual string name(); virtual string toString(); }`. `idx` is a per-compile counter reset by `resetIndexCounter()` and keys every downstream cache. Visitors dispatch via `VISITABLE()` / `NodeVisitor` with prefix and postfix passes over `State { Transform3d matrix_; Color4f color_; flags PREFIX|POSTFIX|PREFERNEF|HIGHLIGHT|BACKGROUND; parentnode }` (`State.h`). The complete hierarchy:

| Class | Base | Key fields / enum | Header |
|---|---|---|---|
| `AbstractIntersectionNode` | `AbstractNode` | produced by `intersection_for` | `node.h` |
| `ListNode` | `AbstractNode` | unpacked by parent, no implicit union | `node.h` |
| `GroupNode` | `AbstractNode` | `_name` (e.g. `"module parent"`) | `node.h` |
| `RootNode` | `GroupNode` | owns its own `ModuleInstantiation mi("group")` | `node.h` |
| `AbstractPolyNode` | `AbstractNode` | `enum class render_mode_e { RENDER_CGAL, RENDER_OPENCSG }` | `node.h` |
| `LeafNode` | `AbstractPolyNode` | `virtual unique_ptr<const Geometry> createGeometry() = 0` | `node.h` |
| `CubeNode`, `SphereNode`, `CylinderNode`, `PolyhedronNode`, `SquareNode`, `CircleNode`, `PolygonNode` | `LeafNode` | `x,y,z,center`; `r`; `r1,r2,h`; `points, faces, convexity`; `paths`; each curved primitive holds a `CurveDiscretizer` (snapshot of `$fn/$fa/$fs`) | `primitives.h` |
| `ImportNode` | `LeafNode` | `enum class ImportType { UNKNOWN, _3MF, STL, OFF, SVG, DXF, NEF3, OBJ }`, `filename, id, layer, dpi, center` | `ImportNode.h` |
| `SurfaceNode` | `LeafNode` | `filename, center, invert, convexity` (PNG/.dat heightmap) | `SurfaceNode.h` |
| `CsgOpNode` | `AbstractNode` | `OpenSCADOperator type` | `CsgOpNode.h` |
| `CgalAdvNode` | `AbstractNode` | `enum class CgalAdvType { MINKOWSKI, HULL, FILL, RESIZE }`, `newsize, autosize, convexity` | `CgalAdvNode.h` |
| `TransformNode` | `AbstractNode` | `Transform3d matrix` (translate/rotate/scale/mirror/multmatrix all become one 4x4) | `TransformNode.h` |
| `ColorNode` | `AbstractNode` | `Color4f color` | `ColorNode.h` |
| `RenderNode` | `AbstractNode` | `int convexity` | `RenderNode.h` |
| `LinearExtrudeNode` | `AbstractPolyNode` | `Vector3d height; scale_x, scale_y, twist, slices, segments, center, convexity` | `LinearExtrudeNode.h` |
| `RotateExtrudeNode` | `AbstractPolyNode` | `angle, start, convexity` | `RotateExtrudeNode.h` |
| `ProjectionNode` | `AbstractPolyNode` | `cut_mode, convexity` | `ProjectionNode.h` |
| `OffsetNode` | `AbstractPolyNode` | `delta, chamfer, Clipper2Lib::JoinType join_type, miter_limit` | `OffsetNode.h` |
| `RoofNode` | `AbstractPolyNode` | `method` (experimental) | `RoofNode.h` |
| `TextNode` | `AbstractPolyNode` | `FreetypeRenderer::Params params` | `TextNode.h` |

`enum class OpenSCADOperator { UNION, INTERSECTION, DIFFERENCE, MINKOWSKI, HULL, FILL, RESIZE }` lives in `enums.h`. The builtin registry (`Builtins.cc: Builtins::initialize()`) calls `register_builtin_{functions,group,csgops,transform,color,primitives,surface,control,render,import,projection,cgaladv,offset,linear_extrude,rotate_extrude,roof,text}`. Builtin functions (`builtin_functions.cc`) are `abs sign rands min max sin cos asin acos tan atan atan2 round ceil floor pow sqrt exp len log ln str chr ord concat lookup search version version_num norm cross parent_module is_undef is_list is_num is_bool is_string is_function is_object`, plus experimental `object has_key import textmetrics fontmetrics`.

### 2.6 CSG term normal form (`src/core/CSGNode.h`, `CSGNode.cc`, `src/glview/preview/CSGTreeNormalizer.cc`)

```cpp
class CSGNode      { enum Flag { FLAG_NONE = 0x00, FLAG_BACKGROUND = 0x01, FLAG_HIGHLIGHT = 0x02 }; BoundingBox bbox; unsigned int flags; };
class CSGOperation : CSGNode { OpenSCADOperator type; std::vector<std::shared_ptr<CSGNode>> children; /* left(), right() */ };
class CSGLeaf      : CSGNode { std::string label; std::shared_ptr<const PolySet> polyset; Transform3d matrix; Color4f color; const int index; };
class CSGProduct   { std::vector<CSGChainObject> intersections; std::vector<CSGChainObject> subtractions; };
class CSGProducts  { std::vector<CSGProduct> products; void import(std::shared_ptr<CSGNode>, OpenSCADOperator = UNION, CSGNode::Flag = FLAG_NONE); };
```

A CSG term is a binary tree over only `UNION`, `INTERSECTION` and `DIFFERENCE`, whose leaves hold a mesh plus its accumulated world matrix and colour. `CSGOperation::createCSGNode` distinguishes a null pointer (a non-geometric node such as `echo`) from a leaf with empty geometry, and prunes by bounding box. `CSGTreeNormalizer::match_and_replace` applies the nine Goldfeather rules, quoted from the source comments:

```
1.  x - (y + z) -> (x - y) - z
2.  x * (y + z) -> (x * y) + (x * z)
3.  x - (y * z) -> (x - y) + (x - z)
4.  x * (y * z) -> (x * y) * z
5.  x - (y - z) -> (x - y) + (x * z)
6.  x * (y - z) -> (x * y) - z
7. (x - y) * z  -> (x * z) - y
8. (x + y) - z  -> (x - z) + (y - z)
9. (x + y) * z  -> (x * z) + (y * z)
```

The result is a sum of products; `CSGProducts::import` flattens it into a list of `CSGProduct{intersections, subtractions}`, which is exactly what OpenCSG's image-space renderer consumes. Dump syntax: `CSGOperation::dump()` prints `(a + b)`, `(a * b)`, `(a - b)`; `CSGProducts::dump()` prints one line per product as `+leaf *leaf -leaf`, where a leaf label is `name()` followed by `index()` (e.g. `cube3`).

## 3. Language grammar (`src/core/parser.y`, `src/core/lexer.l`)

Tokens: `TOK_MODULE TOK_FUNCTION TOK_IF TOK_ELSE TOK_FOR TOK_LET TOK_ASSERT TOK_ECHO TOK_EACH TOK_ID TOK_STRING TOK_USE TOK_NUMBER TOK_TRUE TOK_FALSE TOK_UNDEF` and `LE GE EQ NEQ AND OR LSH RSH`; `%nonassoc NO_ELSE` / `%nonassoc TOK_ELSE` resolves dangling else. Key productions, condensed from `parser.y`:

```
input          : /*empty*/ | input TOK_USE | input statement ;
statement      : ';' | '{' inner_input '}' | module_instantiation | assignment
               | TOK_MODULE TOK_ID '(' parameters ')' statement
               | TOK_FUNCTION TOK_ID '(' parameters ')' '=' expr ';' ;
assignment     : TOK_ID '=' expr ';' ;
module_instantiation
               : '!' module_instantiation        /* tag_root = true      */
               | '#' module_instantiation        /* tag_highlight = true */
               | '%' module_instantiation        /* tag_background = true*/
               | '*' module_instantiation        /* delete $2; $$ = NULL */
               | single_module_instantiation child_statement
               | ifelse_statement ;
single_module_instantiation : module_id '(' arguments ')' ;
child_statement: ';' | '{' child_statements '}' | module_instantiation ;
expr           : logic_or
               | TOK_FUNCTION '(' parameters ')' expr        /* anonymous function */
               | logic_or '?' expr ':' expr
               | TOK_LET '(' arguments ')' expr
               | TOK_ASSERT '(' arguments ')' expr_or_empty
               | TOK_ECHO '(' arguments ')' expr_or_empty ;
call           : primary | call '(' arguments ')' | call '[' expr ']' | call '.' TOK_ID ;
primary        : TOK_TRUE | TOK_FALSE | TOK_UNDEF | TOK_NUMBER | TOK_STRING | TOK_ID | '(' expr ')'
               | '[' expr ':' expr ']' | '[' expr ':' expr ':' expr ']'
               | '[' ']' | '[' vector_elements optional_trailing_comma ']' ;
list_comprehension_elements
               : TOK_LET '(' arguments ')' list_comprehension_elements_p
               | TOK_EACH vector_element
               | TOK_FOR '(' arguments ')' vector_element
               | TOK_FOR '(' arguments ';' expr ';' arguments ')' vector_element
               | TOK_IF '(' expr ')' vector_element [ TOK_ELSE vector_element ] ;
```

Precedence from low to high: `||`, `&&`, `== !=`, `< <= > >=`, `|`, `&`, `<< >>`, `+ -`, `* / %`, unary `+ - ! ~`, `^`, then call/index/member. `include <file>` is handled in `lexer.l` (`includefile()` splices the file into the token stream, so its contents join the including scope), while `use <file>` returns `TOK_USE` and only registers the library's modules and functions for lookup via `FileContext::lookup_local_*`. A re-assignment of a name in the same scope replaces the expression but keeps the first position (`handle_assignment`, `locOfOverwrite`): last assignment wins, evaluated at the first location. `echo`, `assert`, `let`, `for` and `each` are both keywords and legal module identifiers (`module_id`). Special variables `$fn $fa $fs $t $children $preview $vpr $vpt $vpd $vpf $parent_modules` (plus experimental `$fe`) are ordinary dynamically scoped variables.

Minimal complete example, verbatim from `tests/data/scad/3D/features/child-tests.scad`:

```openscad
$fn=16;

module parent(range=[0:2]) {
  for (i=range) {
    translate([2.5*i,0,0]) children(i);
  }
}

// Normal
parent() {
  sphere();
  cylinder(h=2, center=true);
  cube(2, center=true);
}

// No children
parent();

// Too few children
translate([0,3,0]) parent() { sphere(); }

// No parameter to child
module parent2() {
  children();
}

translate([2.5,3,0]) parent2() { cylinder(h=2, center=true); sphere(); }

// Negative parameter to child
module parent3() {
  children(-1);
}

translate([5,3,0]) parent3() { cube(); sphere(); }

// Leaking variables to child list is not allowed
translate([0,6,0]) parent(range=[0:1], testvar=10) { sphere(); cube(testvar, center=true);}
```

Its evaluated node-tree dump (`openscad -o out.csg`, the `FileFormat::CSG` path, which is `tree.getString(*root_node, "\t")` in `openscad.cc`), verbatim from `tests/regression/dump/child-tests-expected.csg`:

```
group() {
	group() {
		multmatrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]) {
			group() {
				sphere($fn = 16, $fa = 12, $fs = 2, r = 1);
			}
		}
		multmatrix([[1, 0, 0, 2.5], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]) {
			group() {
				cylinder($fn = 16, $fa = 12, $fs = 2, h = 2, r1 = 1, r2 = 1, center = true);
			}
		}
		multmatrix([[1, 0, 0, 5], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]) {
			group() {
				cube(size = [2, 2, 2], center = true);
			}
		}
	}
}
group() {
	group() {
		multmatrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]);
		multmatrix([[1, 0, 0, 2.5], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]);
		multmatrix([[1, 0, 0, 5], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]);
	}
}
multmatrix([[1, 0, 0, 0], [0, 1, 0, 3], [0, 0, 1, 0], [0, 0, 0, 1]]) {
	group() {
		group() {
			multmatrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]) {
				group() {
					sphere($fn = 16, $fa = 12, $fs = 2, r = 1);
				}
			}
			multmatrix([[1, 0, 0, 2.5], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]);
			multmatrix([[1, 0, 0, 5], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]);
		}
	}
}
multmatrix([[1, 0, 0, 2.5], [0, 1, 0, 3], [0, 0, 1, 0], [0, 0, 0, 1]]) {
	group() {
		group() {
			cylinder($fn = 16, $fa = 12, $fs = 2, h = 2, r1 = 1, r2 = 1, center = true);
			sphere($fn = 16, $fa = 12, $fs = 2, r = 1);
		}
	}
}
multmatrix([[1, 0, 0, 5], [0, 1, 0, 3], [0, 0, 1, 0], [0, 0, 0, 1]]) {
	group();
}
multmatrix([[1, 0, 0, 0], [0, 1, 0, 6], [0, 0, 1, 0], [0, 0, 0, 1]]) {
	group() {
		group() {
			multmatrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]) {
				group() {
					sphere($fn = 16, $fa = 12, $fs = 2, r = 1);
				}
			}
			multmatrix([[1, 0, 0, 2.5], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]) {
				group() {
					cube(size = [1, 1, 1], center = true);
				}
			}
		}
	}
}

```

Reading it: the outer `group()` of each `parent()` call is the `GroupNode` created for the module body (`verbose_name()` is `"module parent"`, but `name()` prints `group`); the inner `group()` is the `for` node; each `translate` is a `TransformNode` printed by `TransformNode::toString()` as `multmatrix([...])`; `children(i)` becomes a `group()` wrapping the instantiated child; `$fn = 16, $fa = 12, $fs = 2` are baked into every curved leaf because the `CurveDiscretizer` snapshot is taken at instantiation; `parent3` yields a bare `group();` because `children(-1)` returned `nullptr` with a warning. A second verbatim pair shows the root modifier (`tests/data/scad/3D/features/root-modifier.scad` and `tests/regression/dump/root-modifier-expected.csg`):

```openscad
difference() {
  sphere(r=10);
  !cylinder(h=30, r=6, center=true);
}
```
```
cylinder($fn = 0, $fa = 12, $fs = 2, h = 30, r1 = 6, r2 = 6, center = true);
```

Modifier flags print as line prefixes in the dump (`highlight-and-background-modifier-expected.csg`): `%#	cylinder(...)`, `%#	group() {`, `#multmatrix(...) {`, `%multmatrix(...) {`.

## 4. Pipeline

1. **Parse.** `parse(root_file, text, filename, ...)` (bison/flex) fills `SourceFile::scope`; `SourceFile::handleDependencies()` recursively parses `use`d libraries into `SourceFileCache` and records include mtimes for auto-reload. `CommentParser::collectParameters(fulltext, root_file)` runs over the same text to attach customizer annotations to top-level literal assignments.
2. **Evaluate AST to node tree.** `MainWindow::instantiateRoot()` and `openscad.cc: do_export()` both do:
   ```cpp
   AbstractNode::resetIndexCounter();
   EvaluationSession session{doc.parent_path().string()};
   ContextHandle<BuiltinContext> builtin_context{Context::create<BuiltinContext>(&session)};
   setRenderVariables(builtin_context);          // $preview, $t, $vpr, $vpt, $vpd, $vpf
   this->absoluteRootNode = this->rootFile->instantiate(*builtin_context, &file_context);
   if (!(this->rootNode = find_root_tag(this->absoluteRootNode, &nextLocation)))
     this->rootNode = this->absoluteRootNode;
   this->tree.setRoot(this->rootNode);
   ```
   `RenderVariables { bool preview; double time; Camera camera; }` (`RenderVariables.h`) is the only injection of environment into the program: `$preview` is `true` for F5 and for any format where `fileformat::canPreview()` holds (`AST CSG PARAM ECHO TERM PNG`), `false` for F6 and mesh exports; `$t` comes from the Animate panel or `--animate N` (`render_variables.time = frame * (1.0 / cmd.animate.frames)`). `find_root_tag` (`node.cc`) picks the unique `!`-tagged subtree. Function evaluation is a tail-call loop (`FunctionCall::evaluate` in `Expression.cc`: "Repeatedly simplify expr until it reduces to either a tail call, or an expression that cannot be simplified in-place"), guarded by `StackCheck` and a 1,000,000-iteration cap. Values are never lazy; only children blocks and geometry are deferred.
3. **Node tree to CSG term.** `CSGTreeEvaluator : NodeVisitor` (`CSGTreeEvaluator.cc`) walks postfix, folding each node's visited children with `applyToChildren(state, node, op)`: `GroupNode`, `TransformNode` and `ColorNode` fold with `UNION`, `CsgOpNode` with its own operator, `AbstractIntersectionNode` with `INTERSECTION`. `TransformNode` multiplies `state.matrix()` in prefix; `ColorNode` sets colour only if unset, so the outermost `color()` wins. Leaves, `RenderNode` and `CgalAdvNode` call `geomevaluator->evaluateGeometry(node, false)` and wrap the result as a `CSGLeaf`; this is where `render()` is a barrier, since its subtree becomes one mesh and the previewer loses per-primitive CSG inside it. `%` terms move to `backgroundNodes`, `#` terms are duplicated into `highlightNodes`, and flags propagate upward through `State`.
4. **Normalize.** `CSGTreeNormalizer(2 * openCSGLimit).normalize(csgRoot)` followed by `CSGProducts::import`. If the product count exceeds `advanced/openCSGLimit` (default `RenderSettings::openCSGTermLimit`), OpenCSG preview is disabled and the view falls back to ThrownTogether.
5. **Geometry evaluation.** `GeometryEvaluator : NodeVisitor` (`src/geometry/GeometryEvaluator.h/.cc`) returns `shared_ptr<const Geometry>`. `Geometry` subclasses are `PolySet` (indexed mesh with per-face colour indices), `Polygon2d` (outlines with a `positive` flag), `GeometryList`, `ManifoldGeometry` (wrapping `manifold::Manifold` with `operator+ * -`, `minkowski`, `slice`, `project`) and `CGALNefGeometry`. Backend selection reads `RenderSettings::inst()->backend3D == RenderBackend3D::ManifoldBackend`, choosing `ManifoldUtils::applyOperator3DManifold(children, op)` or `CGALUtils::applyOperator3D(children, op)`; 2D booleans always go through Clipper2. Results are memoised in `GeometryCache` (100 MB default) or `CGALCache` (Nef polyhedra), keyed by `Tree::getIdString(node)`, the whitespace-stripped dump of the subtree with single-child groups elided by `GroupNodeChecker`, so structurally identical subtrees anywhere in the design share one evaluation. `Design > Flush Caches` clears both plus `SourceFileCache`.
6. **Preview versus render.** F5 (`actionRenderPreview` > `compile` > `instantiateRoot` > `compileCSG` > `csgRender`) builds `OpenCSGRenderer(rootProduct, highlightsProducts, backgroundProducts)` and `ThrownTogetherRenderer(...)`. F6 (`cgalRender`) hands `tree` to a `CGALWorker` thread that calls `evaluateGeometry(*tree.root(), allownef)` and returns one `Geometry` drawn by `PolySetRenderer` or `CGALRenderer`; only then can a mesh be exported or measured.
7. **Export.** `enum class FileFormat { ASCII_STL, BINARY_STL, OBJ, OFF, WRL, _3MF, DXF, SVG, NEFDBG, NEF3, CSG, AST, TERM, ECHO, PNG, PDF, POV, PARAM }` (`src/io/export.h`), identifiers `asciistl binstl obj off wrl 3mf dxf svg nefdbg nef3 csg param ast term echo png pdf pov`. `is3D`: STL/OBJ/OFF/WRL/3MF/NEF/POV; `is2D`: DXF/SVG/PDF; `CSG/AST/TERM/ECHO/PARAM/PNG` need no mesh. CLI: `openscad -o out.stl -D 'x=3' --export-format binstl --render|--preview[=throwntogether] --camera ... --viewall --autocenter --projection o|p --view axes,scales,edges,crosshairs --animate N --csglimit n --backend manifold|cgal --enable feature file.scad`.

## 5. UI and wireframe anatomy

`MainWindow::setupDocks()` (`src/gui/MainWindow.cc`) declares the panels: Editor, Console, Customizer (`parameterDock`), Error Log, Animate, Font List, Color List, Viewport Control, AI Chat. Default layout: editor left, 3D view (`QGLView : GLView`) centre-top, console bottom, customizer right.

- **Editor.** `ScintillaEditor` with `ScadLexer` (call-tips from `Builtins::keywordList`), tabs via `TabManager`, `Design > Auto Reload and Preview` polling mtimes. F4 Reload and Preview, F5 Preview, F6 Render. `Design > Display AST / CSG Tree / CSG Products` show the AST print, `tree.getString(*rootNode, "  ")`, and `csgRoot->dump()` / `normalizedRoot->dump()` / `rootProduct->dump()`.
- **Console.** `LOG(message_group::Echo|Warning|Error|Trace|UI_Warning, Location, ...)` lines with clickable locations; the Error Log dock tabulates the same stream.
- **Viewer** (`src/glview/GLView.h`). Flags `showaxes`, `showedges`, `showcrosshairs`, `showscale` (scale markers on the axes); `Camera` with `ProjectionType { ORTHOGONAL, PERSPECTIVE }` and gimbal fields `object_trans`, `object_rot`, `viewer_distance`, `fov`. Presets `on_viewActionTop/Bottom/Left/Right/Front/Back/Diagonal/Center_triggered`, plus `ResetView`, `ViewAll`, `Perspective`/`Orthogonal`. Camera state flows into the program as `$vpr $vpt $vpd $vpf` and out via `Edit > Copy VPT/VPR/VPD/VPF`. Modes: `viewModePreview` (OpenCSG image-space CSG per product), `viewModeThrownTogether` (every leaf drawn, subtractions in a second colour, no CSG), `viewModeRender` (the evaluated mesh). `#` terms render translucent pink on top, `%` terms translucent grey, `!` re-roots, `*` removes the subtree at parse time.
- **Customizer** (`src/core/customizer/*`, `src/gui/parameter/*`). `ParameterObject::fromAssignment` inspects each top-level assignment whose expression `isLiteral()` (numbers, strings, bools, literal vectors of one to four numbers) with its `Parameter`, `Description` and `Group` annotations. Syntax (`comment_parser.y`): trailing `// [min:max]` or `// [min:step:max]` gives a `NumberParameter` slider; `// 5` a spinbox step; `// [10]` a maximum; `// [a, b, c]` or `// [10:Small, 20:Medium]` an `EnumParameter` combo (`[value:label]`); the `// text` line above is the description; a single-line `/* [Tab] */` comment starts a group (`[Hidden]` suppresses; `[..][..]` join with `-`); collection stops at the first `{` (`getLineToStop`). `enum class ParameterType { Bool, String, Number, Vector, Enum }` maps to `ParameterCheckBox`, `ParameterText`, `ParameterSlider`/`ParameterSpinBox`, `ParameterVector`, `ParameterComboBox` inside collapsible `GroupWidget`s. `apply()` rewrites the `Assignment`'s expression with a new `Literal` before instantiation: the customizer edits the AST, not the text. Presets sit beside the file as `<name>.json`, shape from `tests/data/scad/customizer/setofparameter.json`:
  ```json
  { "parameterSets": { "firstSet": { "Numbers": "1", "slider": "38", "Vector2": "[12,4, 45, 23]" } }, "fileFormatVersion": "1" }
  ```
  and `--export-format param` emits a machine-readable schema: `{"parameters":[{"name","caption","group","type","initial","min","max","step","options":[{"name","value"}]}]}`.
- **Animation.** The `Animate` dock exposes `e_tval`, `e_fps`, `e_fsteps` and a dump toggle; each tick sets `$t` in `[0,1)` and re-runs F5; `csgRender` saves `frame%05d.png` when dumping.
- **Library paths** (`src/core/parsersettings.cc`). `parser_init()` adds `OPENSCADPATH` entries, then `PlatformUtils::userLibraryPath()`, then the bundled `libraries/`; `find_valid_path` tries relative-to-source first, then the library dirs, rejecting circular includes.

## 6. Abstractions to lift for a Lean-based mathematics CAD

1. **Program-as-model with a from-scratch compile.** No persistent model state; every diagram is `eval(program, env)`, so reproducibility and version control are free.
2. **A three-stage tower: AST, node tree, normal-form term.** Syntax, evaluated trace (`AbstractNode.modinst` points back at the instantiating syntax), and canonical algebraic object, as three distinct types.
3. **Per-node source anchoring.** `Location` on every AST node, `modinst` on every tree node, `getCodeLocation` for the reverse direction: click-to-source and source-to-highlight both ways.
4. **The modifier characters `! # % *` as per-node annotations** (`tag_root`, `tag_highlight`, `tag_background`, `*` deleted at parse): isolate, debug, ghost or disable a subtree without editing the model; flags propagate through the term via `State`.
5. **Children as a lazy thunk** (`Children{scope, context}`) plus `$children` and `children(i)`: a module is a higher-order combinator over unevaluated blocks; re-instantiation per call keeps it pure.
6. **Two-map scoping**: lexical variables versus `$`-prefixed dynamically scoped variables, a principled channel for environment (resolution, time, viewpoint) without threading arguments.
7. **Definitions carry their defining context** (`InstantiableModule`, `CallableUserFunction`): closures for modules as well as functions.
8. **Undefined values carry a reason** (`UndefType(why)`): errors are data that surface as warnings at the location that consumed them, not where they were produced.
9. **Structural cache key is the canonical dump of the subtree** (`Tree::getIdString`, `GroupNodeChecker` elision): memoisation by content, shared across scopes.
10. **An explicit barrier node** (`render()`) that forces a subtree to a value and hides its structure from the previewer: a user-controlled opaque boundary.
11. **Preview/render split exposed as `$preview`.** One program yields a cheap approximate evaluation (image-space CSG) and an exact one (mesh booleans), and can branch on which it is in.
12. **Customizer parameters inferred from top-level literal assignments plus comment annotations**, applied by rewriting the AST, with presets as JSON keyed by variable name and a machine-readable schema export.
13. **Goldfeather normalization to sum-of-products before rendering.** Canonical form makes rendering, diffing and counting deterministic; a node-count limit degrades gracefully to "thrown together".
14. **Discretization parameters snapshot into leaves** (`CurveDiscretizer` from `$fn/$fa/$fs`, printed in the dump): the dump witnesses every decision that affected geometry.
15. **The text dump is the interchange format.** A `.csg` file is valid OpenSCAD, re-readable by the same parser; the diagram is itself a program.

What OpenSCAD deliberately does not model: mutable state or reassignment (single assignment per scope, immutable move-only values); constraints or solvers (dimensions are computed forward); assemblies, joints or mates (one file is one part, positioning is explicit transforms); units or tolerances; feature history or geometric undo (only text undo); persistent topology naming (`Selection` is a per-render pick); time beyond the scalar `$t` (no physics, kinematics, or cross-frame dependency); and object identity across recompiles (`idx` resets every compile).
