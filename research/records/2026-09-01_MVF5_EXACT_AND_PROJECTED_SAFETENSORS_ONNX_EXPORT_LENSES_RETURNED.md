# MVF5 exact and projected Safetensors/ONNX export lenses returned

**Date:** 2026-09-01  
**Phase:** MVF5  
**Truth status:** established-bounded; implemented-exact; source-inspected; measured

[established-bounded; implemented-exact] `export_morphology` accepts a package, explicit codec,
receiver family, and purpose. Only rested-inference requests within the package receiver family can
return exact artifacts. Cultivation and world-return execution requests refuse; unsupported
receivers refuse. No filename, digest, model label, or export version participates in native
routing or capability.

[established-bounded; implemented-exact] The Safetensors lens emits a valid U8 tensor family under
`holonics.native-morphology.safetensors.v1`: complete canonical package bytes and derived anatomy
bytes, contiguous offsets, declared shapes, and string metadata marking exactness and exterior-only
identity. Import reads the package tensor and completely revalidates the native package.

[established-bounded; implemented-exact] The ONNX lens emits IR 14 under domain `org.holonics`,
opset 1, with an explicit `RestedMorphology` custom node, package/anatomy initializers, graph
input/output, producer/model versions, and Holonics metadata. Import uses the standing lossless ONNX
chart, verifies IR/domain/opset/schema and initializer type/shape, then revalidates the complete
package.

[established-bounded; implemented-exact] `project_common_anatomy` exports only a common derived
anatomy. It returns projected status only when two package anatomies and artifacts agree and one
shared inference configuration has different observations. The complete two-package reconstruction
fibre and that shortest available configuration separator travel in the return. Anatomically
different or unseparated pairs refuse.

[established-bounded; implemented-exact; source-inspected; measured] Exact Safetensors and ONNX
round-trip controls, two projected-anatomy controls, and cultivation/world/receiver refusals passed.
The generated 5,937-octet Safetensors artifact opened through Safetensors 0.7.0 with both tensors,
declared shapes, and complete metadata. The 5,995-octet ONNX artifact returned IR 14,
`org.holonics` opset 1, one node, two initializers, and exact re-import through the repository's
lossless parser. Every engine/life target type-checked; life returned 476 passed, zero failed, and
14 ignored.
