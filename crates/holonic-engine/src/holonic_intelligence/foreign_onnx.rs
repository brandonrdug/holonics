use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use thiserror::Error;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProtobufWireType {
    Varint,
    Fixed64,
    LengthDelimited,
    Fixed32,
}

/// One exact protobuf field range into the retained ONNX byte occurrence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProtobufFieldRange {
    pub number: u32,
    pub wire_type: ProtobufWireType,
    pub encoded: Range<usize>,
    pub payload: Range<usize>,
    pub varint: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OnnxOperatorSetChart {
    pub domain: String,
    pub version: i64,
    pub fields: Vec<ProtobufFieldRange>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OnnxValueChart {
    pub name: String,
    pub fields: Vec<ProtobufFieldRange>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OnnxNodeChart {
    pub name: String,
    pub operation: String,
    pub domain: String,
    pub overload: String,
    pub inputs: Vec<String>,
    pub outputs: Vec<String>,
    pub attribute_population: usize,
    pub metadata: BTreeMap<String, String>,
    pub fields: Vec<ProtobufFieldRange>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OnnxTensorChart {
    pub name: String,
    pub dimensions: Vec<u64>,
    pub data_type: u32,
    pub raw_data: Option<Range<usize>>,
    pub typed_data: Vec<Range<usize>>,
    pub external_data: BTreeMap<String, String>,
    pub data_location: u32,
    pub fields: Vec<ProtobufFieldRange>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OnnxFunctionChart {
    pub name: String,
    pub domain: String,
    pub overload: String,
    pub node_population: usize,
    pub fields: Vec<ProtobufFieldRange>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OnnxGraphChart {
    pub name: String,
    pub nodes: Vec<OnnxNodeChart>,
    pub initializers: Vec<OnnxTensorChart>,
    pub sparse_initializer_population: usize,
    pub inputs: Vec<OnnxValueChart>,
    pub outputs: Vec<OnnxValueChart>,
    pub value_information: Vec<OnnxValueChart>,
    pub quantization_annotation_population: usize,
    pub metadata: BTreeMap<String, String>,
    pub fields: Vec<ProtobufFieldRange>,
}

/// A lossless ONNX exterior chart. Typed projections point into `raw`; unknown fields remain there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForeignOnnxChart {
    pub address: String,
    pub raw: Vec<u8>,
    pub ir_version: i64,
    pub producer_name: String,
    pub producer_version: String,
    pub domain: String,
    pub model_version: i64,
    pub graph: OnnxGraphChart,
    pub operator_sets: Vec<OnnxOperatorSetChart>,
    pub metadata: BTreeMap<String, String>,
    pub training_information_population: usize,
    pub functions: Vec<OnnxFunctionChart>,
    pub device_configuration_population: usize,
    pub fields: Vec<ProtobufFieldRange>,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ForeignOnnxError {
    #[error("{address}: malformed ONNX protobuf at octet {at}: {reason}")]
    Malformed {
        address: String,
        at: usize,
        reason: String,
    },
    #[error("{address}: required ONNX field {field} is absent")]
    Missing {
        address: String,
        field: &'static str,
    },
    #[error("{address}: singular ONNX field {field} occurs more than once")]
    Duplicate {
        address: String,
        field: &'static str,
    },
    #[error("{address}: ONNX field {field} is not UTF-8")]
    NotText {
        address: String,
        field: &'static str,
    },
    #[error("{address}: ONNX graph repeats value or initializer name {name:?}")]
    RepeatedName { address: String, name: String },
    #[error("{address}: external tensor {tensor:?} has no location or also carries inline data")]
    ExternalTensor { address: String, tensor: String },
}

impl ForeignOnnxChart {
    pub fn read(address: impl Into<String>, raw: Vec<u8>) -> Result<Self, ForeignOnnxError> {
        let address = address.into();
        let fields = parse_fields(&address, &raw, 0..raw.len())?;
        let ir_version = required_varint(&address, &fields, 1, "ModelProto.ir_version")? as i64;
        let producer_name = optional_text(&address, &raw, &fields, 2, "ModelProto.producer_name")?;
        let producer_version =
            optional_text(&address, &raw, &fields, 3, "ModelProto.producer_version")?;
        let domain = optional_text(&address, &raw, &fields, 4, "ModelProto.domain")?;
        let model_version =
            optional_varint(&address, &fields, 5, "ModelProto.model_version")?.unwrap_or(0) as i64;
        let graph_field = required_field(&address, &fields, 7, "ModelProto.graph")?;
        let graph = parse_graph(&address, &raw, graph_field.payload.clone())?;
        let operator_sets = fields
            .iter()
            .filter(|field| field.number == 8)
            .map(|field| parse_operator_set(&address, &raw, field.payload.clone()))
            .collect::<Result<Vec<_>, _>>()?;
        if operator_sets.is_empty() {
            return Err(ForeignOnnxError::Missing {
                address,
                field: "ModelProto.opset_import",
            });
        }
        let metadata = parse_metadata(&address, &raw, &fields, 14)?;
        let functions = fields
            .iter()
            .filter(|field| field.number == 25)
            .map(|field| parse_function(&address, &raw, field.payload.clone()))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            address,
            raw,
            ir_version,
            producer_name,
            producer_version,
            domain,
            model_version,
            graph,
            operator_sets,
            metadata,
            training_information_population: fields
                .iter()
                .filter(|field| field.number == 20)
                .count(),
            functions,
            device_configuration_population: fields
                .iter()
                .filter(|field| field.number == 26)
                .count(),
            fields,
        })
    }
}

fn parse_graph(
    address: &str,
    raw: &[u8],
    range: Range<usize>,
) -> Result<OnnxGraphChart, ForeignOnnxError> {
    let fields = parse_fields(address, raw, range)?;
    let name = optional_text(address, raw, &fields, 2, "GraphProto.name")?;
    let nodes = fields
        .iter()
        .filter(|field| field.number == 1)
        .map(|field| parse_node(address, raw, field.payload.clone()))
        .collect::<Result<Vec<_>, _>>()?;
    let initializers = fields
        .iter()
        .filter(|field| field.number == 5)
        .map(|field| parse_tensor(address, raw, field.payload.clone()))
        .collect::<Result<Vec<_>, _>>()?;
    let inputs = parse_values(address, raw, &fields, 11)?;
    let outputs = parse_values(address, raw, &fields, 12)?;
    let value_information = parse_values(address, raw, &fields, 13)?;
    require_unique_names(
        address,
        initializers.iter().map(|tensor| tensor.name.as_str()),
    )?;
    require_unique_names(address, inputs.iter().map(|value| value.name.as_str()))?;
    require_unique_names(address, outputs.iter().map(|value| value.name.as_str()))?;
    require_unique_names(
        address,
        value_information.iter().map(|value| value.name.as_str()),
    )?;
    Ok(OnnxGraphChart {
        name,
        nodes,
        initializers,
        sparse_initializer_population: fields.iter().filter(|field| field.number == 15).count(),
        inputs,
        outputs,
        value_information,
        quantization_annotation_population: fields
            .iter()
            .filter(|field| field.number == 14)
            .count(),
        metadata: parse_metadata(address, raw, &fields, 16)?,
        fields,
    })
}

fn parse_node(
    address: &str,
    raw: &[u8],
    range: Range<usize>,
) -> Result<OnnxNodeChart, ForeignOnnxError> {
    let fields = parse_fields(address, raw, range)?;
    Ok(OnnxNodeChart {
        name: optional_text(address, raw, &fields, 3, "NodeProto.name")?,
        operation: required_text(address, raw, &fields, 4, "NodeProto.op_type")?,
        domain: optional_text(address, raw, &fields, 7, "NodeProto.domain")?,
        overload: optional_text(address, raw, &fields, 8, "NodeProto.overload")?,
        inputs: repeated_text(address, raw, &fields, 1, "NodeProto.input")?,
        outputs: repeated_text(address, raw, &fields, 2, "NodeProto.output")?,
        attribute_population: fields.iter().filter(|field| field.number == 5).count(),
        metadata: parse_metadata(address, raw, &fields, 9)?,
        fields,
    })
}

fn parse_tensor(
    address: &str,
    raw: &[u8],
    range: Range<usize>,
) -> Result<OnnxTensorChart, ForeignOnnxError> {
    let fields = parse_fields(address, raw, range)?;
    let name = required_text(address, raw, &fields, 8, "TensorProto.name")?;
    let dimensions = packed_varints(address, raw, &fields, 1, "TensorProto.dims")?;
    if dimensions
        .iter()
        .any(|dimension| *dimension > i64::MAX as u64)
    {
        return Err(ForeignOnnxError::Malformed {
            address: address.to_owned(),
            at: fields.first().map_or(0, |field| field.encoded.start),
            reason: format!("tensor {name:?} has a negative or overflowing dimension"),
        });
    }
    let data_type = required_varint(address, &fields, 2, "TensorProto.data_type")?;
    let data_type = u32::try_from(data_type).map_err(|_| ForeignOnnxError::Malformed {
        address: address.to_owned(),
        at: fields.first().map_or(0, |field| field.encoded.start),
        reason: format!("tensor {name:?} has an overflowing data type"),
    })?;
    let raw_data = optional_field(address, &fields, 9, "TensorProto.raw_data")?
        .map(|field| field.payload.clone());
    let typed_data = fields
        .iter()
        .filter(|field| matches!(field.number, 4 | 5 | 6 | 7 | 10 | 11))
        .map(|field| field.payload.clone())
        .collect::<Vec<_>>();
    let external_data = parse_metadata(address, raw, &fields, 13)?;
    let data_location =
        optional_varint(address, &fields, 14, "TensorProto.data_location")?.unwrap_or(0) as u32;
    if data_location == 1
        && (!external_data.contains_key("location") || raw_data.is_some() || !typed_data.is_empty())
    {
        return Err(ForeignOnnxError::ExternalTensor {
            address: address.to_owned(),
            tensor: name,
        });
    }
    Ok(OnnxTensorChart {
        name,
        dimensions,
        data_type,
        raw_data,
        typed_data,
        external_data,
        data_location,
        fields,
    })
}

fn parse_values(
    address: &str,
    raw: &[u8],
    fields: &[ProtobufFieldRange],
    number: u32,
) -> Result<Vec<OnnxValueChart>, ForeignOnnxError> {
    fields
        .iter()
        .filter(|field| field.number == number)
        .map(|field| {
            let fields = parse_fields(address, raw, field.payload.clone())?;
            Ok(OnnxValueChart {
                name: required_text(address, raw, &fields, 1, "ValueInfoProto.name")?,
                fields,
            })
        })
        .collect()
}

fn parse_operator_set(
    address: &str,
    raw: &[u8],
    range: Range<usize>,
) -> Result<OnnxOperatorSetChart, ForeignOnnxError> {
    let fields = parse_fields(address, raw, range)?;
    Ok(OnnxOperatorSetChart {
        domain: optional_text(address, raw, &fields, 1, "OperatorSetIdProto.domain")?,
        version: required_varint(address, &fields, 2, "OperatorSetIdProto.version")? as i64,
        fields,
    })
}

fn parse_function(
    address: &str,
    raw: &[u8],
    range: Range<usize>,
) -> Result<OnnxFunctionChart, ForeignOnnxError> {
    let fields = parse_fields(address, raw, range)?;
    Ok(OnnxFunctionChart {
        name: required_text(address, raw, &fields, 1, "FunctionProto.name")?,
        domain: optional_text(address, raw, &fields, 10, "FunctionProto.domain")?,
        overload: optional_text(address, raw, &fields, 13, "FunctionProto.overload")?,
        node_population: fields.iter().filter(|field| field.number == 7).count(),
        fields,
    })
}

fn parse_metadata(
    address: &str,
    raw: &[u8],
    fields: &[ProtobufFieldRange],
    number: u32,
) -> Result<BTreeMap<String, String>, ForeignOnnxError> {
    let mut metadata = BTreeMap::new();
    for field in fields.iter().filter(|field| field.number == number) {
        let entry = parse_fields(address, raw, field.payload.clone())?;
        let key = required_text(address, raw, &entry, 1, "StringStringEntryProto.key")?;
        let value = required_text(address, raw, &entry, 2, "StringStringEntryProto.value")?;
        if metadata.insert(key.clone(), value).is_some() {
            return Err(ForeignOnnxError::RepeatedName {
                address: address.to_owned(),
                name: key,
            });
        }
    }
    Ok(metadata)
}

fn require_unique_names<'a>(
    address: &str,
    names: impl IntoIterator<Item = &'a str>,
) -> Result<(), ForeignOnnxError> {
    let mut seen = BTreeSet::new();
    for name in names {
        if !seen.insert(name) {
            return Err(ForeignOnnxError::RepeatedName {
                address: address.to_owned(),
                name: name.to_owned(),
            });
        }
    }
    Ok(())
}

fn parse_fields(
    address: &str,
    raw: &[u8],
    range: Range<usize>,
) -> Result<Vec<ProtobufFieldRange>, ForeignOnnxError> {
    if range.start > range.end || range.end > raw.len() {
        return malformed(
            address,
            range.start,
            "message range lies outside the source",
        );
    }
    let mut at = range.start;
    let mut fields = Vec::new();
    while at < range.end {
        let encoded_from = at;
        let tag = read_varint(address, raw, &mut at, range.end)?;
        let number = u32::try_from(tag >> 3)
            .ok()
            .filter(|number| *number > 0)
            .ok_or_else(|| ForeignOnnxError::Malformed {
                address: address.to_owned(),
                at: encoded_from,
                reason: "field number is zero or overflowing".to_owned(),
            })?;
        let wire = (tag & 7) as u8;
        let (wire_type, payload, varint) = match wire {
            0 => {
                let from = at;
                let value = read_varint(address, raw, &mut at, range.end)?;
                (ProtobufWireType::Varint, from..at, Some(value))
            }
            1 => {
                let to = at
                    .checked_add(8)
                    .ok_or_else(|| ForeignOnnxError::Malformed {
                        address: address.to_owned(),
                        at,
                        reason: "fixed64 range overflow".to_owned(),
                    })?;
                if to > range.end {
                    return malformed(address, at, "fixed64 field is truncated");
                }
                let payload = at..to;
                at = to;
                (ProtobufWireType::Fixed64, payload, None)
            }
            2 => {
                let length = read_varint(address, raw, &mut at, range.end)?;
                let length = usize::try_from(length).map_err(|_| ForeignOnnxError::Malformed {
                    address: address.to_owned(),
                    at,
                    reason: "length-delimited field exceeds the host extent".to_owned(),
                })?;
                let to = at
                    .checked_add(length)
                    .ok_or_else(|| ForeignOnnxError::Malformed {
                        address: address.to_owned(),
                        at,
                        reason: "length-delimited field overflows".to_owned(),
                    })?;
                if to > range.end {
                    return malformed(address, at, "length-delimited field is truncated");
                }
                let payload = at..to;
                at = to;
                (ProtobufWireType::LengthDelimited, payload, None)
            }
            5 => {
                let to = at
                    .checked_add(4)
                    .ok_or_else(|| ForeignOnnxError::Malformed {
                        address: address.to_owned(),
                        at,
                        reason: "fixed32 range overflow".to_owned(),
                    })?;
                if to > range.end {
                    return malformed(address, at, "fixed32 field is truncated");
                }
                let payload = at..to;
                at = to;
                (ProtobufWireType::Fixed32, payload, None)
            }
            _ => return malformed(address, at, "group or unknown wire type is not admitted"),
        };
        fields.push(ProtobufFieldRange {
            number,
            wire_type,
            encoded: encoded_from..at,
            payload,
            varint,
        });
    }
    Ok(fields)
}

fn read_varint(
    address: &str,
    raw: &[u8],
    at: &mut usize,
    end: usize,
) -> Result<u64, ForeignOnnxError> {
    let from = *at;
    let mut value = 0u64;
    for shift in (0..70).step_by(7) {
        let Some(byte) = raw.get(*at).copied().filter(|_| *at < end) else {
            return malformed(address, from, "varint is truncated");
        };
        *at += 1;
        if shift == 63 && byte > 1 {
            return malformed(address, from, "varint exceeds 64 bits");
        }
        value |= u64::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return Ok(value);
        }
    }
    malformed(address, from, "varint exceeds ten octets")
}

fn required_field<'a>(
    address: &str,
    fields: &'a [ProtobufFieldRange],
    number: u32,
    name: &'static str,
) -> Result<&'a ProtobufFieldRange, ForeignOnnxError> {
    optional_field(address, fields, number, name)?.ok_or_else(|| ForeignOnnxError::Missing {
        address: address.to_owned(),
        field: name,
    })
}

fn optional_field<'a>(
    address: &str,
    fields: &'a [ProtobufFieldRange],
    number: u32,
    name: &'static str,
) -> Result<Option<&'a ProtobufFieldRange>, ForeignOnnxError> {
    let mut matches = fields.iter().filter(|field| field.number == number);
    let first = matches.next();
    if matches.next().is_some() {
        return Err(ForeignOnnxError::Duplicate {
            address: address.to_owned(),
            field: name,
        });
    }
    Ok(first)
}

fn required_varint(
    address: &str,
    fields: &[ProtobufFieldRange],
    number: u32,
    name: &'static str,
) -> Result<u64, ForeignOnnxError> {
    optional_varint(address, fields, number, name)?.ok_or_else(|| ForeignOnnxError::Missing {
        address: address.to_owned(),
        field: name,
    })
}

fn optional_varint(
    address: &str,
    fields: &[ProtobufFieldRange],
    number: u32,
    name: &'static str,
) -> Result<Option<u64>, ForeignOnnxError> {
    let Some(field) = optional_field(address, fields, number, name)? else {
        return Ok(None);
    };
    field
        .varint
        .map(Some)
        .ok_or_else(|| ForeignOnnxError::Malformed {
            address: address.to_owned(),
            at: field.encoded.start,
            reason: format!("{name} is not a varint"),
        })
}

fn required_text(
    address: &str,
    raw: &[u8],
    fields: &[ProtobufFieldRange],
    number: u32,
    name: &'static str,
) -> Result<String, ForeignOnnxError> {
    let field = required_field(address, fields, number, name)?;
    text(address, raw, field, name)
}

fn optional_text(
    address: &str,
    raw: &[u8],
    fields: &[ProtobufFieldRange],
    number: u32,
    name: &'static str,
) -> Result<String, ForeignOnnxError> {
    let Some(field) = optional_field(address, fields, number, name)? else {
        return Ok(String::new());
    };
    text(address, raw, field, name)
}

fn repeated_text(
    address: &str,
    raw: &[u8],
    fields: &[ProtobufFieldRange],
    number: u32,
    name: &'static str,
) -> Result<Vec<String>, ForeignOnnxError> {
    fields
        .iter()
        .filter(|field| field.number == number)
        .map(|field| text(address, raw, field, name))
        .collect()
}

fn text(
    address: &str,
    raw: &[u8],
    field: &ProtobufFieldRange,
    name: &'static str,
) -> Result<String, ForeignOnnxError> {
    if field.wire_type != ProtobufWireType::LengthDelimited {
        return malformed(
            address,
            field.encoded.start,
            "text field has the wrong wire type",
        );
    }
    std::str::from_utf8(&raw[field.payload.clone()])
        .map(str::to_owned)
        .map_err(|_| ForeignOnnxError::NotText {
            address: address.to_owned(),
            field: name,
        })
}

fn packed_varints(
    address: &str,
    raw: &[u8],
    fields: &[ProtobufFieldRange],
    number: u32,
    name: &'static str,
) -> Result<Vec<u64>, ForeignOnnxError> {
    let mut values = Vec::new();
    for field in fields.iter().filter(|field| field.number == number) {
        match field.wire_type {
            ProtobufWireType::Varint => values.push(field.varint.expect("varint field")),
            ProtobufWireType::LengthDelimited => {
                let mut at = field.payload.start;
                while at < field.payload.end {
                    values.push(read_varint(address, raw, &mut at, field.payload.end)?);
                }
            }
            _ => {
                return malformed(
                    address,
                    field.encoded.start,
                    &format!("{name} has the wrong wire type"),
                )
            }
        }
    }
    Ok(values)
}

fn malformed<T>(address: &str, at: usize, reason: &str) -> Result<T, ForeignOnnxError> {
    Err(ForeignOnnxError::Malformed {
        address: address.to_owned(),
        at,
        reason: reason.to_owned(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn varint(mut value: u64) -> Vec<u8> {
        let mut bytes = Vec::new();
        loop {
            let mut byte = (value & 0x7f) as u8;
            value >>= 7;
            if value != 0 {
                byte |= 0x80;
            }
            bytes.push(byte);
            if value == 0 {
                return bytes;
            }
        }
    }

    fn varint_field(number: u32, value: u64) -> Vec<u8> {
        let mut field = varint(u64::from(number) << 3);
        field.extend(varint(value));
        field
    }

    fn bytes_field(number: u32, value: &[u8]) -> Vec<u8> {
        let mut field = varint((u64::from(number) << 3) | 2);
        field.extend(varint(value.len() as u64));
        field.extend(value);
        field
    }

    fn message(fields: impl IntoIterator<Item = Vec<u8>>) -> Vec<u8> {
        fields.into_iter().flatten().collect()
    }

    #[test]
    fn onnx_model_retains_graph_nodes_tensor_payload_opsets_and_unknown_fields() {
        let node = message([
            bytes_field(1, b"x"),
            bytes_field(1, b"weight"),
            bytes_field(2, b"y"),
            bytes_field(3, b"junction"),
            bytes_field(4, b"Add"),
        ]);
        let tensor = message([
            varint_field(1, 1),
            varint_field(2, 16),
            bytes_field(8, b"weight"),
            bytes_field(9, &[0, 0]),
        ]);
        let input = bytes_field(1, b"x");
        let output = bytes_field(1, b"y");
        let graph = message([
            bytes_field(1, &node),
            bytes_field(2, b"bounded-graph"),
            bytes_field(5, &tensor),
            bytes_field(11, &input),
            bytes_field(12, &output),
        ]);
        let opset = message([bytes_field(1, b""), varint_field(2, 28)]);
        let model = message([
            varint_field(1, 10),
            bytes_field(2, b"holonics-test"),
            bytes_field(7, &graph),
            bytes_field(8, &opset),
            bytes_field(99, b"retained-unknown"),
        ]);
        let chart = ForeignOnnxChart::read("model.onnx", model.clone()).expect("ONNX chart");
        assert_eq!(chart.raw, model);
        assert_eq!(chart.ir_version, 10);
        assert_eq!(chart.operator_sets[0].version, 28);
        assert_eq!(chart.graph.nodes[0].operation, "Add");
        assert_eq!(chart.graph.initializers[0].dimensions, vec![1]);
        assert_eq!(chart.graph.initializers[0].data_type, 16);
        let payload = chart.graph.initializers[0].raw_data.clone().unwrap();
        assert_eq!(&chart.raw[payload], &[0, 0]);
        assert!(chart.fields.iter().any(|field| field.number == 99));
    }

    #[test]
    fn external_tensor_without_location_is_refused_by_name() {
        let tensor = message([
            varint_field(1, 1),
            varint_field(2, 16),
            bytes_field(8, b"weight"),
            varint_field(14, 1),
        ]);
        let graph = message([bytes_field(2, b"g"), bytes_field(5, &tensor)]);
        let opset = message([varint_field(2, 28)]);
        let model = message([
            varint_field(1, 10),
            bytes_field(7, &graph),
            bytes_field(8, &opset),
        ]);
        assert!(matches!(
            ForeignOnnxChart::read("external.onnx", model),
            Err(ForeignOnnxError::ExternalTensor { tensor, .. }) if tensor == "weight"
        ));
    }

    #[test]
    fn duplicate_model_graph_is_refused_instead_of_overwritten() {
        let graph = bytes_field(2, b"g");
        let opset = message([varint_field(2, 28)]);
        let model = message([
            varint_field(1, 10),
            bytes_field(7, &graph),
            bytes_field(7, &graph),
            bytes_field(8, &opset),
        ]);
        assert!(matches!(
            ForeignOnnxChart::read("duplicate.onnx", model),
            Err(ForeignOnnxError::Duplicate { field, .. }) if field == "ModelProto.graph"
        ));
    }
}
