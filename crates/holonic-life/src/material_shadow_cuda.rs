//! Mandatory CUDA reader for the recurrence geometry of raw material passages.
//!
//! The card returns the prior-equal distance at every situated octet plus a fixed profile summary.
//! Exact attachment uses the complete length-prefixed returned field; the hashes summarize and
//! never identify it. No tokenizer, language label, parser, or source surface crosses into the
//! field. The cpu stages bytes and reads the return; it has no implementation of the semantic deed.

use core::ffi::c_void;

use mount::{Context, Device, DeviceBuffer, Module, Stream, SOMA_PTX};
use serde::Serialize;
use soma_abi::material_shadow_cuda as wire;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct MaterialShadowKey(Vec<u32>);

impl MaterialShadowKey {
    fn from_distance_field(field: &[u32]) -> Result<Self, String> {
        let extent = u32::try_from(field.len())
            .map_err(|_| "the material-shadow key extent exceeds u32".to_owned())?;
        let mut words = Vec::with_capacity(field.len() + 1);
        words.push(extent);
        words.extend_from_slice(field);
        Ok(Self(words))
    }

    pub fn words(&self) -> &[u32] {
        &self.0
    }

    pub fn padded_words(&self, width: usize) -> Result<Vec<u32>, String> {
        if self.0.len() > width {
            return Err("the material-shadow key exceeds its declared device width".to_owned());
        }
        let mut words = self.0.clone();
        words.resize(width, 0);
        Ok(words)
    }

    pub(crate) fn from_words(words: Vec<u32>) -> Result<Self, String> {
        let Some(extent) = words.first().copied().map(|extent| extent as usize) else {
            return Err("the material-shadow key is empty".to_owned());
        };
        if extent + 1 != words.len() {
            return Err("the material-shadow key extent disagrees with its field".to_owned());
        }
        Ok(Self(words))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MaterialShadowReading {
    pub key: MaterialShadowKey,
    /// Fixed profile returned by the card. Its hashes are never used as attachment identity.
    pub summary: [u32; wire::SUMMARY_WORDS],
    /// At position `i`, zero means a first occurrence; otherwise this is the exact distance to the
    /// immediately prior equal octet.
    pub prior_equal_distance: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MaterialShadowCudaReceipt {
    pub schema: String,
    pub device: String,
    pub passages: usize,
    pub material_octets: usize,
    pub shadow_words: usize,
    pub launch_ordinal: u64,
    pub grid: [u32; 3],
    pub block: [u32; 3],
    pub cpu_semantic_replay: bool,
}

pub struct CudaMaterialShadowExecutor {
    module: Module,
    device_name: String,
    census: mount::cuda::LaunchCensus,
    launches: u64,
    stream: Stream,
    context: Context,
}

impl CudaMaterialShadowExecutor {
    pub fn new(device_ordinal: i32) -> Result<Self, String> {
        mount::cuda::init().map_err(|error| error.to_string())?;
        let device = Device::get(device_ordinal).map_err(|error| error.to_string())?;
        let census = device.launch_census().map_err(|error| error.to_string())?;
        let context = Context::create(&device).map_err(|error| error.to_string())?;
        let module = Module::load_ptx(SOMA_PTX).map_err(|error| error.to_string())?;
        module
            .function(wire::ENTRY_SYMBOL)
            .map_err(|error| error.to_string())?;
        let stream = Stream::create().map_err(|error| error.to_string())?;
        Ok(Self {
            module,
            device_name: device.name,
            census,
            launches: 0,
            stream,
            context,
        })
    }

    pub fn device_name(&self) -> &str {
        &self.device_name
    }

    pub const fn launches(&self) -> u64 {
        self.launches
    }

    pub fn read(
        &mut self,
        passages: &[impl AsRef<[u8]>],
    ) -> Result<(Vec<MaterialShadowReading>, MaterialShadowCudaReceipt), String> {
        if passages.is_empty() || passages.iter().any(|passage| passage.as_ref().is_empty()) {
            return Err("a material-shadow front must carry nonempty passages".to_owned());
        }
        self.context
            .make_current()
            .map_err(|error| error.to_string())?;
        let material_octets = passages.iter().try_fold(0usize, |total, passage| {
            total
                .checked_add(passage.as_ref().len())
                .ok_or_else(|| "the material-shadow front overflowed".to_owned())
        })?;
        let mut descriptors = Vec::with_capacity(passages.len() * wire::INPUT_WORDS);
        let mut material = Vec::with_capacity(material_octets);
        let mut offset = 0usize;
        for passage in passages {
            let bytes = passage.as_ref();
            descriptors.push(
                u32::try_from(offset)
                    .map_err(|_| "the material-shadow offset exceeds u32".to_owned())?,
            );
            descriptors.push(
                u32::try_from(bytes.len())
                    .map_err(|_| "a material-shadow passage exceeds u32".to_owned())?,
            );
            descriptors.push(
                u32::try_from(offset)
                    .map_err(|_| "the material-shadow output offset exceeds u32".to_owned())?,
            );
            material.extend(bytes.iter().map(|byte| u32::from(*byte)));
            offset = offset
                .checked_add(bytes.len())
                .ok_or_else(|| "the material-shadow offset overflowed".to_owned())?;
        }
        let output_words = passages
            .len()
            .checked_mul(wire::OUTPUT_WORDS)
            .ok_or_else(|| "the material-shadow output overflowed".to_owned())?;
        let descriptor_device =
            DeviceBuffer::alloc(descriptors.len()).map_err(|error| error.to_string())?;
        descriptor_device
            .copy_from_slice(&descriptors)
            .map_err(|error| error.to_string())?;
        let material_device =
            DeviceBuffer::alloc(material.len()).map_err(|error| error.to_string())?;
        material_device
            .copy_from_slice(&material)
            .map_err(|error| error.to_string())?;
        let output_device =
            DeviceBuffer::<u32>::alloc_zeroed(output_words).map_err(|error| error.to_string())?;
        let shadow_device = DeviceBuffer::<u32>::alloc_zeroed(material_octets)
            .map_err(|error| error.to_string())?;
        self.context
            .synchronize()
            .map_err(|error| error.to_string())?;
        let function = self
            .module
            .function(wire::ENTRY_SYMBOL)
            .map_err(|error| error.to_string())?;
        let work = u64::try_from(passages.len())
            .map_err(|_| "the material-shadow passage population exceeds u64".to_owned())?;
        let launch = function
            .linear_launch(self.census, work)
            .map_err(|error| error.to_string())?;
        let mut descriptor_pointer = descriptor_device.device_ptr();
        let mut descriptor_len = descriptors.len();
        let mut material_pointer = material_device.device_ptr();
        let mut material_len = material.len();
        let mut output_pointer = output_device.device_ptr();
        let mut output_len = output_words;
        let mut shadow_pointer = shadow_device.device_ptr();
        let mut shadow_len = material_octets;
        let mut x_stride = launch.x_stride;
        let mut parameters = [
            &mut descriptor_pointer as *mut u64 as *mut c_void,
            &mut descriptor_len as *mut usize as *mut c_void,
            &mut material_pointer as *mut u64 as *mut c_void,
            &mut material_len as *mut usize as *mut c_void,
            &mut output_pointer as *mut u64 as *mut c_void,
            &mut output_len as *mut usize as *mut c_void,
            &mut shadow_pointer as *mut u64 as *mut c_void,
            &mut shadow_len as *mut usize as *mut c_void,
            &mut x_stride as *mut u32 as *mut c_void,
        ];
        function
            .launch_on(&self.stream, launch.grid, launch.block, &mut parameters)
            .map_err(|error| error.to_string())?;
        self.stream
            .synchronize()
            .map_err(|error| error.to_string())?;
        let mut returned = vec![0u32; output_words];
        output_device
            .copy_to_slice(&mut returned)
            .map_err(|error| error.to_string())?;
        let mut shadows = vec![0u32; material_octets];
        shadow_device
            .copy_to_slice(&mut shadows)
            .map_err(|error| error.to_string())?;
        let mut readings = Vec::with_capacity(passages.len());
        let mut shadow_at = 0usize;
        for (row, passage) in passages.iter().enumerate() {
            let output_at = row * wire::OUTPUT_WORDS;
            if returned[output_at + wire::OUTPUT_VERSION] != wire::LAYOUT_VERSION
                || returned[output_at + wire::OUTPUT_STATUS] != wire::STATUS_COMPLETE
            {
                return Err(format!(
                    "the card refused material-shadow row {row} with status {}",
                    returned[output_at + wire::OUTPUT_STATUS]
                ));
            }
            let mut summary = [0u32; wire::SUMMARY_WORDS];
            summary.copy_from_slice(
                &returned[output_at + wire::OUTPUT_SUMMARY_AT
                    ..output_at + wire::OUTPUT_SUMMARY_AT + wire::SUMMARY_WORDS],
            );
            let end = shadow_at
                .checked_add(passage.as_ref().len())
                .ok_or_else(|| "the returned shadow cursor overflowed".to_owned())?;
            let prior_equal_distance = shadows[shadow_at..end].to_vec();
            readings.push(MaterialShadowReading {
                key: MaterialShadowKey::from_distance_field(&prior_equal_distance)?,
                summary,
                prior_equal_distance,
            });
            shadow_at = end;
        }
        self.launches = self
            .launches
            .checked_add(1)
            .ok_or_else(|| "the material-shadow launch ordinal overflowed".to_owned())?;
        Ok((
            readings,
            MaterialShadowCudaReceipt {
                schema: "soma-life.material-shadow-cuda-receipt.v1".to_owned(),
                device: self.device_name.clone(),
                passages: passages.len(),
                material_octets,
                shadow_words: shadows.len(),
                launch_ordinal: self.launches,
                grid: [launch.grid.x, launch.grid.y, launch.grid.z],
                block: [launch.block.x, launch.block.y, launch.block.z],
                cpu_semantic_replay: false,
            },
        ))
    }
}

impl Drop for CudaMaterialShadowExecutor {
    fn drop(&mut self) {
        let _ = self.context.make_current();
    }
}

#[cfg(test)]
mod tests {
    use super::MaterialShadowKey;

    #[test]
    fn complete_length_prefixed_fields_do_not_alias_under_device_padding() {
        let shorter = MaterialShadowKey::from_distance_field(&[0, 1]).unwrap();
        let longer = MaterialShadowKey::from_distance_field(&[0, 1, 0]).unwrap();
        let moved = MaterialShadowKey::from_distance_field(&[0, 1, 2]).unwrap();
        assert_eq!(shorter.padded_words(4).unwrap(), vec![2, 0, 1, 0]);
        assert_eq!(longer.padded_words(4).unwrap(), vec![3, 0, 1, 0]);
        assert_eq!(moved.padded_words(4).unwrap(), vec![3, 0, 1, 2]);
        assert_ne!(
            shorter.padded_words(4).unwrap(),
            longer.padded_words(4).unwrap()
        );
        assert_ne!(
            longer.padded_words(4).unwrap(),
            moved.padded_words(4).unwrap()
        );
    }
}
