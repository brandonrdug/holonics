use super::*;

impl CudaLiveCurrentExecutor {
    pub fn device_name(&self) -> &str {
        &self.device_name
    }

    pub const fn stack_limit_bytes(&self) -> usize {
        self.stack_limit_bytes
    }

    pub const fn stack_growths(&self) -> u64 {
        self.stack_growths
    }

    pub const fn launches(&self) -> u64 {
        self.launches
    }

    pub const fn contact_launches(&self) -> u64 {
        self.contact_launches
    }

    pub const fn parallel_contact_lanes(&self) -> u64 {
        self.parallel_contact_lanes
    }

    pub const fn resource_retries(&self) -> u64 {
        self.resource_retries
    }

    pub const fn directed_contacts(&self) -> u64 {
        self.directed_contacts
    }

    pub const fn standing_full_mounts(&self) -> u64 {
        self.standing_full_mounts
    }

    pub const fn carrier_full_mounts(&self) -> u64 {
        self.carrier_full_mounts
    }

    pub const fn standing_cpu_words(&self) -> u64 {
        self.standing_cpu_words
    }

    pub const fn standing_device_words(&self) -> u64 {
        self.standing_device_words
    }

    pub const fn carrier_cpu_words(&self) -> u64 {
        self.carrier_cpu_words
    }

    pub const fn carrier_device_words(&self) -> u64 {
        self.carrier_device_words
    }

    pub fn resident_lineages(&self) -> usize {
        self.resident_lineages.len()
    }

    pub fn resident_standing_words(&self) -> usize {
        self.resident_standing
            .as_ref()
            .map_or(0, |standing| standing.device.len())
    }

    pub fn resident_carrier_words(&self) -> usize {
        self.resident_lineages
            .values()
            .fold(0usize, |words, carrier| {
                words
                    .saturating_add(carrier.carrier.len())
                    .saturating_add(carrier.overflow.len())
                    .saturating_add(carrier.counts.len())
            })
    }
}
